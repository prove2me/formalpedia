-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5333
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:31:33.355988+00:00
-- url     : https://prove2.me/submissions/c1dad173-149d-4209-b41f-065bc8dcb290

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 958992805 ≤ n < 959172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 958994055 1250 958992805 958992821
    0xc0d06021e13060e060304030e030a0b010905100e07020c15070b10030606171c050d0c021507030605091603090b15041103091e1c090515031003080d 65
    0x1409599060258060381c00e041e600c860803500b07489071003080224980784140d4000002600c090445451501c90303850035140511110030481d0f00d031140e550702e000000ca034050010300a007008800880c05040032071001ca0000c0e0150040010b02031a0302c10420b0907070b40041c1c80b40b10244141d444410304d19010303141c071038144070380f10340034004400900c1841a01d901a0810340c08407402018104500c80c1c80c0c8002c280c00064081100c41e2a5200702c0d54060340481e085a040d00445290404500e0000100d54040030388035a4000c0e4400342e0051041c590801c0360244815500810302d01c5c0421440b03043c94002025140094616108005604440360b5814000d42c020080c2c190440301d040380301d252512030407420064229500e1f01550405c9500c006040f9800150b80c090070000b0050525181c0001c8005420b0595818046562050580300c081448041da910258030155a0300c440303040e1705010a1051240002c0120302e000e0004104108802d400b10096500741d0760301c96112035446a00c60110300c0609101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 958995305 1250 958994055 958994077
    0x1508120309060a051e041e0c0911040e0c0c011b1d09161b0503070506101a03010b07020301111815070c060c0c0302030d120b041e11221a0c0c0d0602 65
    0xc4c52647e420300900f00b6248046407203001d02802000e0080245102038003840c400d00241f02501e9005c02c0010004401800c1c411922900004011004030407007020020b55100c51004607507820148007800405040e500e88900c0705032680407050400444485402c4c284aa82c9003c0101c49000125440000382c040040e00f030b0014200c0c0e07160b4205042c45030b102e15050320480001b5130201000601074071f03036400300c0c00b00404542034141180e180000710003190f03200660032a0706558500300c45680b40c009601600c1086a412020100c0407101c03000d1020b032404040454075101d405100790000a565880011f05480082c03900f101286401e24040c41100c0b242d400082d4035005990a803505640d120035880310200b982c02d014001c1e00362010a1004680104401e080230065880a24440b200c090b023080c0306824442c5122480c1035880c0c000c00040c1c0d103501901c0380c1c0d0650140d40c10402c000700302e48110841541240c5ca60314103810700c10415a00c60000c1011402200c22604020074010b80740d041d41c000c1006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 958996555 1250 958995305 958995353
    0x905030f010501060906020606011209020105120c0a091403030a230a1d060c0604060c120e070e10061d010908010e0c0109081504061508120309060a051e04 68
    0x20400031907010b07150901484001800750749001840510015041d4040c00d01a1140c0780071008480c0181d014000441303041c0d060240402000003060000300b21988210040010140c450040140007400f654056118100c11120369a2102150ba4044100c0e1000c0940341044010a006c01c0c43d44600d59900d10204200d10304045003148200d9000b64100b42d1498207040844188084c000c00c005003130140069001d000c1e8402e0000400288283c0d025a4140138903041035601d40b0285000c039801d886101203000041c2c0c03c0008100b0404418420300c541002c1e10f9101c2701c824a041c204000c2c086100d0130020f200c071001491141d5030342d0b4000c07040040130b0b01d40400240034040242d03e02c1e0369208208180c0f140046e590490003d81391601249948510310b0342116120542c486440381d0000e0641500c60005818a48030002480d43c420000c080e820100d501c0000d889142900b4031030309000c00200100c0080d41400100b04100c603050052031108000b12f001d51000f03803920304050100d0044541c80c503051182c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 958997805 1250 958996555 958996573
    0x1202042312100f0c051c0f1803090e06010c0213020306040b09090606010f08090d030b030705120a0c0801050c12180d020a06150b04170f010207030306030b060f060316090503 76
    0x610303500b08071070030303190a941401564140744040780c5c00e02c640c0402201c0350880c001e0007800140d80b81c2100d030003503002a00205680d29080200a1251000c2c4411000b15000c500c04005100b04c1a0b40c81c2d602140900f001d14000f1525008140701c0150f1840b101603440d800400a9055915680b01d40c14444d4080c15091030703403074626107155a8100555400d8042b42001045400d5284586079980c400d94000010304070800b401401540a002a024981e60502a007040412a42c41c2d0714400040b4800d034000130041c03002c043c240248000c4032600320741c850364140780030400079000030310440d1040c0241e0603804a80d0b507100030a8003841c079030300240c400090243d80158080c040d4005504405e041c002c0e20204202e00032002c0034002a003d51240800041090000300502c010040c0720f50f402c081e1900c2a56003021503807040718220303840108101e010075a41c40e002e106120202c0e0714594001015600c40c440c9140200005072980001040000c40703004821013625446e02c01c018a50003043c0140c01c032a8403403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 958999055 1250 958997805 958997833
    0xd0302070b212d09073c05010f090308070206031e0f190902030c0d020a0e130c09020a200c0a090c17010605040509341202042312 57
    0x11444103620040c0121a2240b591a41050b009001e44d000c00c005110140c60100403840c184c4040b8614440c0f00041c2c5800f01403104440d1500078003103564400c07071522900b010000b504550104105104002606a0600006050004036003429030105d50701516669141240640040140080c1f90701030786c94070034820290400b2030b01a00819184d2041400f04452100c03100880f40d86040c0030754154424002c00c9000e041c64402010451f0000d0101151541c541448036030124080d1041070984694841c544188004043c654020b04a901002d615181c51404000e00020071844031981c0004608290065800104481e4641071740c0500490205eaa56000940080413014442408102c4581c84456590111248141a610345440c1e0505140c20301050004200c0018031400b0f03200801048a0000701220300c0300380e0344200c42440101c100c1c606090082141c00200800c4000e6801072005104010010040b41900019201e41c034030350741410350010300c00c00380715241000702c0e00846409003809 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 959000305 1250 958999055 958999081
    0x90204020a0207140f06120a0b0904110945120702120304050117040309050a0b0a2a060f0207020901030c080c060703050a051b1002180d0302070b21 65
    0x2c0b440c0624413140d2039104801e2007a502d032009250f9074094410001e890f20300590f034880c19005180040c0004200098801090360a2001e42e0241c0e2001800341c610000c0380b401540566010051039585030f045841c51600042140e00d643e501c0c40640118118040c0d600a41c40d07501c0c003640300f50750031240a0501159610344c144e00010099000b0f110080b1a100c20110000456044030410383d542116002c0420b585803c00c10082c004400b0020400c40008503541d07103d03005c8000c0c0901a00c480e43e5140302c0d00003c1d0442d200102c0c000c1c280da42401a083c0701c149500e20401880303411040120794000d040402000078032038401c000f540080c80303030008010f001c1c107040e82c6030564482408031341c00d14000c80d04104c214011340f00c00400280d0104015201e1500c1400644035507603e21404805c000d001004142c1040d05482c0c5c102103441c0d0100d500d00700b5201006c4903100710341055407002040d0303181d51002510782d11280103550201c0300c0000c3c45e5807080b161110078001c0c0103400805c1251400c081c8001800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 959001555 1250 959000305 959000309
    0xb090a121107050a03110d08070510050601020d0e01021c031407050406110615060d091406100e090a02011815120b010e010c1101030204050925020303090a0312090204020a0207 77
    0x2903842800004140f80c24010710752400d50744c015070200e4080d080c480c00c000140100c010200d40105003800702d000012010000d50700004402000400c0c98505040020b1500c801041b000040000d081001d98440c1d030081b42c110b0070701d00c000041940d140080c0030b040c0e000d0684051040c0314004e01d103040022281e80700019006481c025030301d00114402c0c2d01d8181d5610f2005980400d004024119090b601d840c00900506002d02200c10205440d0a0340c1c0340c8000300700d0304d80110300c0d098000c0c2c002c0100042c500f6021034080d081010003049a420003000442c0d40302c15141c1c000707040c05031051824041507000319071000140300e820702d05e07078040c0b080c03941c010400c1c0d10b814200058141007154400703003507000700c440c0b904007074060303680c0b030030418071074031940b0502201c1c03505541070503401c00000ca40d0317031990081a88550582072030309040980301c0c5001d010f5051a0799264007150400d0041c071403806070224420107203d40528003240705100000101006003041c000080d4401e05c002414101c0e1a004076070401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 959002805 1250 959001555 959001587
    0x402090325080f030f090d050a050601061206030c1814070507030801090c0806040b12070b030115030e060a0b041b0c06050a0209010203090d06150810060618030b090a12 74
    0x701035664000559550720078040701d1905410a01c03010f01d103003103c0d6020701103414008003000c20820180e101c0c0d40c00c0400140c1e095070b203500a1001440100c2d005800e81e00d00642c1d500d400c1014519540394483c01c500c45004001030b41c441c050300399200440542121003d040c1502e90a0094142100c0251a0358050401107022a495100000e0310b000d2a204203001002d4548031a0903981da8901000020108030380c4a0345c0c840740d246100b5004400801040b00586090f201c6a984e95050122241003441c090120f40c1c05c0500b4046240c0d106100450500c2d0003602e4013902003003685040001030003a041251051005054110300031845071392040d0114022401006c003000181c0f46c410250099210752100d45001d03074000c020441c2c0a08100c6100720b441ca021f000c00081000c0c200c3c0d0444000701d40c990203c07486501003009960038007282d114050040400781000e4487d90300301020707490f1421382413101404985108002076915001407208000251b40501c40701c4003806000d40c060034810410710581c0e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 959004055 1250 959002805 959002873
    0xf0a0308040c15090311010c021c02010207081c02010608030307170901020705031218010506031f0216030905100207030f12110607030507030e06240310020f041a030402130b04020903 80
    0x91b24a500070313109950800c0e0080d00c0c10484001c00001d42038100c1e201030080707046201b10380300003071144024005002c034a00300e0f000350101040004c00003401e40b41103030810006500204103106d000380e0824980401c5003900c0b10070103170981c1c8607a565402800750450241890000040117070202505040d44c511607c9214441d0780030080b001c408a00303d030011510aa0503602c0010040f2441c1c56034000310044030342440e400361809d403a9600c1d900e00d0100003981200070520840c024041d0386021840d203c103204003807006011141c03840d203841c1e18603200c8040190680e601e03401011076041c8100914071402d4060011202c0500b42500018000c150488016001924100f5244070320400801c1050160940d2050307000c0c000580c000999407002e40d10300e169418851200c10210701344050015054a0301968102a16249001d410306e026480c80f0034058001c660800070480141c1d525030040818032032008000410040000104000340700f41404503502d441039044130219440c03105204140c58039492480 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 959005305 1250 959004055 959004083
    0x409020309032503080708060a050a1d07021504020d060b1c06061202060f22030b0f0606030402030d030b03120c060a1a09040f03020313060503070906020f0a0308040c150903 76
    0x240803c15040140100084c0d05003001c034010718030448000e030300460300034100344074a69070b04009000300100b0392000c880c100000340141802d501106115901603034034005407450b88c0307002700307400c40c3c141c0c4c0103000a00c608607046603882449881e80c0041441302003e064110454802c04c1c0c1051a40c55042c002c54040d0b0405c2d20124a100c400744240307103d070f5405400141070614840107046d240d04441744800010701e480180580940320038030b841006500800c00041c042c18000d40744c0e2001c0c40c0c02007910b0301460041050000503100022058010803061030005031403500c1c2d4001a00703180b00c0c0d04641003079040c04100c4403082c00c008500540940c0304050204081402c001c5001d4043c0100050241e1000d15500003602041c04844020080c07031191040d2440d110012101d04549030310740d0060310028030f01000300441c0c1a000580c8001500d072600081c800c0340103090070240c3d41c840c10a0020301704041b81012074100081c3c2c0c80d40c00007400c01010071010240781c0d50b000802b5900184070a03240e007a40b040c50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 959006555 1250 959005305 959005357
    0x40c0803040b040504020f1e03070f02120723010e03180a21050106030f140c0a030c060f03021306030212100503100207030e030d0801051017060405040305040902030903 74
    0x2103070101d6000c2200780741824900000c000094005100d843d074885820855100b0007003056140b20b800060740e20019403242040d90005044010032168841035500000c0b0b600ea07120301e07403800d13103e1a5500660640d072115040d02c80705000c83d862042c409080d800c1c81c00403049008c0100261901e14100030b5460360072101e207130400c034000c1403501c540b401010307175102841450003010000401a500030400130665544c0c075035800e184642261001d40c0d80004031201003803da50140700b141071101c41212450038007411a00c85d20030b07000561081c0c10920000c00c820300810350198042d12a0322203003a442101d21581c800003d0007941c031407411508a1004100011241c0304060742100c10342d00701500800c061350040044070000c2d40886015400c0c042c42a05a00c0c503a902006a868458510b5440c080a94544070921a510303400c0e941000a0008140303c0319071480020050b10740c0704008039030204190301c60b4141070340c403480b40340c200011034bd00000c02c2245010000004100000300a0500a10400880c4d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 959007805 1250 959006555 959006557
    0x501110406110102090f0409080408160e0708040b070e010c080403061b080c0a03200c15090a2012031207080a0c050a030b01030e0106090b09070807090605030c130b03040c0803 77
    0x4c03103954004002c4406c0d421600b020350114003103520400c001860103448032980b40c40c244c1054802c3c00c10b160081400e2000c403541c2c8003c10742110039810502050304180c1c2d1500055a0010503507000c000300a84180340613889081e0001d030031504081010313525616410408080c005901031500420031001c0b40c0e102a0b0b1291840c0c9102e03400a5418500300720035003001f02c01502c04001c504800940b003444e000e9240c03040342c0c01840c082800d034000300b407a4658612482e16521004085480341e42000c0396490201d24501a08641c0f8034802c1c60960b0302d0801300700010050700401c0300f00d24203880302040030310024605a00c6030380108801d80b9031110a0707482d04039240549581280c40000244144a000926806900800d0390240d05040c0410300394502d50350142100c1456008000b0161140300c03241150601380c003d0b54020140d450140403034070700303e01d01801151285c81840200040000007071041b031301c0e64040d21001540c55454a00607176442002c0c43d01900140d030141c030080712051000030b010758004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 959009055 1250 959007805 959007817
    0xf2209021504031401061203140d0605040c020102130806070c080c07030501051303020105060303162301020f0403110909030f18040c0c12030e0606190e0406061809050a11010c0501110406110102 85
    0x6a82c02c0d85a203270000141c0030542005031a0000140c4504001c98513030755a0140604c0044c1607030005803030709403038012034a01c070b0031b01d6010040b076170442c3c824060341d258006480c20515400040326a52441035040e45032510090794805040c1e540b80138188501e101d1285524042c06010303074001e002c2610f41408043d100e101d500400400d152a844d081c0c80042d07c02c6000c0c032084d000a15010b144204081c0500707099a01602054403a010006000c2c000c0107241d0300d0000600c4026100500709242c408001da40d21b00c103603841c180042c040031440c90180402142d082c520004068000e010110102e04060050719035224115810b520044200a449102c1e00c60064400f064100401403603e551050122a052100725804958003c00340404c48042c88840e10340920b01c44e400019007030389499000d10001400c001000d03d0749042c90042c501040f0002085c82085803c0001c4184000c48000161001142118020500d5007020380c40014020008003600c01c480480c1c07146a2a0007841407a00c0c200e03c030394 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 959010305 1250 959009055 959009057
    0x4030503061206060d0609031e08092e15031e02010e0301140a0b010c020d050c10020f120313140c040b271803040801020304020f2209021504031401061203 68
    0x11745e1854002c0f5100b500406440c0c1d00a040001201d4003038420046940c5040c10000080b54142051202c101c0741003020500881091a01450740c9504802c02d0645100024004402c180c8030305200780040440d501941c011984600c0035005101c0c0d000804e10780141e4018168082466a038801d9003d0030103028142d540f010400035150b080c1c0e42d0f002440005c00c51100e4050402000c140100d0060312100000b0070040d00a50080c82c030125010200250110111103a20464003c1040307941c10707120010704110701070401400c054903a0b858074070030800110300d1000a0113150208200d180b490401080c980e005100030344041c80304003601380c10f00501010040c095550b00680440d40d01c0710041c4d21490903007181046e0400c1d081c0d9000108880d01d1504642c008828a0f5030010600085180270f150300c019030141640c4079134a0703100c15100d01e2400e00e580c107150720055841720b40e40401c660310424020441407904030004d031580c0d107c2c20641040749c0b2030080d1660640c81d22402003400116181c0c500c4c80c407549 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 959011555 1250 959010305 959010319
    0x901030f0f080921070602030702030303010603270b07030501090b10140f07120f080f01090c0c0203030d0f050c0306060715090614040201020d090602030a0309080c060403050306120606 81
    0x4180d8811a1015100805454540043c06529101d80d1124510b40340b401e00e01000411a042140302e1508180301c56102c0070566004022140040e107001c801d0701c0c11a462400d00155001c0501440c03680d1003d0403100e019101f5001c0030f50b5042060700740d9654000c1c41150f40800c8140e03260704900d011229051502da5005920007138030242c2170f1041000001540054406905159031101800c11a4200c600100c8a800c80c90b15000c0e0f07d04c2d0300240f40344001c0310901d0200411b0401c03282046081c4418000d4001d00b41c4c07145140032141d4059240c200d25036602404403941c8003031403a11040100209480020040d051038040340c40c82d030300001600c0c0101d400030543c0746410107590700e002e00c180d0301322406100300791202c2e05000854418400d1201812480d046080c0d180b825200090400c00414200814020700d074405208559000050f40c070020309505000a10b10a1420170035894014000104c2d2103100720303800c110825501c8002b4502901c0d040c0c40d003016a504100116858000488980c4e0300001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 959012805 1250 959011555 959011583
    0x1903030509150402150d060506041d0a090b04030c11132403050d050a2d030f050f01030803062101150f0605090d0f0f0506061201110d02030c22060905090103 69
    0x4400e0041100300c141c8a0300281c0319a540e0b000c1a07ea812a901000b00060803500c052fa0750440d8804099000941260030030011003076a0310100b441401501c00703001c01181c60091010172607d0350640340b02040081103241c00f280d00070390190182010000800c0401c82802e560400d40c0c03031101140d000c1c5c0ea4044c01030007080220a40072070302a00440c82c0700007000a00c42008558684401952501d81000301c0040c641d081c0222026054030400c0142403041d900e824100070041507d50601c07410740e51f02031007050381d984801c4001000c00300708840c10a010741308521902d10200341540180d21403c0351001c80803030b003030355807410780409289813041c0c0002c1030782008003000a1034142c1403a81c00a1084284181d80007503502ca500854440341d1080b65160b01072000d00906160010400740600744280080c0b00301803081001c3c450901504028000301d603004808250384840b41010f58680500004422075074217400c681d42d042040305d5100340c5002c248800d1020a10b4146102e00300c2c107980c0c1201d02504410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 959014055 1250 959012805 959012839
    0x602030a020405060a02010b1008060306070e03100e0105010315110406080c0403081801080f01080c09040c152d0f110a08040b040302090c0403050a03111903030509150402 75
    0x1510092030412519401c00c0003003500c1ea6840c4c050403188401e980005245518001480100d1010359400e03418401c00c1c0040140e50b0b9400158282c3c007024600d07101003000314101c003107460101c22404034951242040354880c0014015030240b412640602c004d40300050b146240c2008841c1c0315480d9031800360040105106403406404840c0d004500032114510345580e0351a019941e40044001487c00010030720b091a070303581d000035003980004160003050190752500d80c0d860b42d1070f00024000c0303000b140d40000040502854040c010010040003188000c1c1818409000740305507071805007094032941e1482075544401c41101605840c00d4103464044548440c0304043d0b61a000d803801010703591090b181c40313900160324074001d0300040401c16080784c1c031542944100302c1c03a04d00051403d44800c109000c01c001103000081c14800c0c80ba01400c158500300101c4020320b040004554001c00310340c552425440030540e05a0040f4481c4030b008050b100f802d812880c00092900301520003a50100c6d403150202014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 959015305 1250 959014055 959014057
    0x1205030307080411060301030c05040b100203041e0b0c010207051c0801060c081b0606040e03180103020918040807030f030b03060106080705090904051e0d050d1a0613060905010c020d0602 82
    0xd0043c2150b4040d1384080000074a6503200741c00c01c807a20a00140e04101c94201405210481d4008850700d1401600c1d030000295a8044d03031040e160001007400b4001d24a00d04680b40304040e0034180c1005e50b9a0780301e41c075120b02035480303040304035024072800746150580a0351501e03200440800d6610340d119a41307000000c6078003280000040c0c0b001c460410244aa021300411040e02e800c0090024151910780782082000b11088601e612110350810420b13a92500c0241e900d802e00a2000d0030010b84840340000070480c00e808110000284c08610018003040c4910440034103c081d03c0795581440503500740c1002c0741030380c030040002c54041d40003c0042c86281c1c007032403d1903800420b92601c14145010032002880b02c1800341d60079101e5030811117500040c0300182c0e04413264104079030300621015003072543c010618456a44d82d204000e5850000d10141c091120711405d141c04000c20442d02c80350601c5805c0b80c001d40c80d11801c408210203d03c0001d40e0350094a0f10030000360000d1181c000040c460300e40c0406 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 959016555 1250 959015305 959015311
    0x14150f030a0b120114070207060c030801050607050a200a090e0303040b06014d031606060306020304080c0d08060303090d0c030c0816050a03110112060f120c120503030708 75
    0x102c5544420303c4a800c110134800c107250f413500603e040035507081c00031004c0d042040541000040044003d02c410219130414000c0f41101d609031030031540c0e0f09050504505228452400070810065440e407046503154010076906984812a550f03045142d8807005801152550221048107400901c0060041854043c50590042c41818a42a000001000f0087c4a42103640405103080035040c540c0260160031400c9030000e0300084d10506031509151416583d0007219002d451001106501d00304002c0399811010066500c41800d5403a81071a00d014030f415040842803611380e12607429200c900c14030801049000e444090041c51620111106002e040c01110209560310280b0400c00800584880c000e10004c04416000d0320841c0c40318184818280702c158040b07442010480e800b8000310340c00d141c003001c20704400d0a12082808a4a110801800c0c080c0c0c02001034500c142c00000b103061a10f10b110603002d01c5010400b00041c2c44071142174520046906c06009a0b000b4000201b50a000e1405560 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 959017805 1250 959016555 959016559
    0x60a17070309170a1106011a0c1507090617160c210f11150601122d0b060f09060705070e0405030711030307050a1e0c14150f030a0b 58
    0x2420700e41515030f19000361142c0401c0034158030001c1c503401d4066121401d64a07001c1c3c050080d0056500d8001c001503488840d80840c41007040000341d00354110410041d203a0244030704c07246901c0503c2c0200d00544604100d10900001c80c45100360312581e04112802548a612a050b180140a03030b0604200e4007510340311812501c40e188100b051440503103039041500620b001d80e5071118000c02080c4000c2c42c0e510124690305481e4800c3c0c0201007040743c801161580000300b03203041b03100e000401c1c160741e0103040501942030000c40c1d5002c11107040c28038041c004e65400c0414905201d1065140184002449440d44d80003000100b0702c200309052030840018038949019000b15082651100320741080d035101901d00729615400016035008102060421000440c1d044014508005054031145c0c0c6031052003c1c0104480403c101071070226080002c0860080c1e04242c0600f01a41c91703130628105c00040c1001e20b403240a03440138082c0300c005004215191050446400750964590b41c80c80c00c090319094034515 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 959019055 1250 959017805 959017811
    0x1101060f03050604020f030a0308070e0f12060105120f03070807030203070206040b040f0605040605030609042d0b100302060415020304181d03090a14060c07031202010b060a170703 79
    0x303036440911190300051402000581034500305481041400030294442a00980142c541040426000402107034044201e080284034401400002000c034490b20f012540e100c4040d00c0d50b85450500010703150305a41c070945480340410078803042e0b59981e070300394a940591030340b0402000000440200c042c0c0011442801143c7c1002c0480d03000664941160300070b8440c07590003040801540701824080e100a0040741410b40c80c044c100f4400900902c07008046a00844c0043c000c5001c000e2540e010712210517402d141a0307490303507100c443c0710309014160a00b515102445004a00c80e09840f6600e1f01c01c407503000b000185018a0110102c03010440504150198041480000b0f48c10408068200704010250303000950400b90b208148510810404400c0d00c5030700c00c1c080c03000140c4a100d1000306071080004404003201000c1e000502c184600c20450280b40074080c4000304101404001c511801c0007500240304201508040c48201e001d07a50309e0300b000505c20113191201081e00e01c260740e0480018034000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 959020305 1250 959019055 959019059
    0x303120e19020f2116150f0509150c0d0206060909030412060e030f21010f2610020405091302090c030612010c0e0a0902040b180d060c030506011b030f110106 69
    0x1e5a0b50301e070a4050440380c0d40060305914044405c2000700c4010303102e10011400007131030744407009081c02d00c41d1703c60800388440000c01c404260341d184010140c02030200082542e030020310b01440c1d111480e40403004054030405011400034901002e50610a410980085080a00e403005000c0e1401585e0000d071420f6544402602d0503401c240f0041c12061030390170416640c0c11301c100300d0722180d200100c2d001d240181c2e14401800300c0034040d0514411582840c2449490304010030022107500388800304a00144242c80e070300c040641c0c258001e041100c02c12100c20300c082e40d8000c0394005030f242c4050003c0d07020226030001640703064a44041c5030403800141c041c004c8101d000c0b42031421640c2c03101015000c103050b024507000a01e8400d03450700243c45005000e5050074500505294640254498401c5010110a502866885038410f003450325800c4002030000a01c1742002a00610090350500c1c0003030310170584441600d400505081d145075255460054000d040e607c22039982c8180e8882600f00d5480b02d02c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 959021555 1250 959020305 959020339
    0xd0e0f060c071a09160608060a03080f130e090105060909030a050d0b1210050711070329150a14010c0209071b05072103050304030f12060303120e19020f 67
    0x32181310b921150028086402c804d105200c940c040c43d40448100201c80c0c0800c5a961502d81d020780460b40d1150000c0d271100c40c1c004030841c550140b10f1010500341025440040c0a036001030b421406140300000800141e1102020311445500850350300403154020403038804042d200b40c2c000e1a0a1510480000750000000d0005104040c0c81c00e00c482c0d00e42c0b1060304a001182c0303d114a5802003900e0800746203401030f1401403603c40c0a64030010b0030a540c2170000c28010000c4410140650004200003081490b05900d0ba0226050144072140909041c22012640c08010018174100c0c000584408902080c0e40d800c0009405000b0080000c00c01958441e000305501004040350700b0344140040c088050400707044e99855600042000c403042504040440446d400c842100c2d00990140f90a141d0071940e4503055495601c603521503104246004400018954072086007031003100e0b24401488808400129103554540a00000503103003161400100103141880c450f40c5140c03c040d0503140c009002e480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 959022805 1250 959021555 959021603
    0xb0a060314010b09240c010f0605011b050c0306090f01060b04030305030a021c110d0e06060132040b0403051b13090204090f030c0b0f0907050112140406020d0e0f060c07 74
    0x285c09103014004a40041907103001e00402c00700041c49170b000c00c44117284c01d00082c90441c0d035402d150300340c09a80d2500014000c040c42410b014040c041c2c21240c031130409450041d44c8100702206d03141e50794a81900803600d000c41c10112401c50f9015a80c081c02e5481e009c145500942c0080511018214403d60000c0030b8ae250303000301544079200f40030391030f1645240100742082c2c0d4074503443c2d0b01850f000320007009481e0380c02006110103109402c04081c1507440501c840800e04c10310700320180400300003040000b58840320344002d1050301e00c02d00940348891182c00700705d940384080000040d803101900c3c800c03d0301c503081c2d5403116464a0004001150014003519101c3c14500441400c1c2d0003c1c0e40d0034106000c1c01088000c9640011030852600b0741842c002254680381e55103400344030304000000c054940c0c2d001c103d4010801021100f01c00341400d060502d0a10300a41c0102c1c040125503041050301c031003090011030601411140b0b4400f40140c1d030f5440440940d0745d4040c0004071150f56280380d802401c1c641c80341c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 959024055 1250 959022805 959022859
    0x702030d1e1b1a09010b12060c130f1818050a1104021c06062c090402010e060315150a17070507080f0a080c16120306180b0a060314010b09 61
    0x401d02c03040d40c101300d0303026821b4030744030a202070180b00f1661000d2070395440002c1095001c600b00c212a6118250a1003a2087c080c0a9004003080041128049034800d44d0b0003102500100000082000d40850202c0c50007802c0b904101800f60b8024104000102d900d1001c403042900e00200014505011008666000340015075142d01e01540c6080c1803100d1500140001400b0309050317800c203602155400c4c49130100c0104550140250154008a0300310790060700b4480304d600c03005042513100c0ca03000f04541490785561071200d20542c221501001c422305140c003150850102547d45000f03080f4040341804008034041c11020030008100301050102d86607201422038401101e1419a94044548004009820141031214880010813030b070030308103c0011001c2c08542d0321400ea41d1900c02c0509042c0d005190503802441d2090910810740c0e8208025400400b103145c2c115003510311140c0f100b904404a0310b4560b00010703505400401401651980c3d40544600000203088401c0441c6103103090803881402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 959025305 1250 959024055 959024093
    0xb030d0509040e060f0a0b0d0b0a05100e16050f0d060b070c050a0f062f0a050609061b03150d06020406030513080405120a020d03050702030d1e1b 64
    0x41521001882d00303000304400408040c0c0104507a081100609aa4660142034200220340e10308012040e0348903080c000c050603030021954030b2146001c03286070028010403507441558003101034001c82e03018030161005e40540c45001c0c0d081c4a14005003c150b80650120250386001602400b072183c0001c00e0b4040c01010781462400651115002e07d0076580000c1c85811861042c55185028840f045880340c21307c0860740d0604d051860200c180e2403003080703001503010a40001e00144c803820081240000c450b5100b6103d0412501c40303036140016191113001c252588852006401001020390301044c0c0559001999254050001c1209800140d41d00d142481c044610a801140400c180c58040c811244d208044074040c4a50010310355940116201d540140342c85071040d01c200c09d000e1802004100002d6501424400042240d070038050650303085054200e22034480c000800c0c510301e11400c00343c10001440c4031740402c80240078400350340e1940d00c603400960003400074941031b0100b46000401002c030044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 959026555 1250 959025305 959025307
    0x6031924141618050f040b1915090602010902180405161410030b01270905011409070207060813080c161503020f030a0f0212070e01020706080402031e010b030d05 71
    0x500c1005840d1050503604444403c81040042205440d81a000030000204650002d401c1040300c0009180c03070101c030f401010030300c1010408192909407019400d5564440d441e02007007695280000c03426680f00800c000d410800c546038811481750f644103590b81262107441a980801c001c44842e40c0c41c1c2c0c0300784d8407440301402113061440540c1000a900450120f0900c2e05115084101c40060700c541003240c0c88020345001424040110810210704402030700d91184c0a01c90b41d65190350740e07a00400b04c0c4a613588030342c01d10401700304d0305800042d00c04200c0702142c503000e005a5941d4000030740031101d00016220002e0401826101003010300c0f0005a08a40d03c0d4108056814182a0644d1410400124051610402134407400e88401800d40c1d41c030641001c80030a40c010722611000c040e0281b0740203211050001400d2201007900044c191205030000e80c01c54040c1581d8000840e280c0d801034501075050740248451440705242c0c0120303114001c116600204149940201092601c580283d134940040d070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 959027805 1250 959026555 959026591
    0xa050c030c0706090f0b1209030c07180b0a05030a0f020609060304031707210510092c010c05030402040207060b22050a1a1003090b07080603192414 65
    0x81c0240703c804c09001045e100480350f6003480c28103001841854070b411004008a00081c958031010022226001010000c1c1c60410b0f58411080381c000c0d044210314031580741002d00980103400c04001134001c442e4010000c0040b1100380c2c0321902d880490713a80c26038111404000c4a03501e51079020086025030302c640d0302c11a41c041840d06556444030050401c40801c80030240340e044203030980f10440c0d120390071050005050b071181c04004507601913590100c0d00590800d04007111141c0101c485188010001f00c0c0c00001c0c43c48800c01d14201c4850702148008a01d084c030226025061540c080e04001d441074000065000001c40011300711043d90340300b024070402c0004180d5840407107014450b001084048280700303907490740922007040c424000310340c1c2c09165440e9181081a109801c0184020342001c4151118141202c1c010942d21088524a000f4800e4405040503070020035560380d84541c011118112880300b09070100c0210121000f0a0140c41e260303800d00e201c0780d21242d40a80200035070046000010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 959029055 1250 959027805 959027807
    0x150705060a111207022406210322030501050a021209070609060e040209030a11011202310306110711010206040f14100f0e0c10301a1c0c0b0a050c030c0706 68
    0x40207030b2948464802314100c03940342144002003980c07000e07003200480b18031004203008100c20030b644580c8003900b990708100a01c0b1000c000e9600400000c04542c021120341d9442c0c02402daa918003912640c0e001503044642041818422000407080d40c10040c0050315002c069030002c1e00d0400601019101c2c0c11348844801825a000347d0004a1041035003070079810500c28810040140c04c3c5080d0307000c80400341e044a4000003034448880da014560040081101d5a1103092907a5260001d00c000c031041e2034824180009036000080701d03446158095008001880c03070b0755920325401c140a80071002407103a87e4030b8058141080c003c00c5900110010001000b100c0710003c0ea2400107112074803070250a001d40e44507015940b11010254049900040204c0c0301c2d42a665a2a051008600300144500d855030351034041c83c00200300721800e1411a25034108000c065001e0050124a080040080c4405181041001142c1c3c01905006805003441030034058801003d50569200390300d02081900680420f01001d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 959030305 1250 959029055 959029069
    0x10c0809010c090e1603091a0912070b190e01060303021f0209010801120839010b0d0f052e0606090506071e02150705060a111207022406 60
    0x2800e40745002440f03103150032a01c01404802800d0014031950340b42061645501a40220758003650001d6044800c25180d01400429001600c040102d400b40c0f20a03110322602c000151070310546c22580c032b0310190700c411100010750b040c80b281c0051000e403580115001a0020301c141c6000b98000d0b0080c02e0300041010302ca001d4a4210003013165000e105008240450340d01c81718072415101100d0382c0460400250074041d80a02502c41003220174924502c10b0110200c13a01444da0780b00c5a069040c4240c1c1526403603244c00d0b1219a030300c0940001c00340606501050309294210040c90240f0255081c0750240f507030403030f11107014540d505c44840c80f40d40311080c0b05995114090090256141c01c0c030050f428480003c040348035905002c0e00e00240203000301010724030802001c4d0f803d68000e10300e0030705405c00c40c07079540075820490041d6418081c4400065039002e240c024407040d0540b42c03d03120318150f100301d030301c640c0f440000d400340d030452042104c520400030700802e103407e030410400c1201400b490031000300486 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 959031555 1250 959030305 959030321
    0x20c061b010e1b06160203010204030804030b100614130e0c030103020102120301051327051605181b12070302090901290309030f0708070b0106051e1b010c080901 71
    0x45a114003442011540e0307401440b20740d04400c0b58213960714010b02d030241c0ea1200000001035850351000500100b0011200010000c40f0301c1005141090341d5a1401c14a40305030500c14071012a04a0003d004800900c000400041e046044009495030300c4400050381160101d1b4400b200c4840080140b044d036070108910b1403811401c81455140d58185008904a10042039003046e02644400d007044e8030f1013400424100000c5201e454100f07a02250034826501c40c4410690340108502580102e60340c00c00b20304041600299103000042501c1d203c160b0314040c941d180110403849014842c540710512103aa00d140a2065540d003d81c545034a901004164081a4424aa00f03031140100301c070b110003500b040034000da11b00449541c0765075a0f68801070a512a02602d01003080d000140807003000350b60006440e00501406e46020141c2c1c030b6060644003441000a420001c00e4040c4894000c0864000106000040c90940200c3d000300f259000d1309517210344c8200c40c0410b04010402c28014424455000c0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 959032805 1250 959031555 959031581
    0x314090a0c050603010305100b0f031006030615050607110301021917010b0405030a1119120606080d0203030f04062316181a0f0f070b1e16020c061b01 66
    0x1c84c552444c1e030707007654413078262101c440c041d603d8124030251503a98503821038003c2c101605031521300300d41c0f01941d00140030394001103a2a0f45071100403d44414100041415501d01404903807604c001c44d01c400d4501500030161581c1507400b0001510807581e40e0704115030b400c640d07031201c1d00301e052400351703c10f61682d058002288018051108006039500024226889900300b103c2c1400c1240b8a0040b0361034040c4c85020000001b4856000290b506d050121090914021001041000d0b100d05032280c580444e115141c00680c8140302081e602403c5203045500148103002c0001c070f41c266005c40340040b40e015114184040814820040742101c4072800e0f6114441924050203007004400f00211300040601800c0403000399456981c43c844410740443d86904580e0802e90345076000b050518440d03030b00c1548100d400ca0340f0200815100701a10780d900320000d80020a500141e51b54074032048946c00800b02c1c0000310300c6282483c00c0300c2d403150401824112614804090302c05000c0c80410300b500d0400c4240e030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 959034055 1250 959032805 959032807
    0x20f090312041d060f09090a051c020106080a050718090f03120b01020c0a0b0d060b18131a0904060f11090a0e0c0a142502010323070f0314090a0c0506 66
    0x1000d6517403031195501c00300030111800700d03250712801e03c01e42c07501800e03200042080c81003c605000743c020f007440710301480401b0b6001b07110b101e498807055508d4030038001009103580e208440600095040404210070004000000075188000e0345444113070074000b02050300818884d60200061414500400c42046402e0000b41121913110011900d0661a44150240150041100d0350b0100403504042d0040c071030b110646444001001640104281c40c4189510481c0410380c05035032203446000e1500501d2007140900340c03810b04c1100b80240918018400c880103552881c80c0a5000354910070040002d44038450280c850100405002c1009102c1e00200d0403609060104640d42e1140c401b12090362005180548407914481d8904400b402080022004c2e0074420f410310750907403a040201252507000341e0f0f042c0044000404812100703030508402800c1d100c5800e0002d1440d6006941910b09460710b85030010703911119250010354000c080d41c003d69907410107009002400344080c0490003400d0300320354071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 959035305 1250 959034055 959034061
    0x10311031501090218030a05060709081507050708040b07140c030f1903170406140c0403022409040f0b0406051012051f03080910031806020f090312041d 67
    0x141485400500c90310305030f581c00088089002a6203541d0300702c0c4200240403030b010303401d89252050300c450046501c1c90020b03490300c03400a5414400104840900780504550038251900c0104503090b5100c00300565280208100c0000c103192160014080e690141d014444a44100d0312203a00300391801034940d10991122190301301d04034004c210050241e006030005d0f40c50102c1ea00d42a103a41c148018001c8080c10120b00b088144803040d0807503140c84036003507800900b669900d000340140d40902c6c000070390003003601e104600d9100c410036404200303007280501140c24800e41100040c00d5500c440f195403609500c1d2001c000060405c1d01a94001e40001c6407a0901000c420b000103021031100e42d003500c50242c603003002c9168041142d420f00100c000e42039440c0b008075161708150329140d001e130f8a4540502062181415818803a108501045040801c008980c5035680c803460041d42148075403102d00f00c2d007041080d0f441d0ba800c0041c6c49800d820010b809407210324004240301c000d000c10203c41040c051200c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 959036555 1250 959035305 959035333
    0xe0103050c0f0706090b131b060804020d060f050a0f150506031303120221060a0b0415110f0a0c120b0a050a1803031e0218010806031c0801031103 64
    0x290380d1035209000100d0f03121003490820001810042a01030300354960301040c03080c040d801d03220040446004404907145d0903009491031500c20701038421440010b50b404080340040c90301c44800500940900000b0810354481040741c1c04440080e6075404401e582c4d01c2c401400402d141c06a05540240d0566034210b143c90032000c134640f0701c0028a03200d420701c0003014090806004240031040003101c50821500d41855a51451100231543c5800840c0030009000030084c0c504081c54800b07503003440d01000c0c1450b291014520441101118003410310400641d102c040c00c2080081120b400729600080c0051040f81c00c0c44d00d5044001d03004a000700780d4010b247d001190744c18100c03540220fa079010004e002e0382c448085070010841f46d00d50030852038188100009040e450380101c2482c0da1070002d0f10300308900c2c050241089100381c582002030400c002042600c95130054480a9104c040034043d074002c40d0400c03500704461f00750800c000e004520440010700034494038118085028106400401c2d212800e611 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 959037805 1250 959036555 959036557
    0x80a090512130617161e050409050105090402030a08031005060f0a032a0c0606032405070c1e0c03080c0f21030f041104110316091d06180114010e0103050c 68
    0x81008460385c0112405d0100ba840340e4800449807144004600d154210f400c03004095038070601c101854141000d001113124500724034002d000315801802040712a980360345400040c2c100800d14030380c000030a800002c0545a0000a04842501b550400d50b0b5401d9688040d0441c7e03000c08400c0d40500c20b215255007000103e07507600c045d00c2c2035400c1c105043ca0aa01d4020040c005941000b0600180743c80c59200c21013505803c0101c0403070307400003071040d580d400b6004c0f90094105c40c070250031030840d080c0b5615483c40714030b540314038640210445038409450340c403180310300d03803010003040016404080454010403041c4802600000c014625054485540c400c2441601010b00007e0030303240c816000c00c00300b0281c01c8212220140c00341081c07000e1100391103411015001186d0f094082034501c04030a480d0f40c8104054015242c0702400051140d90090200100c0301c0010b0100d5004110002e040c004940340e40e21050003841c0d41070209900388a06400148208141d01941d41070609080510401c008444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 959039055 1250 959037805 959037811
    0x90604090f180f200d0503070b0c03060a0902070f0602190810030f03270f0806010b07080a0f180323011401050d0510020301092004120201080a090512130617 69
    0x3089031034681c000e49044441e104811138035601441203224041004000700140ca40d5601501c40200660b030f0b1100480342a100031907080d40e001c51101d0051049611550180c1602d9019100d80220039950307584520481c1e003c0c0c420901c5100580881010342c45d07102000540c0400b41338280004140f869903940000c99807400c004051110204065180c042d28800c0034620b1020603140c058881e59840701c4050039071050241d2401401044001b1400c02c55043c216100c0643c0003180300d00d09850002c046903143e4000301c0000c10031800c900391079094140d004104014500802003480c01d120f4840304030052041c84154070f0520f904221b28103801d40e05c4a0b00c0305044403401d44e0044400c406a00d80a400c1014200c28110158030100010400341205c0d030040e01e07070b01200444913811608149003103420340900e01c695200e1080e0000d5550041d403240390703480c2c0c0000c1c410f9804200b4584035600c80d400d0110603d01800000808208680c16201680840004244038181120586240e0f1100e140002000b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 959040305 1250 959039055 959039063
    0x50d05040b0a120e06040c06030b0301020c0a06090f1703150915040b0604080f07091107050a111f230901081f030b15100305061014090604090f180f 65
    0x100c80100a00b544640181d042d114000c425500c0d1480d00e03147c40d80c0078464034018580003c1c64030388500228141442190210481d0300020b220010071651144003400c0314a100301c500d150030005000005046114a94540d0800380e00c0715101e160203180d00414514000b8a18031034803204003401142a000c0381c0701d0041d11000c2d200171680c40240e901141c030b45d2145500c020424070400881780c50901c3c001c10075006031201480280070078109401a21035034024002d000d8155008a40410001010700400500e4480f026140400d0109228215002e034003c809403100810503090925004000e4805041c01c05c86940308031274201040c03000020403581004001c000050803049601c44010f102122410065612000c3d2461614190382c8080384490340005144c001d18603941d0f8104624000e010782e901c81d42001d80203000c61402032000f110491034220000c1a5440c0070003000500b40c84820092015129050b00400c024051305802021103454680a0050321010b100d0000000d00d041418107400c0d0700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 959041555 1250 959040305 959040317
    0x30b0a181a090106020a110d080702132003060306090703050303010b0a09050a0b03060a0f12060b030133090c1b0219120213090302070308030c0c070e0610030501050105030115180b0304050d05040b0a 87
    0xc133820f480000d013841c02c000e00b0094020254400021200e00c001c5101e84010340503201662600315139155920407900005000360009c0c40148800c4000e2000340200b0011481c002040c0c558900201d00c030b841040d01b003c50002c0001080061508040009000078050640c0580a8a2130b044c07103035a0251400000030711150f102c82c551102a03600350081440c0c00a245100c000310711410107441c0c0640300f00e00c0300b0002c0006140002403c51035520803182c1c2d14a0742c0c0c5a010102043c04402c208403075120800300d91201d542c004034104e2220850000000c1d20744c004d00c0801c00f0015004203c294903d80120300034a5080602010000c1e5020a94008403640091020340382c1e100c6900d1500d5034020070324503010034801c0000002d020a0b81f43c003694000c09090310b1610a440d8400c0081b81580c50900610b070100f80208010000c0094003010190f0103481803a21682d48404500e002802042660056880d4040403040c007040c4a010b100c0c441580e10342d400c29a150920b00b0500d941d29000b0400d0034018016 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 959042805 1250 959041555 959041579
    0xc0201051309020910051c0b01050c011d192d050f0a02040b03060709140a08250b04060215060604170a03030b0a181a090106020a110d080702 62
    0x10203001900c4001039451110a0225100c02484000790028492148520901101016150300400071940c41c2420000715a401a10204202c130203042c1d010082410400e08000c040c0000c03c0a10841c111802d01b007a12503e01e800300b0545030f140c000c0b8507144401141352613640f680018504481c3c145480b0128126240076030341d1501844000d010071802a210b40a040d1600f000c828012805002e42d500c2120708000700c0c0e00d803409060303503650211805400b158081c1010700c0440340d005544100d80600401e0200e1103904e40450508000119000003003d118100344001c0c2401c072500d60201600020584505048c40c00d00000d580b89101e443ea90942e05041c40862010380350002141c010300788100c44200c0b044c61511102d95107a5280340b0513000079141a403481c1c402d1038007040c101c0840c0e08a4030700c5050015080022002458802d4030f020604414100291143d100c104071540202140e4001d4001c8004a080c0f40041c1d140883d205842078030151854400100d0754015940015015a00e07000000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 959044055 1250 959042805 959042807
    0x1050901091509170606130207080703030e0f010e0601031a040803011a040308041e0902040510260f090f061006030c18260102040803270a06080411030c01020d0c0201 73
    0xd001d0341c101e0b00d040c00040380c104c21882c000058240c003429003070b599200d07101c040c1010b00c000ca00444400038800d0804109200201e4800c0c2c00003041103007000f05990074400380c44481401c481e106410111540c015800400a00040074001e552540015a4205481c90195a14181071005020302d5482d114210341500a5081c000d0a80b005158090325007a5200e4480101da1018403414804481c8469113807408038000c140b81c0251070807903501610310b02d0f01c1d404040f030031b4079400e0000344040203490800c849030703d980000d0382080e0300401c0301000a0f1681d0420510a40c28846070f0708841c0803035800401440400142c580161048038998a00043c402d0054001121008010401304404031610940403030710b800e00c81c48c4108241400250142e6042c01c00c01c5007801d031b005501c5005c020b90010b0016550701c0141540c1404611040304a10b01c01042420014110a405070003090020b41740c03038200003c20484480990600b581200284a4580c101000039900c0418801041c100450a0032030811a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 959045305 1250 959044055 959044067
    0x1291614120406120e010902090a180605070e13060e04030507050307061104090c080103080d0518060103060c110604020f060c0c09091c1b0204051506070f11010509010915 75
    0x108041c0c0c1c0c0c05556550b0381c09001344090156445460680e18000d40803520841c144a40402e15034050280b40d007070b966208940000781480b880d255610300c41054103c00082d014800c030f40c0b00320560307151020b2640123071080c041030340c0d00703000034004807481c02170305115441c102c10000341d01c282d0519185030785820b68580a41140a4020300402413810004588036001040000e042070780d0b41e0010410480c82c00300c000300d4100c4020311000d042e1074820801c94034240c290740c01c401d5001e1929200700b000c00450b03400c50707843e1807000d9105072101130380c034119692500e80c0001c2a00d82c141c1204c005084500f020b800040040c040e41000e10310070390001650800a140a02c5085228803005100110901d00894416259412400c4c0d5401110360040e0450409000d0914030a101c0b207086441614035280d5030034040201800f0304010310340348051282000c25901e203001803059500c60a00e41c8881861407504810911750b04240d1414440144070f46511a40c2c40f42a001c21180062481d02044000e0741d0b0584035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 959046555 1250 959045305 959045323
    0x207060609060b2d120a2f1b071505030a0b040b060d1d0106030506010302122a060f0301030f020414010b07020904231e1c0f0e0901291614 61
    0xd2040c5001c20902c0c040b00c5e13001042d80791364118105000c800c08410351f504402c02d010b10300d0700c44030240441180128060021518004450104d40b1610b8803444900c00340c0420a510100140001041140e144241c1c043c001d1000300070b49060244c401241c00081d007601440349168000e90307950320100f01c2c0c0540d2803a554400c803141d00003004620744a081254440c81e09000c103a0003403055006500840500040c005941180c003112075070105507155250100d40034007940181d2201d01802002c6203111030100841c000c510902ca0708010b008a40305120a07038210648401d40b100c0203000421548402d01c08484d00b5980c1190001c102c0c0d5214901002c000e148410390706426016006c103407011417800500d0350b04402104220600b4043c0850303e440d950011780000d5050204007810602c0c02a01822000802d9642401d002c02e0a95604021481824090f4480c9030f1210398460001520a80d0040d00c0d034058400504551404154281c0f0500200356040010a00300032514896a02c000074804446 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 959047805 1250 959046555 959046577
    0x31f0b13090f14070c020111070509061003020d0c050406020f0703050c01030e070807030b180a0c09110d050a021309181101050c01020c07030c06050c0a0303051302040207060609060b2d 81
    0x1c413030419020041c0340b0381a240c412400f0824203407182c218460300203010f80886800034070f070b2245a81c034502401b1482c810750310000c05040d028400501c20082e035000d030386c0e003018165884640b0f81e1b2130035000038500800ca4202f840030780c00114050004c0350340829038401540c0b080c2800b0503c4100c0c442094a02110765110105a020b0400048200303c4046c560f507004901300d84401007500c1c000f444980d140c00700001c0c001c0180c60307824000c003e5880160085150043c09180250030888e90705400000d5072412520313088001d03400190244810402c06054000c1d02038080204150490014074450824098102414400150b442800180e104504551450442c10004d42d181d00060f42d403266150050301003250207049210010031414420b8040d80d070034000d0203008200721401601e00754000c081c003034a5110107942e00910b210160301c41d40001e00d82c052082d4000151285418003000464400c2e800c0007c0c000001c000c0d04c0144c0c0800102403842e0009104207500c1e220b440c018084039842040703101c036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 959049055 1250 959047805 959047841
    0xb13052a040f0e0106140a0806010c020f090711010507180302060c16170c01080601023f030f100501020706050a0e0a080123060a0311030a08031f0b13090f 68
    0x70070f003440340c80807083c101ca085454030003101100b03c505803014004e00313070f40100181d2000009080340d03104880c245181400a070403180604078032404a420800215845400f19030300200070f18004100f485800c0d0703c02e01c2e0707280030030301494151034950040d289171001030b11801c8046440114070405011429241e03c0b0070021210941e81c0c0c152004074000d4031342000760b050040c240d10710520350140d24050b2140005074007030514a03800f141b40090801442040b2a00b03140d048951501d043c4107100b80003c0501c0c2c8503c46520381c40c1c16400d00492074802040603442001e036001c10489a60005036131026521107081480e200d40015000301c41000790a004258130840d40f10300022400010f50080814120703840b1210903103171031242d440c2006107090310201d4000258001c10404160307850b070074002e03011008003071b40d0f120340c03558a40401c90f13002a00d04030840007886031a20818048044510018600124000d081214408220a84840360b01c501c440b003644903c6118071108040e03000d10749080c40c0b11010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 959050305 1250 959049055 959049059
    0x5091f080f071401050a0c0c0b0c01090507080a0809120c03120d0c020c210f010e0d080112020a0e0a0b1003050a11070f080912100b13052a040f 63
    0xa540c5904840101c42a4003900d000801d000e0f15016402060901c103840c0e0b1490250306620885a4819002064485003100040403900f0201e030301c018150142e0386000070a07464420b00342981010415070002a0590215000000140400d01a21082101224011426505141d0140c24031696a03076560b0301d4000e501494004100840c068181102441c1e0704106a12400c0740c1030344e40e80018584c180d8002e11158800e008a9000c0000d074102030100010f030b07840c030390391006d80c0c60a44440e0754400109400c032904c0d1071301541d400982c0380d004002510740100d09a9040c0c001c1414015613001d8141d000c8086400208070000c2508801125a0058401c020f40c4010220003002441d050740e20000e86800c110950050307200c004280e5107900d0b08202d814615a68607a200d0b585944900c1c007454004140d40820380442030144480e06580c2480400458044800c20402c8881400c0e440620407003440c100900200c000e00505021640c124030070143c01c0c0018040044c0c8503402103a000d800d803281c2c00000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 959051555 1250 959050305 959050319
    0x5060f09040c120b0a060801050609061306080a0b09010e070e2410090906090e030f0705010b060708030403080604140a0b060408160e070504030302060f0a0609050a02090f0f0a05091f 80
    0x84c0511070107240d10100300941d101c0810b00e02380c070b00990f0000c0d448507501c00400d001d4901880e004080b070b8440c1c03100154141e03a6844240c10020f0442c2c054980721000300404c10503100c00e00408071450541405418990b040006038540c1c000c000c0d110036500c0e504178070540d5030100001407954041d20000c04664817070100807001000c3e07400c07034050381d01d405040c43c1000403010581e02801c980c07109480d000c2d44c10410300c65071030034a030b0b00300f01e03400c0e0b850b592241009400b68503030000a18903035000300103c59691505040140035400c000e000280102e2400190354000540e00d00d500360442d060a802283e00c00031800040d20501503a00200303164080c00f40611100315480503d181107130041062410306944200007583c0c41d0140d480040d0168000744009140003810030207182d844a00c0f41030002e02207444200346422a071003154050f850a5000501d201d1902c1c3c10020f1203000c450450303103685070051490220348000c60070b01c6110f004240207004a45002150040c2080700b1060500440c0b40c2c56641d04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 959052805 1250 959051555 959051573
    0x50a06092103060602330412080606090f0915060c0106081c02031c09081821030901030c030b0d0f020a0e010f0e0c1306200105060f09040c12 62
    0x81c0c1401020321003030703a001c44034024002e19084802e1500a0108800086c00000046c1030340b8420032040300c0d41c00c404100e40200e030000d180c0614041d0032035261401c544a00a0400310000d0300c800d04c2444140061041c680c0c441070847c400220036a8400b42d591250786038840c5a0220007507003984003e001c2400815858158400300887c0c00c010101c03406c4c103c08840e1040c4020b4080142e0f00140c204101c942c076007508400c100c11601d00f0178540061803c185484800607500103003043e20740c040d00d6010b6001c06107014902c13010210f6140070440c00c0820341003c041d03600d111340c501e081c0c18581c880c0303441128640680d0044c1181031010300715070b42d00a80c524003031192114044040b4030405a85002042441a0230ba40034169800340e1900310341c0f43d050490860b01800010128030480346c041102003102e54400107500003d082e151140d402c032240903050080d65003110841c0d0500381e1301d42020400b1682d00d204122896000548880704691510308004101007682d4210001c0352145111071720802000342 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 959054055 1250 959052805 959052833
    0x2100302090a0e010b03040209091507090f05060c070e0c0f0d06090501060c0b010e280506030c220b01090503030a0c033e1e01020c0705030610060804050a0609 70
    0x44442d20425281e03005500300300c10a00411343c81500034000500141801c1000300d40103458001107880e10000d004012400b0141211220000362280c481000007040c03003146400988000c81d6054280300694001c190f840f4150312488003d015488003040c8049010306c01c8540720750f403407100c15581b04c000d00000d40c00783c00e5a100d8000c0c90b920f000c000042c900e1041c0c00b03060220f603102c00c0c015030302d900c0c00d0b40c000700801016110348220744950103002c140c1116240340c00210740d24460301140d185410820581411004030182c2d00900317911103000d94400c0c2a00159441030000900084d156240c5030040751420b905401c056018400041c4a01210340c0041c440e0101c584203956001c00c03949401500011040c0313820700b0450312003028030003040c214146024000c010130345004940c915400c00c580b201c0e49000c0b400d00161113940c0000c49411802d410b101c19405044164010a418200002200310040c15882000108821013000c10308004090241102c0150860317014040b200080c1401804a03142d8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 959055305 1250 959054055 959054059
    0x2705030d03140906041e11090a090212122a0a03050d0609020906042d06091e1a0d140406020306090a060e0106050912240a0501140d020402070210030209 67
    0x70b60000b00c9403040054141d100e564805d140100d040e4541e04204041901040100c845403250030701044183c95020b4828411000e640000c00c0e003070500d0040c8516894600907020b01c681102c00e148401c10468001c8915030720301d12508030310600804420607c1d000d42d4100401150150145c25410315511001901c2414982c01c030822005a80303140c00402c0784a081029904030394148001c00c40b0050440301032015403000d0700c040480b818201806010001035400c55804207064800c00c0c000344008000a14444140402c0d0106082c2030001103090015415000e00c0358582c0010209107500b480d03004090006d805007094500c0d8100361501d6000b07500200e80141c09607000d030380020003040c450f0203550210340c0008070000e116400c0c8242101c02d035206200e030a8024079240040d0050000c00c001000c18005401064011b40003500504001201c021300030818907400c140040c4441d2080010005400320100c03400e14a07a2247c0c030114029004920020394011000301500841c0c0703406800900d138900c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 959056555 1250 959055305 959055341
    0x7080403080a0516081302280501020303040f060b011709010203180c090601050d060e04150b010504080601150c061811011403040b0a0608070305030c19032705030d03 73
    0x303052610003240c000b201c212214808200008198501540043d1b821001010722200e4608042d00800e5045e00050b030011409a600c919100d94910912070b9003000c0e0000744082c502e1418540c903102e1b10324900b150007070a003c0d651030074020168082c0404802100d014640d085082c47c190492078002c2d0011500a05188c1c050300594201100205203d1080d08006040c1c00d0642c03510b80044501e50094000c00700f0241d6144400300300c0600b1101c80030b1089110b080030784120328841d400c0600740e40401c45d02e1810701c1801d100030322a0340c101049080c151011131704000390f28084400122a580c0c222100580b0f01d5103400801103107045010035241d12a0300034112140c41074806c4004444010942e403520030f03602e806101042c009000056025000303200001c0100d0741c19191a08036081c01c0c0581d2044801c1d90000400c2c83e00181c0602c500f818140f00c507028903003628800c0d180503050410000902842d401851071b040c115603846a4034001900001d412198004005000074000300103180c0c101c0d2011030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 959057805 1250 959056555 959056561
    0x15060608070c12030b010302090d110418020a150e06031608060a0f1217041805310501090b01150801080f031e0c030a120b01020f0d1211030708040308 66
    0xc041c560b950b4119070f02503603103500d480d41d07010101c008000a083c0c0c2030415408110300c40c2150340e19018140c54a0107107003422003010031102004125007140d00c00700c0c0300000803080c10780542d40c1c3c0194201122004003c0614400b4500e000712500e812010f106507100358003009118400000000c1d848002820303403220030040e120391040100c600c5d007500c600c4408010300d503c1840042d0028118541031481420034505070079102c00030055980068102c40c035001c01c0d400524800e540395000300e9401c80903640c0005d00c90501c82740c0b0702d071119004040440f9000c00c8600d05c40c01300070095001481c1c0a40080b01d801165031240f445c2c02400303220a951400140b0200008210020041801d82c1c488001500640c13901c0d4030081001c003050a01c81404201940c14000b100d07440000b07000906030600b0a0740d4090300301d07140e1031850048031280d0000c90704643c031036a805014080c0c0012080d004010751300303102c814505a0440c21010701861704800340440004018405510b42107a4090b01032842602c400c4000d81e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 959059055 1250 959057805 959057807
    0x60207140613052a030d0f0f050a020a080901110d050c010e030c0705280b0304020418051509030d090b0403030e060c090d03092c0a0606080408090d1506060807 70
    0x105142c10064075a400002c8100082402c42a010000340c034000c0900800403a8080020300300222560075001203604071002c4002d030703540b0030400b1150b0302c2d0b5800d0503410701450110094bc4d0311000390300240b4403107000448ca1910781c000c4c4120b110f550311110071222440a482801025a000280d43c0c1c16290308111141c2d03941039000c4182d41d0480e41c030700010a1403d14100030010110482c3c0e40e2501810070a002075148172404c1e901e070034082d110007280c00c3d80d00c0c1010701c10b10048038130100e81060300328004070030351700040c0d40480c59500300c440c010071004d4580c0312a882030341540305e80c140c6041c2d482c0c42c22100c24200701d2100303641c51069010b51410071141da03900807402d84411007104d42c3c0d825468104810704982c038040c51320030f99540c040d00e440c81c44141c980b030085250201010708008003c141244039002038105003981e030750002c8a000c080c00f003130703103070074000382105502a10003450b06101107120046602e030f403a492070106400221f400908030ba0511004c0048c925401000002200c03000012341c3c41d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 959060305 1250 959059055 959059081
    0x9020c07060207290d0207020603040b19060b09130b030d180b1204031803060c0203090330180604030308010e060f100f14210604180314070602071406 66
    0x41340320340240ea940b990001040d072909038420105130342d150760309204007800342e190f403c041c0d48924030486e030810352414010700c9641c40900b5915200c250351304182c028003a1103203582c1a0b410185c4180c81440f4031041c10710100c03010300080d00c62642c0610400e40035612050f8000c4100e142d0400360000b2140164546099201c9403086200ca581104401008240041c0c41a503403d88505800641038a985032030f0360395035003a038501003000c0c070050b072011402610515052043d40040d9995080d044208031103402c5004d05090907a0b4090441000410b5290780c94140741b20381174035207000418031a07680c1c0d202e20307016000d018207008402140300d4110018050b800d00030b060421484c0b00078004501541c004038200c6010080c401d44000300304840340504002801e10b0050f00c04079040100c030005040107c0381c0150398880080009100d242080807801003c40e00343d42103100d90703401d840c12101100e118108a207081c8078609009003210f01c0000c3d40c0e0309101c440300002b02040c8140c41039981782e40b03982c0d10394086 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 959061555 1250 959060305 959060339
    0xe010c1e050306150702090c0705060702151501050c100603140a1e0809090108030c25030b1e01090b04060602010515060904090503071a06060703052209020c07060207 73
    0x1168042002c11020b1030109000d0321030f014001308103850104540c0c040b036035504050f2481c1e41c0f49030000c1214810880140f0405034814094801440704003004d0340c03011241c0b640680240f60b05d8110130004441030344103104940d4803100c10411a01e4500e148424440180300c1480243d07464015a0a140820300001c03818841807500404012000702c00c1e96008010782000f42001c86080d1000c010201154580440080c000e0001c080599128029140c11500300101880442c600c200d0b008000c1d6034200108445000b03898100300a544039544001c4410f038040280008105400030030400050300318810342215858074010395060240540e1600164240d48003039171840b0003078814650003c05424410b01501545400034000719815040362507450859205007800e490075101818460644401c1c50502d54002d8400e443c110300d09010340d10005c01074010141c10b49140c10482c3c040100509081024070050401e60340c08660303c001d401c00c0c80b5600d4145205140150041c100c0010b6080404400928 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 959062805 1250 959061555 959061557
    0x7030b0609011a1c140406140109021215010e0306092a0f0d022407050613080f03100506030c1305010810050d050304120c03030e0906060d0c120e010c1e 67
    0x1041ca144d400001d107509600ca1000e100f4030b80e441451407121840c0c50180c03400381d40a001c0020701300700095130450003c281600540341007401080764800300b21984400c5540301903084418a1656041c00048030b503011400e01941c1d042c40307000e080c4881e2040109054168041c0c00800c070030340c2c002e00d01e00c0c0b850740790410300013383c041400c0c3c42240042c10502c01020701c00c3d10040c0b641005118041001274130031144d031224402d116003c90b400c1c0c10400c0800c00710782c0089514a2000b041e0000f580c0d220f0030b0f4400d0411460445401201061568810505d44405401e008084a490b40b8000d42e560401d41c00103d00303400c241e8002800080e030355024a10ba2405845500742184015041c5014031004456884084401c2d10041100241e50300000c503200d60444d10503030b0b915814924604004000b4066510003a115098141c14001030395250001c9070a281002c039804188031034141d601303686038000301c05041c40d090700f49945400c1c811410750103101144665103a85a121203080c0030b006140701c1d19407482d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 959064055 1250 959062805 959062807
    0x20105100303122a090b04050a050607050a05030313060b09060a050402070512040303030c0206070f1d0f03010903050d140c0a0302031009020d020a091e03020111010e07030b0609011a 80
    0x400881e01c6001034083e03680c0f0f00000030403a110601102c00084d0320f8002c0804001d440c40303002d11407495000000c40b004080004a21b41060b0500f4005650180e991050700d115190010b05202004011701c0600c21a5800c801070765189c1c5041e01c12042e586444000448842d0710b420070083d10343c585450820b02a000160002406500301014000254028a003c2d91944588400030301d403551000000c0002d98070036078000c10030034040c840c003a18140010384140240080039249111580c0c1c0105000d404c3c010400c0540070103012000031541250040300752581550070075000005042d00300004000026100d01c0820020441d0441c0c0d0105400641d280d5004c031004119500d103041c8281c001d55081f4100035201d03102160790b1058841242d01007130040d0718141d004155101d002d604100c0050090002c502140b062080f50000c08028020a01009050083c51401c13418002000d6006140d94039600f000ca07a00140c4a0401da42c1d41001210018410313040c540010582d8540d030030340b220140350560555 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 959065305 1250 959064055 959064059
    0x120f0109022a2104050103060e150105090112020a11060a020403110907020f06040f060b0109080d180506130503280f1121010b1219020f0306012402010510 68
    0xc0c0303044061a010045951040c900f04860440180c050b84040e0400d2502540d5541d2a120015040c3d48141c0c0c030180983c00c08104003e40c00510480200c0c0c442c0f000d29100d59580c0d19440141c80c034041b241402450240b01107401c0001c1c9401014040c0d4203403226045480755980c40d2070100c2039200da0300008110300c48928014026041210700241c0008150054030301c8078403010101454100221415a4104501075190041c0003c92244107030041f021303e40410003034100000c05a850420465100c10000052441d1500180301c8070208003410004058903640e1a403000320212a11240c00b44d64400d007d2201d80c00c040c0742c400300307900304c482c0b0f0004c13400014900c1680780c035440301d15136030400d84140100b61803458071980c0d0a00303281400319101040322414450340400c1d03401c40380e40f0302c825400b965140f9114039800c81c0015901e0b0500712040744550a0042600c045800842c1c004010741d094881c0b0800802c5410742c070716000c4900450881c60544000c40d03203c040342610701c25030304000000e20350882 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 959066555 1250 959065305 959065357
    0x601090902090102250305030304081206030a03140d1b0c020f0402070f140a080d1b02060f010b090301060b0403030509030d030504020901031e0203070602061005010305010305070608070212120f010902 88
    0x981d141e4549045d041c2090303075940e4642e6070640e441210304407000c10000469081d40e10503010713040d401420540c010002d410789035038054211044003070030000154001c900c101849100350440500e0005a4140010381c204800307014000b01010b01d4228401c020040184d0700300c5c1494030035141a19001006201c0104058450401c2c0d82818042e88000d03010302c0e05040c000c0b42c0b20300010001042000c40010f00880006000d2010013a55681901150004801e0000c0c176050002040d064900c1c0d0395445668000343c2c1c00182c01085954041007050707501003030010078980c1090241c051108294165850004004003c80c115602181d00941c0720080340300520206600048840030801c160a9450002c0c4040d00001d280c1003040d4841401030344554200700d5602c00040c81a00140300030708081c4103a504580e105902c60b60329000348010004071100107110b05108010f900030300749200c4880c80c1e4070030350072405d280050411680b9400300c034404000060b200f207040c0b00312495000b040f01544094001864 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 959067805 1250 959066555 959066593
    0x26030f15010c06061e080a03140306010318080c1e072106021b100b0a090902150a091a07151a041a100c0b1902210601090902090102 58
    0x490300d810018401800000207120384100400b84c59411207200000200208241c501c016035003085085400c25140d003000213410050f0146010f50260089842c0d41e110310048004108224074030601d81f2441c2c22280621040380001c2c2460000241070301c0c444a83d410340a07034410070030002d0310070035403001604125100010007404103120505404c418a21003a48800c0281d8016a0740290340070826003203080740a90030421031000c0d4180590610a410050000480d400424422110017640302c0036108215a074040741c1201444e40c6440d6075440d44510030b001001008503008400880191680d0518007981900a54240c2980b1501803048008012103000c0501801c80b60280003010011404076540d445004060080440800510b06424001c041002d000500f84454050142511111b40422401c0107040d6028001409120380018807280c40c130024422200900c00c5010050384003485056800e00a90080b402660342d01d44294031409898100d203c0c0c5030784c40d40941d11a80d550340e003002090f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 959069055 1250 959067805 959067841
    0x170307020106050a151206140d0c0506030f100807030f200a090c02120f0304021e0303072a0e062b05030a18060f0302070f050a26030f 59
    0xc0300219485565001252a103001341d000051552203010724004010b80c0010700c10070441141c58180201c03851701c07000e00700482901ca0345c503000b40141c3c02540d00784401450403c0042c440540010f0362864090041e444a8006644000820070140742c002404040059118290303500158180e004000c95600c16820b9010303800400404c00012100310b0080d95142c00846c01899003400120384d00d580202c00900b0b14451000c85e00080f00140101446c4042d05426a80c0c469410303103114040800981c04041c1036404880800d601d840000703045420080d5900c40c040d4001c1c0b04810f8821520304045003005900c1081c01081009100c550005031145400c1c2450300700d002148084990000103210303036209400c91801d05440b41c0c1c2c400a0b0300d5809a601c50950340d023480c40702c4514008142001c1008007900e540344a00d01c205500400c1d15414010520a032622059200086904085007480c2040f150814040d00e0040309401c0d2000c2c145120f0b0410480348100c0341000c1514903039490503084c4075050454 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 959070305 1250 959069055 959069057
    0xc0e1305100e0a0b04261614120f041502151b0d050405010e07060f020718020c01020a02010f0f090c0b2d0705070b0427150e04050c010903170307 64
    0x1401400f40411106424103015500403920034980003014041c101850401004010b1000c008110020800e1481486000c82d56406241c41c190700c0c162680c03c601c0e1801e82e1100455000001034000100005c0308014000c581542040640f031850b110703016600c0329028598840c182d0b0702200040d85070b030031500b50560f160307a20603506030404601c070403040d089442c1110111a942c1d9107031351080d10718104008902c0103000030b203031182d0000c450702802502c1d10003902c07928a0907006000e84070070040c12601a101241f030604000c64030341d00d00d400d000703010746400b592a00c4100e10340180ca0210420072b00442182640000b400b0802510300b2184100c1588001c0c103144420409104ca4000f401208120014011120850a80b200718604049040501d240e10201d003656042008100d0a030603110f48160b2000600f0180640c0010b038107400300500100201590380000102011541d19070819007e80118062012034001032950307001552002d00c103020252148102000072107801007100700460f401202 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 959071555 1250 959070305 959070313
    0x405011d150d0e07082a01020a08070b0403170112030e120105010f17031e0703031116170906040e13020a172a0103090302070e040c0e1305100e 63
    0x2190741d121094101c0001109101d482d224a0030924400708040c4001d07082e000041e00520802c45c2c80034500d144404c19040508641000d001740a83c001d000d1030741c0b45600071b003801e80d64612600d44642c1010045408134046125112103011499071a01000d059a20302105406d4201c46600e00b0348200644210341ca900c80700500d1940003051080c02640c3c024007881d0403400380c05040c2018460f040c03041d0792110080ea03105200301c0c1d81c100110090307603800840c49840300380c0e240d0740e5007000c4005d0500c1c2e032080f641090b0001001c8144c2e0072901d5699240c28001c080c01c0103a144a02440c20040c81085030066006400780070600440c003041c0c540f10381040148040c008503042d00d6010960031645540218640c48940e0180c1040c00c0d0309002890141400310310002d0780c480941901d011410142c0725040c101a90303184e5600405008100301806030000100300d03202c500d010f190144010b0302c0b900030b00c0d00c4001c0c0704000c00c806028000f42c080c091a8018003401c3d07943c55540c0240001e1441d4007000e0300c50b200e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 959072805 1250 959071555 959071579
    0xa0c09120807150b1305162f07060f09050904060b0109030f080712020c030714060c0102030f090c0a120308040f060c0c030206060d02060d0c17010b07030e01050405011d 74
    0x10382d11104020b903020000f40494000700540812411011160314034a045c0c2c1040200700045107840c1c0a8100c1000178107049050000d10207240b0038018660f038620b222090b10080400da11580050054211103442d59a2901e24001c1101202c2c030501a2103010741004070840442e0000d542c54104040c20b0b2010b240c0499959035a4840301e102641084059031800c8000898405004003400c1080f40c040c1079000801500c90900c0110340d03500c03524070820007046100300b00c507545903440a003140c00a1412500a42d141e003080c8507884c002c840300303580d040e4140c0300c4e0b002c0184850800f884801d04580701d0034000700d0503010a407000d5440c0c00740144126580c4203640b03143d1000400a00c5407025244a55540c0500f4005034036010745000c0700944034a101c1d2042c0d000c18001a0780e060b0417144140f0600b0000704080011000c207841c0005c5000c418581c1001c014000704240c6045805880454005da4034094110000401503071716109038003c5600007241245030780b0280070381080110105201174201104031f4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 959074055 1250 959072805 959072813
    0x50a230f0d0303060312030902212505030c0a0e280905010b0909011802060c0f0d0206090601062f0f01060b0918090c010804050c0a0b030f0a0c09120807 67
    0x1d101c00030100e001c640d442d4000d10030301c2551800851084144d0404000680040c1c00003401400400c80702e10000c0307440045200360381c50a00280155010b8000b00d0124880d00c2011140400e41c103028040c000e2083c000080c08524080c1440800c88092280c4182c6940314062074a43d00b0132046080b6003500c01c1c01120343c5042c1c8151203880300c8140039000014480e9203160401ca01c4603000b51081e000d90703062205205001102840416881d5411240d440d914440c0c2c0480314104111059420500c0c0111700c1c030300840c41d4010880c01d00c141c1890040c2d0b0b01580c0c8400d000d0380d500c41c03880c0c3d080c806840c0c81607030030b5440068a400220315042c031030100e5120340c80c1e09181c1350030344620b504242c1c0d03084008aa440640d00307086038041d0080181400300c191524001045550790440150140d0401003094042018003030240184030715420b0280c107026001c0e8550300700d98143c2e401078034429101c03a800c6001600d84983c51140c00a2203106513076020246241000c81064507013101c0d403d50b810003040020b44001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 959075305 1250 959074055 959074069
    0x2160212120d2a020607230406080402122803051309020406021506130518070311100e2d0603010f0602010509121c0f091b050a230f 58
    0x6500c11003010070a0342945403482d41e0483c60307a402012116400400520242c3c001c90369641c0001c003442e019408400504000c0c010240c0000d810310403803070018010621a0740010700c54800c500035110f800c0601e40700d500e1150780f50140c5c1d60000c02a650302c030700c02ca00c1000c9042c1128401e80a442c24505103002580c1c1601c885503d5880b030000683e001608000c0f00e50103100400d050b070000c20382c00c2c1d030350324010340400c981da042c1c0310007140e240d0740c1c41000812519513680c06801840d00d10341240d2210303440e4a003854040340c0c04ca4000f84511000e15404650074841c640d50060003401500c452155410014980c040346020300210340d410b00d00818114550316008091402000d5410039000d1035450460042d0859601400c03440d4107400140c4a80300300c0390b4072011256810000101c43c0742402441c6012001008030030300b211849400c1c110340c6814826450b01c04408502003c621001c070a60f178100700070784003030386100f07460381c00500c6074000c5405a80c4090440f0300100c09031a60240501c900f0000720b007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 959076555 1250 959075305 959075317
    0xa020f1f020616020708120f0c03030a151403030921010903080a06090506030d050705012018010e10030e0109050d0c03020607090501090504090c09021b010b040216021212 75
    0x160701034020003a0750048003020409a10013400508101402c00440a4507103900c03000c00c0c441e050780000c000707a85180030740845221080c40000c2c1c80e02c80c14842c85100c060b00c0d41c40700c0e6941e548408a008281d40d22103812550806100400079890201c03ea0203000d40014a0801a02500c06070030200c84110030a005604125100c3c0c0d95003401840d00120307401c2100d8607500040b00c041c1c54101000341a40300010a02410342240c189603803111414a08140580143d83c0005e41e0b2441e5014801d0f881d0307c215002d01040340a008400c00c0034900d81004440280b01041c2c2568030100c0d0040d41044d03680203500c0018510701901c00840c851003103443d001d00e0011000d101c04000b0f0101d0103d2428154103111082d0401c0ac41c0c81d080411505e8640000c000707203142e000342807080d42e90324044020003170008c035400300800351640150b4a8500c40700603038442c520780240c09070842d42001070302c40f6146402d101b110b0b40c0414460114040400719001e0041c203010440310001d07030388076803055110b00d0180c54028241d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 959077805 1250 959076555 959076557
    0xd1a0301020c07061403040c0635060f03010902060405130b060703110d0e030c150d06090204150e06030f090304090905071d0f150f130501091d0a020f1f 67
    0x43e894600403008202d8039120403000030401e82841070200140200c003802085a00d02d240410010501511207426020140614041071043d13510112005103c0310005102e4101182c602c034114092105242c01e030390020784000c0d400601088144030381e10301031401e00030302600d64000207124040030000c6009540120015800320b0040c0400d44202039080107401d007031400500c0c1048245420301c011a40e01c080000000d80b145008140c0c104174500c100098846020003070f00d05100e51682d800100b802540305008881c0020a501c03c1d0340ca2180c081c0081064601c0080d084502e5561780b004800c0346500c002d01541080d0104000015111510703010395403103140542c000d4080030780b804441c070303c046424807102c1e11880481401c0280d011110005650300c500503050801110b46c900c00004c0170014a095a558803420460a100498441c1d0388030a040c3c82c0c03c3c100404c0b00c541401c2110b40f0006000c8030204065021070440401030620520b40300c40382c58050880444c85580e840e20805c01c41090036840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 959079055 1250 959077805 959077813
    0x50c01090f0c120809060a030225150c020703060b0402040308281707230d0509010b010203090307060e01030b130c0306052722080c0709110d1a0301020c 67
    0x1014800c030341d142c8030700420060283e64078100706695050356031302607200003c0c440c3c00081140d161907802901141c9807003a510400000342204840001035000c3c00c404203840e0ba40542c80001605010361042844400154000b80b10541c035540d212400f0300100302c5401c3c0c02540034440007000640b4200078002c02c00d400b607610410b0565080940c05034400c10440e480801001c0412003007002e14940e030f8981c020003035107031014056003964119a00302c0160300e0352141030300000444800081895212034054000320000384602d112038001260789001d0710100c01d42c19003140300200301c1103000300380e0710040c01018180400c0c50b14603400028507245254984811054581c80c1c80b1203010b5152107200040c03c03040325442c03061400c00500b400f0380004220000d41c80384400000c504a0650010502c92141d2503180f0120a40d9a0380b40a90858110000f9850a44159007000c5007030040d5004111000f4000050a8240074106d0a4140039140340202e4010441d80342c5a1344085032007e000604070891418020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 959080305 1250 959079055 959079083
    0x2040605041a0909010605070501060b18030c03010605091303030b03031306022103010b0c030d0203040f0b130b041203020705010f0203061e0306010324150e06040525050c0109 77
    0x8044400d0840100710000b0820411010180daa400000d4150b54851518a440302864a8002e0041419410000f095100494a1001044940080f0901c3e22041d401c1c1c8003c0d000700f0007451301381d503001d000b0350354000302000010f1084111880c040c1e88141c021700e008600920700001090542e403190b0b40b40c86101c0c02240051060360340401c24600b040080c034074074101c0e440044035110041d0106028a1016550009500c2c044100c10416103c001d03900500442d6241800d00e00a03014614040e01201e403580194002800c4004a030001c0d01c0700d03908004c60103555952956401507440f1a41d184400389a8240030403008114241b04441c0346480711070006941e8282401003041c11004900c18400e1405901c034102030701d81300840d000341183d40c4600344032626809801d50003a820780c51000d18410f50300d800681c200e1800d541003060102c850120341084907407900424481034034800c441401072000b52040034440a108508000501034580c5025800c22444481a070b09494032080c1c1038990030002150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 959081555 1250 959080305 959080319
    0x12061b160c0302271f0305070e180a17090d050f06070e15120c04031e111e090712090b091009021302090607020901030b19020c07050609040f0204060504 67
    0xb1200b820450443e4102c0e138103041c0c1d1101401483d000b85808422444900c1c07556a0455904002001d1135000b000e5941c8152946081807010700100c800001d90828030384211580c41c4082500010150800c2840d480d425510340d1252a66000d496800e401644885054010071000d00181d003880c1c200340098415410b01540091400107481011362061542c44440d51416203003d048600502020424090b956192041c0386201e001e40e600282c0101260b0750301a54401c0f800015911f050303c91091628a50b0f8032030103100886c0d440301c81400c6441c44480000095103060b85d4071650244a503d4038020b603940804012041d9143c201040390000e0112090109002050040340f61510044404004901d800d400148001c1812010301d07048030b030b002a00444a403141011200016000340540070596541d1074041c00840041740c103000c4010f400949417604100b14001c403000050414002c5c2261401c1404110b8503501006080c0d6010703a540480003184a5503001500007000640c40c1c0940325854075035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 959082805 1250 959081555 959081569
    0x6030507080f0c0a03200705070602160302060702040b0307410907080a06050307030b04030f03050f012309070806130203070504062106080309040b12061b160c0302 72
    0x2450307201d282002000f29407581c081c00e40700c1c421100e203000305600040d0071040c020002d2000403030300c0115000030b220040c0315001460710110341040d0700312401101c550b50039019055841c04001c0d0302c014100550300c0586031607080b0310034509004080e114400d50342c038075207040350307078464141072102e01d402030b05c265240607002000004540520f440000c50300b0140008000c44030080c80340080c411150042101031a03e80e000d4405840050211100d1030785904102240510407602100080c0918900800c402c0c170034000c55024040392020100d403030b424049a250917514440900c4000e07180041d100d0410740c2e0300d4403040e02071601a100c449440c00c200301030016003561a10324040c45030040091025140d44007040b2821115203250440b400c0078880d600780040790f100306d00b611003203042510104211070040000c10003c1707811141000b11042e01000e0010281e40041e0145580d044500040c205100d4403510303110f4400707140c1c0c040c3c2c501704035580a82802c90303110000344c807000c0c0024010300450078108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 959084055 1250 959082805 959082811
    0x80f13090f060b1c0e0f0a05030d050c070c05060c0109062406020d0804020405070509030f06090c180f180706050a02060708061e0105362d0612010603050708 69
    0x1c12080c40d1403080114121040301541214884c01c1d07581c5840942982d0a000740a403005100040c1ca200103070303506040d030780c980080c1d400001c01840d000104100054000031248565408484c0030086403a1000300400c03070304590343c010515500c0d034140c0c90001c0c15034450400e903108506a070007103146a010790000070080d2500072500350b60140480d000b41c2038100f002d90340d000c2e40c11500414143c2c1c4450080340d050041e41d40007501071140c40c09500c447d49001c692284102c00d00000c85408152036002c0200855000c5005c0a001d0541c001240b1043c501800d02548101c80130b80c00030b003070143c45281034a0040d19622a01c0000d0000c20207d00d05a4144070640d0400140d18020300b103414103100203921032100500381480520202c9209402c0d90068054a58059800f5030310801403409003006810300c1007403500b00400c44c155001c0090149846950742010302001012480704501c1034a18441c200307a90321401e42e00500500592084102e031180c0c003400f03040940e034040b0712030074030f24400707098030700c020f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 959085305 1250 959084055 959084069
    0x51903050c190f1106070209070503060f090115080a061203120609360c090b030f01020705030a081003060c030b191406090a1d100806010b030103080f13090f06 70
    0x640c02c41c50110b48a441040011904003e0782a540c6020b1302c0000d4141c802e11000941050155003040049074000010754480c000c141c2d400030312445400108180070000b401282c000040508528140d9449080385a80c402035a00e03000036034941307420500f50408802c51045000071140c103240c2c449031407940600401888480401d00098060320740c3c10800c1201e800500f16080c0d106842d0704008030212810359080da812040c1410500d45404002000c0c010700e00c4454007030320070500160400d400c140308aa010540140155040c548000822910b0b03881c0030f0b1a6540c011000c26000c0040783d0584156900c0c0302e01501e00180d01c405500c20310071144c2d180418805a5001a0420002d8603181c003007041002a0844072103533619000701c0011114101a0403c001014196100280500d01100c106000b80103003141d103205c50361744660342541c5400c00d014441d9001c60600c0104005142c80c80504041c0e420328000c1420307e2601e43d9104c0025000342e014208880e22a101b088210341d040c40354102618071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 959086555 1250 959085305 959085343
    0x1f1e171b0d030e15030907060c08160c031a0601030506010e09010b0318070f080f03030108210c06090a060b1206010e060d050601090207020f09070e010804051903050c 73
    0x4400e10314034400d46030305041402141c401c021076041610403000408001c0006004920303014100d02c00303071256042240c941695104440340800d4003401045c40c403040a9101c13000c2071a01158500071030b210022441e0449040040301404400a81c0140a404040c03002c1c010761204c41c6020f000040c140e0300090481030501c12002105032207915000850340c152950b1002c0c50b940c030788403c8a505081c036400b4030314810078003850310007040c440081040c400c100c480010441d01640c51120219880e44000c0c03180082c9580450520010382d09120200c200702c0440c00e070b180b400c3c01807640c41d460403c1000c276580c406580100c941c000030090907205000c564a0306454142c40324190103885580c07990180183c40000c00d00f2000207109940e400281c40d2216804428ac41032940d43c3c2c203000c0080c0d0441e203c12032203060300f1034040c003140c200394510302e124490542e41d0b480b00001c1c60b80151a28000508244e81e1801044d96000400060b00803214007644a82e40d000e0b07603100050711160401c0c410040c04c3c0c01d10700f1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 959087805 1250 959086555 959086573
    0xa02091f1e08090d0f200604050d21050a0f020a020d090f1505090406050a260a030c0602030618011e45050705091002151f1e17 56
    0x2c00503120a0350152420000070801000600b81c0717001d900d0380721b141509001e501108040c04c50205000d80070303910590032a1403140c0802c0e415501012100c074223509043c0074180e58140205560005508000d140f40001010007107200718174181d038010080817015134800400c40318500c0d848032004bc0100b1031244503141890901000c462000d8580c14008200500481c058549580300e074400d8004040041412540c20f03950f180302e101920f15030745c1d20a1008201e030b01c4a85941000b0034000310865056403040c190180c113640301d0340250409801c86800c0054040010742004000c1d021b54064194280708092020038a180c0e06c0b03071110309410003603080c1582641c1c1201c50301c240c1400000703c10b00703203800303180054000411000c08234840007c0784070f642040c090040440e00040105403540d42034414880c54880c9a030282e0781c800091520a421030b040e88000340b01540801c103030384103020041503221100d07580d80c40704101401c0c0d01d0030300921307500000a0402080318000c550f95035056a50000d0480c4130 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 959089055 1250 959087805 959087821
    0x3110f0d21050103030f1116060f1701080f010b0f0a0605090d0507090b010311070c05090c090a08030a0e0d0c060c11090a0f1a06030a02091f1e08 64
    0x850103540e0310a00c0844403110268101640d5400740c05503403110304000b20740e0b580c10010a003817000010300020a8000d80c041d140104040f419040c4400e45901e140051032078a00211a003403110b4085500300152403041441441800d1202c5d80200b42c00e40c010000c28180c908264211121800080c1c4540c40c010400c80268036a600408125501410070030380720507070000410007035243c0b03000081c041d0254110205000d1901d46c0800c011000c286e0342045250b2070f1003d80c0e0828030400c0c10140265030088810813507454034000030740c0c2c00042d0000150800395800040740d00c000c05a006010503401c0456041c81c03150344160380009401d41222810013421407921034580e024941d028000402c03943c1112242030020356044c0b00c9900f08050813048280c90304038030750001084c02c2d03083c41c8541c50800720b0380d0500100d5403101e03010080c1e0061041c1d1842d142c110119000754082a48142c100082c110305d00c0c09c00405a0b1081d030b01c04000d481d40e03640a001c12a560354603080c0000c559003407001030404c0c80810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 959090305 1250 959089055 959089063
    0xc0402120c0703210507090b07320f0105040b100b030703050c04030f030f03051f17010e01050709240c030c050c1306090e0a17030703020f03010f0303110f 68
    0x1c03074035012166584402030309048580c5085074421001654201d1009a04100039900c06807007020035503101050b6541315108655075201d10300018040f1044400d610500c0303100300c100d82400e581c2c0c0402d0303d500c40703ca28549900707020488d09030b55600e075554420402440000e0340e201e5444061001d030035160a04001c001d102c18007001d454041019520800519a519080202d401030f41e0030114400302101c042c60300500b101d000c160110002418000811a00c0c4642c4008640341081100c06003c03060410703903116081080c860000800390f407240300c0d25030482e0080c41118020000c682c0c070814054100203160031040701d94011003100030707841c10742c20810961000000040650506d8207085220050401e9458001220402e40d4043c000705034100580c3c0c0c00380d100c4030032aa5072400c10301c08a84100d18054a80c09541c002501d074034022030a441e01c04000c500255409506800c00500785007101d90323240c80c2034009070056190f07450142428824180c004d0a01c5940f01120001044540010b5160a8503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 959091555 1250 959090305 959090311
    0x6080108121921021902060405120a170109050907150228140c21030313030212030921030402011d0a0504050a06090c0f080c0f04030206070b04050c040212 68
    0x2000d14110060b0014500c00c10294104824000d401e078041d20b20061200700a600c55a00030300f000c0003101c85248000c2c00412403070b10407034114011348a010814001a400741d40800c00319400c01c20343d03c10786403588010084581c06000115030015992500c030b0060341c175011054021701d96040d07042c1c8221810070b80c00581d0b800d003441845000d207019000722401d441d2441d030506000302016079001c911a9807200000e010084a001120404407503121800c034030b07100b803420006410705a042003000801c0c408201c14000342c014400e10484408040c61490448560402e880f0780900da0088107040d10321002d039280301c01c4002060401030389903092580c0080c02d0760800f00e108c1c096108c1c540a441c030507695869000300040c0800391040c01280740ca422507030300411043c001c2024541c030300b1200d800194819003a06101c0318058540b044682c0310031480400d10b0b04500d4440c007411030304204c08001600c1d9003002d4518188120f40400d61760810b031a000d418084481c481a0040c0c0c030500035004981e94054203160 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 959092805 1250 959091555 959091577
    0x1080f01051e030a0b1f230f03191a070804030e0102190807050615010c060b1504060201020703020f0607050909040c0e0408030906060118030219090e070608010812 72
    0x2118290407441041028510401c9940c9030068048600c18400d04607180e80c803480e6072030f41d03041d604e10f403150002042e8001401541c1030ba603104007c040414450b00841c0303041d80001003c1004642030200020719010700311004003600e081039000c1b0030070004e44c0098200d40b103025540b80c0c050703440c0c90440100291070041002c4c007040662014500540d00901c80c01c0c103400d200207400d96075101071341030480a40d0300605045603140b1a0b440054140101d00b00801034919059540d400d1b244030036101c00c2c0140014440199025001c031a10822805400e4010401004c4903000562924010300b400390401c121140a181d0b20381001c4100103d0300d501c20200d4160100441d00f51980340c0703484c00e0009a0b0380094111a008414000c20301043c030088002451042c418001203900ea030341c401d001111104200d01004e00c10740c442410620040ca401003900300312958400700422541d41c0c80d03840310280c8110503400c1d100ba4014041c140f200c1540444001d004d441404020503d03c1180181180244902d2000c6c130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 959094055 1250 959092805 959092819
    0xa020c0706231e1b0105070908100209010806010c0c0503190b060a030c05012d1701080316060e01090f110a14090705090111030a09090b01030b1f140412020f01080f0105 74
    0x61145a280081c139800c550048008000500e071990028000060038010001944a900f064100c01001402103844e840e8040e0348001881d202c0300015030380d07004d040768100c52241c540b0301c0200e52034038108944450000c14210710031564005080180702d4140c060301c0640111402300301400412400075a0350200c2d8400c0c038042131020301c41003d401c410005404c0d102e511810408200481d02e51013546407407a400324869039241c80c1da842415554030302c43d0b010858900c500700aaa0400b01c4e911b0f44c04540d16001d1080081440c00f20756690340484c248504c0111001850200104845c3c1810101c0b00c0107406d6600c10780c070b8a20f05290005500f540020040420008009106452079200c4e0111130b00052549048035260110414041c10b40c1600c2e00494200c04e00d040780c1002d142d0700c03a0040d54560310000d0321015008031400225030000d0050488041401804611404a0425007004000910070545460400c0c2c8080c410001442c41c080521810000080e043c007002e54502d01b080307811a00121002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 959095305 1250 959094055 959094067
    0x306040b0603101805070f060801030305091f0c0506060d0201050d020711061308010b0906062d0c061801050402060307110a02150a031d10050a020c0706231e 69
    0x2440c0018020380e001c119400c000032904d9440780e051404040c5072051041d506502d1700c03104a00454140d500c2a10b000898402c0104013090082000708001c20014014440d2010842c00d445051400312a451002888507048070003805000c2c031a00d0740004040301e800781c0c0c080c460f07000200307140076002501e030207250300250090811034904014a0a45000303004661150a800c1421020200600c511106542460100c1401d071030500c0940303124440081440d410a40b00100031901790411088040306440080e0000811014000140000415880050030945080e1141c40191040030510300c500368180018400103030b480505680d070001c0c0b80d1512840050452400c0d601c1c01c03142207000782d0801c0e0701c01c2c0310f00e4603092070400500da611941d031002c0c031685588842c820b0020110040300800c6401081400743c45c01d8071a007141303401004500c00503040c180c0e001c01c00e504114099200802140c4c81c08400707102035064260003071005d0504a40d56042504094000c00072410703d06994816040020700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 959096555 1250 959095305 959095309
    0xb100909020c012714010903050403030c05160b040f050307030f082805030402040b010906210f0f090302060a020f0a0c0203010213151205151504080114070e0603060306040b06 77
    0x130302181c85044400f4180050500015407100d20440800d4600c845105200e08010005002d14140a503056031920305e864915102200d0600d189081102d46016200f805c005040252580601405481001c240d41d5450441d00c807941c01096800280643c00c440e00400200307042d940100165500840346030381e110104488000c100c585010382091510f00700300c103d0740c3c090703010780a948203910039203041142e40455401500c03032000714466800060945040e1030100904640c044030b0445203580b002c111080b1207a210801d4410304490100b045640d40968003e05904001e40c6411895103002185480303078000070b5185910500f0618414000c030702441c0011506c0c254102e828200d040440112884d44408400c4094000701341c0e070b0f20000b58141040400600c50703204d50b1f4010400e501c4614559400f402c2400b501c10741d01060040024801d020008242c002070003032501000201126241a280c4102d02800c4014440e45043c0108000e004006954500140d0282c010307410100e4404159a9100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 959097805 1250 959096555 959096561
    0x9030f07020d050624040e0607110c031c090f060c020603130f05070501080108010209030a0f170319060f05030a1113020c01051602160b0702030a0b090f010b100909020c01 75
    0x10414401c0d11300700300e0010141e00c0c1e00340888400494075150f56040702c080000380c802a8030b44100c242c009801054006009001200c800c411300d10994001282a00004c0e0810742103044456010503840e82c3d00050030350001c20900a481328522240ca0f66042c003000805400101c80024010600000400c5160480307003900ea0f48a030340030001c000b1444461801588800da54030655010800040010943c41c1040c02916600180074000308484401ca48400c40c6511140c01d06840c616610b070441841107020000071840b500d28650350100d0212841844404c44900c0d0b4402c0075040030ba40401d00c1b040c0e40105081a465412210888089454900151a07075540c42042c1c62420310003e40d0071010181034000d18030078000170502090a41c04600143d880301d4003000142c401c42480d040078030030a41d1a001a00000d80090201c80c1c84c4007145e914140d10a1043d519a00c20b40e00042c105070501c2824010500300c0d0b442a18500402e02140501815100003401200c8000c0c2d0013042010303640d0303002d40c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 959099055 1250 959097805 959097829
    0x1505090112031d1f0e090105280905040819020a0206030f0703110a0e01090911040506070303021c06051009141e18100e040309051c05060103031e020609030f0702 71
    0x24003120306445515104000c000102d00d561300400e0640300d0041181c500035030760074102d03100540913000d90f0202c1124808030380788004004004449030b41c0007144e5451244641e0744a507200d40000355a4501041c407400b2141014070b00380007154891201e507401610344038266900701d40051244940f68580b070006030f01408102d6885040b1280110b540c00d03d00f548400c0000c0642000c1e00c4070304009445100c3c0e84240c03602e04000820318602000100031905160004103641c0340285001420318040529002c180400002e0348090b503a260441403166142000084a91000380e080c19012189401b081b942c18034404c2160b5803088610711001c500b1815400030103c0c000c03074010a01c1d5814241e80c0611406101d09a070102240c5046000204881108000050142e60183c840c5d1030240d2405042101e01d1008002440070808100a6140003c1c0c1c1000840e000c0e5101e40c4900e2a484851481214510300f09007000045621107008d1050040c4044101c50346000c40d40340305a03039a003c60000c0b0b40c07002904c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 959100305 1250 959099055 959099059
    0x8150a1b03020a090b0c070308070807080304050c1516061d01050f0a1d0703060f11070302072309010b0307050c03180a09020a0e121207061505090112031d 68
    0x40300e102545603065004150480315a110a00b81c5a1941d182107441d0144c1e190746c0300b140c1c1c003504041c00810b0192000e03050080c41003001030b1401c0c0080c0e603a5181038000741c4003228140d11044d0a103140785440c88200f55407904a0302403038102040340307400c481c200000a401418483c2d8071858440401d0940003103007a00c02c0b0160082c800c5041040001c0d24108044502d09402c1d86007110840d1038040310343c08105101e0f19180146010384c2580c45140041604c90031b881c10780c60303503041c00c500310030440d0000d010198029001f038680c440c9001c0048901203001c0703005e50804445040c002c2070701e540b403100ca103047d00c5120104d144c072656120070540e52441041d41200c0a032001044460120341c11060400f00030a00b960070500300c980d9001c1440c1680106a00c10f004681c1109052009060041e0040000fa1060b003c442c0c50001070040310740c4039444040150f174641c3d00c032074546203d2146240c60000030300040e00c003803140b0741c5041080600b1600040006003003107544c0d0a0718000c84888001d1b00c13412000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 959101555 1250 959100305 959100341
    0xf0227010e0d08070b0105010206060a090f0615030903171603051e01260a11010e01230706140103030504030201120608150118050610110a080a03050414030408150a 72
    0x220b00f403e02981c0c01c20f0004440c1c0c4110080045140e510104d0040d00401002d0680b0910606000508014240b62661303907294541e41c03100005c00441d07440c820350400599807000600740d011420000d2001e180c02c9400b440c0f0700034000500c1004c0b490400c0104c1d01d101d06140000d0942c0742c0b8103a09074494490300156131003081d6803001103040c2c008030341c00b900c031110540f142c25100c4c0380c070305a07407529405007a030040c0071842110b18040340c41d4000e9004440d504c505240149140c0390584007000d16054010f12218031590200362442040000d2041c14201e80300940818100d61569800600511441c00000e04200410010f50f0282d10360750400005001600e09072440490f00c0c0c61480c1c08140300748103c410200981424000c081030a02c2024090781c005408401180003002c1d090b1002c9000c48600c66a6220b007105000204202c0f90241c509020a90741c042060300b01420800d102c150074a030000c4c02504104420000c039240003c0d801d607095014043d09a450382d460f9101002080340300c84800220312 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 959102805 1250 959101555 959101579
    0x109050d080a020f0a0c03030f200f0111040302030606010e1309050303073e07170a12090e0a05041401090303050f1f0b07140a06020408010f0227010e 66
    0x12440060320052090f03a0855041c91984100345944040c004c001402005245106001191143c0b50005206249090a02e406038000385ca034504c12501024896844c0c020300414100003a00703000d01208010b80308492401c150440d000203860b000007400042c1408404c5c426412140c44680340c185041012480070001070005041a40c1c07170b5402150101c000441c18000a10100c40743c490b4044683c81014840c0703e48032000480c000d0f1114058102106440342500008240e04160300c03d0034204482c0c0090400c2005038901405043d400040601c288600d401d8288206d5050180a6900c100680d40120300c13a1180d047c0740c5216504501451559424032036298280b5030180c005500802e2040d102942641d0352210080b10141e00f0115124456055081000340c820711602405000740900b49228030084c00d20502032611441d09022100150086400c0080e14001c1c4128000311801d20401c2d880c02d0b40300524010340500d2040f20041180e080d00c040d0005e0f034841c5201e4110740001910f610601c007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 959104055 1250 959102805 959102813
    0x5100512010209033711060c01060e0703020a02030d0f090b07020a0b06030102090102030f07060f1e0c0815130f060902040e1005100f020a0b010e090c0409020109050f0109050d 77
    0x3512403003c5a020788160b40000c1d40a01d001083d080c07031565804110340801721081c043c115099683e28090311416a40800d0004c80c0d0b54000041490b180d0740c01c000070b00c00386020112520b60382d008200324180362041c030840c21021340200446d20702c40c40b400c6d0005015044007209c10000d020180004d071003079101c10200802d05030000f0310000c500c0e00501029001d942c901c0105400c5c0c0c0b1a06001c180160410b01948000b041e88202600300b4502c41d00010820114101d60401124a403d508002c622009900c5641001903445216200740661401c02c0c00ca26100540041800f03090200a0180d4065580c9255510b4540c0c0260003005006406010381a038400c15180170f07420a00a0b502c3d50301c0201c0220340415503002100b011550080c066065525681c0da044c5c0358500241c040c04254043d003107481c00080c09040034507000c0d05010103101e0303241c00c0240b1b100c1d00c0c02c02c0c0c10030070f01e003d00e01e0014201c4c0587c0e0004a600700b240e0048600d007601c100c14000407900f4001030742c4855040041d00315558100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 959105305 1250 959104055 959104057
    0xe15070c0f0501020105090f0c10090504050903030f0f0f06060702010302070b0108010f0c05031b1e0406050d050901050405100f0f0f060302011701120204020d1b110d0c0b0109051005120102 83
    0x114001d0313000f8002030721610141a200c003210411121030f5400f040b034490032070506424041d801000c500b0500202c80e0b0780c101040980c5c008a0722218160000400c20081ca102618503507000700388004000102e2030b207a1407003904100050300072449030780c0200f10345045a1007901203441e0141d02801e2600e43d565507280c4a40a0800070800070003003410007101c008124807600035a232140b0f08a203482d0401c40c00082c04a40c49500c82c0c5104280c43c00d0f45081c41c5041c2800e84018802450a03664841daa191042034150031038901a102c025240d0405040c44042500050030080380cac244808002040710815180c10000d2100305507240e880c034142114000b05180d55440b12007124000e8a4445958100c0b4041d02d010120034050794007452240307030141001d42000c0c0d010304458085490b00150400302c59403c4444590000101d20000d040c84003101c2d80b00b1014480340070f900036603091040001c0c58582d90702042c00c9050103914409a0f41d0b0b0005100c0340404d0044400404000d0450000100d03107111950203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 959106555 1250 959105305 959105309
    0x1f200c010e151909410a0308030402091308091207120321050709090207021c0b1009020c0c0f04060b04121a0402010c021309060e0703020a0509070e15070c0f 69
    0x403940340700000030755074211440d005c80c0189841c01c40c451905440d084402d5068610864496901601c00c02025900d4104042d009580160010b6481e46031920410001100080c2000070140064880070b0001e00d00d50161411841d0864030101000ca00030b6005241100710b5100343c810004080c0304005058006070350542044031900000e0761460407049440c00c0e1002036410800180208104000e805266400303442c14501c010007940304146000040303e40109406010f59026244005010140155081c5d5000814051909500f4080c80952003521102c4203903040e8001e0351200b9050307080c0e03074803584104081c0880114058542d601d03060086120743d0a050200c5620070720344070213019502450000b034032a84d416512a41c5120a940c240918070074044940181561901f01d114006020b82c0107460800b130424006092540c9540100a00102154803150107005540144100180c0c0030162000e80d400c240d400e0240001f100324104801d204522014184264203030002c03414020581c0c50303100f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 959107805 1250 959106555 959106557
    0x20d06080606040510121a0c030601030e011116020303131706010e1003031d030a120210050c0d0c1101140a0b0f0a1707051f200c010e1519 61
    0x2075030b968100500044072002e640020000e103039078004001c5c0c581c0d801461241180300d0a141d05000e0482405512001e100b699070401240c400f10802c2229685885205001c0300b1240082c01b646444041020051080c01c00f404c1c1c4200400d2034040540d1410400c42d52000c581c1f28001c0d010943c0c0e04500c003c262201c49441441e80545c5000194034244001039600911842580804031031443d58191140805000d140d23054000c032143c658030071350b0305000a80e686070141d404082040303c0045c0003030a0000901c01030b000c182c41c02d014070142c124800d040d245040c0401d200098410003444c0183c0301564066180e004075800c1911160403080b184c0803170341c042c2841c1103051007451039000070010702804009026400150074002000b540303850060081c090000c41d81540c01603505c900211f0b501c000003807858000340700c407080341d0541150f1100760078040640c03034600985c444c90180700080e00d070012034000d2810020980359070b000f41d94844500340c20b51400e48a4207a9210503805051440340120b4400740 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 959109055 1250 959107805 959107813
    0x1603031b0b0a18021302030a200d051009090c06020106080d020316211101060f0302061801090f030f05120306130507050d060830070b1f0b1308031201030213090501020d0608 76
    0x5481080c81e0f03006520b00300c00180c2603801c00490141c804004c18000307000cc006401a420005030030005c5101c1c100f40580207000b0800d1183c14444e0190940c1d07159404005207620120a1841c95030740072064600c42076034104009052309007414a426018442000501840740f07400012031941d8101c2113011401020100030b01070155200b0030070170b6100042c8000f942112040060300590307054400c00c0322100301d05045c17046c0c2580d142c5440069001054204640c00002180c0040030302104000a600b800520700ca4640f030f614044c0b0129003a00e11404200c00c00d02e841d40301107003800e80507038140c8e19580494401041703040d41d5042c0c1c0070f80e91914044001740001940601960906080b0000b040d041a6200c2507484d000c841d0b5210722815000a00c245c40c0d4450355031000619480000c2d8030801000d4500c5900d480b00340750340c61240038100c0f6074840c92040d07008000306030340d541030201081d0450303404a8112010601490b40b410150480709002011548001280402c1e000030f64004130a8503648012a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 959110305 1250 959109055 959109071
    0x71a1305010509150d0f0c0c11040c0906050309010b100905010813081b0a0f08040501170405060703050901091a0a0c05090a0509181603031b0b0a18021302030a 70
    0x199070b244030b01040d083e04402d818984004056661004080344030255400299101700464040121260200c002000500c2060500d041c084c01c640b94070740540c0c00711020407041c5c041090280400c4520301c104803e12401200054000c034084d070061082000c041c01c100c0007a080c0400040070007000c5c3c024180415000d40c081002100c016640b8450154051216480c00b80d46102001c1400742160844440d4443d04804500266140c41d00408091195400f2511a42414000b400070b0700c281418401104050007008003280d0000740540d004402400d00080030703180c0c0c040003409803078140000382c50041c25217001000381d914107000600c2a41c41000402a240d204c035004c4540d44112283c856000b00e282e0824881864001d00d101c0d006209040d414054808041d651803d20180050403400c000706586c0810505170814010341c0c054070a0452040e142c1e600741d90f8070004020192410140f1655070701c0c0c000c0d070901d070401740056803600180112503456064699802a600c220b6103421607074140428 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 959111555 1250 959110305 959110307
    0xc0a03050705031504023f06030607021b120a03180602010b240919030201080a0c0518060f040e090106060e060301090c09091e0c02030307020c06030405071a130501 72
    0x942e070050450f5000c2140204c680c10801c400307900060700007981395040240d880140c0201c201c5200b01414035800218440c4070702c0b14512078800c001400c02d402034206404000c091f9a011030003003148001d40000c005900c0e035060100d1800450f1501d81541803054800c882e0a0640200c81d28403a207040007206c040c1182c48080480c280da20750312455402045c900441b100c5900e40d20080c0d15441000c0d100c040c1003d1000d40040d44d080800164100a039915030303070600039942e026400503400791030b082c400d001031800703c0c5004000c3d00c01c2c107a91440401c90058221895691142290740c00d414104469440b1511443d42d03545107201070300c0039922580f03440c0c4d00141c2123008084032082030400600e004e05681c80d00365190301401844040c5030400401e2280480c11070300510900401c9609a10301220340100c000085c8215003c468805c0150740c07007441040301c03080d80081c0c424050181544c1c60350b1680c80c0e0b0305d4101c0ca4484660010082c2840d002440468620200040d083c10300704900c1c0540c0b800c0e40d402c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 959112805 1250 959111555 959111557
    0x100e01091d1902010507060209150706060b030720010b040203271501180605040623012c04020d090b0417041505030717040302100605040b0907031806050c0a03050705 73
    0x160b0040c2d28240442d41c800950b014001a18425005403805032078010f040c400201a45e4480111102000b80415000240304440c46402c0240c1049841a459810024400340040d9110503081c0d6440700301c0d0910300c507483c4080d001104103038400f900540d00d07424100b450b425109442c0022885074613003a0b5840c0c540c43c50014004480e9403000e0b050511907400d10410000c0380b00e44d40d4907074000b00c0e200d5100141c9500c407485040b0081c0ba098101d1a42110801803118103504200405410400c642ca4181001400084811050b05850414440d044d00d08030100b0040c0c020020300903241407801a0305414009000d14062049114012000051030344d0300429046004a0181e1010700300c1040c076800d8090b000704000c0d500704010b400d002d40242c0c020340e060454540c040300e0403001030308101000d020307002d0139000700d0014003001c540c18010742c0650b0b408a244848000c0041041585510b0000c027070010020700f11020b90b0300b2800c217000c185062102810a030b1b104407988000a441c240014021a03c100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 959114055 1250 959112805 959112823
    0x6120403030b24090126091b121506030c0a1202042003280c0e0406051002030706110c0610060206060a0521160e040c08070303050a0305100e01091d 65
    0x54512410850200011500d5a0704001c2c052104a0300c0750b141e40b282540c4c43c14092147c4d680da4001c000c48410804c00501403c07041007803d008446078099800081c0300400c108551542121452901b55525030002c1c5c5050130901c9c0c01904094541404598045441408200c00f40262003c0c4030700da405409032914440003010b0181c0b40801800410518207a40e401c3d07200341d0703c008405040a400e40c00131001101c200e10002408920103001400c0c0c14205070140d0801030000325010030404ea0403050180d1244140c9500411040d5202c41c00c80624071103000f55035103004484200d805914014008103541c2481c1d01580e00540315140004505180c004041820307250090454042048510800c0b80b800c084003000084500414040c130815074008440c940050410070001101e5051a0401d500c1c0411150007204480e00480c1040c000709420404503140340710701d481d00054540e030352540e8103a018060b412003040721102c10000a20703c440c5030003403030076038070141040400000001c1d101380e91102d0319 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 959115305 1250 959114055 959114119
    0x60806010515070f0b0c030a110405150f19180509040c050d060b0324060402070b190906020403081c060f181410060206010602010e1b06120403030b 65
    0xb028258001035001e4080c2c10700328480e201c0a4940000d0b6604d00c411051308440e420240d09000c82080016422400340b010303410a440704d01c0d032415040a0100e07004c62012110340c6410b08000030701e0620084064112039015600314011400034244887c010006100b041c481c0350502c000ca0004549032030325950640c02258000d49407421146003805004c40b110b184d1a0035140181e50758020310468805005064013001603450504a00c55080e0401b14100310103003405000e40c0c0b040c801100051144407400c1d4106103d1641408480710a5246102600780142c0041016001040001c00c01078210701601812480d4090300f1901c0c5025102c45085400d2072243d8480d6804801c420420310740801200d03000704101140100d40c00103001084005940e098030005c0301d03031506139010811380c0d50500c8218050301083c030090200c0f10700402c80640d80d00403150084c540c80d554010910040e07440c002150300710102c14400311418a05418050001d20b504964503000e600d030038403c414504042c90218043c1e07000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 959116555 1250 959115305 959115319
    0x6030b01170702011503050c120a050d180f0e01150519050a0306080105191104060e01080a1b020d0905010521100f0b07021f021c0905040c050408010608060105 70
    0x40070003804098090602400d6540c1e440c03403000300590840b48031000d14000d0004103810b10b105010300c41c544606901626950304001d424070b00145d000320740e00101e4649071030414060302c41034800e0001403034540c0c0801083d682d0740800048018044201d01d040303031010502e0b5480c841d90b0140640381c520070140604001044014919000c0b0b000c1e50141030b51100701c2c900000d950340c840b1400d03421a042a1078045000c142882071070341400c0140159070090031815140d904040c649103001d8201c0c0c801021850501c0200710004210514590003090420f0b41c000b5070705541800054040e440e401c40203e04000a5111500030903954026070840d12100d010748280c200c4207100c4c0520286150001e03040d41c50f41c030031190340000c143c40b1100c0d40c007010f8101310341320340e68030b2405204100000e202d08400e007203c0a004888040382540105045140076000354940301c0840e400e00c42103807007590941049a20920b020a28400150711002510030340b60008000c00540742c5494040d13542c0c140910030b03d0f6011302 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 959117805 1250 959116555 959116577
    0xf0d0608120a0804230106060903020406061b120311041401110f210f07122303010302040b0a091506230313030516030302120a1407110a08041d0106030b01 68
    0x24034031255110340172844402c113650001221403182550784551007640080c400800031320075450648500e800414141c14154021104080043d90310f0704003220107451250340da13600380301031030090b081008030462a5600700d9071140c4440b000c06c000710301100740b64009000070240018074840060f00a03041000100140002c01600d0342c00444041201030711044010107220300380002c7e19440c054503400348540d00c038003400f45043d03000903c0305c0c00c0354003a034194808802c0000314807140303541205c0c10350fa0141c1d80400d0444041010620320b0f281a80402001d9141142d245001015559401c1c02d1b07400555600402c03403465403110020800d02c0c003c4c800d4096080001c01c07540307128102c501400501c641015030901500d82100070011081c001e0544c0440d8000440388109110307a1803883c0e020000b1071007001811081200074004440040900341800460707580104490010054090401d610003030056079140c13607084c00c2ca48954004100001d059120700003098984c003e01443c848820706035100030000e2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 959119055 1250 959117805 959117813
    0x310060f1404090c0e12030a120c12090602271e030c01180e0f07030f140106030b0d0807050c030601061d011808010e1c030c090e0403050f0d0608120a0804 68
    0x43c801ca000b005d2290842540300c080c1c0307504110b007500f43c484201458540092a8001c0c0001d6484049145000c2c54541e8041006812507042162007000200c009480d40b010703d0420300902c9481040d2280001403a07201c014090b2401010a00d201305407440000d18200141070301e480700c40150285e5060300b15603d550300d203510a90a45079101902611610301c41e58480b80030f11000e200ba5003100c00f406129080080458040c040c2c0746043e00d400404104901200c90540044241030203404109921003e60907515030342d4a1248054540152400d6614810f52503c0396941c00490656170090040100000d0f80d40c1c01403c80350311080b2400e100280c0140d09a0044901c0c3c0c403c4052000000b0389080c01140000003441080c8101c19808002c01c8170030b8001c8000303034801401c102172908040c00c01c8542a0960340c041120700807604070311550000c41c3c07520302e40ae9650f4001c85000c14031404000c1807020100c2001e410440c121803886050302c402e00c0180c00b41d0a11442081041c001140c00301c03000c41d00007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 959120305 1250 959119055 959119061
    0x5010e010c08090607050c120109030f050703021b0a0902040902090f090903031518070c02030115050102030912030708070c0e0a02041202062d0c0115080a12090b0310060f140409 78
    0x501c0c891020741f1802c8038a01d0000b001813070b803c43c1010960795030341340304020943c02c03903410700300280e1781c2c2049410601c0d40c0d50000c0d590b162450183c452030b140c070b940c031b007c250722100d00c290041d0000d03810546d1035036101c1c890b6500030b40000441c0c500c61042c40640e04a00c0c1004a80c25006103a10340242d891030b91038101494a000d0381c41324480d000441740e0f99541c840304003813050314020112a51011120302241c0105400d44d08500c50000c889038594101b003000f81c2c0c00200303c842d00c0e1000c0e10f040d0ba400d00c4030901c1a0460045003005044810300081103c1000310203c00b000995040002c00d0035aa1210081f41e0200c1c0100d005002455100700b01840152030018050100340542180607840c070140e903108200f420180c5101e0403119080402d014921510a004488120400c1044e40b010300740745c4041d40342e03a21441c60300948241012211090303270300e10801008011302032030190240c0ea41000e003284428800b00b480344e140042c0a4503a030741da403140f0031030f118180402c2142c034403800c107810182c0f12001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 959121555 1250 959120305 959120317
    0x1020c120c0729040608010914060919060f0f0501140f0a030b041d0f010606110d111c021e03031b0309030454180f0c05010e010c080906 60
    0x20507459602d10401070f00b4050b005001404039552480360302c3d4940185001a141c1e800c0200300300c0c030740410801c006621072450090b48400b00c01c03108554170007000c0740140244200e401402c000390480d41d0200b4070400014903003040390001c0e030f25100116169000800e107030040d52030b040c0c4080810000c0034030844c440d0308050074102d0300601c0000c42d50042c44048d08601e149201000c405d030442150f0f01c580314400e200d000300401450800100c5540c8400c0c080c0d031500e15000c1803c2c20b00405c41071081d6030080c200040d807161509002c0f00a00701e500d080c4007a6030b40c2a050324904058030b1f14650441040d002009032402068025106241040000c2c4540110b0704028003040030341c4414040026038403122040c3e00c004020007000401802500d030080e40c19881034240311003078280d00010070420190311002e00d80c1d1400c200c820000b810100f5800303480094550540c043d144010b03291040080c07068030700686044a00c00d032501d000c04049100192840e407800f200c0034004040c10b00010800381020b50040c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 959122805 1250 959121555 959121599
    0x1804260306040903030b040905011a100e0d0c0512030705120f03040f060b06070c051f02100b0a030b07080708060a051309080f0c0d172e030b070201020c120c07 70
    0x91906c030030402040889020740350903034540c0e440d07000c400c1c910f540c00c41c28514000d9080e81c51a646002404000c5c210400d280503141c002d40d41c401c6d0340e809210308014007401400e001420003c08241d0008480d560740c102d0301044e038060050402c0500307078000c05000c60b11300340006411075003541e54948032642c034080403e0083e52090784505a42420356541c80040441500c5500c0111701a4141818800d040801800c14100800a0020801143d400041d150034542c0c0040002c580900ce10001c100a803030319900090403500c451082c451000d41010200344581600d9071000002c0c0c1d19103041184203801481803135044065041d01c1e25020056410918015008011071840d0400360004540c0310303842680d2881c22908405141170029501c030b2841039074124900107940060424881c440e0310842140010329081899000c104581c83c1307034120f00740055805c0344401140340390850010b4081e41c80780c0d038801514050b00403401e0003004400c041d00c1041c500c100c0108149810401104000103141c0786103a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 959124055 1250 959122805 959122811
    0x712080402010c120c060b09060a051215070509010e041b111207030e0a0806040c050f010e0d0606050a061b03050a02030c01021804050a0203040f0818180426030604090303 75
    0x10f40861400404424403011583d03442040d04580d09148041b600848040c500c00e6103000305000e01c540d200c40140041d00c2e02207819401246001a00c24030301111407902c505030071900420058000e41240107404d80000030389800151032010402c000c11540c075110800c1202040c030402000d0144200034403ca2000716108607800c4030102992811141c00a60044000801002003104103040c2901000e00030002c40004002a06007951110b030510317520700441d03020359110000484981e2141200d6000345801400585003458a030410301301034482405550300030b0400c0f0f040003640318810f00c1f092000700c9512180c4c49100d455a43c0888813a441b40b42c0e15811440140400070071340c9428270040c0140c0c10143d01c0090f800b0500d1701400b040d50f10040c403202c040d42c03050040002142003501c00c1016140e0200030250b44a10a0900240e0700d801d00280c0d40d00640000406549605112081d80c000ea00641740b040800302107034203100c298140c0140d0002018001c0c00841e02030f06003500040c68070344c401d086c08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 959125305 1250 959124055 959124077
    0x50a020702150a02011401080d0c0609080d0f3602030a02100c05010b2e050409020c0f071202030d0e03031b060f09011a0105030c0409060b030714071208040201 70
    0x80e00102c0b60281071109100700240c0d075015240c091040720540340c00007000d02245e40c9013400043d1141d100310002001e000300d0280880810103164081514035030301c2140b80d601c50500d10307480b400600001c400b04880d10715041c0d69030040c86c04a5518141c100940c0c110022040380c00680318081000c00c5e1040741c05100d5801c200c401030751984140742c1526040e6850102d41c10160800700c1c00d50381d0100000e4080c10b00b001c0b100d01500f245101c402c942c1441d80b60000501c1e0258a0100d07514403680d880000403900c0400c070358501c1d94000c00d1071881e10b02070b0004c1312041a101c29141da43c000a004001b54544d00c2400c07290078007802802c000703954400040c292400c041c2140e0344143c42240d241e01440007600800c3c200640385a5803450f4a420002c000020410b29030a000e600d80c0e02100b003040c2c5810301c0404800502d40e0a1032400300c4015001098040c0250381da42c9690100680040c0c030380801044400c40404c40c0502200199030520703402c9040d011549003200010f4800b484082d1045e0304005206201c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 959126555 1250 959125305 959125309
    0x10050c2208031606050708070504030222020c030c0c0a21080d140601020d080601050d0216020406030629130902130e1e07080606040506011b050102040513051009050a020702 76
    0x150062540c3c800021070001c1003860f02004030341e0010b19440a004140c024001c8856010b410350301a0782c0d0643c0c0b20a14803000c0916011207085811188847d540001405002c643c000b1025200007114132040340d507a203e90800300b01891525000300c1700c903c406442903401d62182140b5100c1e005003e441d41c1441c0082082101e030582e200541031580002040007030004650f4100480000c801051030809440d08050780020001d20a0000c04044035030081a68142c1d01080810880350315070040c0708001e20f965070305e04040030f00703481c1c41100d03081c0042b042001c0e45c40100308204400c0c050014002c60420000108910080080c94004d9070045586040340c054001184161241c1640c0c0c48020300e141c040f181c44020201e420403c01e042c2c542c000700000c00c114480065981d8103c58101d87c081000d554031801228086100c505c0f52a5043ca01040c000074410190f005109641c000d440140c01c80d0300203100c003c10380b001907030a40c1c14140c2310242040110710b1030380541d410410034540546002c003aa00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 959127805 1250 959126555 959126557
    0x3010b0a032d02031e0f060103151d15030607020304120f0218090601060e0a170f100209010207060f0f0305040215040303021f0605031903030609020406050c10050c220803 75
    0x10580c1c661590010502494090340c45d4039403402a40b9915013070807441c2c003164258000602600d054140340d1904110b40600c0700d500103000c040d0540d0a00e0610301e49010114086c180c009a920b45c01042c600d10185500c1c3c00c01285003846224a6001103143c2440d0617124188424481801d42d036841a400300c42005a40c2d00001f0284141990444001401c21a03c001d0514106034000c1051101e84258003029460329031031030080318201502c2d454010945a211403c00741d400c03000d030185015152450383c9511856010741000042a0700b2111802d890703032415940050350380f9000b40030401c52403821840354404c0e04451790051018200c6c20000124003010800c03038009802c2100541c00004a0954035003000303102c4e111280541c4030a1085910b868042500c689000b4075010300d0001c00c0131f503002414002d803c80001080085011950b80d0380c3e0301d40040c019005400f00512a0054081004800109005140c000c2c0450b54445241c02c100c142c0358042e0400203d035101800c05994000035507910140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 959129055 1250 959127805 959127881
    0xa05090a1e08091c0c0501031a0409062408010507260601020106050319021e06070803070c0803040308040b090a080f0a0207170717070e0112080d0c111203010b0a03 72
    0x100000800c0b02440c500205117040311b0300801c2c101458688014145000852903040c0b4081c25100000c5045076810900060a021035003060f03510103150401008506031b980c842c00f100d680340c00070071060f02c810a084500d801a90308681e0380804e07024406030441740c8171200b2600048140000100d05999070082820809010038070050141c0c0c10050b0000e50420400d64001004001810b19a4110b05e1000880c18010240c000d030403c213001c80003c19850040c000c00005540284620361070b8685803500800d00c450441d0100d804a103003030302041c641440090481c41c030f07a07406a076440c00e02c2c000a00b411100e4120b401c800d0308500c245400024803a00141040e001106990003503d0028100f403c4040301900c1065182aa503000345d40401c803030003048041a040d40d80c8045c0b4030b4004a81420004901d005200076502d52038900003011000f1070700400d800d4a13240f90307801913508002c0b0115500c001c50009104107101000c08001e007030320191107035000b1821031500580d0b00f01c1c6803120f0303070b9030f1441e20280d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 959130305 1250 959129055 959129089
    0x90103090c08060a180804061b0c080607090e0f0a0b0f0d0b01051c030503070c060b12070e0601020312040b0403021212011806050d0f05071d0a05090a1e0809 69
    0x1c40f0500032003000750300468a140554030701c4004280c00c41e680d0610130344100d00c035080c20090003802c000781d000700c20520b5000d8a0303000034400c40c0c401d85076400561550700a0b541c3c0c001242c0310400000300307540061440c5118a00820103070145e5a00c0070240c0300a8500301c40b110303a000c1d08000c50130710603070340700222618800d00685851529604000c2840050140802d101c48040a04543d07003000907404812294030083c1440e00d82c041490928107080034018904655500107640e00f610040c55100054000c12595060401501c0e5100d800069881c0e01c640045120740c0300c0b0050010b00403034a0120ba041d0844e00c64811241842030010325050150421075071054040e88446c0104030041e800c1420303c4140082050401c81c02c0d190000048044082c2c14004080c10012010841440f80c14000c21006010003141551548401004c4140788801210140d50480c03611010a04032a400100c060b01158002c00e00510011417003060300426506840441d0300903405c2052142a84400b03120741d810800c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 959131555 1250 959130305 959130313
    0x10f0e0610031b0809010b0607081803100e15060108090a0611070209071e0201060f060e18070309060f0e0c012007030f05061f0909060207230d08060d0602090103090c08 74
    0x1048011b0f0a5501c070980710381c4100018080800401c604000b1280c1c40c1921201400030548240c2c0424284040807210508031850080710f0300b25500c2c0030410a041c4220031303a1740c84155907060015541c10714180c03000c00c40c5e6400340e680000042c15036402000a101409120b03800c20003e54000b508000c0c044491600040d801e229154043e821200f450284101b6800244045402d150b07101c00c2035a010300c41e903020803409400c1c1d40c00907250120809142c0001074901c00341494000b0014015000018044507510b281a210229001c054400c124491b56840d0151804e1034003200111030580900a22014003d94100400100b590400c10702d8001d51190a041080c1142030800e142859402071110b448002801018884c04282501c1c10050343c0c1500c0b8005103110305420082e00034084c00c03000401c4010700e034880340a036003d07028901e00704c030b605071003104d4420710004400c031131065050355150740001503d03000d180042e40c0345e0080d05800b9010300d0002050800b5440d80c1c13014085a078030920392a04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 959132805 1250 959131555 959131561
    0x30309040f0212010b0f07020108040809040c030b0a0909050a030f090b071505060118060f200105040618080301090902061204231209090a140702010b0405010f0e0610031b08 76
    0x6006083c0034018529144500d0500240341004065486060802030401a10390f0001e000c0107c100182c89007030202400400184924a20280c02099007031030325441100c40003000105d041490148102c01a07001d0082d03d000542580c0507904144484203003818400120408100216404003800f03486010f06204a0100400c15110080b92005000603040024016050f886580b080c0c0305a4101c4000707251498110400420072108480c500e01c1c403030351980c110f030595842118150401805140254000c10050021402c107100e10011014020078100c024001003100358140c0e4459040c090015042d24640b01965890a0020000311811149a500c945500c0044501600503254555038400280f440c003140c8840350002d8019410741d1442280c0c0140007600c21a200e030042c030403130703943c00074a06600e040c1504081e02805c262940d02c0c3c0660f142c02c00028000000f03207450421140700454121300c40d1070304018494020121045417080c540c907a004194002c004000e80200c2c60500d64511015007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 959134055 1250 959132805 959132827
    0x7021203070b07050301030b0601080402010302090a14030d02070f0608100902040b1b030f0403062a02030a270611010b031e15040203031606150e0f070f02030a0c02030309040f02 78
    0x70000e003c0b01c0800400381300600005481548150b00148242018602941c461004070041d00c03c11001d10f0b040480043d000070000581301c0e12010501c000c03403d80c0c5018085260407a41c411492240c0d04101c1e0520b1001c000301c0d030003241101c5e04a69004002c2c0400d0f900da00501c404ea0b40b0580c4010113090700050402c031130310080c1031305220084250028601d03040c80c4013030b1040140594000608015542c042a00b0205242c05142c0c080e0494512404e01a000d407802c040d440c0e030408248540410317080c21110406011a8410710403951100200c0095a400e04e08110760f2807014000c402203a641e02c11030400507540420540448118030056103140401503450541011207100141c2443c50120050100603940441650720b40f518014a06040d03820a09000e0003414086081e00c141404038940801c060030710030303040c1384980f48481415072241c03901c020440d055811140f100005804c00e0200d038500b40d21030903100c003009000408072810308005000017800c5074240c2c000a0640b41d4000303425803100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 959135305 1250 959134055 959134073
    0x91110140f0a0f020a0c0b2101030b1b0a0801030f0201021f061404060807060c021c030c031d03150a0204050405011e0f03200105070b09060403091223030702120307 72
    0x903c0e1000d0030582d00c0a680304032500700c0394000c0618800000c5021a1000c0c22000b081072013594a2034540c0c0b84c0c1d6543c0c00c0c100310000043e03072103400416444004409039050311040b00d200c0700c101d83e20244540c3c6191517041500c44200d0080381140507440140c0101503c903942c4030201c0c0d01d4080c0004400d403a18600781c0f035803c050300d0341d680650708140c0c0c01c0101c03200108601c0304648c8581000407295041e44005001510f0b0340201400c1c0703c0300304200000303145d03001c48540607031882030f152940d40c44441c00c3d0241800c110151101d5156000398802c64040581c4074009820042030400541010703100c900040c2581e80076000300442940440341615130009510a0500400205252040b802e04685070090002c2c0b9120110701c2d23002c101100c2c500c850b4864030444030256046100c603d4641050341d0394685644c0c040d00c05030300040e111840824500d0300c2c290740040656022514400390289008014900340000d01c02040c0c60105200c0386000da205d40d50441844501c14003d5039960070305242903a90303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 959136555 1250 959135305 959135327
    0x30c15010807081b0d050d170604140412020106090c081b030f1f03080a0309050d020316110a0503061006030501060e010e0103050a24030c0801091110140f0a 69
    0x780364442e000400a00300041000e505050b02d41603a80c20441d424030101e45407807141c1d40010240d00c1107103070003d5943d42c4950035040d040715101c0c001045880c2d14042106880c0395800c0d81c60300d8040840882c00180807603440001030700540c000800c0c080e5403000d44900311070501d5604408140e940c0f00b0040749810090ba01620b117041c0074401801c40c02d200d2203454264078020302e17241d03544010803000e2001000940c0008011a40540c8640d5109038550004000d040110412510362141c415403205007400407080d01c0d041050781d141e68164290a8980b490516524001c6a8002c200e640010600f030700c0034403290784141380822400c40341c14a800c50080450740141e20031010031040e00300341c001d81e03a4481c50b0040c1043d001d10b401700d8035031110781d9a08002c0c1074003d40001680300340754115802400f20041c0e182140c1c02000e0711202039543c0e036106400e03140034440081807000903400034034039464031049608036010f907454040c0254910290a441e00e03070190340c0808550f00082030001c580c0d98850302080c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 959137805 1250 959136555 959136569
    0x50a060512010e0606010c060e030414040c0e01020c01030b0d05060109020318070806191503050c1503010302090604050c040b0d02091e010f0503090c040204030c0303030506010507171b030c1501 85
    0x41580b0702d000c09203480c1e130005070440b4100300d00402640d01303008080e000703540e0500c00d01003900d0b65291f0b914040b2040e14000d5400b03a010b2070030185040c0d003681c02825a012084010b8020b40003000374080114000c2c46180724039030780030501441101c0810300030801e682c00f0309401d22006960f420841100c00e0040d203000b41210480c0c0c0240342c107010514003c14041d81040030001c1038000c03500c0082400c0043d164103d02440c1c1c03c04030b00000404e000c0300150701c451311303e42034030010310140888010342075601c070074000650004812004030301241096482194803c22800b00d49003880d0310765201070f100b036211100c0f800d031094000c0f40080c920b181071010515030a1103110503098902000002072f10060b02080507205109010001420b0207805025402c2140d070001c004660701d41d100c1c40c104103a9441400706078002490b00d80040c44c0b0354002c0c0100c56a0a4102e2002c0400c1d0b01100c01110190b032008007500c095042c0d220700d02640050400190074112000b901031300b0400c090f800b1b40003003008141d002e06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 959139055 1250 959137805 959137811
    0x20d1103010e060a0b13030f02180906040b0114090c0c0c100908010609050708040b04110d06020c010e03070503040306090c050405090d140a0e0d3018030206030a0f090501050a06051201 81
    0x610100b1161201b04201c03907000101105203041d07400011003800d0444c005818012101d010055907610110b801c51103141b1411034001e03141d0701c1c3e4004141008080d01240c0d0080c42c50408180c40041c400c000c1d1003842c0e501c0b81291061117008010615a000340c00e840c40118450250611241e8400c2c040c0801504502404000c10314240e80d004040e41401f4101602000d10170000c0b42c1808500304100f501500080c02d480b69000d8240307014002540240710f844034035464160700c2d00c08414040201d880b145d41000055003060b0650311080010711801d9012154010503250001301611a8000c080c0301d4403c0034068403106014801c0070301148904829151b038a4400c00420b111a60440590b036030301042690034a40c403c03400d20b020000389007400d010800c040c003811243c40c00850b14160310300910259680b00200280d08030041e81c1c1c48541070100a502203018000a110304846901590800c0055200403943c2a01a05c0341801c40d801561103002c0e264403400c0a11507800c10610b80701003014284020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 959140305 1250 959139055 959139067
    0x3230d020a0b04030804020f1f0e09040804260715020f0105012103090503030f03071d030318041815150f0b03060303281407050c04020d1103010e060a0b 67
    0x1c1c10b01c0c003100030710050500100e0000301c0e040d5140c4002680e1344d64005808080120101d0075100000030484080400245444684000c1414155599401750f98050300403403e00341803075030081082464940306d40350031201c1005008282070401a0b4002048943d100034007403005d0040081c10107680c150300102030b030304040040119000d003120144050762101b00785901d440300c6160490b00782003160301c003a50503c40400c2c8041001c0d90080290b0040040e41c481455a250740b0501c50201d0980c2102c4aa0580017070200c01c403a42c56080780d9480342e1400400c00901c0510007460b040d82e02d103016100713480e0003a00721040719a40c1a18801c0c21103518207198080c11301480e061411441e60904d0051304504040440812030588080040e1074402c3ca41c0300c00003080782c0e00ca099203031012400d0400c0c0c83c0020950051f9010214450086a0307510390800050880b1501110600000c0c0d4130602241c2c1005594408400c0d0360242d200265000e496005039403045424080200120754030701d034200c40240d000030414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 959141555 1250 959140305 959140313
    0x7021003021603260a020310170c0603042405091b06070f051609050618040201020307020f0307050a090e12042301031e0516050315091003230d020a 65
    0xe110060349450b110f051840c1c3c0040110800b00450f2450007000c6054040c02170b40300498000d54410742d00b00140c02890380d500d070b40034250070428802c552441d410000c0e501070036050030001141d100303002c0c00f06905030340d4118a0700c0c6094040d04c900c81034000d5680081c003014040520030301c034198918120220956110708005405d42c0300d000c3c00103000030450205242000380603c503010500048601c2c80f03014998848101015000c21520603106010080551120103540d000181c041d540682c021800c04841e035082c010115103520f121035040c03013450000070b0305984020542e0068134a41401140d0304600003101440d0503a80d0300104684403081c030040c041128004d0f801240e2161001e00956130450f2100141c00034401036110101004d00781c0c1e260030b0148a00c0e00154015440540c0110380751221807411203060006486c0460b500769840300e0420180b5000116681200310f103071001542070b603207644484105803148002110844641040c1c10b01800500808441d0800d600141ca081e00d403a9031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 959142805 1250 959141555 959141587
    0x50405010c1104060609031502031902031504020a020a02150304032f01061706060d0c05010f210506030607020714040903110a030801170c0a06141303080702100302 72
    0x6990400a015511200303101508a2541c0c030b00350041c00400069480d00c0e8020f11840c4140003d440b07800700f41842d051100700314400c0302e209803d61303484004911183c3d4810f01c065803014000c09181e010400c2144e0f000c3e6598402005071000540050a1408081c81403040f040714a0400c3d5280354801d00820000c290803010303907041c004901d141c0b01d1080790310540c150921031124043e0b100540c6080004207041e00c52010601030103050750b048070342c85d03030740c44041180d0615015001401001c10386000c02c10b950103104c0002031400c07203003048041c0502d4000721041103090141c99500d040d0325082442194207090203003a8104000d4409890300c00d0030300b1079002030a40507026440c0280d9035498405c0030301d4403480700750304000000c0081c0d954119260800501c00700c0d0a000e210902c4020480c052015100003030038010603c40030b0828880d55207844815a0b02c8900c000b6560490ba0703042150042e20312019404102a51243c0b121b103445444900601c000a20200a442d0506104121a680840d0852 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 959144055 1250 959142805 959142809
    0x804021c030207031202031308060735090a0303180c05101e020d020d0201180f080f07240513140f070f0515040e0f090a0b340504 57
    0xe042082140309601d42246418081e40c03002d48401060b00704200b4807640031001380000c08030301070801c203800d40390a1b42c640c54110684410021800c030103e420407050a90b003004079081c6480c0f05041002c84a40ba404e120408116009281c582110f04c8080c00c05806100304890004018284600305940c4d540344120810f00380641c510030383c661000c030b00f201c0b40b0802170b071940c1c2004010202d002106002010f55140034070810000036004885449e0380e4648144100b4038261a5420002c0221405440b90840f5241c903034020380da885010440048207010800040c40064030800c400400c0d00d5a400d49810601c1c48820b60300841c1d4204130510583c01451417407950120f4003d8641c4501850645a1318070b4485008078039032407402516800140303902d00e03180c0c030422244242c0d030844c0c1410304900714444500c1180210b044c2c0c403a803100801e402c0340d501145c003a40918910700b140c0503943d05841304952000c1c1200c00384400304010071007250007d504564810400b1440c4a00e041c0901450001380c43d500941c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 959145305 1250 959144055 959144089
    0x306020c03090d05010507020601080c0d03050d0f021b150c0909090109060c09050307090c05040e1b0708091f0509011b060c0c02031216020609010e03060a020c0706080402 75
    0x2103201100568284210b5110750350007007a000580d101e82c0b0748a030181400301d400b8005030041100004030542c1c0800c0382041103c00810341e141900f0345070360a48807a004105404c00c026554855415148100d10040c2042070140c81e139400b40310302c0140e8043c41c2031580b81520310715280700414400c01c3c0409501380e440c0c40d40210740380302d100c0d074614800c2c0b4010242d018000d07040606010340030031901c1d080600003003035070016002d0300d48042d107403060380003502e101042307820008030208010044510b050384225041070100301c80003092115242141001d402c520015100030100240c0700721540f0b88070180c02100200000c905641010b140000380c0716001e5004000d060020702c060100359458155000440d00e17521140810407190f9030310004000070009d03c4e08070702070321440d094101064607000550f0b1100c0703280b00315840009010380c24054650490401241807000c2d440c090817860b43c1c1445114401e909110b00103803a29245940b05141c0443c075030118060003801401e01025031100b1041c80354910304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 959146555 1250 959145305 959145307
    0x1f0c1109100e072a0326010603140903030a0c0513090f0b03011b120b030a050a0b07090e07140f160215090a030b0c161208010e01080d08091c1e030c09030602 69
    0x3805e0540e0200c60040700301c17002041601c01030f030390a100c1d034031254180c403845e41c2c00b00500f0384034010305401c148058030700c01029072041c0001082c0d038544d070704014900304180c548941040484550300e05211020b4114918580d2a900e110701c41b10124403404050341000c83c000c0c0010200000c04400c183c504080800420803000544901c054858101c0e080c80c40c4054100c5201c9041418500d443c0d15100d14201c41d910940c00100c3c0d021845035902400b5983d09500ca040b007074494a1059401030300d01c0801c3c100c0ca010502002441500d01001380044510340a1240b050382c01038070401c404c0c40482c90100dc0412014417543d810345d01c2d203d20074415668094512103041d21842c100041e2401105568040a0b0000c0d00300402c0180d40e0281040c02c09042d100c0c0885a41c070b60000345158802400352031003da00c802000c280360352060b01250382100c144410341d181c140a441128114469510211020649480b044160000104070303550041e075070ba103000c0000d2602103800401c500000d210107403016030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 959147805 1250 959146555 959146637
    0x3020616060b01141c112206030603080313171801110f030f030a0609060305151509060f1f0c051b210c1e0f1f0c1109100e07 55
    0xf817554440d032000d002c5048002d4803010140e030804d05106081c4c141610300c442221000903443d0281c09102d05403984049007906580d900c1c008921050ba583c002038070f41084050003102420340407030003801c2011029100c07008091140300050038400b540c1d600d001c29580412181010f161022055038144079080c0c0000e07030389448100740c81000d442c003038101030080c07803a0100000030800009644805400100b0f1500225550810b44c400d440c031482c00c8468000001600081c0180351104100702c0c000c2009182220307403a40078840d024050b50b0140128085080c0c1540482404002c115514034050b450308260390176001d02000c90303001c003241d2030721400d0492103124003d8455402e00c42d49440c620041d01d002101c20000201c80c05442c440200c041c01014004440000c600703010640c0075004e001044190303551000310004490040140e0780644400c4640304082040340c3d50700e6003c0d40902003e26130b02803914103142050400342c0e000307003c120a01500c03a003030b05008049840f840d401c1030006141424000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 959149055 1250 959147805 959147857
    0x60909061b0403060c0503090f0a030507020d06022b0b030703170c0f06130c05120705010806040923061303081f08030d1409190f0c03020616060b0114 66
    0x10040303800082c40c042c1004004802c455015010314441c00f00c0304c1c22502c003100084c9c139035038840001480140014401308141c00140c10700c1e601610082e8401c010040c0703000c44802c0b400c00c940e41d810200c04030031021a083c0544c64451030141c0084110124041c1040500e103030381e011410851030301c00c12034000010170205800d4070144030307000b80ca05166041c1e80552078805540c200070940880b0445d05002ca0001c04141428580c680001201d4514001c1a81c1c0f4244401940c480b400100340f558800c0c0c441004500048411003061440499408640403c021440180341030a90003094408502c40b400700c4070001ca648140000e4204928210548903404024408405140ea58100c0b11441c0300024140500c103140350303c000512010102400d01944540d001e0544a00140424200301100702d04204d004c919548240b028092149084030404d564a41c0821010b8105030081046200c42c1401041440600d000340c0307000340402d1a0840841412a8051416000d48043c444608440000301ea120b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 959150305 1250 959149055 959149057
    0x31501110102070c18111218030301031a0a0e1b060415030f052d0405210a080f0106050417030d05010b0408010e0606010c061a060c1e0d0c0305031005130b0405060909061b 75
    0xb9012381001d0b40d44d00c3d07031a820014074100030300c5049480038040c42c00007410805288220481406004040c14000b1520311162034101c81a401d400d9201108200c0010560002000060241002e0718045002502c21804504454004240c14910540881081240328500701c14000c54074141012446a807a5070911910b04034003d014009058411802240408940c4001e000401126a100c120b580c0d0b550311940742d900020301c03440380410b0040c0410301011a21081e240c0500004100712810144000c4000c0241c440c00c0c1d20803440c60000180500505c20203000e01141c007614407008121506044000802e0402c680c0b50181443d9980c80d0031042c4504000ea1a5010110080004d81c40b080040020b54550304414007002c00c4c0d00b20441010356000d00814038409003003035511911507003002503c007901c095200401070540c0000b03908d070200d4580e58504259140303d03800680041ca81c01100140000c0b5040a000d5502c01d904031800c01500d4480003e4180d480380c86aa5510a01d006001d1030a080e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 959151555 1250 959150305 959150341
    0xb090117071e11010b0427080d1b18030308060d26091e0d0605220c030c080105102306030903030406110708031501110102070c181112 59
    0x100503451910a001d40c2d801049944a0030001c4020800c40c1500010042151140d86100b8007040806142d43c7c00b42803a507055104107409620003601c0e062468016004886d000e89a200c0d20070400d508804400e07074041d00c0e0242100741305070700c40601c500315100601480c6005018038403c402245000e030030000c02502034140002d1204e00404040d180c284003c20940102e120903020f5403a00b032001c5a40190500000007010002d03008001b55a042d45034074000e0900203201c11000e60030207a0021500401c44100c5059600400503c0d811a04516000c2740e0384800742c1c82214540c1c101401d04c03418503042c01c0f001e400c89803100c2d1201c42e110b14a03030040305201450a09241d0122020003000b244c0407020008500ca036109131400c1004850311341041c1c2c0f10340a1000090708441003071000400c2d01c0401d0701c20b0903000304141032040c80382d52580502400ea9000030000c0794071250587c0d08000300100d029008241e45640341062000899195012525000340c1d0f580038040c4054a01160081d0000300c80d0200b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 959152805 1250 959151555 959151587
    0xf0114131113051906140306060415050913110a11010f18050f0f15060103380a080a06020928030c09051014030f06070f08010b09011707 60
    0x14a4a000c007010742d036560128441d460003100114524903040c0440d08070801910025101ca0703003502480025050741c1e4000070502500540104000b0070b00718038902003146410103581c0e03460307942c840a00a01c2501a407000418440a0808a03030350120020682600c1c1c1001440c9440e041d9001410081405020406030601e9187d00e46201c03040032440145c40c0c0304205000300111282a02400b540a43d109240c000c3c481150f0003903034032540766601d0003200542014052401180b1400000040340480c0c46002030200e1300c0340e902c4a0000c0c040e040c12034529581d6401c59800041616114915450b201c00c464020246d03680000c030034a1980d1394440c05403501c1000c091285100481c042c2d9120803595602040d180d4980407480000c000d0082e000b1035101d41c00550030100c01134502001c0d1409101d505c0d644130b926000d00060081524010020300b0300c0780c6404d954080d00e80480b030700003802d0400b049c0c01001c00c47e40100b00e00d895a0340c001d017000c5010b01c141e03150745590b56250013040380d03545460f00302c40f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 959154055 1250 959152805 959152807
    0x6041403271807050702010201060503070e011a0904110a02060a05060109090e01060f030f02030f0c0604030f0302010b180a0c0801080706110f0a03050409061e030b090f060f010602060f01141311 85
    0x18443d82d010024081c818400c1e002085415110401c15036611900d100c1c03c0150300c8a10010700150301c00e050740900c04501c40c035010b402d01d905400000c0a480d05184580e44503100491070180c4658108020380d040051580200684c1c07c003000001c000706040d0040746001034449000b030308000c500b5403080004150b10301100d01e03032607240c0c5085100310308003460580c4030703100328900c070240c10001203403400c843c1100a0030a46058655a1070f81815903290800394290355840b4070f030841c0c946507241c54400d8404460704403030061604040420031a2103032a100f00030080315500601501c20001400d80a442c01801c040c00c8180070068914034019042101d1032070780c040c0449180070581c00901400c00d807550201c050090340d840d02d62844620070141c02d0b9102c035500001042000c19134a04043da0064825015540c0701e400018496181460030f0302e2280648600500401c04180d0500615402146140a0300760b40c0d407406075154041e082c3c06805a210b0720000e1f1700c600141005900c03100840c00303201b6400d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 959155305 1250 959154055 959154061
    0x91104030606030c3f030c050118020306280b0d0507030f060b060a020d110709090b04060b060703120b1c051509071811040512060414032718 62
    0x401380304407040c4142024080d000440c940c54000d00240680942035a0750b0f0744162940500141c00a0040c1307035815401c2c003441c1d01ca80300c00b1540030300800340103948092030700e540341e545803040c9403900600502c615070100e1102070070708080c5914010a600d0001c100000b082c0c8030b226030000351400b012100000c0c0702d4880c0d1200042081f607076040001d041e0780105001c201c2403101e081404484e1050958450058104045140b0200e000707021f407200c4c10b00d9140844581c642c4410803181220013080d01a02c110307400030701b000100540d9000c0c0303600b948401c0c1d60b00f604000c3c003036601500c1c604001586080d0151102e08554643e240c40c10007842e02c4000021214031901e080c180705896509079403010b0000312400001a00703095000800300c3c2140d01800c0d0311001d4030021b003405402490040c50140c0690b0301008001402d540f241c05901242e14101d020f4110703403d007403404000d0010086000705082d0401d004504140d0042c000b4600d80e000480c00030f0b14990329000010b05060b0012440c414050400c0c014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 959156555 1250 959155305 959155313
    0xf0f05090a1506080a06080d0e010302030916140f1008160c1209061112030a1806060f0501120b0307030212100c020d0f0809060601140f040e041e020a09110403060603 73
    0x604d0307000d0f01c0d41040c10000070b900c4160041e01d6440d2010080c02040c5500c2c81d0031480c1d44240d00a5030721035458002d0751084498124500b466075202e034021000f6a4010708010302c0d82c80d1082c0c0b1402025012962006100341840014000f50b00040018444010310401c10b21301d280141d14003400561301c48450f00849038803180182c404a05406444005101c4141a0303083d50800101c8010100000490742d0540ea00d41071200003815a0700d09041510080080350300c00910580104006040c9a501416044d070511000520780d481c83c0065428560900030100c540d40c0b0040f4070390342581c0e016100c030454406140107842c40c09901e841d805030450700e40000300751000e48c04189d44070000c1c2d940d5101110248000800c0740c440a09540c00e40c40f5821410101d5059806201d001c0f48030100030440714201148021505500e030031a45c4442c3c8074001400c1000300308081c80c00180b4030041401d14162000c0381d03d401084c00319180340907820905560300a4a885404150287c0780150741c042401d00c4039649910b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 959157805 1250 959156555 959156567
    0x210a150f030f21180501080622060b0d0e0c0d260f161110081303140301030308060901091802010309170a050414040b031f0f02040b03060a0f0f05090a1506 68
    0x220b5420b0111350140c01103a1584a05080d50140c0402440000860010035050300c0b050f450740400152581d4900c4001500f00406001d0b202406a48034001108034105682604240c1c412020611401c00484030000040840c4003007008640c0d0601010740482d03405030440341c0c501c2818070044090f40d0100d190790301500d24500300070780c040c4144038929216800c0c3c014014080945555140031034a007000003117440d1300040880101038000d1805c9a400f501c100c60803141640280c0003540010700d0700080262900307010a1640c01803050b40e00410858440c00e0102d412152440340007810982c83d04013034414031400506030204d5005a042060390380c0a800710140096000e4400c100340008175010003000da00c0d19100340c425001c0c02038090110400060368412403d100100c21006156607032852320114081032010300b01900f04051051350301c2c01c16800300220141c2d140c2c04044034a080305814003c840d441c1c5504411248180e40040c00d50300c448043c0000381c41c40440c490010f0300580400614140e02c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 959159055 1250 959157805 959157827
    0xe0402040902190806011418060f040806101a090102070512010c08010e090604020d0312090c080f1216050a051507090b0705150c210a150f030f21 64
    0xf9461608002e0540549040c981103980c1d6000c03408402c52442c1840c503100080220361324020040c40140d04540024500d500702a94000402c90b02040a12050000704290307500700c0b80194114009170700e091004500200000d40000a50328042601222079008102120203804002e1803211440c00c2083e140f03000700590407401d000030310f07a48000034141e40b201c00340b01d010b407a0f888041c05250381d41d0340030701c5040c000c0c0700411400c00820f02d4200d4595a03807441100445485842265206840c000c0e1280c681100c03000e4005160704840a080f4401c01c91604640300c10b400035881060319401d5041841c14030a82c506c01a0242c000c1c0c0600c10940038402000034400c0d02a40c0381c241e5040d0310303940140782038010b0305070040880e4402c034080782c0792000700710003580d11005002d9418a40b07180a001c0d040d00c0c1100880301c0901008003020301c0158503480c01001e61010110104420492800300619036916282c80082c010030700e50b4a400050090307102da103041c00400150084014560340320b000307010307041c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 959160305 1250 959159055 959159077
    0x1908190e0c13200319090219030f11030c010e0f0102120408210a0c03031505030f0a030311131217030f010f060309050a02131d0c0a06032007030e0402040902 69
    0x80610710000594801c01d5900854440718850404551a030b42e21703000b480d14140590340b010403140610078140d0000264400f6511588800a00580610302000b4100c01e04c050541300b1340200240d46000d0b40d01403058411a0000c036000b25079580e01c00c0050707041001c500801c00710100002408502c074036000400c04110703024542980d041141c0003c000060b070044822000002d08600700c0c2e03001103842900710800040401c0c0e0006d0307000d0368620000b85016414004101140c0058002109041c3c143c40b507a00c0341c50448200a242403030051078a0b0b11a079a60040e6100f050a0a8294080c00340c00c03210818840c624903441903590405040e000004682440381031000040c0400100316140309000d480b002c1a4030000510034080c866003042903441ca00103880c40300d03540e9a8480e81d08100c8201e220580c0b11141d6000e00304074401001030140d8003200ba0090300c181400c100c0d00700e042202c0384104516401d5100601c6458903034502d0100c990b1516800d12690050000c2000b240179a10b5500814000c452 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 959161555 1250 959160305 959160341
    0x5070b150d0f0c060509011d1504150305070e03100e151003051219030b1306090f0b041b08101221081506090a030f081908190e0c13 58
    0x10f84e42c1c0c12074080c450030740c9181c0010350115201907860a01901c0d11400348004210012415032900c42c43c040e904250302c8803e40b000100030700c410355601407043c41d4000c0e1440ca8128800c0740041c01195481c0030303411500700e0035695a0360391000400244120245618114030298450802c0440010650494041540c0a00840908142c600c091100f1100a21039420820303107000c41c0e00000f5001800010407454110246282d40180c0c0521403050101030303c8500c03c005024840c0c01c004d81c0840d000c0c8480c00d03018500d021042e080e1106a164140c0f42d442003840e01c4c010035560301e280c4010311141c980c080003454441c00109000c101c80000560054440750100105c040b0341c07000c04407400400be4951400701e42407003120251b5400c041c0002c042d0500054005194165a0344e615150b4401909040d9181c18022034421608000100101d1f40e0600341e207017401040c01c296101c00c0741c00800c8144207030314940c2e40541b1078601e4414041135080c0f06009041c0402c2c3c030040105003002d00001e01c0d9900f00c40c44 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 959162805 1250 959161555 959161559
    0x90c060e03101a0109150c03110f0105070809071208070f02060c030403030503180312010e07090e1305071d0f180109050f010f0614120304050d0302030c0d09050105070b150d0f0c 78
    0x24480300944080d00c1b895450802d804666102581d49604041d4482d1542c090441c508050301401d010385801b44c8207958454210b8944240054104411900300741c4c1807940e00030f140404100141c040c3c412143c1c1044102082032a10310000700c90348961165420140400b040c00802c0c950010055071041003a24400c001500c0b1a94040da00e030b1192296044c0343c0d8903c10014018448240c00f49580300c041424081c00b10760300c803154200882e404071410380400c104005084100715042c04218010820003c15500c105c40071201010300b00320042c080a030744524a40080e5100c1124a10350503d0348604000304498652030900c0d40c0c8034a28015100003d60038041130f446440e085105003030844007020864092826100c04103d5515a102c4100480784030901c800716266680207800c1c421188a50015a0350b0300068a05030b0030580c40c4803a000a102a5120130042642c00200311018140d00c440c0441e16661800c20404465040e58540f42d00907000d02190020012103000e218210707030241d003144030b400d5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 959164055 1250 959162805 959162819
    0x6070f0b09120301050d030c1e0c1d091509010b09041101180f0308090d0c120510050f0411130606050d050c0c1f0605090a1a04090c060e03101a0109 65
    0x11100307205c1c0e6074016000f000d0b01004603115941007051180f11307541d0010006200007408201c0710310f2080503110b241c1401420000c4040c0d080e80307100000c6442c440940c00e07141c040079247e15880300980d0524a08003c80c00030b658806c082d8002a810107005003001141d042c0342c02c041907035152040209000c601e200380c444104070004081e1408a9075035079008120241165070320310310f41e00940c3d041608000300305c10000c0000c4102c40300704054050a100b01542c803060782003007490542941c0054080ca850281030140c80c0c0c0c0381510046d8080d400005082002d0304d1100865482440414840e00051074114049071003903210780201940003c000082c45907880744604038440d80302c0c0030860201e41d441658140c40010940c500c2129540884000241c0c856aa2001c00c403010b90440b40201c03202d59415003081084410035044044200c1502c0420540c017241d0b1754000b640d0490301400082c003400ca19071401c9940d0402084284a00c224030a001007403048404424560506a0150104000540110b284 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 959165305 1250 959164055 959164057
    0x60f1404060305121635090307050d1b2309091e120c0307140613020603090f0102040807030506010605210c091903021c020102071406070f0b0912 64
    0x80c94101c0d01504881340c0e030900801455111407101700a0030383e0b5404001c04075805c403038030030106441100d000d800f4841d007800c83c58510b0002080030b104410309111021040e10005100703010ba8809030307419400f42d5003508045046d1003003104e40c0200d12643c9200440c84803080c502014004550300021704070f01c101c042c1005600399089501c01340316884a403000c3e01c1428460b010312609842001583d0036500310044c400c507140d000007602002c0340c1c000202c0004002c02c80070199002d402520150029041800c98400d1182440c0d001a00c201004404035254031810300100e10480c4811008543d500d903039240c2a038803905548425a128080d0320000680c0381e001d141141c072181a02d901d0716003000a600641136080002502d0700300c06078801d12040d41c03503448010505000741040c0c0080320109107548104a28016601c003001c1082520104440060340c00044c844140c4030380e0410000c144400301c0120318030f4003600d14040c00c1c422030082848184036212840c240908949002d031100c551b0311180b00312003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 959166555 1250 959165305 959165309
    0x9221a0d0b0604020a090305060106030203010e010f061205040312060f180b0136031a090d050a08040f050303012603030417031906090b12010b0105040509040f06060f140406 76
    0x280792080000951501d80b40d4001d064440150031302c219910303160380383c05113489002d802c00d40c00300740d0000c01840a00c02c00503811380145104400c08519078101107004040a4032a0305c8030820f6034540e030100e010540a007004142510650304208107040c0d480d031611019090724400c9002c0c1040c100c000319010001c41c083c1100d01001038403103808640b04241c820000b4604111526080b00c40c2c0c1240c540782d0901e060220380114044c0741c1c24600010401c0d00c401c3c01c050044c05450913075000d42103056649400c03074141c42d40b8040383d04040f24541d649082c110b403901000302000b001d900000001040018100409211021b850300015415080c030107804c90380c9200a80d40541294000722881e1255100b11005603407100e00c00c030620500c450f481c00150160b0321942c1000d00001e450b005085007a01380070980201080724440240014030003074002819a00c100e00540d0f0248400303100203424040c18030044070590740d2141c1c081040d00d070b990041a103070301c1e5a80980c0328651035100c640050f524160180e501 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 959167805 1250 959166555 959166563
    0x614090f01050105030703060e0a061509080c0f061201061e11060f15040608100e19080a021c030504020a051009091503061a010215090a020609221a0d 66
    0x2a90900005641c0da07003001b0b10384420143c172440042010082e958205000d10500b0002080490910b10150076a841d180b00543c10072400d4041000600340004444c08981c4054404407104411440030500d140f0401d104020100301140000800c11340c00240e240146404060003c00a4044e600403039590307000d031481040c01c0d803100e00420200b00100c2e11964005100000c1c072040d0010400206059580580c014403140e001400da8810040300c60107050b240e4403400c4040c00c054502c609090345844400e0001516045001c40c01480d00c60080000c25980c1d04000d82e032240c13106994100601604e8211002c81c00303014001d20006060800301c0690190810980f01c9014441c208008a401442e1403242c00310096203c19000001c02d90500c64079000c0690346450600d48a141000a440c180341103005405901607074040141000c40880d00844203907040390b41c259241c00b00390000d10140881f000301c019682d10301c000c502c45101c0550100d43c003c1c0301504640503890003c1d0400c0032819003610050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 959169055 1250 959167805 959167831
    0x6010f05240418090b13020108090d0c060c02070b1309060b040e04020f010228121107090c02030d140603010f021603030e0f0a051005061f03020d0605060c01061409 72
    0x101c542d445941180340c2c03d0340580800102600940c545140c20b48082e5556030502200049007010765a00002960340030381140c00409044014500062020702000304c0680300b82c1d6618000b141c414800e00c0890020b042000d403513030700c403000309206000c501030703a10800b44850b1802c4000910700c402c070f40c285d4040300d0140040d0720f195901c940900004108103100c060440c040e41c50442100c40e180e00801540d1340d1a080d6122050300070b8504164800c003105080c1c420312500d4282c040c41210300041c04012350340f2005000c00c0002d01500160701d14040c140882605a04041102920781070002c5a6480344c10304800900048110028041c201d1241110485071600c00c80e1078030010034003a0b0032a5026101c1002103810100410721172605010414004481035002101040c003d103e8034010307140c0114003110210000c80d15014010100200310500b00305050700404d480342003144c5544020001e0001600c03043e038811140340301d2402070030140120b0710544107e0f4509052828050340031380c03080c41031400003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 959170305 1250 959169055 959169059
    0x604090e10231f0314010b0102060612030418180303140708011809080c060903270a0306050604150f080d1404030b040f120f09090e10020f04030506010f052404 70
    0xf402c404030481507070501c00d00041c10010004009000c1841021380f03007400012818900400241000806011a44203e00b500d0101903c0d01c2c000c0100c4040755440c1ca82e000d131005442010002a00b085540079050006480d8032005154141d003004103094840c0040034002e50b81c5400640f0242c20a00901c100040070040c1c07140100c029600500020380101801da0900c409881100d00d071100444441c0d200350804075454540b0103285044018000458070100c02c0d02c0400d40100f902c040140c03201902980e01d540100d60251155803004401c42240500d51500c40c0c0c5411400040c0c070710b2440b58250034486c0c0c045c0d40d01101c0c03040c071440c2c42c40d101a0710243d280a01e581c403041d5200c04040c00596284143e401031600040b4501004400001c6a85072402c2c04a44e4a0020f48203000c180d101c04042c0742401400510a6008203a4642c05001c002d001601c0700d103a0031206905000f80e400003803c034400c900011070f46c0040c8400e2001124030841c5d8402ca401003514000341110000c0000c0d00380e002040c07000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 959171555 1250 959170305 959170321
    0x1b28032703120c08071a0108030c030304201f0e12100b0105040b03040f05060601080403080703051807180506240702040b0d06090213150b090604090e1023 68
    0x16a100c690a4504901d5465043d04c5249a95001a1044840e1003000710079443c803c0700b41c06018010000348011310706091001a4050302c0b444010001014204481c00c001074918214040c08844030b4003a007030300300d05140c1050002009104418002c04120740100003490780c0307040c0c4c1c81404100128009007400404198130800a002d201340814141322017408041041001c0c00d01851091b40a80400007400380741d4201542800d5010308a05e042009020800c80866040322481c3d4100005d03180014484e900d50000980710810341c109090103004400700014008115401c200360810702c3c00b001c1006032108410800603c51040f010354201d5170b203040644007030740780c20040d240041c0040c03c041121041000024010341d440c05003211b041d0345d20080035046d4184048002e10b0482e59060401004102e416084001b00b00343c880c0004082d0b001628404544a81d001d80700108031080040c09800c0c0c44400c00340e2542c0c2c0403a040c882d8507140001f030351180c500c401d40d41c2d481ca800400048403140c1721045 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 959172661 1106 959171555 959171573
    0xf0c090207111e06030c3f0c070606122913030c020901080601061e0503060906220203100f05061b28032703 48
    0x201481c0001c00a01001940c0b21040711035000420b01401804056443c5811598014a000c014000502c10700b001030150381084c0d80198079450054041c480860880c041d142101c0d11030101042c452a202e0007120f030700501c0b0000c00514018103901c1d100d0540d4a1507000b404e01c00140007101c824800c50f4080a0300182201103000c2e01c603d0414064031200d1406406001034a40015103402018045c0c0070903042554098001500c5603581d0320300644601c0240f0940d070110701121002d641c0d400c0110540f07102800b898580c10308617180c0c0014466060401001e458003c0d24502c0c50408000e41c668800300304c1d8841d5007000d680d038501a40800f200411540c04114020f85070350f8103100c03542d1042e05030354040000d085043c035441101411245802500f180790500c0c1030310b40c1c000c515540c05400000c82080e000e500d070205c0030b6401d00e018100ca46411322100d441c0503400ba206100241a0203 = true := by decide +kernel

theorem cover : BRFrame.Cov 958992805 959172661 := by
  have h0 := BRFrame.cov_init 958992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 958992805 ≤ n) (h2 : n < 959172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
