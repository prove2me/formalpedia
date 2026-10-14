-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1710
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:23:46.005336+00:00
-- url     : https://prove2.me/submissions/4d657cd8-53e8-4453-9d93-2546669897a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 307374100 ≤ n < 307553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 307375350 1250 307374100 307374121
    0xe03070f050715032c0a050610050109050102010e070515130b070605181c0521060f0d0b0c07020f0901060f0e1005160813060507020907090e0c07020117 67
    0xc100c03607842d070b1825000846104180d0030380780503071031707001480d50f001c2402c0071641c900c4008841d1101e4071104940d1448501da5a007482e1210a841405014490440070002c07580c0c000017000241c9020700c001e0048803d03050364185d9824590181510400303104400921410503001581c03c080072680c003184502d59111003494042e8000c0000b6103d040c180703c00980503000c0c0b0608034020080c0c0b203008240c022400c0c004003819000c3d1020303141c1000300c00c02c124504031680c00c850224220b00c01550b0086410301e0310800c55120783c0c400c0114096002041210046590540e0030340e44a100b2260080c1c2c5c86a1900c000fa81107402c0f4000c0c0c0b58031030650800490801d074001949004010103403941d40c0685030003020071031492181552007000410400c08484c0641808682034400c510491603e410202e03103030003070003220143d03421520000354042121000c0d840d200171442d030050240e0514040d0941414154840c00300001c02507040d000d800a010002c45e4428074110340074003040f42c0e01b006035042c01425a07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 307376600 1250 307375350 307375363
    0x1d1c0501050106030905030f0702010c061d1e030a0c060e010c0906080903090609011209020312070611040803070201050f070c0b0408100e0607030f060509070f110a020a090e03070f05 80
    0x26141507181000200384640640b0070000007030b8100e001942845103880d00c5180a5100350030490400410300102400640c41c2e000340640742c00328101150342032070304002c031a00e8240f024040400400e48410b44181c006004001c0720180b403211700e8400c02034a403d040c182c000e8580c0502c3c0105642c070341044019501d80c800010015141d0f5955214080e40f1900c88003641d9004060a0340e0b4004030400c0b070300055600440005110210040010070b045131319800203803c045010820141602c00018400d0820040c0e01c41c501c91048040303286400c060400741030f19500d008010000307060080c00540950b59107031003001e84145680c41882d0300425601d58000742c000390014400d0301c0d074610402d0501c03001d90070b00340118201c3da031100d00200a5075680c0082100904030826501480503660300c1c000c1125101c0200d00c500c50724075a240c543d908111725070010030070700d0005688002034000802c240016540c1c50044001c42c3c00e01c45000c04c040050b207a500381148581c00b03009150442e0740b10800204807020a05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 307377850 1250 307376600 307376603
    0x80105010f0201060630050a061e030c14130203160908011a040506130f2c0601090207080415020a0507050402041404020309010e1e060106050403030f1d1c 68
    0x604041c160410020707801c0e5100c03401200c01152003400142181c0101c0422610101c01080c0468031401416a4070710440e001550301c84092520345005008001883d0b540071003e048040843e00018951303214890804264040d4044010300350f0714584095480c001c414900c2c10a8210841d0760303082214082e80c4100700070122078040b405e07a0200041c013001c18480c0795070304030b0314a000c1c107038981407842040001c10004202035440304545804140400c003610642d424049010710004010640c3d0303010504985030030400d0180c58007101040105a88003041d641d044030000c20015845041c0d030701e41814180107903004031008251a15417a5030031a40020314400301c6020764255000c4030384a9040c0300c168070490107074454800074100c00f40e00e5401c00358000c41d0320010b010000600300902c00c03142420304189503040c0341607064101d8036044450b02031090900410312418003d16292440c3da0107803642c0400710b05d5100740640401d04540c000c07403259100346903180007413044800c8009440c4403e982084c4817030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 307379100 1250 307377850 307377857
    0x9152b020102150c030a050601020115060e0a0503061312051b0a020a090b0a06050d0603020a0e15100c08030402010e13020403051501030c15180b0405180402130b01110d08010501 78
    0x40e44407200d0184040f450080b080c0c0d5000910b1a0354a0042202502c009000c0c50b04541d038840c905c46912400724540802b522842d600c15207006802001c000c648a81e40e04414400e422031420f21561001000f0b040030f05aa00040400410840c01810b582ea4002e0a09042d8041c00e241d030801079084020a1540c00075100700c4813a445eaa4445680c0d4084800ca0481c2c55040250714106001542c0144098003002184074800719440c0d440e079001c1504011a0b03071011003d18902c1040c800c0c404800d07007a10fa1141e50a540c2002c052030f00c9180180b04071154500507100900020204041d6403050640c8008400c0140102d4140341f0180080c030004c3d80544070a40d21780c015240045040781072060804e04a035000b0903080032807403c015204002d600031082031010300007079002c120080346103081034500625000c0d950680740c524010070f011020400307000c495002030000c01003200507034420f0f80d444a4064040700010700c10707241a0060301c007025240c00e80131252142188285096912020b1241658400e0f43c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 307380350 1250 307379100 307379113
    0x801060308091e030706270e0610030c0801050405060d060e2a0f101701080312070c0201120506030f0105190e06160f0504031a100f030209152b020102 66
    0xd15143da0b0f80c400c545030f1039254100c90020051a0b2041080984405042c21404040f418401040180c1d078929408030708203080c1401049000d00d0020071240c0382c01030a00b02400a020000700c020642c1c1e2050003403e00c1196500d010440d240c4404260021050303119108004451841c3d4055684c0c00c20410100e001da007901d441c405568041901070b0b070060102401c601a001100f00800040d07000004140d820042100c0640642d0341c52100628000c003c410040c5680b2140b1658090203000014202c905001c814148440141d90011012480c0c801c043c400140c0740c0c88000c0028140031072111402001d40c05c01003481041c00810000e4021006032042c20020103088494146d101d030001c40342e0a40703465800c034100c41c00c00c0c003c00c1d011901001502d81540703019200d0342c400900308404400c1e848200c0b41030f8108141c40340d150b10303090040d0210b04803a561340e6183d0703400a515121300408d203281c80500401e81035025110a03a840c05441c03018400940441d48411401401c2c0d200300301d05034010711810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 307381600 1250 307380350 307380379
    0xc0903010c23040f0302040506010309051501050307091802040e0f01140f0a20070215041707050406050f04020c07090630020d030c0309080304231c1b080106030809 72
    0x1c1c0200e074103d584c0b04558901207407542e020080207080007082c003414152a100300f500051014000d095513075254034a40402c950420b8281440e204080c0c01c651030350340c500200d85601080480c405000c0c40e6041b10301080380002442c1090034512541d035611484e41c24000c1010071145031071001e40c42600440c01880c81c81da1241c04c3c803415282c0745042140d0004807840202d80304680700004045490000d4810a10900c040504c00201d5006501c01d0304c89400402522081c40f00a0007510018141290300f4003415051900203030900700700c600024443c0c2e5002541c072800e6501070207550300400d400c100c104143c0703598000082048841c540e00d4000d2000c01c400c070520100f1400d01402c45280c019200c0c0707100c100659800e942c41e512003030307007a82481510321000902640410042c400381080520480c1408000c5e00c036201200d4101001502c10b0701d42e180103058103c40441043c0303440ea005101011503200442141d2068003040d08100032950900d00302000380140031005110000d41540c184901071b00d007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 307382850 1250 307381600 307381667
    0xe070614030106051611060d0b03010b01030e060106050d060b040f03051c0507291503071a070803130512040e072c13020706050117030307170c0903010c 67
    0x24040c4401244e0706210f000910f40042d0f040c21101889014030040c4494484c00190064112040c00500943c0f19885c0d8070030f6007020700400140f1942030070140703c0c840840f4110340c1c80311414010041000303030214143e10b400e809a004540184078604002e81d4441e2100035200340c01c0f0740c1d0301080c0c44c03e02c030f00e501c03003200080c5145e42000800d001d03565040c24980c40350740381080441703030b035403440d215900016400754040b034081c1342180102e89603820303108148054014503050108a81c0126844140c1d841700c0101005950700f01c0b07040d2503101842c00c1d40c1c2c0d0340381172a0b2100390700c03005000b070164480c141120108000f41c900610941d84000c0380c41c2101d58601c1d204660b0401040380640541d00003c48103001c2c0000e51340b60302d030310f0341d001800582002441c501c9401282c014941c00e42d4001d485070010060503403c104210740c0340d030408018502d141342c48500600244009410081d900d101c0d07500260320098810b05903600214000e009200714900303140001c0241005282c4108184d28084d0840b002d50f80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 307384100 1250 307382850 307382857
    0x120c0b0307050a1202040302060d0b1002030403050c0d020418051b10052218020712180e040302070f06020d0e0307060e1905030a05100b090709050d05010e010e070614 73
    0x165584141c0f03848295041259003400c4400391041413034090001000503a54031340940f012020444000030743d940950208043d154429105030190b4104210510220710b010901102072941582c00c0d0202d1306051010800822820514404210028152034100500401d581d070780c044030056a40c145005607810046548480714440001c00c00070800801c0b024400803211581142500c010403e2541d42c0305001c903202203c41c030b41c070402540000c0d01000c0041401085011a400e464030030a00d50010140b06444080c500404090400d12800101014402c100c2d55020749004014103117610b50300e64010b1340d44e000403103680c000b05508442200807401c2c001904000c403031085d903407400682140ca05000d18040181d5070603108003003044000c04c05840400510b0b01952203100100022411071183ca02160101700006201e110000140011242c0c41082c00050318070441740000f5030071591800c0c034014110b8051010309075090007034611014102054041c2194070300e0703c84044840c17442e42d03488041d11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 307385350 1250 307384100 307384111
    0x7090807050d0201110114150405132a08031606050702150c130f061110050f070305090102070f110f0109030b0703020c0a05060a020418050906010b0a120501120c0b03 73
    0x600300c0c00410256101e00f4045c40c3d910342d01d100004d6550050700802195140c00c580b006114020040c0c43e1090381400d02c1503660280030318003407010504080d503481000782d203885c0c4150945034403401925030000c03d4580810080444c90110703680d030410800310080c9022005010744d40145403c00080c185030000c9000d042d01044050184881d42d103001e250740d0217802502d06460180e046a90219200000414503c0a00711a494210300000c60b00c441500d48070841560690880c00c040a00c003222601c00129508a68141400310b26035407481c1c82e690090064010240102c20410490024042c2084407066049130070394000045001e080015a04d03052503100c000c001d80d40407000140c00602c03c3d400f8254031040301e0299004084140c90300c41c40c0400560301049641d90005007005440c1c0c080001e403680000c81c410510103468a00186612001d05208500d071403d00059540c2559100e8410b0303d60b001c510302e504200c0307035840b0b400e824140d04a405088850390350f64000414065183c1041d2131061 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 307386600 1250 307385350 307385359
    0x10e0606041505060309070306180f060b01050702090a05040309080307080430060e070f181113030f0506090c0a381801090b0a0c0c0503060702060709080705 69
    0x3034440005110050203403040701446440d6059010440d6911400158021043c0c800208030150960400400320f44104100c190340d440c1d1400018001400702c0c2e00c00c103181e508083c00040b0190510016650340c490340c90000c3d4403080e040c08100b208446944064086c60083d80ca410a841c0c071605410303540c0c0700b00e4202500301081031000300415003c99a8a0705114402e0541040c0d500301411090900425170308221441603c0e0142c0c803802e004d04011a03070003404503c481c031440b94585101040031180303218440f45a40d403510051030020701203104507400150500d10308000240c1d2801d10040c90310341a0002c91305801440d022a101103000900c628408400900c1080c000e450000310640300780608501071920b030000c502d01a00307852011604102040e41c01d45495464003016031540600c1c010480e282e06000c800318050111a10800c01e0303510000d0710303082c19218207105003030100c2103050942c06640e05201721820000e40f5540480d21380d000702c2254651410440c0c803484555100c98003800b0b1503810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 307387850 1250 307386600 307386613
    0x140109180602160b0408120709030309060813021f021225060e0d0309031701030c05060d060b2b020906160809032b050408030316140d050612010e 64
    0x1c034055074002e00d06044100c207a0b040b40c40c9a6592202e04402c103d9090310700c0130380440c01c541c404400100d5680d003c1241e242030b080071400c40c7d0300a00b0048a0b80661010410102c1c0010078401c4401071141d420380c0c00920115030320102003048203c0e1390780d0401c007400500400c45070640751a0a41c041d9201503005a881c036011011036140d00003d24038503401910b500d902d4080106e414103050001a1114005030f8020410310752a04000d0320040b005600d1140d00880740c3c0040002c1040f012840d01602c108441c456071700e881000d030480141005030441c0e64080800102015480748408000d0401d40c00c41b6040e0040c0103682042504078012032400c11381000b01040440c0314612070787e0f070380e1100e5840307004014244026800805e04d45007144c5105490070290040313039000300c3c413002c1c0504070500603480c00a19103410015540e86074040500101c4101e1983c4040b4480c1c5c0d8001e200d01c2e50b444882c00310141c2ca07520000e000d440584400d9490358000c001d28a05281021818003172000041d1180004042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 307389100 1250 307387850 307387853
    0x5040809040509072301030b06090d020907020307080c010b12071202010e040e03120a0b032d15280203010602210d0e03090a080d0206040305030a0204090f14010918 72
    0xc1d00c8010041c1080d401882c3c4e021844aa0781e4100141e1a1115000400601c84071000502100d69644d44079110307490074020303090140d4401c5040044140c0c10745240c00701d51140030b0103a285000d81e020050103a030f00800c00210f000030550001d10300c45012200c094030021174100b119129007541c0075110840075042c03e03040255004290103140040e01503c002120080b1811381d9007540c10a01580ba540311125040c8892084180540040c969089000d4050010041142816140852041c00010b125801c007498442414803120b480c5800c4030194648900e401c050441d4440d0680e00000762194022a204051104c0d900c2030703134103031400c0c1e80003858049080882002004007004081100d02800c006130390181e4a01e0003042c0c102c00c030780b0000f940c0b106e0001040140c123540039004007900358050385000d850503034005491a00560981402c5540e41c8920341c615001e8802c6400048055042103180c44c1480115441079040034095075aa81e440d907203c27400d02065500c0c8031183c0c2015a400c0c2180c03030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 307390350 1250 307389100 307389109
    0x303150a12060c020a0c030602070b01050108090d0c050a020301022208010501060512090c1002010c08240603090a0c0b041e0f06050a030213260f100203072708010f05040809 76
    0x8511020f240122405580d6981d81c0c1d400490391034008864aa401003001d10400c20594942809402c090820461034034004010355940d030326048150003001000ca00c034070240003040c4080d900060b0090001c0d0750303400403e220fa00c19078100800522141c030002100007140041845843d043c0c81c50b60750391501d82a080700c1c10003400f0201401481c01c42c00388800c00c800743da4441f4411079010350703580c0021405c0c0c451200043c151a900a080740c070724041001000700b6101c0740e18034450242504403911030305ca072245101141342c07598183c4010f20301c80300e5510100350750b04003401801c101e0310a02035400d000c5542c0020948051010b1007407440600d06a42c0901c0064095800782003107020519005060030070b40b20b47e404a2042c00d0384120344031401a00c0741003200307030070b223081007041c0e444100205103194441d08030994a2181080382184154044042000184030302011030355009031201c941c00c40c0d114a03d01003500c03171441c428903041d0f40c686003401c02001054040c0030702c80c0350010041e5007414005010310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 307391600 1250 307390350 307390361
    0xd05040905061801080105101a04210c0b03060f2706120709060501020d020d0e010e0d050a12030501060905030616030204050603070504090b04052203050f0c0303150a1206 75
    0x343d0340802842c0308565040c070400c1c52540200002d100110b01420040d11148141e007064110154031208030807031180e1440e20000311822203110710501c49910300380520f800212200d0b80001401c01c00d9a1a0008500440c5006540218000c443d003a5000c0940c400b00b21841010b80010012034a900f020341d45400c0d000104039600c0000907100c5202c9841d40c2c00450309060941d0006540595540c00034005540d04004680c400c3c02c640c001012a86034400303000c4c00c054100300c00749040204140783e9403840d8031503100c5050340e507502c54219040000c41c2d00d400c0443c07a081d00005000640b0f0301000040c0c1511605484003190400750142241d510341403154100c01c50640c41e04428550200400030b000c1c0c03115001144104166071715291240d0a19007000c0503074801070005c0303100d0350800d01400661801c8e40440214200192600c10b5071341c07410b180a990328000e00e031351035080786400701c2c901200308000701c0118446c1d50551001c009502c10b120070400429800e004d400313640e58410021100060030340c0d200d23 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 307392850 1250 307391600 307391611
    0xc0a020d140106030311062d0a020d06030303050403031a130b1f1709030a0e0d0219090f11031b03070905030604121d0609010c170d020415020d05040905 67
    0x601a014920501ca0070740ea80c6610072000501760f800d0340000000c081c0050b5420800c031150700031080011051080a001c003c040707900d483e08095000c03461443d515811241003081030182442455524140038005280891301a80071a05007210010984184c0034480d12009000300090901d403d00d120610041c80701d45000f5802404044c0300180e100c0d584903400306403600716520156015013038021840300400c080c1900401d42d0090017580340305038109022040114055510040018180c0001000186000c1030418020075920b408640d84400340c08c02d000025508c1d84c14404c4000c5008043e0700380c4801c41c1d81b0000c030f40040d991a00c1d107500c03500c000c607000219403804400143d02d0314002820b00030141c070700701e5014245ca19882189a081003c0300100d40038070560441001800000c40d0142c0b1036660b1203410000481354940410041002d81c81c400c00d145401c0e00e17103589580580c14001e5005000d820441c4151541c540c0c10f0740d200141d0002a100c0a40d50700e42450f183c0301da01301c06800081d00c2c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 307394100 1250 307392850 307392863
    0x3091208090315041e050a031202070c09050a180b01210b09060711160501110304081606090f1208090f060d06030c14030a0b07090b0a0f140c0a020d 65
    0x80070041e6010420202c80f10f000030090346072820076150401000c0310b2018118180f00104c0d5110300802c038041401c9140c40c0c1c250400186481c1445051402481170840003010b10032490070210b40d406c00c642c4a035208406d400c0c0708110780761b000125200780c1403c018009010070030010040c400c042c411604c09100400c1080315010512081d5604104d4403c21100c08039103504c20400c00c900300f54030010130031850364007a010b08201ca4418148902040b034900561f414040320175200704160b9801c000f220024820502681c00c50030f40c3d4071103075140ca09140b1071080041e89e01d0b2404156520780d641030600712030311450f000e80b9010b055500d92500360491070299030300c020580e449145585860004001c101c000d03440021301c40b421403804814981ca150080000c40101d9141ca8030341c0c0d100040c003100b8160b0022008000b41e600d400046a0381c132519009019010310100f591118181c100c0300c424581c02e0a49c68001d60f094114148802a004141c6c0c0d2074a16404030440c080541441204051114000d08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 307395350 1250 307394100 307394107
    0x30e01052d04030c030501021e041211130c02031306140a03090809090103060510060f0c0b090a02060406020d0807180533070302101103160e0d030f0e030a03091208 72
    0x200d0b0f103444c51410303610030b407810b940000c1c00c5000c04d4504003098081d020804041070030107042884021411681d200000c11603410b2101400303c950300c8500b59814881504400e20146070070b10002512908403446501c50001d030705d100030950310300a4914414041c1c4454a5504000c95007100b00c01900200c0401d50f85103e00f0081854035440c5c40580750301940c020f007000300e5030342019400061203020395403201003000160b86450031807552002ca441c110715004010040c0a88030350368094240a0301c604000e40c4204009000912190089814000010161143c002c1ea6848a030161024105141251404180760b0300030710143c68407040d851030b07030040c8000c0340481c0746441a0507a1000d600e03d0f07050f41440c002142d002d0400d42d041000c5074004142560620003c41c08403280d8840c0c3c0400341c200e00524064800c940e08551260415500303400000740319218503603407410003400e400104407000000690072140741a181c100011269140c1d0f80c540e8521000d140f0f8495440140c07030445104443e50075042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 307396600 1250 307395350 307395353
    0x1050d0f170d050411030a0201020607051c05072601152f010e12070f020904021302070605180d0c030f0e0604080c040c1e030b1305070804030e01052d0403 68
    0x381c041c00100c14440300010303203403d082c1082d140b1940300c5002c0b81d129510140001c0011f036400b29080c0d0300100070703080c03168450030b8500500c0881390350201c00301c21261600d000c010b03100350300c40d2149075003006602003544114050704000c8035945c000d001e40681c15100c0010b020f00144603c0785901c0125aa4a480c90f11150060740c2e5003120100c0c507000c888580d110f8819401c7c1d403105000d010400e0700340004082c40c0a003503980352550f9140d0300f5000b83c42112240002025915107a0009000722141c4000319502d20a501c2d002e8010b1a00365200007203c0d1800a04d600500c1c40040d411003010000e443d6200c04801030f9804403803e00d02c0b21010b50401841c00c0b03e030f04168a5948c0030300040c0c50024007402840e00e8001c00c0c0000c8402c40000c2508000000c1001540c0783d6001c045180210182c0c80d000c14002c083c1400f2907c0314490b1810102c0140c940010000203a50028105006a03c01d6032207810322218100115410700409540300c00d44510409240d038114020a018229503d00b0300c01c99060039640d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 307397850 1250 307396600 307396643
    0x151305061605011e150501080a0207050109020d0305071208090a0b060415080a110105030c04090c020a140a0506011a04050d02030703080703020f100213030b071206060e031501050d0f 80
    0x1001d000030300219203060f030103944042c60700036801c460f4004005094417a2911000810355080940140009640082c0c8101400000e410035424103802909450744640300749030003030199101c500300340c60030610000d06008082c421103069000700401c50042507043c4081d00c907098940d04c094440c2c2e5101d552180c0844000c42100064802012107070041c1c1042100c034204040c01204400170300381005010810000c0116003141a60b040c0c1d1582c08001401c0842c214082c2c5c13508410420140281d03040c0c1200154074000041ca0f590035134400d000307851244e44da40b10034900390f410100307280e4040c40042c0014411400c05115140c0d41500040885000b20394035200d0042592002c2811f030010f81141603040d403800c404001840e90140b05040071880e0109284078041d43c4007090100030a41c4043c0008a1146c81c850402d01ca0f40032900c0400f042419690031004d4250103240e00700c0d40c064028941d509609240d4195141d04030707030018060b900307001816a600c80b60007120100856244411950116a0306203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 307399100 1250 307397850 307397861
    0x19030606090905010b040605090103030804110405240d030e120109120e091302090708090319030213120f060c18081e012a02010f050903070215130506160501 69
    0x4010300016000310302d4140349003510300e4801e07030a01aa0a0800400c8191039881d11141140d4052a00d40829141c609c0e1109000e09100303251070b07000e804e0070700f0711180707115201680ca1110113540070180d01040d0315060008513040c4d5003000c1c003c240c40f02d80000440c00c2600e04812a0b14082000207075802c2d441d80c0c2da550f00e0264030b07910400103d031012040c03081c0c01c05003216a04900c2d40e0203d407003004030690000303420180c02040304041100580200318041c008009a0b46002c1a1280c03400600914420040c0250030000d2543c404c4038121030002810a14000c90300d9125400800b9025a0341154603800c0c09844a101c00e44100174414072120b1040908240d210b015281075005020a8103c4400300c4180254000c4002c1d400d9240003a60000e414074018061000700280310488640421740f1000e900402c42e0544408486007020200038031603a01200801d400e500c00c03103076a0903455540070303040014020703800d8050b49411a488140075074030309400501000c0f070a03c4a854000b2810f50785040c25602c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 307400350 1250 307399100 307399109
    0x15050a03151103090d0e040e06070206090106120305160f0c030602091e01021b0609060c030301090c0509010801090f1d0604021302090a0b070503070602130807080102130519030606 79
    0x2035556890441a01c0318042c40c00c204074402031590a608000540c6a240c030040016501409a84d01d44c031000d0783c8480c2c10107100d851800c0191800f52900d10006900e0f15400c4030300c036244d540703048008180c0041c030403960034400d0b403d40e540340e00b40340c0b03040c05940c01070200c00b00030f54800d24420000b00000f0301d8424003c020318899100582c943c0c0e1603e0a01c1500701c140d803504418942140c0117012166030000c0c0316080488040840c0c01a040c0303440c0850840d116019103607421600000f501a030b40800003000f54101c499064080182c9600310b1012105402503c0a0b540045c401400400c4642007503088551422240340d03000030808054400440c0717080c041c20074609613402c81000c0005500d0030303450b07042d0b04034045c0909500d00203141002411062090040841c0000c010403a40c0a001082056901c2d85501c103c086564600400040c40c03040e40c03e11541d40c20f803180480102b4400c0040c0292381e00d0000800b501d001d05410142004041e45243d014100240411078000001c00c80601a840090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 307401600 1250 307400350 307400363
    0xa1d06040611060108031c051312050901110607050a08071101090c090b011e2006040f0215040602031602061e1b1b100512100611010b09070315050a03 66
    0x85841c400b01c6051200507489000c0355002400780c0301544070340c50810380809540240018903a92003c001000034030140340b000e889804189403c13150749401c2402041281c47c00d0701c07004c2800c20300101c2c20365900d07000c0340c107400040c070140034120341c2c54090b100840d00b007540c90600802c03480b4800d190608451001000b55400040d11004104c400703182d110795a2280030a20f0081030060301d502ca20b001c20301c0090480000c2000e00b15003034400c0c030288003e003110040c050040e140ca6040034100700e031620420380c506a02c00d003941e142440048103600201d0b006c858454000c1c0d400c01f030403030740b00c0c482050110344184c1c3c00400c10011000080c20001c0500315101c80031581c107890b644004d00301540c9410856030050b803648100e5a95650307031403042c02004508801c4603c04181c00f0741d03100031142c0b030107140100320304a02050706115640c4040751542d400d9070902d075600a200100d040036603003030719031040081e0782001195001c104110b1103074018045198448880241d00743d524000f1904101480c0d10660b0003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 307402850 1250 307401600 307401617
    0xe07031203270c0312030513021509090a050103112d0d0b0a06060f031a0f01090b0a050901080a0911150408031b07090207080f090a17010b040c020d050a1d060406 71
    0x1005240345d0800d092600c0c52a0400003803610150010000c1809070000e0300c00c80e82500d40341a082480c40c2158000c0310f000c3c001c505c16041c50a42100904006e000455011802501c41032850514180f181300078200b0310b079450000d450156801c4480c0f0345800c04541c01100ea980c1010200710442d94480c05a030780c895000071407070300d031602c000c1c45c0c001038031400820103081180c0b000100c10700103100300b0500800c44031802c0040b180f10050b02c1204a9502c000006040458003030300254000c0043d16561900380c80c1c044855903841010401c40b11140383c020510800d0001d20713030481c00e2003100d003084440044009450719071154001450754002c0c44480491101503d18040e484100b403098100600000c4425820040c031959900c0031805550340c030700c12441000c01d100c22642d4811082c0780051101101c010601a01294080c0c040d0410185440c00340341003040e507545042c07000440005181265a525007045804107007203441c42500e014140040723000c01c0c0320700290340d40c08004100400107078a90081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 307404100 1250 307402850 307402853
    0x60a050304020f010212180a03170406090e25030e0f010603150207050c0909010204030f060b0f150a03020a0314090a020306010b090d020f0d050109060605040e07031203270c03 77
    0x120081c43e40d9041c1190410049a442c5003c44e01c10b4402070031b100d002c2000d1410850380410b4135100300b9800603042c08540e00c0a90b029440920080017520159a10a03410781d17280e000c12056000152850003169010b440740c040b005800c0854030102c040c0c185004215138a03101c0c0114a80700030740c01483c40036551044208100304280c00f00d04002c0b400c0c16010350418101303444490301d03625203014040c001d15035840000c004030b40a5044801850b072002d03014821044a041042c000e020401c807039030043c03141c1c6481099031700e400081301c0b0201e01c1000c1a1450072400e81400c030080d402c03018020042c0743e2200075070038100c009485c0051040e41c2d010020324042c60f07107004062600380c0c1a8007528000b8000c2000c0c1d5030300e0300c8200b01100020b8050b01d44e0064030383e142d004900000c1c08200080c06035442c0684180800c09207400010403224111814800d02c11038110403602c1d140548401400100808240c0041600070b4201c0d0324180000c130111800b186102c01c003696885030042b0100e418201491040c030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 307405350 1250 307404100 307404109
    0x204050109061103070b0405070306090305250209040206090607060e0c01021c02211902061503030408100b060c060109050a0c0f0813050f010e07080606030610150905060a05030402 79
    0xd008200628010f40089040c041c51a280c3c13160729800b6000034540d5002406110040103860025603000c0010401c08409080083c524ac21185158004501f2202d400d01112041e5a1808116800400307a48554503581e0801c04d00e644941c22103500702c402070011501150051052410138003058001d0107124500c000024204178bc2c0004043c0c000c0d03080385c103810b11294000307061481d12030811510403a00b0800642036104d4001d101220f080901e03c5410f08010035800318102e805500a003a000c03804034030000800d0345a00450003048942e0344007801109040d4000d802009590030b019216a181070305034800a404e02000b40c20145546880781d042c402d100c66280b0034194881c02c24502042160720034000240b5020020300059a42800c00d2201c1050020038041c0500954030390008200e2102c27421003164480c031003842002c0c00e5009040006100d03040101d1030070b1055126213441380840703003040141050a225950781c0000c0011b0821702144640701d031802000017000d562201604c030300e010f10401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 307406600 1250 307405350 307405367
    0x110d05040f0b0708040303030906320702011a04020322081c06030b01031529090108030c03091002120d0504110f060a0302070f020a03030809070e0c040302010507050109060f02040501 80
    0x311044a041048601003158072050b07a0541c0d9152801140e10742c001e080c480c02905031b160810001c0307048440304bc06000e1080b0190800103401d84840c280e00d542d558001c0e4202c54000140004412000c9810031081c5800da008590041e54044507008482c50071420b480c1440440008071814040080e4007182c060b02d07000303580c5c8840011042442039030b085a6455080100c1880b0040c2a034616400f210708052407504259500039142c605564801c0d03901c0000c0350381100a00c01e11307001e65240b0f000400e4540000c401c90720542c040c0b00c019850482004240040d203c22888403800318041d282ea410b4240000200030640900400004511810300f4144100c56002d49140e4a00c00c418101103c503003901d0b800c0a641d8045464140141c0392040c80c10b100508010840b0002d5016110718000300805400031040340c05140000d00302c1c1c03501910b9940c0e2a00000c029101142c000788148030070401907204200030001507200760b0001c100d115071540c401051f0380c0007041c6044071076008142880356580c401c656 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 307407850 1250 307406600 307406609
    0xe060f0309010e1b01021f02120a020a030e03121b070606063504151d0115080d05030118020904020a03062d0510110d020703110907021c110d05040f 65
    0x500f441311513028000f03951480b801080000920a103030407600710070110f5042d00c0c0c0d20700c1101402c245c145041c0802c9002540081c1028000ca07241c1003211703170868400403e490f200c80401045e0710641d2100c0c1c4400892034000501983c1101d01080f500000603090300410000f00100c1e142c042e8003201a207103101400e141c00036100845050402030f005d001c4201340310281c01940200b074201c00e1560f07294881006e0031280b5030f4643c4810013401d102540402c154004640034507800d900008542d100c880854942a01d010380400003036041c401800441e026141d841d40c60030100000628040045004c00c050341c100000c0038000c2941c070442042900165003107203414410080170440c4250380b03000d00d800000b2003809942d00458080e521402461702030f85064109004040c100c6000000070b0070000d64072071301d50004440d8050f240405510608102c04018000c1242e50081c10f00b811641e80f80d000c00c4040041c04070204030600801030881d04051054a0030350060341d88103659039052200a566691491b4007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 307409100 1250 307407850 307407883
    0x30203070509070816050c0703051501090e07030b15150c011410090b0409060603081308150f07170705070501050105060405030a030f030b040501230108040b070e060f0309010e 77
    0x1040b1403241d100f8100d5500c041c0703095650070b80d1031700342d40c08035024001e500740b00087e032003029004024414001a40c1c0d48448200c001c1c91400c1e071720390540d0380541e0b61010400401da40b08010510008501001740c9512855000c0500560000d42001400d40003a9000314105070301e0000b4088212035003801162110803a031405003400e400c00e000c24540c00725062041001c4a581c80518150326600c0b604102c0803540c0040c4140005916420581e01940c0010365001c00e0b00944000010b104102040d8640c000703401d0111210303035985a41041940d81d40c000d000ba820019148405c1103501102c0f0560350082c80c10303669940d15054035203030a40c211001a04064818201804104820796001814152896051810900c190b100100680161101c03000d80d03503000b030801c000440e8091f885d03c15141d00b80301143d0300d00142050180190780041050f00c002c3e0281c0039182c005201c0f02e00800d030040c20198060031043c039000820501c203401741c000751001c1c8400d944070b013031500d1354000c1002225a03d050115 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 307410350 1250 307409100 307409119
    0x1120308070905100e03010207140c011206140d02061c271101050a1803150c03050f0a0b0a030204020d0504030908031207120e16360b1c0302070302030705 68
    0x40000d50841c90040d010005c00c541051042825142074058030001c95202c0342d006501c02d042030405840701c00701c4a8860008041d100d2510420006001e144101d5405440c3c00850954000074007404401114043c1e8008100700048180000104031411502451070070004c1c00407120301210030305107022200100090240041030010541c031260502101400f420400e03910a142d01054800e00c1400c04000c20440c1001400018404180e03a5001c60b5078082d8410031407144125816400c40f9016103100c03012400950004986003241d03441040d01000040124641c1583e0707500041c20f03a405100c1d00366640b500c51042c4410036801103410405002c80c0c0010f14104071071800c000301100e03002440ca07020420f03021081148401d40c0d500181c6103000701c00540750841c41c14002007084485034480c4600080c80b001d030803112040c2d040718000e0061160041da0114400d844a41800307004444000c0f60f0061440c129019810440320302080054480c0e0041c020380c0d8550300405040240030740c0480c0c082e04030035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 307411600 1250 307410350 307410359
    0x5030604110f06120c09010c021c030201142503060911040807050108040807060b0f0916020c0102030f04030b040219080703060b01260702210c07050d0f02210303011203080709 77
    0xfa06081c0d10001702c1d406280ca5815000048595442c10680650481ea24424005030041c82c4100c55095a000c0c1d0001c2c041d4104145c0b44213204a005c5540b00c458403101400c2d18451a030303400190fa9600c09a1901041d96a184c1c8202011290a030681d990f181e423000908001600080c060140180b13006d08092546142036214140103103d810302c0100f41d6659500b4110080e6644650058603650140c114202c901d050703c1c428031a5690040141c004d803142d4413041800c0d61000080301c5000c0c100380c042c20b0602e86903039510502c202d4040c100326806502c000034202504840c1c2c003070100030842c00c0018034010b0314604280d0125801d080c11503041190034501581c111240030b400c81465022340c42407050554917020103c0c00c3c04120100d811aa001001303081d051903012101425403800460f0a480c0724540c0c3c1e00c20000700c8500b0600042c040c40241e01408058608402d060800d4903641c1040025402903d0034542160710981018014a900d080018141035028000580c8000242001404c06d408d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 307412850 1250 307411600 307411627
    0x20c030d08010302120a15020c0606090105010207170304050d0303020a120603021e0d050a0b1b0c060c0f0c1f142802070209161404030b07050f0405030604110f06 71
    0x1400080d00481c1ca555148164030b904106178a0f4203500901f160041a594141d0708010303521824000b40d01c1c0c0304500104440340340044a803030403544142c000b0318450b0b00c0d00c1c0e40e50850720810030728402140014000041c0540b20300f40c000600a00c603680c01640c2d21142d0300007400070700c401c20741000f0a80c5440c1c001d100603221005030490210102d94240600100c00c0c1c0018241007402400800c039018841d50401004071440c0b42c1400340c2e03840c01c021240601c030000216054083c00d0030b043c244d903108501055004486400506070a00d03402d02e42c41c94051003540c1b441c5130103400030b46081c4038202c0c200c4038903041d6a64881d104d10100c040050031074904000380c04039021468031000d10030800d01094203507084400380c0d0448450640c0074242c0301961801c00b4910741c00016400314034000c0380ca803220480070321134a102140c00f500c1d4010036000d0b06032150f1208990b5070300030040380c1c1800041000042a00c2c0d600b08140b612a44c850710400e0302950080041c443c40c040a0003895029540030301408414520 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 307414100 1250 307412850 307412867
    0xa4514161a0d1e15060e012012040e040614040f021504051201050901060605070b040b132f0105040501020309040504150c08150118050613210201020c030d 68
    0x105100c0291601c441d07101032002400020350f02c21080c49800d6407034583d0f40140e0070400c503003c40002c1030440103641d0700c02581c105014105d031900062074000800c5410f480d02c6042d0501c402440c04440d14944107100c000403c3d070064100741c015454a50801c000c0200c0b9000700a000310f10210790001904095990004481000000a10400c0e80f8950100003001c11020f070313002000c2c0248940441804010340318001e200a59040300c60703500348600405d0040c028000c503052554400c2140740c0030b54442e1030710410214003502d85002160090000c0c40450120988040840c43c0088402c000b070300c040c0c0c04819465024010541445400e00c0f0400103aa0003006558000c00b003641d01291943e1035203440c0c08002c401a4281c1003851806000c5a03c0e2030344044020303ca400000b65440990218070700560300741815410001c1d020a9000081c001403c044000d040c5103980030a100003480d4503800140903035241c40c020303040589400c8008005540c1d040021140302481a0003500000e240101d000b0f28144 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 307415350 1250 307414100 307414139
    0x606050d18240e070906050a1e17070306020f0a1d0306070e040207050d05071511040b1b2e051909170c0604020103050a451416 56
    0x90b08261000d81d225a0441a80c01e00c410040d10540b0307031a110500020130060003900e0280500103400f081c607107440081d20102180e0040f42524181c80c0c4280c0002c00f10f110740d94000c1e42e0058801c00070000e00180050104210402c281a0f01e502d80070600828030b1201d61a401a51400c0310700c0380040c1d4a02141c40c0d50024950f1070015082642c02c004103019120b1410b0041c690311816072103940c040d07030050144c04854405c0d445101c1541e1115980170031b8030005505a07003854010001046440141c000400d0608074043d240a411a0702046c02d034217000802030b000c0c6071135a40c00c442c48882c00d003c4020103200d41030080100f1150410494802442c4400f1908200c0190384100d0740061246075180044484c01c00502035130354190800702140c4614054400b01d020a04000100b4514150307030003500202c00320303040071100b000b038078012031119041064982c0c0f0300d00010000c81401002150035040d0541d0140d060510703000800c0c68220300d0300016203100f880201100009224080e200050168903c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 307416600 1250 307415350 307415393
    0xb040204020a27060809061b18040207060605150c0c04091403030403030c0320120a20070b0a0e070e040221010507020106140319060209040606050d18 66
    0x240b0742403505495501c05559401e0205089050b100d400b08030f40c0002e00c060350764170f0740d0300e48040c0c9540160729640d0105507002d262422000802c41c1c0940d4020015100d0640071292101d120244000828103d82c01010291501074980c0801d04c000c1c00c24011001c0102e01203003600e4038010021a9040d10340a020105612564503a48420184640d21580d099058602000d903030703407070a00d0b107000740051a503400c5141c082814164071102c1c07030304104000032000b0700502a007445e040443c090b200740c202c00100243d0015585864490f183c0303d480c490034440d8805024400d54907402401e020054020040055030902d0800c00c0c19441c140e804542c0078103e07108810320302036689a40c800203882d0025841d107820700346600c0800008200c4150000c600134802c5400030271190317441e0384007450002d2034118410f4060703005905403040c0d036040b06401008103001d031000504108140740090281d4a0300d0f40408001f4502162681200b1a00d21401035101c6c2895039a14031542e0319600c01010107200c1c03071800b428 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 307417850 1250 307416600 307416607
    0x5061c060819111816030c08060a17160b040608010e010f0614070203151915050607060b0d2607050604030509121e010e0304080c0402090a1203030609050606070b04020402 75
    0x954075450241d40000c5943c0140200c140f5018003d1605413a5040e4060000fa0807d0b903101e10707850042c2103d034011000542888921400d0100f1380d0032a120407208034855100360181c05080600c0f14483c030001e000306045044c1d03510328009004055010681043e1401400e07400104404040c00807410203d503d80d040420f003000034681c0002da5402010310203034060042c4200c09820360002c401c100d01c1440d0490200c41031001e41c0030011304484214484002102c04400203004520f00503000c1d0030f00724071a09012072411400c10100c0c449885840c42200c88600802d08406c40c640482c0078120f41d145514019410700c1d060b6241e082d0f8488002d030014040c0800040c03400d443c1d4946902d403040e01e004400856005480c1840303c00100c143ca86807030240e035441d101100d1580394000c0111411101004000d0680014040400000358401e07041c080d80300007131303100006041c80f04030700d5260500e02a4400051740f40c038000c41001a1080200b00d40c0c030400c0304024000004100114442d0400e0f019180144c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 307419100 1250 307417850 307417883
    0x60914190b040b0403020405011401020d201b01031803020601050d0804051002060f09010207020a030209131203020901170105032509060b0c01060e160804080405061c060819 76
    0x456140c50781001c4502140000d010482544040040084902c00d950802c2030f030303996072140c0307480b03040f01c524103401600030b401c150324103621a007035201c68001641c0810202950803e1040c4c50665071900400e4405515a45c4208540c0c040c4100360b801001071310104c60030304a54dd4000d469100c14020103105046024401d018050f502c0b00f960050880507000300495000701102039076400c0300700c1e4240c00c0c0144002c000b400f0001c060080c2d80c3c5590b070151820780c031141140e0800008190060911324850403824031000417441045c100071000c0181c0d10011b0ba81e528003000144060111445215002e088000401c45500c00207000741000039100784400600d0781c00d0540d46107691640e489045001d040603800300303000705180300400b9003800b1a8020008641c1e2456102c80c10700c803c44203014010000c0e59035240701809201001e90144c42401c04910b0300c0e48580024030541c100790000364103403032000418940483c0c5441110040c0072000014032480300c080c1810907450407807083c01004041214201c40c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 307420350 1250 307419100 307419139
    0xf0a0b0c090604030302061506090a090b0612040b0403090806070806010c02041514040f0504030c080708040503011407110c03031c060807030623010b18010c02030a1b060914 76
    0x1ca9074a0001d18040e03983e9981c1c14000d548038010b42c1c080800d0000200200c0c03a83c907104e0111540c8005c00340c0782a81951400d0b20344002844160343d04cbd50484400c01000000000345500244070f0b92190b0342a0303001d800c041c18001e06015254018108a80c400c1c000d0003c1e450300141020350080c801d10f4003013408121440414042c000d0b014407030003400b0700401d001c21041002510000d01c284151801c10983c2510b40604091756401c0d2400340200381006400800302c1c0e8880c0003000d400340100c0c1001c2c03400b50b481d07010a08480c0e601c80307801c2d2440c442304203002825501c0043c0c1200030b80b040000300f083d200001c0003c7c2c3c60744034030384124480785540340e0300f044061501d070008001030284805030380f042aa00e0a000000e80b07080344400c4510910424006601c2036a4032039a4145c070290301086041190407004207480081f5068514140325078170b403510005903810481400e082e0301c43c5d000d20010000040c14841c050b6003980150701030101c041d005200d0150910f111040301e80c02191000038900c112100c08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 307421600 1250 307420350 307420357
    0x2030f1503160807080c0312071b0b030c0316030b03070e060a0e090601050f0907090e130f230705010e040203070e0d060606021c0e0f060c19050f0f0a0b0c 68
    0x20b07aa40b00d0410005500c040402c00004480341c420035503124520380300401d0b440d18800580d0528101c02131100e44007003000035034000b0100040342d80721700d00345440381440300050304101c0d0b401403080800000c02c00109200030081862980c0c6003028081070981400298503034686010362110740307401000207011640c1760340320b01e80205504e40c0c070354200b424400d00294440509006035800350a030780403401d80c141441135106203d070000f51344092645040000d04034103c00e02410301d400e280c10120480010924040600d000c452180c2c03800700301644180f01201544000d502180c0700c517008000100641d90b00301450302d0040804030360040e07481d80d0b031427000d0320503001daa98581e400c041003200030710802081c0c0d0b11087c1958010b4007102c1c290704540348214030800f018100200043c0003e4000c0e400b6003001812000c0d8407000802701030a08000b030044518200002c00e44500e010070241aa0007441006d108031618940303081c0c09044a000c6080209540b08417040e80100344603072403400500c0c10042c0754140c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 307422850 1250 307421600 307421623
    0x9171504031202070b041101170a1517030901030509121605030d15061101061220060d020d0f0504030203030f0907051903120207050f040b0a0b131802030f1503 70
    0x115200c51417401c007040b0324102100d0072142c01003c46e100d03850035030041c0080a5070186403602e0f8400c5075958440d00300607100d540f0030b81d244809843c001094080c11000e101e400b003200071005540b52100d500004040d184098002051904400c90115242800c8000c80355180340c5052094048402c1e4600249180710380f2402d000403603d065010316080001d20a40c40c11115283d540341c240c1c00000780d04034200c0382144250380d507100340140010001aa00c20260a2032254002c408944003041408618240c0c44a081400840d50000300c0340f5100a0b50b11850f644040d2929080100d883c1c20303500079640740b1000c6c0c106860a030060000440d00700c02045007101502020304100c212517032011100200301c00c43e0204032200d0020300080b0065a200158100840d20002c2840f010224010700f400010142014201d40001c03120002090035a0f813800100000407100c00c240300e440340f408440d00300c4072900e851448040ba00410900c80d680c003006200c140c000c20f1200c203142e8044800e100007490210340503007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 307424100 1250 307422850 307422887
    0x5070201110a0602070212010b0904022e030f15030803041416030605160c02130515030105041a010b0f031501030f09060506192d1a09010917150403 65
    0xb0401003004a8000e404580d01c03d90703010ba8600110710989090f0703001190611b401140580020307016103804001d4ac0354a0b0341d1101200304061503068141103120070441c40c500860f8075040e020000041c240705004203d580614651806411691061454403000c0c201a003001e540c0704581a820405101160350071f001c0b1002c4107403442e924a001070281c46d0071917070b03070703442c074180180814105c0e024010800c81d050b4010031420581607010307042c6004140c043e0032004840c600103860100383d1000d03c0303541c5c082c501801303108049180c09004460b0040050b0040e40d10320b0000e009000c10600e100d4181d035001008101200440069100100c004060311541036903440e080075400342c00c0c030005500ca9030003003c0030b481c801002d5040808954003420184070b2150500008000d00f00300c1d40c504031010074600d8010400304040c55882203018600141c0102ea82c0130300790002030390051584c10030141001081c080020742c414020f441d0750182c542440f00e80c2c03d586401181f000404051048403e4110b5015050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 307425350 1250 307424100 307424113
    0x14060a030b1609050a0f2c0a0903030605101707030e030f0706110307050702030106080f0a0f0521030f07080114010c06140c07020f1503071103040b180102010b0a0f060507020111 78
    0x203c2c042040c0301b02e40304034500340741012101001104c40560f080b80301520700545071a903444240f80d210060016803020740c10141c4e03400f0701049569030060705000c42c54103035862418100032030064441c40d84001e00b410b0281442c01107101110400442500c06200e8136490306501e07100103080100c042c26400c001400404400000c12461540210103880043d009070000c20a80e40c0780c14a055807600d88940c40d82c141e5010030405800a0301d400c9241e890345102d0020741c0e01a00200541c0811945e37862052104000c000c010411000b8204080070341c054214370f02045a940b40c40c03203c11a104039226098100b2000040c1082400303265003020404011000d40c10483c0c3c5840176860740b0f52741001da0124800e0441945502301441e0619211038841d06200314140346444066082d148180d03511511003090205000014541c100b01c40505002d5041075480c0150710000c0c070009027100d88509603248682940c4000781305d08000c0400310420b58209040c540c0c0d90704d03d54001a00e846c3c030340149200491140c030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 307426600 1250 307425350 307425359
    0x8030307030905100e060a1a0411071406010509070503220c060906030204140d030908010e0105010f0e13030f2a0506060d0515070c02031014060a030b1609050a 70
    0x1a070040010310b0043c019115002580151042995090302441095a200d50301013002104d00741e221440008003007c90729000c90102d0045001c0c0c4602d040a424000340102d1413206200140310100340e40c420200240080d90b041030001990500050500b5081010210020750204c00b8005500c85000300700c000c1280303606642c6401d0607030b009039009041c00101e0000000503654003d000762016600c140e101d0030f03500003191051102c03c00e1760220580801042e0030300060031040038440c096142d810341c80080355941c108600420500c60550003c000d40200e0810821000d07007410303904c2e8030141d0602e0151300020403003e040380c070240355022542c61754000010031583c0351040f0842016a0b0300c510705443c0b403660307030004110580000180152080e00444051001010b641324110b81c41100c074105076400c41100e4000c01d02d03096404220030406a5a4001100740c4240750800c80d501c05012148400301ca415035455840915011f080c206400080440c1c0003640c901403545103003d000701401c6188080d645 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 307427850 1250 307426600 307426607
    0xd11070618060c02030a080a1112040804081902010e191502010203100b0405010c03030b060d020f0918060d021504031415070306050d0b070e0303040801020a120c02060402060a0908030307 82
    0x10481100c00c9850f0401c070440182c00030068801d542c0303941e125110169070769111407014121300c0c2900e0072408010003402d10881c03078410714240542d0060001035211030034104610f02d00710161080b181c400100d500c0d0840186c0c2d000500f00d401810039600003103072042c845054a000c15a175000252460300200e070207005658154051440303105140011400c0c140d644541e1000f5119030301455001807020f000110109001c2d030484690303250040c00c0b0510b089801040c410032038001e807100c4820b00c0000500003140d441d2512220950125100c1178101c0d504041d400501d54020b80000240035502220f5114040c601e0034040c0c40045401815800b0201821101c035500c031081a10a40045079000c40400c000f14801e208030400d0301e0b00900000704002c0031780c07212071608400500b04010002e2031410f00760a0348051020704010a0030b40300242e00e0b88810381000d459030042800c41404185007000d0302c455243e001411a42140d0181c5000c2c0d40c9000803101160f804d015500305810b20702c000014440003540c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 307429100 1250 307427850 307427891
    0x622030618060b1207060507141b090709270207050a03090501090e1b1c0f02190c0507120302030c0307110a05030d0905061b070f0603060b030c0d110706 67
    0x40340504102802078001006071001c2c4c81c00e91011698001c5405004190042e0004c100a82c040c60043e50031034009080307249070101130100d2991341c00403010040c4032400c000a035a50000200d060540c46e041c101060354a100c0170007019070b66581d45d203440810020000354111504241c00a0a483c0c2d11449810b029017148040d102d824005800381c44d0028403d8156000140100c1d189080c14100c0344102850301340c56044a4034aa50300c0c04114040c4030307040c40174420100c585120390303005a1a502c50444815005580c0c1c1c00040a1100d80444400043d00120380e5100f03030360a202462072a60054102203140d40580c1c2e4811000e440005118024032420203910b0000d290119088036106460310145030b166441055400c010030f900701c8041c4014500321000e08103c00002d4503426400c001d400700c072442d003050359222119182409009001d080d50500412001d440740d44000c0b403960401d00b05005062240a4100e0030a5a079669900d0243d00a00111405942c21101c02d0181c071107494402000c0342c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 307430350 1250 307429100 307429103
    0x22119030b1332011409060418140f0a110603070e19080c040c020d0807180e090c0303070203030304030309060209090405030a080907051516140307030e01020102090622030618 77
    0x10b900d42c40c00c00400c00303582585410b07966008505ca81d2803c2c01800d00c40d031030fa0b020341880c0e4070984a032800d034110003441660350000750240384544907420311000c0c0942007221045451003a900161410380c0492040720b64a0141c9209032109950703a070307441c10100d40701340084241c3d030780c45001c8a40a00601000340d51820950b820748050b0f40707104017100d04020031501d1841c802c00150304141c000002c200c0c05801d18079484084c03410711781420300704c20105842040d034942080d1074210064090082581007040304002c08502940110301c0c045464000036a680030081008080589a0111004018640c0c058944048025001200d136051904d082d585980003910030b2000250081c0c00584440300002d080012581d026140c070307249140340c07541623150783d009080f5a800403508240c00b40001325a008c2c0c4110100c1e0240185440e2031151400514440364142c000e4110ba00511281c9941ea41711000c540c1d00141540070310501510049181d1081c2d6515031001c2e0980e86400d9080c0c0910041028106809 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 307431600 1250 307430350 307430411
    0xc04030605010f0317030405211206090708010b1810030b1905060906070609020901090b010207080327030a0b0916090603080f030c0c0d022119030b13 66
    0x140c0e264019100082c0c3c2c0c2e480f0241c0303c803204a0380000341d010b0b02d4000b142c06c240a08191030070019815103144102d59803010300300203804d00040a44000d00256002500140112030b1480f00f0b061511004250300018080c0320110500021030300c828528030690ba04001601401113103004c0412040640103050f08242d030b0b8050741200c0c205146125206c5c40c49011303264020141350030840e0600a1001c15088100201c850359a1000c410016950b0811182d00070310303007100045099500c0d50300081c1820226400090240d0051050102000340c4c5515801c450107141034010080307a03000300280c40d0480f503103400783c40380680005000421070040368013400e0002c240c814550903030b031300c0c4800300c100e8900d480040c000001c1400901d0310500078a0065070024030b00e000d941d041c010399003285810060000c007040b02503401202500035850b02c0d16541103c42c118002c4050900d20714645207012036420300070110030181d031014105011748d103154515180d05c1c010003003005404502418402202c0c00369108a022 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 307432850 1250 307431600 307431611
    0x706020607030b090601020a110406030f061d0f0706030504030c0f140601080304050105040b0a09031a0f1302010f1202040b0d02040f1a0d0f0209060a032306030706050d0b0402030c040306 82
    0x13803d04001076405400d041c0d0080c4202403003a20b0391611304100354010ba0340325498040000114484810005096000d000002071140c00002c480c403c00303c0d000200295a003000307040c415603540c0410070f1400c0b56154100481d00355901d286c22640c40040080003009001e07012200014400c0160900d641411504220360450f42c035101e00e00e98074025480b8003030001c0d504100500c0480c07000c02c003401845040e8101400d0982d244e56038450348030218002000c14094190421410000c0b0641590300000d500001d030081c503080c1d400003403074a1642d201034004d00c541003001d00c6c0310100c26412540245140b50b521034454a00d4499400a54230602c1800c0e90881070341c00104038906030007084444111001c0d0303407514140c0403842e00301c0509aa00038980078a9400e0002035241d0f02c07210010b11000540384c3c0d002500c904c1c00800036039141d40741c4040303400c49004501007140a0710300160301e60645981c4d0400540300c0c1207d81c2c2d0140030b400c00201c220f420074000304c1480341400e2990f010780142c91040d04184013 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 307434100 1250 307432850 307432871
    0x30a020112020f04150203222601150602060f0c0304022d040204060c1103010507052d07030f170121050304150507020109150806040b040e16090b0f030c011b05070602060703 76
    0x171616078000c5000c0403011480c1c0b05041031342c1d40b012700f1030302d8010400032071000001110740f40c515407540d101c840903030012001c01c55021946002541e011441010490843c06c050300410304003103d04030194200d0711140482c209200e003010050031190401031041d59110f484030380080501c0d5101c0b04c01c607500c201c1d1003000031641c07506009030361003203120341e4a1a0030301008142d022070881244000740c0c51412403c0104480c040c9503030007410f202d40241c0b5094000c1e001024001c00f800700d83c2620184030030f15500188400640940c01003507008d030314056104011400c0c00d10604606c01c40d0b10800e42d441e0007004035080c2c0d81c0c004002d031040304e000340c032481c065640d0380070720080e0001c410001e400064054030010301c3c50302e065032128840c0040500006180414903d841d8a052a103542e00190324a1710f040030005001c03030340038180c1e05040c10f07200b0160425071100400c2e034811541c0015814800102651260804105100f055540c1c01504842c2803656682002e5141e600aa80d0400001d050051031030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 307435350 1250 307434100 307434157
    0x30809030c031b090c0c0a0303020301060801090b0f091005041803030b010804030c0f1a07030f0c02030a09051203070213020a0201050601032a1206090b0f030a020112020f04150203 79
    0x800c0c512041d410ba014143d461020801c0202e00203043ca62040010b1084203201042000040310691094a0042e42c82d4140180608922016407024501d13504080015000c0d40b1190818168060165411040390300d401041005003400342c0c010b80c0d08640b8055001b52143e40c840404111340d40291000c005230401040110b8100404903400380200b0b06d04002d480014645502c44480c4074050708d11111043d10181e10080c01120583d4460f001948aa5510800038a50312450f80c081969000a51415101040250141405100300d91144102c0314141d0110340091046500d01c0c1ea0007800c0c24094266203458100035001140c2e590010362030100000c12550081c850b03a0711840d030301c03019038100e81048480440401d0071850b10303008002221142d580c59070528000d0402800e503120020034080294428031002c145250b00803840f075407080c242d000150760490a070520499607200050b80d10390040c00084200e00c5290f029241c204180202c004c4040e5021001d415104440743c500304c00d0020141504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 307436600 1250 307435350 307435363
    0x5030d0f06080607050a02012c0607050a120506030a080705070303030b0d0b060d0309051002070602061b04060518060d050f070206060f0d140a0b09060a020f040510021006030809030c03 81
    0xb14280d4032100c0483c00c01d50040e4003504034110706100108009400c1203080002c2c0044003003000d4090601140300d220658180052070340701c01c00c1d142c00c508114400a004000700b85641c241c0740c0e46c0342c1d6080070520036201800000541908861034951341c2ca41c03442c1240e0780c1c0b031152006800007454400800c1c400e01c0d00f6244242469007082d01c8500640f5010204020390304a040102d0070310114820003d0140c40d88490700d2000c407070603009048902d19102020b400c0040050407690a010300e4029603848006800a031415502e840c94181d4a400c8002c1500d040c01801c208a103601041c04203288007210340f103402661080003040d0882507180ca03891000d0380e4800043d94180c1e48903a1210030501e05062003142c007e8458081d001050703180c801b1803000742c10300100020982c1c04040304020051000c00c20003606030465500c9004503c0d00f024050b845030303240190f005031446422941039a070800d40c400c0080403090801980c081107a50396910707040740b09500441460707019014050080c4240e00d00841c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 307437850 1250 307436600 307436609
    0x1f030606030b090f07031106030a1d0f0111070c060e01020f07180c020303070206010e06030a08030f090d140313031218020132071e0506010f140d060b0f0d05030d0f06 73
    0x8081d40c1a003004029049c1c100620f603218a0b40d80700e210440b20000e1b40b1008401c0700b800030240c068441900100c03401d41d42e8289104039110010420701c0001a070445407001112403510303200c50f1820103200101c0c1815420503218407240b06840c0f02144103003144482e031081a00b86da100b0002c00c03100e11000e031385078007044a0b2000035802c14401000b50910b0b50508550221b001019180312286a60f990b9600741c01c1511007180f07550780b040404c1a503a5040180790403c8540c0e09140819040800100000344002000c1c61011188100240b0401d4082c201c4250790340b40c0402d050001100c502004060b0000e001e400b03a00003a00450794840740040040103184009a81050300d10003d49400b00904075402400125064032240d10000c0c0010700c2c440e50082e2580c03149000c0c0c440740d494015040400230042d000a0041d190b2070054400541d02c2c1c5002482c03003540080c001c250721511b400001c00554284e13941e241c120044500303c80c00c1200110042840b0034840c00300b004a01500d0f44114103d5005001d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 307439100 1250 307437850 307437863
    0x13051f060f2a0507091521081201120b0f15011404030f030918020f07030305090a0c08071809050d0507080405040623040905061f030606030b090f0703 66
    0x2210348052007605820a6070765820241e44081055801440500c0403210083d103540d082954207000610203401583c07074000381100482c181600f0b001c803090704002c03d4020400000b08210903c1c042100d07003400d0b141c0340028803144514035a504d8070f2131741070310b0304210003200c6c6282103d0000d0040c407100682c090085c03060461203003080000c2c03801074840805a038003041c0b956074140000800130b001c5a883e42d00141c030940d207411803d450480308520841a80911004c22401842454417040341d940540301d0700b68051a0101f000c1e142d02c2d1030135007003044042c0c002d00034500518003c120350b04009484821540d581e00c0480307801d140b603668407046481280d002400754101d0324010380c5d102d2040001d0f141441c054030340c080c81c155807940042c04076010381c3d200f03068017992103416402821105081c0030781c100c42a40c09000301041d56444130b88408000b0030407009000324010b041c1004801400000155511007401c008403503c80c100a107584508480c20f00b954403490001c48100036002c9050011246c0c0310b132 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 307440350 1250 307439100 307439117
    0x5070e25140703020f0f01021c02040302090c090609031e070e0405060a0507050d0e150106050304150c030902040203041a071e0503060d0f2103140406020d02070213051f06 75
    0x36a000d000d0307101034410780843c402d00741d60703860300170301400040704405081000607502c00f1860704c00c070f84030482c00001c00340d4584180410000b589984030140d44c0688458042c507030710000800020091f000d9000b500c2c2c6c15124681581044205e000013140000c0342070707030445049d1075554101c00b4031b26108441c001d1090700100b000c1070011030380da04401d8100c60a820300c3c90a00d6590a40f807001c071154240381c14100d0348400c040d941c02201030109140075020350b1503c03526524003034071365940381d0000c41100c04040e80d40e6859140304038032030fa0201b140c980d4014020340d50b03424113050440480080c1070300580048401d00120b001d6901610713000c00011000c240c8031184810a250942d00c60b000104900e402903802c44000300080d0b01001040c000e644a941800d0710a1341074003c109030345401c02c1c0210249440c1c00801240b446a030300c003085d07100e9030101025a4809280700c2c854041e0040480094102c9402440700342101c2854020300d10400340c41c41c002c0241412903841c60400c81052144d80c001c43d4004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 307441600 1250 307440350 307440377
    0x40f0b180a0b0703020712022b02030a0c020307050402040308090f060a08071d06031810020a0212030a06030b04050318011b0b062d04110403020f130905070e25 70
    0x81102c5500ca84181401800c01e0f005071150800c08180000c0c41d0b00603004103181003601099030408400f009401c0c1044106c1203007100d0069036038868107000c2402c0c080c1c0611400110f603001c11201024110191065440c0c0e5600c1c6440120b507003004207030621590f68000c40084030305250742074480c000d600da901d860007a11100030070342c0d519102119128641410840010a50725040003c50117078014924501480d90091401c60401e410b0804101c01e242c010440c0f803c401c0d500081c000d4810241d8200d0540d65140c4441d04002028075910007450142c00310100320500c000032014252001c001c2c4040030f45445c40400440b070695500000ca43c060400112503000300c0d10104a29902c04000b401d081c007400c0d20079101c00e415010031004061640d59203c2040e1a50070075000e6107940401d042145400c1c5419035000452000300700686d0303401048500803c2c00510803503003150707110070780060603944400d498400600d0032500498000c60080700c81c040f60803452440c0403114a200015580c5d9402c02d0340300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 307442850 1250 307441600 307441613
    0x30601081306020903190311010b0303191b1407141f0201091a01050307050904020907050a0210090c0e0105060304050a0305220905041e0c0b1c0203040f0b180a 70
    0x3060340e50b81d6003405422800d46041117520010030142030038081e83c0000d40703802450004807010300303c216410850303108141d88000098a49000d506000c418040c8405041241c0d1440c01d000d4448030200005600c80c10300c1178104a0025940b041016108099243c5120b0081002c421003c190040504050410014081140156042d890f4070001c20a0002340d21240586958120300050003c48080100501d140401c881c1c0d00800b825110081ea6180940000e510218000c056409210000405000052007408108a20150514108510b608500781460709103980c2c0642044541d296002280501d480d0069030b104076404002003040340c10955040720f03640c21904821a0000b0150945144040d11088a1014010201c400506891f00b81094000c84d206201c001280c0301c4003420304804910400c0204055034040c1141035655403098400020400220b1040d40084d032003c000d02c010080409000408140101120b05c032940f03c40040101d50103140100880711343c400318000001408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 307444100 1250 307442850 307442881
    0x1a010f090c140a121a010212090103090804090203070305130807140c040f0509240a0e0331051e09190903020d1e0c080c0703120c11040203060108 64
    0x1891810b8422860001e089921641000e202c0a001c68482e4003400001450361244408002d40e201640f04640c6000b40041d448501d55003642d00d000b00005034500090340690440d080382a480546555070720340c1d400c4081b0003900f00741c0305180000d090402144404051203009140c1a4121803076914000081d502e05110350f03100c030356070700060181000c1d0b281d00b41d40f203200300c808040c030025008c40d0320703d09140010708048035003401c41003000480d64210740c8904422a90b0790701403804100022802c00d00c2c200546540034100f1480c28185c9a4007401c6004134410600f211140c000c400e6101c1407941302c1c4200540201440c0e486e82a00219481d4202c2c0c0d490021410794001c8401001c5144170350b280d0004c2c0c415a06048816405a44052848802144d00410064004105449900070384281c2c0300c0051407428506005440c43c0004500e485a01c8010f120203001144d2040d01c0880b040b0465402604840b0124415507910034410401980c3d41803900071030740304800580d50080310303640b49a501d406806 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 307445350 1250 307444100 307444121
    0x1311010c15050a06050603070203040305010b0a1a0a020f030f0a1b0203030a0509120106080606090f060307120303021903050118060311010c0c08010204031b1217030c0909010b071a010f09 82
    0xa0304c6050019064a50200940c001d0b40203901071641d0382e0443c1412401c5d143c0044156004140c103140070048000ca0080f202d40c0041c15030943ca9550180c014101c2c0f904104d0303541c800f940e007c00180c00814101c82c034024400040c00d52981031060702611090401c0c41c01e040c3c0d029402d03800c00c2200142440c482c1c0c0003030000344001072120f07440301800d034405400c644464100304229406101880824900702c80c1c825488411407102001c10b242c0840443d849203c903100300100510102d00c82400c050003501518514134035122004161240c44200801a000c2880b401c40c0e4000b04124180c3e02c000700b0f00428041c1d942019000307111521440c01103803e604001c0b0152031a15001c02c021610301c1c0280001e1004601440c40c210b44150802400d40391041180d100128401d141d20068002940901c49034043c0d80480c0c054903142e0355000e210070710706e220300002d19900c0041c3e00c0000c1142c25402c006440e4460049042501d040c1c01e004d1600012034080c0560207640455020170403650750b860b0082400c18 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 307446600 1250 307445350 307445371
    0xb01030b010f1101180627110603070c0213060513090f2009010602010e01060611060601120e0a0302070e130309031202100609050711011a040e0f061311010c1505 71
    0x17114485065045000b00103030807501c090b20f170a41c0c8601410140004841003280c44403c0780041490765510303050b4405101c06501414020001440c0c1e10b0044020442d299000303000c9080c3c0400000354800100801d02505105103440f400c42a000c140343e21915070b002c1c2c0c0c00800002100f1240c0c5601d20100d0300200601944031040160081c00d440d022281d0b402442d6640010400d050f85030200b60960301e81d60004010420342c8a40140d450030001042904a04207007810840781c42d1108030270000d040160f1002c5030368842c03c0303503240826500089030411106481a4007a040c1c44a00c1074481e07070341e003105010740052408142400895602c0d1403100d40864030b4011661106001c0b45402c003550702c554480c01c01c05507124200105a0340000c04181e01c4c60101c8003c1180c403084200000041c0e11050801b802a0703a19010104101c0c010400000105009070803a5400d180190420780c210700f01d160201c4d074625060b80c059040d54000e111f4581c03219800582440f4422500780c800c4000c08e001001d6426030b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 307447850 1250 307446600 307446611
    0x315060d0b040c020703061a0a0e0a150b070c0f08030f0d0905010603110f0d080d0b01050405033403020303030f06060d09050f011401050307051c05010c120b01030b010f1101 76
    0x150350783c2c45440e803400520380251401910303608000c012106824a650090f4004100189007030b65800b003524259200b0300b2090082d0f4070350300804030013011201c00500000c00042c0c1c02003040408440500496803040707403d0103000d0b8440c219221190b1880c03182402d0741e4402c0c003030b10414040701c801500035046402c030002640c00a580741e46080d035036154016101e11a001c444400103051080c4507802140058900c120354001070b984039650380c82141404440940d6a50100166071f105400301e41c001c2c4002001c40d035100300e59103255801041503d240c0940000d01c00460300b207050b42e440d1b540003102d030000e0241d800c69480100991540800a14036a800003040242101112081c45042c10301d034002c000030003070000c20400b820b00310741640c5031900e821140d010041085a80c0082d49006640c000d8488010030781e20302c01da4945080c1500c030010825400c1810440101c0d030f11043e001d405150079035043c003c0d030012030300550407601c041c107005000171400d10f1081a0703140595140c042c0c00401c58000101c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 307449100 1250 307447850 307447871
    0x210303180609080304020108070512060415090212091c02030d0b0406090c0905091509040f020402040b0d0902190305060a0e0309040204030b0901061401051b10020708070b0c0315060d 80
    0x2101c001100031100c50783c02005000035540d00c41e25030707a4001d045082c9546800c41c20780380c551220f0001010144142c1e2034280003c10481019101801801044000c0d511010b40700440400c64900321044100d600c508060013241b5859414013031142d06064028610f001550403c2030080d0200f065029005526241c002a40811612442c41e40e50f503c0d64a05d4285410301d81003104401e00a803a926004904000090055440303c0f030711a00b140d8440c0700d01d1540340c65480890041e0207290300002003150045014203404a203900049020303842280c44c0d840c00071000040707101000301b80c08060115488400015410700e8160300c0f040380442c1c1c0008490400d0107660000d410b903481034008a8076070070f180041c4074450000b4054a40030700a0848804100c800f0140000c0460107807045a51801c00740b03e1101c0c06880041c01802c41c01080c00030255590025814560410303403181a040b42c5103040800022101914042034070f00070041403046015540c3d20004110f0540c101116002e519030369107020f001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 307450350 1250 307449100 307449113
    0x40314010624080109050108100504061104080d09080d090b0c1204090204170a02060f1b0105070804051501060e01030b0102030c0d030905120306010e042d0f0621030318 74
    0x95401000d52642c4140c0a02c01c1c401401c540c41a80702c640d00d03a0502c00140031041001c03488241802e8505c03000201550b440c01d000e0054101502c9482c040000000e02103004c0002045442e01a110307521a000566519049981d0b907075281c2058030002884444180203103100b600042c244000040b04172020b603020407c02442550041e88581040e542c002070422050910207552100300b00340d01c0142810b0032a03500801c1e803a10030304030a03458403000060058207408178200d080841444800080125103840c4401504001d0240e0b0150345a1040d4086103010310040344800b8181d659659400b1071002e07101e001900584201d4503140d055000a000c2030a8441c000c20600024003100d50700411400107504045051404e4540d0802408a04004001c0f450340c0100d021038401c20b06a500290f00c0c202c3c1005c0c9210a03400e40203103900c0c02c8038815106a51031154100c0000c18040d40810840b142c0d4447c503410752500c42044083c404503079100a4004170340644d20070b00000c0d4002d0f0401c5000a0640d42e060b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 307451600 1250 307450350 307450379
    0x703020d140f030d0b0402041d07090e09031806031005011101090813060e01020601080607050706090807210c030903230f0102070314030114090a020c1219090302060403140106 77
    0x605030f07600204002a00722410f0084403100c1005403030461406080000d148000b020403070201d40c03010110360100d101944580b5100000f462801c2c209280750070030a2205450381c1c0513510300300e07514030301407000c1c4400d00e081c0d021680501c090002c03001003c1d241c4001500c52140901c0206920b550b110700d400c0202e00510000c00c0784d4141c404182e50f0050410724080c00c290074003072800d4110350105c0014030080c20700044084c0c00175078608009484032098500f0340c020b82051b440003089850013188400802c46541e4902100c0080102820b840703030101c6038210741c008010200640002d01e4000204040b03a00ea002d05a007850b0865284038421054682172458544901c0040c1401d07980021804103055004140c8452000903115503480d5525102d51418946890a0301e01e12505001c03010600c5107115a0450320341079032200170b542140401f400300440e25040807424500700c04260781003030b100c248102c00d09010f07a40c0c001c1c02282864196110700140c030700004100d515540d40e9000104000300c140d00702 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 307452850 1250 307451600 307451623
    0x1050a0b090f06011b0c051207181107021e0906030c0a060507050109020d0c090510230d0b07030204050a09050403021c11070b1c09080a0c06021201030c15110703020d14 74
    0x6d400c600b8680700a00c0f001c090080102d4032260081b003028441400c0c00d503100300044118080104034904910b500400318032402400a601034107071780c6c00b0142e10140340a5000105811251142ca685c1c420b010301d5140c11041002c0c0d03038003490340074080c42a00d0007400030300040c6006000004081c0c030356501103101481510030945402802910420134000c0030f004030760744102d0280a104905107044208e54418094034030026912501c0a81d01c0703882e031201c04c8040101504002c40f04268180714601034020750090080c0c81c0141e030740380c5000c90540010f009050060b5415801040c0e0a41898400341c400b40c16450880100b00d801003040d80e00500810420018001c00c030b1006a480d40c01d411214000c004d040c412100190070003c1040c003084614043e40e401c04054103000e518140d262421900034890321540000041c4003c00105c10300c400d50042e4400c0c4c40e4000304920038042c0041c0b041d100c800780308101822651200d1401d100500300201006159841200010103107122421414102a01e1900c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 307454100 1250 307452850 307452863
    0x30806100c08070f0b0703021908040f0506360304090b0a08150609240919021b0d09030f2009040605040303060b120c03090f0307030302090301050a0b090f06011b 71
    0xa007601442070110039960090306c0d90804610b031407090303424010006070881e100414020800005414000501c10050405031722905440c01858841091f480e0b9105401d00e09060958128400c0045801080b072448010a4100254141880c240101c0c028250380c017500358000460b040000780340c400c20041c9040721050701715030040d2881d1070320034040784d480f0042ca61a0f130b810402400040b000803404230014aa1410355005072556280c0b0030480030394501d40e4002c0700c414400140c032000720342003600c0042041c801500355010240c0400c8100c8001c6201d0001900b00306030200f4207000907070404014029103411400d01da081340242c0c3e0028507040c0f411102510f0742da4480341008201a414070641001e0170b45044110b00f0102010007011004800911015030042c0c00004500819400c0010b8000c404074175080b260394502030300d0010301940040440038065805c040100740f28a15600400700d580c3d00140c031a81166569030601c02100c0c402400442c1442511148540c12402040c840d06500d4080c10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 307455350 1250 307454100 307454123
    0x60c0a0e031b09100608071223371e05070507050c04020f0a03051b0307050409060e04030c023c0f090405030a0c03050f040f06030e0a030806100c0807 66
    0x20140159254010311a0090015401c1c0911800d80c0104002c7d4101006140040304c0d80c050b16099030050141c1c00c91302a001052094200c507035150020f40a2040c840b04a10186900c00c101c030100241c1035960915110070a810030110f802c28056029a52480861464403282c4500c10040801c9038419501c0900007000080d80e242841010441001044000c1e00c6c2103241088541c81d02c07e5500900420008254546c0701003203880340361001d880c1120500505a958070b091411016141e0780c4640b15240040d07003020300024400d0301c00c10820340328030340584901c20031030910303420420300710b03861045400d00b06581a14030400c02100c410a142c610201d0007c44031b4020f00b202008803030060360320000d200b071221600b000005000032050b60781c0201c4600303014040c202185002e550324012404820356018002c03600013212180301d00c2c0d80080b0742490302c4c20801255821002511035880302c4025001c00c125401044190408495941005542c3e1a08845840565403942c40c1ca500121040e1010781002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 307456600 1250 307455350 307455403
    0x709031e06060e181f0209130212041505010819080c0f010209031b0d0f020a09090501021201080d080106080c04080f030c071d04060c03020d0e01151502060c0a0e03 72
    0x1060195402444c2000a04030400045034840c402d5a550f9605180903402050128003034980302901d800001103c00e003551502680c02805400303400484082c2d940404041c000c05044c481071151074142c400c110301502981340c2540074440c22400e04003040303410203820031011803d02d81c03d00c050fa140500301c100169895010008040c642020038003140b040c01e11412000703049960700c0c2c01422030203501079011107164921313000046813400e26521804c0541c2c1483c281c101049419402080e841d80c050b01090110390325a000701d5a90081c60110300f000c24801801444014050301c035081d03009003402401454151500d00c501c0c20900c9100d10513074103910204031700d03492503400d2210002814001445095100031708102c07101d48a800b80001e4205581c982c000f5404900c01c2d01103d811081b050300c244180081425081d0007044d01c8030a468506084402c04121806d80601c0801c50040e594000c2c0440d468204e1009966403110300028140403201014502715182070200d00651050b0491042c00350310308 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 307457850 1250 307456600 307456621
    0x30501050f090f2a010e100903120e1008060f0604090207060c02030f0703030e03070f0b04140613380a110403020a031b0906081e060709031e06060e 65
    0x75142001264000074502010542856007035481c203801d01980c00740700711444c00140d4002c1124400b003a00107030404030580c2c0302d0342c01a030a0b0007120b1183c0365801c4440c511010489a200082241941c0148004d010408240c86003800b50f400060091003500e240d03480c0c2c030000e896035000d03030b204840003a0049021824000c080c41480829041800076615000c907901840c00548188480141416a00d2000f8416100c0070070940d900700394000c61061341c1c0e440d1810030300040c01c001c5800f00d03510300c22107001c0548001c0200c2d941c0c1c043d070040c0400100300d501a5a600441036011940c00d4215010541203e4400d001c2c441e00c0d0008005070611840d20f070130b001030346000740c03071188241c081e0307071181040104016100d000542c3d0032603410040c0c440c200740700c08000310710b4003119034016080503007010400305044802003506d6030a01803048850000d8188811543c0c0c54110440341c1c0c0002c59020f9400700045071400c82c1030703090301d901a5401c03020401d00c2d98400d000c8564a402c43c08101e0b003890100042d0641 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 307459100 1250 307457850 307457863
    0x903120c160e0702120706020c0a11132705010e01050406050601090602070303050f0f070c0902180406290c06090604020f010c050606040b010203120f060a0b0c070b07020604030501050f09 82
    0x42c9002940614a0120000b03503603410144a8040084000100c0030300707100255051300c0c201d10381141a503001d03000506110702c494014101da02d00c90200d00d820010125100c0c810081102c02084440074001031a1400140e001d41c6600300f5106075403601c2052584103003c1c840c0324842c40c070030301c070000c2c56007041000181030700707019001101503500c000000c4c40426081810b403524040e00340c1801d80e541e0315504540d44a40541100100700c943e00c5a00480c0000c1c00350050702400350000c100181045a207000c00080e0340070380c400c0c6414410856440c11036259400c21401c2c49040e0f03094018608422800d4052420f0011110406d16400940a1004500e0501c0101728103500034038281e00c001e942510344545a14002d003500380320f542c1e2005042c0b5580d00034002d40780c041c2c80f40c0014002c0da20782006a8820703404103c952070320651000b00040f4160785004255919101c3e100000d210060900ca04600c50380d1100e9004c4c0d900482c02d2000100140090003202d1156a400081218a040001c0c03c02c1c41d010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 307460350 1250 307459100 307459109
    0xf030a06090501062303070e1c03020105090106030c030609030201061e0504050105010309050c040b1c050f060714030a0f0209040e101d250906121a0f0105060903120c16 74
    0x480720006046040c181c202c41c40889003034083c25038903150150141c0d01407034071a000c540c001c0300047e0754440c1c2003009c3d085902e5050082c0c00a0260750b0717031400810b00300c0d030542c0801407224801c10014004a5116070200000034407d000015030642c40306987c194401400706036130030400321f820080c041401c06000b01401071500b802d090040107850350b0755a4803450f0400300c15000d50354440f61101e8990f5060315800d0076002d004c0300c805101c3e1041c1000c0f900c40344402c01040c040d00ca40d002282841c1d200b03140f0040c95040203c005821920307645000000750030201104a01d21b40c0074461809650f44920400078000b0001008212085415240c0815512000b1512500510f060001ea40741c2101042e840c0154a284100060710340f003a032182c0544000d0f40d0000480603152010210f5141c8500005000304c60003402040c200c290098010402a0000c83e081c1040d2140b0310b0041040342003901c040c18600038000d042c0c400114102071314201035000341582c40301c0b550000410000c040782803178940c8041c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 307461600 1250 307460350 307460357
    0xf0e010e071505040f09021812030a02010b0306090304030311031e030601030b011805130e030c010605030616050d09050a050d0905150304020603010509060a03121e031806020a03020f030a0609050106 87
    0x90b01d0140b5111703160040b8411804040c1e0005028004210b282c00d440f41e95074401092218400c2104400d250742e500803d00800156191203c641d41c5850b00042061041418100079031800782150740840340c4a1f8951048600780c482407018650240c07200d01066003100c440c400543e16850a0000181620790b022869410700000200e005502d02440c00c5010903104160380303200459007101c80400041041002c5404a8040480c2102d0a0041904141d0031143c0460442d101c0d510b030204007480c80020801414042070b01040700c0300d0b020440750000128940581c040e104109a2903e0340d508105440c10780c100040c03000b40040c030440c6001c40c180020b0001c03080f0500d05616059022880b14441030040c05d106014401c0018219038070401560040d40d030206502d00201d681d444043c0440b04044004914400d00c0882c084180c0c0c402c0c490703c60012005c0082d9100e60040351100002980904441810140c00708080f400740020700000354055404148006213051801002108a13101a0418400c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 307462850 1250 307461600 307461607
    0xa03051213051e010e06070b04290f0601081b120a050a0b090105240a0c0201020606040504020f330304140304080706080919031106280f0e010e071505 66
    0xb50b20803410403001e00c8085c2450312110644500090590207103240007041801058200320400c080c9030030140380c1000c00400c841d0403008550401c0801c000460b4000000c40720500000c503958803540600e50090030f002d1040c01208030034180d0254a40c00021040c0105100d501031110f0f460551007403940c003017030a00d01040307000c0e2080006a9a4101842070740e01c1810344c9422040da101402c00c1c3c401a000074940142e94980c6281409484070114920aa001d802420300107400b50800d8059103210340d0b4014440031900d01c01804000301c0500403580f0035603074440407260b0010f80704080c8014030200003815116407245050300d882070a4036480c2e0181b504640040c007040028080009900302650603c0c2000c3c8156503550030f900b850100d401140c44a0103010008001c03d00d5000b9000441211105007943c1d0315a50f030402c40000c81603044c2031000005a6103912103000d11203a840189142c03100c07200402d1084004e0032480c03d5800f890070190103600314000401005050301603c081840d40350900904 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 307464100 1250 307462850 307462879
    0x270405040320031e1803010603030c1a041739190b010b0a051c090b063a0203011a010f0906080a090809041508390a0305121305 56
    0xf80c02c0760500c0c000d1341c2e00030640380002c1c0052010300d44031040c0a002085165521b04005208038202e520540d42803840400d06c00b194004100024821074106a00003c3c60102145e24621a480081840501d02041c01941c110300c40c0c5280c2c01c811417082500c09141d00e40003101440c03c14092101188414060a02c040000780134007901c0d504440c1184406900c90380c0b52031098032584904113103c6403c07103240754480e070094101d5005880490040110000542c3d610003403090000781c115a600c011b402d81d00c502d0395045041d2202e8080300d1102082202610b01079400310b402c0d03c000c2440d03c80c85c0800441d081889507402034041c500c6c140c00c0d14040f10028a0030700040c29040019003000718041e100d04200d030034032000d40111110020090300420100681c02900564000e06001d8405203002c0c1500c038100640408034000050340a41151381c420f0b441404d00341e45141040d12880741c00000c5a0000004500b0034407007000008114012190707144c6040480171803006660300300398800d5840045180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 307465350 1250 307464100 307464127
    0x11031b07020f0d0302030d0f0203010609060201020a0915030e01052a070f1121100c0e090a02090307030203030705010f06090c0807140919050901050301020f27040504032003 76
    0x100c2c402e0960b03800102c0d00d2142000c80c10742c0303e9400b0283d442410403c00e2401c400d081d0f40198125021a500c80c009a03071902422401c0c0d01c91441c0c4080001c00707a21082c4440c91400361410810245800c00140c01d08140c43c4003402c0d0303030741117a40118200440b8180348407182000c541082c2c607094844414036200b580c2d03607100c201ca2400e07200030346104030039100e1400b551142102c00400c00d0407245000c04255a90a03445d984486560380011030900705400c2e034214074014000305444c0d0780020f2480001c0c0eaa07105028000303401c0300c80307220381c140b241450001c01358606100800b07189000e4000462074036400035100c01555616482118101c3c54400100e8007250f0011b11981c103c0305503d465a017842d006495820f09024590741c0c254411101d102140400c0c40304020002103038400e03101703801640e83e02d03801c06080740900106823000e804200411140e404003507030301e40e11914000ba28030401009101c040b1f401c13203008a42c00c6000c103031100a5044428400411228040400c000440c5003150404400303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 307466600 1250 307465350 307465369
    0x60906070308130b040f020f0102011a060702060f04081605090613022a0c030f07080303010510030f0903171303120b01030b030f010516111c1211031b0702 68
    0x41d08020442010484034070b0520481c00189800c1041040b0f41c0c100707400c001541c00c100d90001c0340b1032804400c6d203485a50043c02186403500d840c0c2c031025560b1446900f800300c0b50b4800d06049070300101c1040008a112010300140c000761070310800070112040210f618100100c0c0b40c1d00303c284902c030013504010044e910150b0180118049420142c1c860f240786007010000d0104164044011154500740e9050f1000003600d01d0740d81d6011800c450140130204180c0d502c8264902035180641c2080005008504040040342c0b54407409240024107076801c1e6810360202d59001c6022000503407012041d841404214201640015102c1c60700e804445450f540a0040041d1850078007059486100d091950386c006e60000d0106003003e020b82d80e048500c0c1260304d0081034212100403104060b4801c0c8420503105000d460a441800d00051240b54140d107440d248448588264004203d900e0051180c601d00d0750007000c015414200f0480e4a0741010640445025080060158400307424085a00541d40e140c541 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 307467850 1250 307466600 307466603
    0x1030305070f02030106060e011b0c0e06031203150a061701060e060702040501260a110d0c05030d090602071a03010e09190c0905070503040201050307082e090b06090607 74
    0x11540c80840e45459000c91841e80c2c00a58103501e4840005605038011580309041c0000b41da82d400c0001418400c1c0085848101c0041c105c0b4024600c00c2c46001c80040c0381c3307a0800001001c5502406503042482019802200e240400301c0403c540b2001c242440f0440101405850504c41d02c0e402c9403450260b07030381e4414030a4400300200b40305902d4050700d503442220103c940103070052004d0740c1c40c0c4a4200c54941c01030840100310301c00c66200e40298001040041e04a940488100c840d19008010450000190710040c2d40e18020fa180c00101e40c0da003000981c4501d103540c1c0302d003000c0d9854544042c0c10003c40f0b43c440030300c480c60000500b04c1850300307400b2241902d40b00ca07210100c81e20707000c030320b50b1071304100d40c030089091140d1080d61000d0040e0359400700100c80b0f80d14400d101a0b5070b420002c0300c0301d000544000740411018004110201e01964020364890b0714a15203443c12030320110500400b81c403034203000e4035285840d40e0601880c5040e000300f0350041425a50035140210000c0810303d107101d040c20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 307469100 1250 307467850 307467857
    0x30906080c16030311121f061205090102040e280b010903080f041508010f150e10030b13060305070509010b0403030c1707080406030b0306070519090509010905090d0314010303 77
    0x14800402d800b95000c008040d00c0400d1081d100d500312000c0c0c00d2405800c0d81d102d601211f000d05104082011080d4440642e1100d80c0c5060341a00100c44980180038040c04c03105603950240302c0400c105103540105c6201d4041c2106529104044a0070521603803880e10040050600700031981c052030b6049481d02040b02da20000c055503500044602d11594069508201c403a9034040369012100e95200d01d10034161007242c0352000e034050340c0b014420701007101e480841e40070406000104440b458034050303440b01108541800b007194078690300054905200c2c002510304a96076a07000740103110042000c1e030040e12059900141079410040000b04901440c480241008407070900201005016040c030181095400e00c002d4541c0d0075454207050b56001400340000013841c0504803142407900081150107407a0a46403989021224201952544060441c040c00d03c41d140b800040c842e00c038052002d00a0048020002e41d03802c00b88010b90038441314000c0402090b0a0038241594424a0807009045a51506 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 307470350 1250 307469100 307469137
    0xa12020303040e090105100819081606050a020c15010e1602120a090311090709030b0703090503070507080d08010303080f06150703020d090501110a0609020607020616030906080c 78
    0x1002a01c1d40c40345801c02d00d04180800300740646440c05401003400351040000c503440e11038035640341030703034031945143d401619160303c1c2c1404021031400c0b0020544100c0807644820040003c1d200c407c10b4800580f00585403940c0011603c00c42134013400203c1d020a0711140e40a40303945007a00b4042544c001402e41d100302410300b80b403810003500801400d01142c0414524640720500880082d05000f5944020340f0381041c40d60140754249480e020309803098445072038011245007552036040343c59030000c1451040c5942c6e0801c90010030b1041000e040300c6032280c001445010300300341d50b003418030b103507148543c0900032824010300000b07410013080c5a1120403242a980c0d20f41d0349500040741100b25071440040310500044007000c1c541d010076035161898413a2500d255003a0781d13000464850980d40060030940e000658044005065500801c0007213000800c0c05050402e00c1c0c00088181d0b02550880103403c949085001c10142c11000080050000e82001d00c0340381307130035518a01a845500c07180d4080c0010305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 307471600 1250 307470350 307470353
    0x11090a061805101214010c050c210c120702030706030209010f05070204150803030403110f07051c020a0b040f1401080a051f0603060e1305121303020310020403021801050a12 76
    0xc61010000f400c5842215034140c202d070500032180d610782216402d255087c044804640c9000c2c46c02c583c3d101500e2002042c980882d400c07c1c03002d0f08401c254000b0a20700c03c2165482c0420108101035013600903280042c1d6828061040501d0b002da182c0c08042814014025682c141c0c0c0c12a00d49a4034a074682081e0380d440c10b403480090b0041542003100340860450250201d40f1a030008013039441540320303444c2c124060469802d03495584007080002e00055010f081d003070100d0f0500c0c02c0e0b4244010380c50260507460b200c256000440c0c4034059000155080b9000c101003054400c8440b04000502980d070005171070604141c0001d00c402c0c0010704040f400b07900c4402003080344403200c00c61b807007140e16401c5a014154482c0001000b80609115010a0501020126002c403044040140045620600901c85455041990a0181c001d10158211039160080c00401b586041c04900d040100800e00180d6a908500c10030030b04006040e031041c120030480d40180040c7e00e0307600c1d0120543c0c0c074071202029010b606 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 307472850 1250 307471600 307471621
    0x140a0306050a1e0501030206040e0c120c030919050304090c09050402070311070f0501081b12041101030b330c0f240f0420062701140901080a06030f11090a061805 71
    0x110130b03181c811481c0701c40800035003400000c03b550080b00b142c0141c48040070601d0007810003010300c2030042c00390b8108001c1003004c03004940c03000c4280e07429810402e00059644000400303c0c2c10046045c3d010507007404641046103030a20501010f404051301a064041c01c00380000c1000b00d0003080f10322103c503002d0500c1d0620b04050240da000d141c1181000c0d410b407415141c640700c14000900461301280c01e0044d40e00642c0b030858030b400c03907480e080b070400d42c8460408401c3c000c00046121400c2d8000504000505000405121414491000500404000340c12280d07031080c640340d83e45095280c002903400c0c840b2080c2c000d05c103240c1054014444184d401c802d10107500180784ac0c02d0a0380d50100000072030442c01c076a040050503940d0100d04001c0200306c0d0600040d6810906a0440d00c1143c2c420170943d80558080c0d20b40310b4104000490029007961a0b658020000040810586000c81c001c0b801104520f8072194042c3d0111010340c062104624002c14403c2c40d12000c111102e00c00d880d080059100241e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 307474100 1250 307472850 307472857
    0x8040215070f0c03020907020111180411030109020c1e0a14160f180b060703180f090218190302010302030a02120f0a0f05060a140a0306050a1e0501030206040e0c 71
    0x41028200101c502d00b803a01c80c1d000348035807004900909820000071101e034010b2240c0b503d406400001c2d80d1408008489076603c038100f403070340e40c0d034059510039241c1c04100c003603005503001e003050074001079031051209902c0d403400030381300d440c107030310044001548820b10804225800c00c1644003e0512a16295020303941c00d15812001c075a44900003038400042c2440c0c1440380200704c44107203071444c104200f850f6034072050300d01c000842504802d08000001c0020311a280e05021011001140303071403652500314003403003919030b688901708064020a554a950105001e00141d805040340c0f10310310211004d5819019036030501c1301a041c50750201c001080d2000540440b145600300079001441854903450300f0350b80c42070558240391104c1c40c11030f40380c911110700d114850107840000e01158440e850261000b690852010060350402d8800600000103079240c040c41d8001c4030044004907404800d0540d20026995030b09182005a091100400240e1036100c03c56017651800040c220082d80c40c135010903024030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 307475350 1250 307474100 307474103
    0x250510050c100f0903090b0909161b03030c080906040209010621061d0a060302030a0f03020c090702010c0f02160b0f0f040e100915090e0a060e0304050a150804021507 73
    0x1400d000c6000700c40200350f4130802c0410b01c20745a400020b0b885100b45030003030150481080c2c00c0a0000081100c801e1688412142c0708003601e80410000a5091070402100c040c800c11804a5150a285011540c10a2500354000b091400412480c6400e4000a203851418481e080911940d146162464810807282e00c2800c0740034070003400226038814011044007041e000c043d42c1100c4400200d009c400d62800780100b00c83c0c00034001e105241d100c0d1203900d03000064207000c40a6209040d911481900c885c0c00c12842008079400008526002c580090440c540e1049987c08540000592150a0718421031f0301307042c0c440c80c1c41c01603101c40c00b000c1c0c0060b084c4230f20ba03281c003581180030a000901000c2d68030080e1040700d09080114107603546692140a860902042c01c0122040c85010300110806510294400040400702c40382d150058440504607400c03504a41c0007504001000e1045d424400602c0f0300500f0700c2c0c1001700007000540301c000c1506c0e01c0680001d204883c080540b8844403030041c1680c2607036 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 307476600 1250 307475350 307475383
    0x29030712050d030506030d120506010306030b1501030b03010b01021e25050316030f02040b0a0911030a0c0e0a1e030b07080403091505070201030f1d250510050c 70
    0xc545052007a035a80c0c520a14500003410180001d0071802c01085005030400a0303100c1c00d14440c1c1c050405406060000c141d641011b550300300c000f01003052342e4055406902003000c0d980003480c140d030005059403071042d0024000da040c04075041a590380001e00301e07540c02d4043e600290b40070342e0303020a40c1807204a5a6146202d10b00150901c0741056010102040340c1c0210100c0d0302d034503034900c5d4404100c2d04605c00034164500c5845d1140141c24141c1000d038400800803c00c0c842503450355510340840e401c0c0d0600740c0065801104110300f191740c621074024a10349a0400080b04090900026801d2807039004401b00400f04882002986241d400c5078006581d01a10030b0340da0f4540030304000c081800480c0c0c160300050b846076000551640c6801040e80030111303a555103182038426001903000e080c20300c030740c0c0341e02a42c1c07080c040d412240044071100503102c1c2e4a01400c0b5040042c1c4400700098800311035038404400300d44c410401c2c2c2d0307104004200142203d080850b151604035030801d003040c0240001103000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 307477850 1250 307476600 307476629
    0x60604080a15051023030c1e0102011a06070f050a060c1707110606010f02030708030a02030403120e070315290301061707050105090d240609290307 65
    0x40012020701c41c81c000007011030803c99603842c10100c030588100ca120b5181062038004442011959400030351705100c1003d01152118040607000c68103141c2d50744055440920040d030b450200307680c28014201002e0711200e2000038511000006041407040004c02443c1e07403184800442040414409003100d02d81018080000d0040d6601c05407103c1c1c206250148d16200950005030311500502c20350000b407940c1c1004102a0340d422006450300c0359000700c64019480244002c8000440c03240c011031140100603405a160f04241c40e015100380003e50200002505281d01e150204000040a03012a904a61309041c41e10003c1907041c010540807100b20440054400415209050980448001075080d00200400c40d59080c810750940d4010180b00074542240104004640c4200d000d00b001c1400106106140b101c02e80d20100107405296192100c2c0450714043d054564180c452040202440841407120640b016034040100b91545a28007064000c41c003403158a8a00b00005d2001e00001c071070600348c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 307479100 1250 307477850 307477853
    0x1b05030406090803121803160819140d090602070206120103020f0102030a020c1224010305120306030a020904060209030d03150f081e120d0c020610060e09060604080a 73
    0x8603540640581c40102d62118400209014000101c44c01140385001104081d103e490200c02d0910101540b011244404e1041c0088400c10b03a0a03103641a10030303036078142d8428403da0491030b19003514544806100411110441940314541111440c55030305400081e655001c0c60800000e002c0c504029401540110f03840400721070514156041e00d000b2900061403400ba080120b030f1303d12134424860b0040c0c00031080e0b4106800c080304103c04500c0c40e1016501c0c103808000c0342210003400c91a2510240c4940340042081c0102480070b050030440b003031001450b501e0b140740031a41d21071440800074004c244a000260a00240703905441d8a0040107007500c446102c80e1500901400142d0303d2100f4203c25450300050340521005140101c4041c10b02905d98800916864243e25055101c204001c0c09818101c0911052081c01410b04440707e010000f0109040300000b440e02c00007d0106280c0140c00d0707018444d1940003101240411421211101c040d070355100132617001d01640d4880c0c0c01038407850b8181c40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 307480350 1250 307479100 307479103
    0x30c0306090c05131a0a11123f0115110f030d0e0313270603080406030e01050c22030f060519020403020f01120e0607180f05130c1b05 59
    0x200682c0341d41d240f22461034a82c0c03915001c1ca8800d880c4801c600d0305c20000a2440e0b80210003e48681d00d02030103681c180b0104074402900c590142241c0b8806540c4001c944041441d00c0c05e00d031455000700c94000d105c1c0142c41d0a814048001800f8501d070011032500c200389041e10a81c1280702810303504e001c2e5003807443c40740c101d030b41c3e0380d0809000d00595500301200341161400000c26a41e03420483c4418024441c504034418480c0a000303500010802c0319810090a00044c0d030140000039031144130307841c1c2d955191040040403030312031180d544070710b90400c000d201c030444d8140c082d124500401c140008114582c1c54007a40a0740c100c0c1d000034250081c7e01c91100901c0394991203540301d01c00d0280c0314001e40c00c102c00750108a11507170000a500c20800c0c00e09610303551042c910b47e1518480c103200043c401c24044101840c00c1011501d1900089000c040700156185209060f030003040d0000880102e1414540060081ea0080e51008040360b51210b410f950b40c1e00c203080724882e0990202808524402e6402d115 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 307481600 1250 307480350 307480357
    0x230f190f051512161103040f0306051e010323160617010b0708030a0f050f06030d140915040f0303020a03020606010903030804020d0203010b03011a0a0509010f06030c0306090c05 78
    0x651103040d1100c080250003141d80c04403001001803411098403955140590400681349140c03500c10800049208044050204001d00c00f80c01a203080d404404c1c60b61422030706580d001001000581840b8a95901500304501c10300d0540e544800b4052280c141e0f41c40340088103155000440d4244a180610108505c00b14848415685107548419070100d284a046074410000e115280340340400300041c901040886024540100e4039004c041b80d00d221101c40c860a440040e54100340b0910140103100701841c0411200e0400595401c00003042030318400f600382c80b8024a00c000d03008a150b84d0581c101c11201c40304036400703043c0000c1c60f8407030aa160704000796504036500c0200d0241c821a000315080f903000d048200b0407240d0650b5843d06507540c59084c00903407800c54034102c1e01036485070303142e80450340e0078010034030700300c15001d511a03615a4090030015110170340d5000d680100200302c0180450181d645104064602604002c60079680b0214100c008049940c80441c0541c035201800783c9856001008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 307482850 1250 307481600 307481609
    0x1110a09030b06010c1e150c0201020a031a06090108091e0a03020106081609091703010909050705040507020c010f0e18041209081c090504050f040b01230f190f 70
    0x12600d03640c0d030703c100569a02c1581c1d54003910700745841c1d21040d0100b090003130b007841162280d8690700038203092560000546203902d032400091f0750040307030b980044c46d454410301c58843d408100440c062039900020503201e1060040d500d0400102600040310300d0b070200b2152901103500c401c01440350b8402da03041601c0d0803486000300c00650800c41c00050400000821841040e4400301d503010035442e080401f8020006442d00f16200700700c0d000865000340d50000134600030303c00280d021915080e0740c5800c505007100c0f9008a403085240005008009500280d84040b6901c01e0a00d5400380c242a042a21b498020300c00d001c0c1c0c4071b10312400007600d503850175402600171403040c14102100e401c1766006450b08202400307054810340c8540382242444c40701848a144140c282c2c1414071040b91200085010380341c040311341c003c00c02034420a0208011400c2c207020b0040c42c103012003240410f1210b02e288141070444010034400c4800741c3c0800003669541441d8082800c0c812141e80c01156900500100180c49128 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 307484100 1250 307482850 307482863
    0x103030804021f0906050714060a0506040f050f010501051303050a080d0606020109020904021003110415021c14030a0e1c02011109150f0403050a0501090c1a09040b0301110a0903 78
    0x2040c520b8030400c088491045851500c81652260500c20111287e03000000156400e54082c0000204005d081c23049074010316290384003103404d1404806000507560700c40203802c1d80c0c916140400510152483c00300b0305407002481e080303aa401740c2543d0441e08586542014081d405201e0050302005410002001010302c5170030240466503890070705030300b2a002075002940152a05000a00602d090040301c0c8200c0344508002480c034004140c0e451080d0002d40000644100c0f042d80010303003503010071010a80d80d8a4500000743c800400300000c140900c0680002c45c858400300219841813090341001590300042022101d1000402d00981c0c500c01210041c080994a003840c101d40320551001150007000004d411640407402c0451009056840100140c03108042448040f0000c0c100340043d4168034090400440c0c48840ca0414041a4049a0060500d9034110700440e554856100c03c0c3c91860000b01c400080c0004c0ca0300100340503084040c000705460100240442415400903081c2045d40c0c015007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 307485350 1250 307484100 307484119
    0xd05030a060e160c0201030f0608060603070b19050a0e040f02180103020a0509010806122407091406220b04170c030a0b0714070c0501120c0f14040509010303080402 72
    0x4503002e1501640c151060200000c003d074400c034001c0500c0000c4c40d1040c98001600316240c460f18088510076000280c2a40182c410b04c107170361404101002c081c01448400d140342a5203524503174400220101b0f80c0c0c0c00c3c02404030321004041d00484400348a084041d100707100d01468030031108000c0d4030041818150400c100d01882ca2544a031094a6201c00161641d91070111002c1c0150350a19008020340ea0041f21186055401501406005c598210643c00d41849030840400c8a5040d24020b01c00700411070b19030410000e811762010041e014020030340e001d543d50007000c00c031551200b4285d802c41c24043d4400100041410040009208076142c1c3c003500c54403120040360864940b15070000d11507141d482007804ca000728101076480c680150389030400195000c600b1700d0300301071340c0c01041050340d0045480380700300700950308032603481c402014680c810400b5020524014100b80714964800c010400c001e5852525502102c04031000340c00020940f0a0a6030f41389002001d4540448089000b5240320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 307486600 1250 307485350 307485359
    0x3020d0f0221070207121704080105090d0804020306060d1401050c1c1802040c02030706050a1a03240601030b120a0c1a1c0209130b0102060c0c03040902070804080d05030a06 76
    0xc02d61140100d440340d010740354040c0b400383c00c00e003048080d00080d182035000b42c40840d4611030603c0200000d00218001281a160900341c040c1416120880c41d82030260401c208001030380c0102d03841e030f4001400c64216006008a0030620b24420f0444d1640b5030942c0703000140152203455002030081c0200503980100f2414407010ba56054407103480403416403c40000d100c800521b0300c1d4001000401c101d20480e420010152560010781c1c40940365003101e217944003400000d04159141000720f00201f90000c00300048000083d01d9030a0725006182c00b840808400b03d12103038869089041d0821006040c8134003070514010380f544403807929204a40c111044640080c0d0f248000078501000f014007000386e800c00e442013a0b40d4a81c0d203020161408025400c01410300c4607a291408008004088000007850360a1000013900d0b2074000b615415170300c20140207405043c0d400104a82c155052000c025865840600d018046802242c00462080c000e880c0891079095110024520450581c80280300c0146e54 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 307487850 1250 307486600 307486657
    0x115030b0109030210050f030711010c090e07030c0306081f0608071d1f0b07020108220219050402042912070c1a090a03030e01020306030606090703020d0f02 69
    0x111005680072450030071080015203081024a44540c01710300b48940361000a115440385c42c0d204491030030200f0303204582d480c83d1000034411000c0207641802c1042c501e03818000751030a600d20040c001c100305a02e580100d81940d00c40d03089030f80140074801c12038a030720317001003450940300000d01d0407824002d00d0070000191b010400907400003120a0012112801c10700c0c984071132500040182000c06042c001004540d1413030010560a005201c2e540e03642d500c40007988001045240050b042804a01c49042805490380c00040e404a510350304035946d601641c0d0340300c4030701105e042d140c5c01700707034041d1001c00c2c005408030084403584007503000d1641d01d454031414500010740d1401000c0c020320781600f0440002c0c1c402c03030044942a42d554041c640215070368804800d8120074240449075518140c02080d809000c06415001d42da84000000000f0b41c01c40c1380020100703580d00401410144502c5407200070800d224040d42c1182c041a240b8002440404400b00c80c65001c0d40c0201c1042100000302d1191080c038800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 307489100 1250 307487850 307487861
    0x70302010e0c010c02060705071a0706140f0c0d0905010e0303010f1203050d0e0a06060803040504060603021602042a091404020307091a0d15030308010b0f0a030f23011503 75
    0xb05841d264140041034082c030200307410a100441d4903100d00d83c40031030b070317501d101082000d449800714446541d883c0d0792a01005481d030148220317507e190a1802d01c02c032200d240d151035611002d404901d94954004d492a20087d000c030b2070010302294a4a4180702d2104c44c044000c506945d01c16000e00329036540c3e08600300a21540030000780000340113016000c2404265084580982c0d04001110402c4e107aa03120301c41211501e0740303d60201d07400054100601e0078613009103002800181400c508080001e4042d20000d801c0c6071000b44201c0e40e4850f00814a41010689800329000c2d1140c04402001460040c100001c140076030b0017108801410540c9525050003228410006a41c0d2629420f142c006040103500307196001148021080c0494803400c402c0b0304c100e11026040c421800c00503440d5040160501c941078100340c002c40402c00007418151924000c0f038280d45441c1c68005000c0c1c0541d4030a1009114035030040d84194000c040124641c260414181d06807841c3c074110305001d6442c6003080d02241c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 307490350 1250 307489100 307489123
    0x1050316081b121c0906030b1c240603030e100c121215050f0402161e0605040f02010e0102010612030e03010608031303060b0d020d0605040c05060f070302010e 70
    0x14480b800c1c11010022000541c1c1d8075440141c50b044040c04608601c0f03051283c448030801e4650722000b40c1d0b0202c60750002e56040101200e04081229401510102e50304000c01ca113520300d000c0b0443e1088041202a1020301d070303982c0c09400038080d61401e03c2149005030031144030a03000102d10f0508001545083e0503051340301100c0b0f40721481403055030350f2607080e5081007404903810700134400d14000c030250300ca010300a40100b088405803200b90a2100300000781f120340a0f00ea0040c0d01c10b01c5000a0001d414181540240c2c1004440d0084040b4180b5441c9821200c5002002582020300b44820468048100c00710b003032007601c0e0352101e44500c0004908840aa2040758822954480010003082c021700fa6409142c070084c0002c11001d131102d401c0342c9140c0c45600035515484402c4003c00070701ca114802c42480030380c201c50000000c055600050340084c4401e1f0007a00c004d54a4011504101e01304144a0041030003400c0d0320f488801000800b90290420070081d400b650a064111501004c0459810040b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 307491600 1250 307490350 307490353
    0x705060301140409050f0c011b08120c0d0609050f060f090a0c022505031204030b071b120e0f030a0506040b041b03050309101706040e07050a0e0105031608 68
    0x580c6041d441201c03402e21100040d410694607522600466000d0044000091604006180024007440018000c1440858640c5041443c080080002e502c2c4000c40c1c3c0c03d520103071080280e1ba103a1003902001c40c441c51141c00b5000303261960026450286800080c0700d5802c9581c01052075403004180003d20341c0305030f0382640c01540c00700000ca013119541c0c88041034401da441180ca40646404c8441301c4610710180a0346606403540040280b490b0410500214407c000c0d0030b542010314603521003100c08030141201043c004030130811505003034401020080243c0101400214a1701da0384041c0c006208003110b00c2c0504d00d0101c5207840c604000914022003130388100103142c01c0e0f8668513030b0307a995140030b0402c440103840081c0380c0e074040301450035a8001c0d42c0100081c3d96205681401c000100300c0c41420403050200114180300e2070565400003e9000d0300943d000701e101199900c01e81e09200b135035009964001858640441c0400002080c641690320903000c60360350300010307207000c0619070040c803034030096 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 307492850 1250 307491600 307491607
    0x2010e04050c071a01050a1e050420070b01091104030f020d03050702030706030b04050a0501351203010503120f0f0f1315030b010e010c020103021809040c03050609070506 75
    0x900305640407662004190081c1410311180399a046603c94400450301e20501040c00180a9854103000010013000f01a403032004424034100300d90380040f83d0f4400e503480b1781d40d1a00d01e007001c09054004501d84105101c032465482150f40751450100c1da0a01411a06a00d0300d080e80d9a440358040866080d00d4200c12481000c1c0c00310b0382001215280002e046040040170b000500042c2c60800101002d0141074501140180e01142032000719400100f00c000c00c030303083c07000401140c0e84040a50794406062103019111800c4a06406500521000840910b108e62400580010540000345058480c103c040d94840e008540108450b401494207180443d40c0400486600002100050040044850105080c0352800040180807803907988075242401d001550720b2101d66041c441c80b1407007042420031003c0030481900081605282c0080203050550010b00742050060524100018080c010429a042d20342450403910300c0007607210454151242c031012401c0b0007000f041d4001a00c8014124505 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 307494100 1250 307492850 307492877
    0x150c0120120c040f0b040602010b01080c270a081b060403170a09031a04031b030807030e0109051603030801060e0f06070212070b1b03030c070308060312030702060406060b03040201 79
    0x50050702801c030b103054803000c1100083c032660082540000307009011703401c2e131140d140c07000103405d499101840d82d0421030708604004c2c844504d4002e86003c2407a400c5040c10300542d00b0081c0d4101494624420b901000d80c0d01c0c00039485400050000091607400200a841d08031101441854040c4d4040100100b81d903032070b951a601d0b04680a13000c0c8403003a1502d0300000da681e49800d41000d100510410010700c0300010403060540008107449004e6100d6040325042c030450318000c000b400d01921036001c040c0c0307132941c1001c094000d420000b100d540000030346018080c100c203025960b030440d01c003c030041044c18000252060280709403c0c180e15001d0800700001108008202d100d81c840081241d022010100034000c0000812161000d080002640d550301c10f007204a0021a10542c0045046980200200000200006c1c2610b40300d40e13240c00c1460483c0c6039140000e0600d0380070118000041400300400824a50003d40b00c1d00550107040104403186c1c55074201da40030302c0200c2c2e0180c00b14080f290001c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 307495350 1250 307494100 307494127
    0x90203070e190e061c120e0f01141e03090a1a070c020603061f0c1104020421022403060a0603090b160306120f05010605090f0109110405150c0120 64
    0x1e0744804001c000710742d0010502046001c1040a17501600d601c141a8030360304000d6040007180360702401c100c91401c000002c4400090074451003440700c8a4000d0f020500c042ca40028004504000e02030889454483ca49003d100f5690001c1040644000c000c45040e405101c0341d1011003030040c1d01955520b80400450f8007404020b13032000d80841d07002440b14914002102140c2c5251542e1034080c3d6511545503400d04201c0080101c00c0c401c10311491040008014030140c0031840061480110040345400403240001441035030800701c0814035a904144045150622000541c41040e003140e03103601c202d803184802c500721a41c48200421380c0d509100401c00440751603a000c012090140b4000c00c2740d83d2190441421100d0441085407801c55007002e00042160030b0182c2d40c0503000590340d00c221440c3c10500b40a400e4410b100b0101125901c41c4541404114902158050800038210340403a0360071101064442d070091598200d19440c0032000d41c43e1014900a03051055407083c601401d180441c0341c0003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 307496600 1250 307495350 307495379
    0x31b05011403010e0903070804090e0d0206070906030b0f03060c1b16090506030f07060203070308010b0a230f130302040506030604080d180f0b04051216030806010c020901090203070e19 81
    0x5e5031144824000340000446000003003001d0054024042001410725100ca46000c1c044d4260000755002142040a4568840004070450b042c07890041540c0340c80c00d010840c0039120b00e0780a90140260401c0001140d00c02c0c0007000070344404c0504e0381624039240d00b483c1d126000280108041c2400c0c4008102410140d0005504600d00600307480d4001051400b484c502180c40d0701640c0541c0010580c14203154004000d9070062000c141020318140203040300a240c0200c80d5502c042125040c40083c2c4500090802c0d6103094401e644003070b03070300e80700414a40300c403009601c0228492420200041d100d0305010070b0340350003560312000580c102540120aa4040d203444401102a1200c1003002800b03e848007030b03038801c40342c0142a01c44a6082c6802c196080c91000d01491040c1c0030100254881800318074001c0806c0d5406182800d010f07194140102d03103003862072801070f43c059800c01c00800e01030225401103015000ca5100c0302c0f0040d40590500421650301c03105071110307001c6400b0420803800d20030281c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 307497850 1250 307496600 307496611
    0xf12030a0f0504030306080c010809070e13050f06011a070f0b0901090f1505060102060106080c130803030711011a0603010e04020414040b09070e01030b1501030f06031b05011403010e 80
    0x820020350346407420088540c1140c040e00000c0c1c488804200b454802d001040c5025820300e401000d0b4a000b840d039954400c100c0c494001222180c500080980c018003010301c48650703020044d1103501440d406520b0760398200703004a107254507605050341c800c60182c4088560060b400b640c0040d400009888040914100904420355035480d0140a0f000841c800e18904007148507206540b0314070022820344007145d600412860540d846800140907154102c043c09502441c8201c44c140d03038015440b07035150386c140207501603180d900c07000c4113203c0800e42004001000e0b18988008000c0e51303074851601108130003241205600820204010b111001030b130300b000c582c000c0c00588041407020b00d0100b41c500b00001204c040e00c2c00b0710000300f0300c0680241440560010010414031120350b505503241e4001c440000b40c6216845854911102075a90007908440c040079810b203410466965681014040c62661010700780001c8040900400c0c6503004144044000103404034207070441e801c4c0710180700c0c0004041c00c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 307499100 1250 307497850 307497871
    0x7081303050d06080604140c0a0308030405010f060311130b01050730171308160606170a230312090a02041e0e0606011d010c0206070614090f1203 64
    0x100a045070114003860005100c0039004100034905820280c2070310b1f065418001d141d4014014190013651101003841c20740e074108014550f20b8507141741840c014010301c3d041074501410001e0010512540140a0103c01000e0b540c4100014581410701c1c112014004064041001231240e000842c0005000111900b4103045442c05042410140100103848194042c0000d00e920107400001001d895095040554a051408d956007a95501c04950103a042014400041c1c03104290500078203800c0380b0300500400420f040c1820080e141d040c1c607105c90200558040361111500d586040e0030f04003e54504213810080c509103410b00c000584005e00240504d0210b2250101c11409030380d0341c0c41058008480010301d001210304907000a4240c400b0b000182059030080b00421165981200c0080304581d18045501e07804850003005941c6111032000280d000000401c40c13104204103940001307020301c0d645c49000c91070303501c2c0d516543d03813910030246019158102034454107103e11514059034100b00005c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 307500350 1250 307499100 307499107
    0x6010b0706141302031203130809180a1a0d05060a0c0203120114120c010e0402030618090304060809030301150f0507050109050105040b010906290c07080d090e0708130305 75
    0x100b4609103598141e8110b074500300c0b03207200b0104604e41080100804241040403a0544c50503035140001d5003030001014041030030000340c0000a135544410a01171091100d0103221a04046040d60300524003418450843c201c13400a0b0556072030906030005180b50310100130a42e5a4481040e080500030101c00e0006621050054415404203210303054040c260410207104c0c0dc40ca030030200020741d44291007074851500403001e030203101d076400340004145a1003602c025075a0788468010881e503c0b0044045020100d0103000e0100580b4080020021610560303242013950321519440c40d00ca100a101e02c19880700610800e1544c640201d0300704000012505040f400c00c46152900d5007550590304044500380d64841c2000101b000a03118140900600c2c40100034860030f00100c41005c0d001060407920140f4034100c071082d101203c2c1c3c11100d1014400d02901c0d03546035500d030080da40b01c4e00001d2144c0443c3c20b10b03001050900f03249280303510404060743d4121b11615400303a0061680a0a1426000c205081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 307501600 1250 307500350 307500371
    0x308120a06170c062104030c0303050c25110319110a08100504061407180807060210090519080711010503070912140609030c01050615030613020c010f020309010c02070806010b0706 79
    0x14030b445d0b02c268081d1f00c0e554400301c0c080c5401011181e0043c5052240303441800102030020390308141039500c910400a80c29401e42d07904100d21032100540c459603140c41403450501c0404a101045610341d03105060401180c0d00801c200f041c5040e050040b1003182e400b100308a201031016401c2290003900400d4001020360004444070782ea081d003181c040c1d0209804201c4420844c0240314500300131f1403403e001d88495414054000c2d203034229014074400c02a00c81003a101400400d1109151404c0c842141913038803040d5280c8030f803030b68021010aa4032070062028410265020f8801c03a0301c144810f82e11004000c0c01e010104403800001c030015a4072000100340841d45620404c906400b42c0407030b00056444e00141c3d40703c1400d4841c010000ba010300002d03800004041e5412003500c2d00504100c542810040c8501e82c040000d016103080d01400e50f0034030040302c500d58200d07401113000f1031460000f030184002c01c1c7c00603686e036049440394072082c0d8410401044030385640341c040c000251180c00007103103e4111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 307502850 1250 307501600 307501657
    0x3030c090d1b090c0e0d080d0905030c0d0c1e030806060c0a14060603071a0d020f0c121207031a04021e030a15051203040b0a090308120a06170c06 64
    0x60380c203d0003072581d80b14504042c0c117400c00000310200c1d9007224400342610385540d504e0000c5c0102d190502c50981c4800c0482d003001818020796013400c0c41c1a044610203144c642008292030711801064039480700079007803003440070808142c600129406444039605a04c507042405003da0043c030310301d0180c0c0030b00026200040c02107250300c1034131300d442ca0062802d801c1c48010103003040f1403680107402891341041c1050001c08520291106c1c24440b160040e150050580850014850865540e005000e400c0d44165402a0803000d0045140300480c1c810051381e4980e4140e0484a00c81e40410401c43c0c03d80c1101c00324545a0000c0c8142e20344c11400c017840c8002404c803151150410303101c0d03c40580d140d044504221600003903410060404948456204200400070f0740c07644144e0051030607109002440c800d00da0301802d42e4500441c4d102c10401e9032811b2880a000c0d61100580d4654086800d083c0c0002d410703070384840300d010742caa1030001505508000604100ca01d5110b00007480e0020254481c040c200c014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 307504100 1250 307502850 307502903
    0x8010f03030f0507020319060f020403020f0f030c0a060201020d06090c0c0f0201180305070305010f141302031f05070e0a0605090108040c1a0c0c01020712020d032a031103030c090d 79
    0x142c49907c000108862074050191001e0400e0602003a105000030400341e0307550004070007455801d941c80c10304186440003080c2480c0503184d902d0b4018102c41400141d42d0790541c02800c03880b48814041054a84074180203082c1c644503180c0c600040e030030b0100000800c0b0000c003140340327591050412964414510b0b01956007a8656881035582c4c0d002902c08109001c0280562081c0c408451810000c400c2c02000719031000340c015061030104201c1290000c00c548040001659440362180313540e044808500310703140a41b2003101d0320750001d00c50413542401410035071030b00c200341e0301181c5506040c1104040110340440b4018004d444034000c880d000942c1c03498a024031525246240f03241c035610a280d14800340b4200c00301107140c0c115800701200f0060241e180c0d880c0c151040d411160a204199541412034100d4100b00d20349007080c4003041480007800840c82c140e54101e103e83c0302d250188103501e02a0741c803030004031100b2038141d004010501c1140703400c80710048100e205402c88e0303071503500700098800a400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 307505350 1250 307504100 307504123
    0x80105010e0154050a0e091009080a0314011a180d05010203010614030408030609040302100e06060102070803032403120d02091f0e12070305062508010f03030f05070203 74
    0x109504030341400a050a0803c001c503a0391041e084604038680400726601c20501c1c4500b01122403540c0105000d09000d00040c0e0f0440c0c2101818080300d40c0c50300b400307407071b80e8070250f070600c0402c1c03400b0034031502842a003011034125041380201100001d862035182c2101d80c804400c6940d28140440b10358425034400e150090803a014100050b12907042c42c001510300041c040700200300c200705008200014060384203da80c050000e0741e4003012500e0f107250031703403400702240b1a40b49903a0501c050f440c43c51100207647c0e44124000d90842d000b03141e40c1e40c145a01d034402a030704040001c1012201031140f0758907400c404107070400541104d17200200c84090b500300b60072a80441500580009490406107882020800d08100400c6c0562000c403407448098000c40c408090360f4051a43c3c0d0340e858a01401c1804450f0003140c000003511803a150042c0d089480540401030404c4007103180c941a090310f40300340881810303100c50701c0309081c80038110b40b0291580103c40e19400e040080030401e1400585050003100d00d000f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 307506600 1250 307505350 307505447
    0x90f02091c21031503060204090e0a150f18050c09070314010e06010c0c0602030408100c0206040204051909050303040213090b0f06060f0c0309030705010e010e040e070b04081507080105010e01 84
    0xa50915003009c00b600e000c1045200d940c1d21007454800494111001c0000642e0401d0b000254189820840006072403500c0c90202c4062203080c4410611801103501914410121000c1100d03a0701c4110603400c0b609102100410341e1150001401414640450660045414181000488003e55888080d14220b40241c4e0060b000464100001e010070404c446110740d1079a0207109034081518000c0d940c20703000300302912554603140031032032032824034100c4072107100c01543c1400704188034242690740c2d61090350700300e004514804071100400024890b503022264001c240405a85035410a82e0812502412056010760300704128110001c1c0c038401440318146032005944c5800310541054100704003a8031603418881141c00034a1141c0c4e003c02040c05c9100100c82c0050304810401610b0301d03081039600043c001440020300400d89200002d0320900301514041800525641c040741114440800c1c0700b03d502003030120b400c03800c40b5801f4a5240003050000303c020b280302c8014070100b402c4005514250040c9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 307507850 1250 307506600 307506607
    0xb0c030717031623191205010b041211030316330e030903060f180d0c02010c0206120f060a06090b090613090f02091c210315030602 58
    0x400055001c11014001c1e120a4503095180024054070301c5000480c0a80402c0011100362100311403900c103101007501100308498035028000309882e20f0300300801e0880c001c540306241c1224a494140a61810b0320707600041c1504061a0981087c0c40e90511a82200e516986803441003041d1010000341c11040b0852041b01021070143c1000004402584421000c00d080303030102440240f4412a05e40121180010004681c4071806030301d13065014a4420507818000c1100380285c2c65059a440343c00b409a101010b100c00040d901415918400c0b0b040c0c40300441c0150048a003d5070182a40082d000e00103841ea901d0040160701c403060b008001c40320b41c000c0281038800e0110f42d01f801808007015080720708060414508040c2c4009040c007951410b40d208020010b00b0f91a0340546400e54002001a134006004404580040030080e4003c0d6400a008504406c00c07a2035034854170084041c82034009100b05c200005003202554800da41c00d4070754050640b00c01801801d0a440e845100003180079480c0141c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 307509100 1250 307507850 307507853
    0x20c010f0606030b030c010f0909110409060b1306050d09080705060a0b06120f040807050714040c030c08060111030f04060c02120106030203060f04170412030306080607091e0b0c0307 80
    0x4407161a001542014680103204840740c07000030307202c03039080c4090a02c8141081c1e8100c003150444140d030440c08411b41004901d1a81d03032004d80140080d5029820180902c1d41c0b280d600101c82c0c09403400402008007508010025140607030020214a150700002180030700103902c80403000d9202003000c98480c1d03c414100721581400340b05d203a00400f01185d030a8948004240c8038000306a0150440d031781c032412240802d04001801c403c0b112083d03404825540c072540c1d1208040011050345980d00d020b58104004482110f210f4460b1380380394482900c8a0040752030701d1004407014481906401c501d8801044400655030300540a030000307000301c3e502d8003400e072082d1040c0a054110002d00068682c1072040034001690003240d910340c0b0850024110b2030555450070480e21085120b0482c2034094000500414041d40ca154031002c118080d850500034243e0301c0141a95a050071140c03040000c0d0003034401e10491084a20041011b400c44040005407610390019002075400303125030701c1080e44005100c80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 307510350 1250 307509100 307509131
    0x8060901060506030907030303050a0e19050c040c1202030402030a0c081b0301020304030203030c03070525060e0c0a140a0902040f051c081c0e0a0615051f030c02030706020c01 77
    0x380640000c3d40d0f524150300f00121816a20509400010305064075100003038074075286a0f100380c0f2444c005d80cac1118000200040382c0700b520340c80c2c41c00650703140c01101050703426400e040c0101140712515903a0140f82809103140180203402c083c104a0781405408a0303503007c50b9201e000701000d800c880024210300700c00d507042d10040c0d003484442d03d4002c0e4010300c1003002098011060720390191140c1e4031b403542da9a032910102c0703040c45580400b004605141d00d03558080c045420028025911400d81040032880d40b8080681c0c40b031840148507031001c0b00c604c040c02a200c140c400141c840c00c000d8250100c454031408400309036040b07900036034180c542da54020480c070701d000d441720342c0840c0000b0184040461281c45803140340c407540850801d4251000c0e04881240140d5020400d24411002520282480d40c5005006041804404080c017803100c03802082602d001b002090020700d000d9502130912100300c0c41070707011f41400c0000c0c4055000900811010541a0005003140c10600000040003507000314840c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 307511600 1250 307510350 307510361
    0x22050f06011818020402160b090703150209100e041d01050a0b06030f040f150f0902010221030a0f0b0a06020705040606081e150312071101020f030a0311040b0408060901 74
    0x40305200d080a60041442c0020803d48100c43e030150717070269030368220420040014581080050910660b90f04004008002049040550f4482c200e042507e04044401c40142d000e0f8544541e40310b0007108a800074a0302501012580d00303009000412840740610300500010f0f0305201842159460301c0401c10f00309200d129046590404032407040c11030502c0c12074000002c2d401007004101b6218558040c040c8000e001004a5210403402c0600c0541d04542c00035020703203e4010101e0141c07242071f1540303000c9402c08505200a401668405096942d04d02003900038207810004e0404860740c4000a0541c0e840b007001400180c81d42d13070028415949420305120407120b50741d000c0d2040090080c14000d40003130040c0d1012040541840e024059100c18482d108009100e441c0164144540000c00710f1080920028202c10b90256130940c2ea04000440107988940c035203c000c036031582003007140c110907600aa11803c15400c503400d61505240d05c5000b00c2a003940503410105084d48003000f0001402c8090089 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 307512850 1250 307511600 307511639
    0x50109150c051c06030f110a050604080c0409020a080106030b0f010f05150702011107060c060501050a0303052a0a0c033c08090a0b091002010b0922050f0601 69
    0x2048040c06010000341a0b00480803800c0c560508a0003624000f4201e421a0001d1034000741070444a59070362400e0b801034684280d05501070200014002494600030b01a18101d03410318000d000c4203081c26040100400851034103c0c0d0000c486000840c00383c0d800d128880185100e00360300c1c3c246080540b082c3c001010143d0100040c0f85a49000340010740301d000c0c8000d40182204900c680314080c034801070f41c03440601c403008481840b88450026901c2e034000603480105029a80801c180e0341c0f29000e1043c542103a000260200f0810004101c03c03903190011845100c071802c442d50b14503c040300d13000b824520015800e031030101403600d0610a20040000200440c6030720b00982e08a6010395401e202c00c4035070740c8440e82078950714a52403400e00900208440f03081400030301400009450741018071041c1c02072904507026070841449400c080707005104559032994010166404d95071140100000d284814079020503009c0002040400034108101115079070346400050b241c251304000840314041c005112 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 307514100 1250 307512850 307512893
    0x30a020405090a09050c060903100e0d0f09080c010c0213020a05090906030109020a030201032403050a0317010f0e13050a050703110a050d0b15060c01050601121a0405071209050109 79
    0x32240082c800040506d03200c9401da54094460040700006810400145a0742058504040088034808030208483e540c9400c00d482d21146c0c640300c0c4c541100c2100c0540564901c2e0f501c000140820f960060140e001064401400030301012400400340084e6045014002c003c18004a80c803c2c0034640164030a43c4008164020400c608084e000078500c0c080a21010f4185540c0c0d9094100b0000d510180715040c072084c205603103106680f03250044c5d407070203044d4007034000800c0800540300e40c80da05000c840c100d03a0700e40160038030241084148140a0000703803a43d50b0705000f42d243d04000030014000401080c2c02035020b465081d00d5400d01a40c00742760511914403a480755501400103a13109102200b500c3d0b00700e115200b29643d07a864000b2aa00f120140075404800810300d5131100205410035031040f582a07807070090b5400028459010388201e400110315140b0980c40d04c080da801c290340300c56484007191500c4854440800d004c401198032030b01007500c07603035101c0060400344101901c01d1080c1055070f00307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 307515350 1250 307514100 307514111
    0x3010f090209030319030b031f06060f050403030509031c031d010522052b0f02030304080d180c0b071110020a03110708060a0c030b030f06070302070f0602030a020405090a 75
    0x100004d460303218001400c9090398825080c04400d510940c0060040031020301220014201c08889a00140060006101031401e01c440418501e202e41207a03d00c1140d143c54a504050031541d090b42c65400c0010596018070460002118143d07a00084101d111440d480001340c40342c1422600c1c10b0f2201c0a62030808c543c5c14070b0180131008503103a110300c1201c0d2a98811380d0404040780b51881c244250180e00c60302d0884150b40300c2c0c3c9403440e85242102c2c9003031107445490031070600c1401680c99010440703010345546003e000014003d121500a00b00c0c440c9142c44840840c00d60781d8622075260f205802a0003200004500342041040c11291420b402c5000c40e0080e0040441020080da60b40400e400202001078140700c48540b040c0410000340501441c0042e120a072400d49101c0004083c004205000242000c900030400d050114580d102e01780c003c8050450b0b0303515014254045c1d4850001264003010854074800400c4079840611700400c0c1c03c008c0940c1da1460101040303443c00e00584080001d0389400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 307516600 1250 307515350 307515367
    0x2070b0126011a04020d02040f0605030709080d0206070f121d0d0306030b04060207020105040320010912020901230a090b04060b130e04021309111207080606040207060e1203010f0902 80
    0x1e103114450f02c28221009a6100003580281000e8051a400044640d588105c045040c0360440081c6102e00f02a559402d4032a903a0032440d652140091110000341c2c0003e800301d01c00743e1080c917404546940da030030110080d070a03c40034002195010302030b00c003001444032000d90300b00805100140110710a483d0502500c0d013151500d44684401030030040803941c0c00600f840443e4044c0702990011030304008140a01c242d04001400b0001441102c1350001d1150840031443d068814111851160060304907a116030030844d004140d1540189001c0c01c8120780c4258a5140d501d1380c2800004d4004000007003001e0b680e420500c001e650058019583d900c03010f202c0d852180200110340c0c012035400461400340707074940e0f00100e08605032070081810000d042601c00d04c240100440080c02c4407030144d80801241350001480760b10303003005000f918540d400c8040420540d281940143c03020328002e00f400500b58044a030340504d045603246032f4000c00b81d804401007142c4841002504010241c00e0815032420209 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 307517850 1250 307516600 307516631
    0xc07061805073f06060806010e0103260d0c1103041212020a030f0c0305090d0602030906222003010e0f010e01060b0a030513021c050c0a051008040602070b012601 71
    0x5000031581a40f410a541d41c09021940d04824020125001a25050358440404c1031401a09000549180d106400b0046100c10a41c24003131400320006481420003101140b803030040c140580010080010344543c0c03101c00c03001400103100405c41c140d0303034510380310203498000354140440c020034003507402400d240d202094100c40342168006c807500c0e060b90041d0584c902501d03503001d031120789a00300751485208e00821200d54004c5015013202c1c0121902c541d01c4186812080d00d51070301034001000049499400a1030704804c1c020a44450220325000c83c43c0000468216043c0e02c90311102c1ba84140c00412030301c0b40a225440440012000130302403182082050103180c0301d0b088240c0d080503aa000013034401c619000500101c140e0040c04d071005c6080b612244020f524042c20207a5660080c0030010104d460302c0f104100c100c0d41c0c058880e0600802004058441c00c3c1c2c018400d86085800704007040c0028090a8118040c000001102603c0c9040c0c0d416800a80b50340c0d50002c5040e0b141040d070300001d048 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 307519100 1250 307517850 307517939
    0x306011505030912031e151309170f1b030304020d11010302070204111c090f0201080c16030305070e01030203151201091e061407080c0706180507 64
    0x9441c00c02030359903280d90400910700758000100f9204880003006000c2d40c85800d0308407020b0f690011003582c025441d42400c1d212000b1a40741a15845071100c4044018441c65801000031903000e0302c0c22109101282040901613805184030100d1004002205112103035200800040710700344000960561402e5030100e0108010000c0c003600211001d060014260b209804880d0260f078081c001340715190f0310ba603143e40c10740c000304502d50000002909103501240c10307100c0c001d10990019840744882da000e800641d50a0000b501c14410000700b000003800d000c400c0c0444400d2140300b550300088a181800e80148107a4500070407504160040050001400044000c10b5000741d00701c031011400000c840e2040d004001040000f40050403068100a0000f40025805052409900288002c9800035002c01613104101d803400007040a01011900d608084005842000e1003030400040340140d590000c0700d0411908411501c69104110501c0f141e00710040340c0c0c040c1c0450503044411103140c56081240c0d040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 307520350 1250 307519100 307519139
    0xd09030308060f15130614090307090c1403010e01180509060a2c03040801050c0a090b0a05040909050c012703020d1a0c190203070305041e08010f0b030c030601 70
    0x1400c044100e1a542e0340043c240344c02600c50b4115503548a0310701c00840d419007511a807804601a031400f010f03c005094100ca4080400602500e0802d06080380c1100402a154041040124100c82080d545110320000c5000e48811643c60150351714128107145003541070380481142c1410541401010030300020516004000300c100400c0e503000070380306e5802442e5001a2014110800c600d0001c000c13401000602c25038000c14000d20241ea910b03e2080707050f1144600c0300000401c094803c10140020402401e840b00d00703450075900d09659650900c0648100079002d850b96004000002881e603004061444c0e02c020b0340b44188510b50a104580361050064170000e401080700313000c800200400c00042c0d001ca402c00314a1141c2c1d41c10440180341e9650040c8040d214130130f6410004c86074080c000400c1d00c1a180d0300d0307581c1d0752034181800341c450410843c1110346202c44420010100f100e0200703016241039108402800144070818508141c80c0c00d401c0d400160094018200500c0281e0380f0300224000c1d603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 307521600 1250 307520350 307520359
    0xe04152018010e1309020f090601050703051b0109060c030b0a140f03010b04020301030308090f06011a071a0a0c09050406140913140a0b07050c0c3f0d0903030806 71
    0x81030038401070b20b200c54180f030700c00c0c0c1c00307550705001c4c60300e0b0f1342c41d42e0180180c0c074006d80340405c0c00011a002c1c0082d035035060701c0190206900b4020703440000d01c500006c0884501104d6907800e4610402881030a540c3c2100003100d40b123403101d20825106030304d44181407504074119034a00c42140340041e0081602c00d10140f0038001c1c0c0000000314410b4509401c02c0382e0720705014204540d25a964100105204819542001d00340603a61070000d02c130000041143c103a51131100d40302c1203600c3c07981613007905074050002104c0307104460f0840300e841c02582e11800e214007000701010401403284440107004a0071a00094400c3d450001c09111490590248140c001d0055a1621031519580540b19021000700c40040801c2440403424015440c013095012580340700d03640b0f050380ca469050043d54070b801400d01d041d40640c03003020210014500010f80590035030030080c00141c20500050031440c0310108070b11400859007080d20650744107000b0804400241038520b003030000b0f54210741d00100070745000742c4054400d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 307522850 1250 307521600 307521637
    0x30a08130213050a0605061c0b011409041a030312010501080105010c150906021c09021005030f0628080f0708070501050304060f020904050703050f0108190b0a02040e041520 76
    0xd84903036110781e0186c04010030b8140c542420001880c06040c9031300200104600b44100d0b41c07107650240c220010004c0407003154904000d911b00c2480014070044001a0700c4203102c01141e596606c060000380741c0b900c400c542d90019581080005001250180e0000b41000070490003000400c4054041550410756210302141303c41d201d06002005c0d010714501d0340b01c02074005010604e038000c6e83c0e22214030f251080d0b410880b441c45c04501034a007800100d5442190504460010b00310f0318206c8040b480e10103c480301142c1e04072507215054245010307504564002c0d0701c405400c0c81000d07401c0015a00816445000b8038041d803c1030002440c0d40000f6100800306c03600c0d030501c88100400e41d01038070741d54400900208941e01d0201ca008006d00804d640700c0090141d41d030004140c0c2240400c03a9004c0c000b141d1a40d0782c10076002c0d80c60400c0c0a070000d08091103542c1c00d220104c4e1018292400f0750099004141101c1504144a10001110400c0302004203e41e0201d602a0407001c6440940d0742c50107140b04140b41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 307524100 1250 307522850 307522861
    0x120309030708090f21060a051006030b0312030907050a1e0b0d020f130303080f0c0f1305090c07020a06030c020c1002210d0f0212040b0912030702030a0813021305 71
    0x9070110f00184c0b9507100c00144c5c1d10700721410701c81d01c4031008a500c1008640c1c240d118005050102d0b6419190100500349020040c0b080324043d8001f8488000c0140c1200e000100501d10204142c0007500c0c43c1c0d07015000540f00f04824508503000c10041c020b8644644400c40c2c1180e0145a56160382c410a03440000114014407004029419150441c440c1c40781e096880181d050041c455601c240022070204803140080381c1040600880f1602c14000b603c002d520780782540c0003800707454002c542542ca01012094000c640b40d140c07000d0540c00b50085045954444080c1d1041142450b500c1e0006005c0500d0411072600349603000807400a204000d130b460030901c00d10088102c1c205140f20180306807a200900008003959032950050113900781c40101000030b82c21101c1c08505038410803161414070035101c0c3c0400e001c509007000c0f40ea00000b0950442d25503400054140103d0303041124004056000441c580200d50f81202003140d001881544202c07040d119a400240c01910342000c00c00e490b43d40310300140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 307525350 1250 307524100 307524109
    0x60305060612040507092d0b0427030f0f020d0507060f021306020714030709020306031606020a120806010813060b03071e0f031a0c04030f06090512030903070809 71
    0x1101c100e546204100146040c3c141251750706242d11a0303445651400d540a00303040c203501c1007032031548030b100e401d560348200c5011000c01614903070000320b0b4800e55811414862880358000100e101d100300410401d280007500b00134000d01c031201840424805100796020b2081d501103561300d9421007a081581d158025400c282d80186100c44c08010202c1c0b0000b01d81c0c50301050418a0422100705608a410050f00c40307a0340301d52100310320a01d5405600c00b800030702c521549900a107501c04005821034850300110aa42c1a0418a50384500d000d40c000590b56400c9c040d914800d0145242c880c01d25140da07090a0000071302c0c01c9801000c00701c0701c003000c2441604001c0c440d04a24078820004007203802594456502e0f040410301081d05d40c9a0b040316940009040c0c2c0305500b6101180d030031810203035031100c110407114805500100411034441081101000048850340300090b040d01841c0c1c0001e1030072051804503d4860f8482e6200c140388400d00c10010f200030300104660f8034640c8144011385038500c520205 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 307526600 1250 307525350 307525357
    0x30819020a0815012a080903070e01031b050603010b07060906060b0d0509010c0c140a02040f0605180c0a0f03140a0219030b0d030e010224060f030303100603050606 72
    0x1601a80002410010320354080552801403425007070040205504000548030140e5460042e1191050204a18502c0c820060361084a41c014000c10f841c1800c0000000d0400b10580c00c9075412080b800d005105000c0002980980750f40c98590510043d820b060002d1440d00051040c0c10308100c001456a04004140e00f010505550207041844910b4403105486140e401541000c021b0070f00c0c010010342900c1d4140940c07988010251a0107404410b09d883d0145011894a42c03441c0318440d0000010050b101d070710601e00c0d100c0e070702400003422a083c50200440344083c895108038100c204018404268000782c01c40d1054083c81c181343e20360724101c040c01d5000e01901840b00240030759010801005600c036400070000c0102e8070032010904400820198226003c400301306d5007200903031841100003401203152504044050045424528800340d030340c600c1d600110172100f05034028100b131042a00303010074005121303031044028500f18505540200490001440b42c202059150400b10300306450345403c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 307527850 1250 307526600 307526641
    0x2131109030f030309010b0405041a060a03051209040c050316030b0312030108060402040e0d0905221b0207050102010908070209100e0903090312040302060a12021c0b0316030f0308 79
    0x3500e07102c40d0840c0300039440b60011102100b0b29420b04607031010300c2c60184507043c0309a47c0420301d140c4600e2104071a07030888000601f80743c0c1010a15030048003240c0c1c1080482100f07030441c4415603581c9805c03800e2206640b40250450b041c00320031f006010b01c02001c40323000c05520a9600d0001500c4d0011030010b440e20810000b42080c0100c000000b0076000004202d0904c0780c0c0c0240c0b024845991654000c0360b071004200801000168050000d02861800c20403401c07001021151000da4103070300202080032100108510400000c0c4040103045081e01882802c006200900003040b1742131441d22581c0b00c620032124000d1165544000040541d920140010040c2800403600304117460100d4100c1d941e60f100c091104e12a200f0005c402c0c0c2444400307001c690650b5400b90403181400c908820641d190107204c8000c906186e0248400140701943c5d50060901008014010404480160505090440180700f01c5da445881007014001310b070000201241540d41440d00401598540c201c40d032a91058060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 307529100 1250 307527850 307527853
    0x15030b040b040f0b04060503071505090310050910050f070507080c01020c03031e091b0906010c21080108031603120204050a12050f06040339030f080a090213110903 72
    0x101c40340c0f64400740e00c18010b4140c2a40e042150949400c03c160b40d600040c0301d11000428010400205c02d803180010706000c10b0050229500342000c2c529100541d501207619029039030041000c0d422040950051941040d030140000c011400c1803030000300f1900c50441e000d0700401c40050401d00408003503045824580001050380d0300c030b0408e00400b00c1020041074002541c0b006030380221b8007414000c03451941c0312400840c0701500c2c0c0c8101c414481101c00c020012418481150110380124003c0c1c071801c411030000c481c520480460f00e4401400a55044e04820650307481480709001412111003a18111901803d03c1c1d40001d800d150503002034480e80e00902d41125501400040d8034102e010003c11483c81102659000204001004d90343c1204440140010b4415030030017030141207880e0301c652040e070901c8d0240150f542c9000d01908581e03100000310005020723030b840c060340d40342e10011480e0024140103060040d0700e0560009006c5480078079055514542c0c809400201010090884d05d28080150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 307530350 1250 307529100 307529111
    0x7211e0c1b06020d08010b0a08041104110a0207060908102a02160503150105151b0609070b0f070b060a18060e070504050a180e070f03110a15030b040b04 67
    0x581d441e01000c25108900262140c00030b403000c403e0186080038140c4080716502ca0130030151000c1210380244c060415038510f41203203803080d51501e40f0701581400005480a86641d0711204034000d240071440c0e03100f01c04000c403038282400000d01c0404d410500f000100c0010410300c00c004950f0006008803043d40000a0784003141040070303600442c080e096460901c1c42010515074903030a1640b01c11480c13140c00c01861198005002c18544160740007408820b2b00e03046401d2640c504030701c5410200c91b002a1480d60300c03180400901c80820801d250240c00e411b103400d41440c0f2032600c0710620f0f0041171001030501e0134000000d040340e21200e02078401040116401c55140c1d500728100c070028a028011613010040b0400000c00ca240200d01f1201150b4000c3c050340e240c14076195030340c8520108031000f049440d8a8061a40000000304075600181030032082c0b520a03e407443c906800036514801411b03020300c0d0088000c00400c20625a0321108015600340030415140b0030000030002c0c459070103090340c02481c09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 307531600 1250 307530350 307530383
    0x206191b0221091c050c0a0f030203010606050a02100e2409011407091406090603041b051c0204051015021501171c030b03010f0207211e0c 61
    0x100b940600754070804500444004001c40d40c218481c08030b44680060b80000300400c561118648040d1035405101621520300121002400401c829403004800040f04070091003585028440e0b00000c0440c1d0610f945040b10061010f03448250841c1c01c641e000e59692045200780809000341164020104103601864201c09001c40412030251491078032036113400b201e00304c58800315140c0ba002d43da0360380380d1144092505e038400040090b02c52000c6e8120009016004640d101c1c400078600881c400c40302107010303000d032040c0303400744407425444107201d082110703029006000c4d074115100c20b141d0140c0c0d021070907940303000880f0100c0c0215400540e03485258401412540e5000c9a2099105d8440c6440c0a6503644c900180b80c0300d001c0d499a0704240d030440c0114042d1407100000022426040703043c04141c010050740000e0844d4206a0b90b1312400e5000640030041144e180046100824804100304100d002d6a0300148070140700c40d01020007d00c100409040070b40110380003c01c0c150722200015840848 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 307532850 1250 307531600 307531603
    0x1b0503030f0304120c05060612031b150906010f1403030715020c2e0209011b0c0f0501050c121b010203043e10030608010c020703020f0d02010206191b02 67
    0xc403404d81d0600f02512400324020320440c1e08010aa40117001840d031074a4100801c00c0342c00c03003d80c0d1038807944420005004900d0106007c0581e600750140a040c4018030141c040a28000c001d0460042d6040305005001c03d65815180d03100352561400d039450041c4c00c01002c6807451080340400b800f0076031802c9850350a240307207400074a80481c54a094420820f8101a54242400c2141c03c49041c00c1c40400c109801507040d9001d03141100c0c7c1454810400c3c29001183c4501104c0781c0800c1c2d03403603103000c40181314070390751561102d000b0102840c0141c581030b410000302c7d40b40e491925014210990000e0068003110351640034404108850f00215545d060914010864200402903030a1b109100100219400d420802e402240d800b44150b8810510000c0d080001d80c1c0c030003555100a01d42d440c0c00120b003d240920904d24240c6031a002446043d0850042200c3d4625480d0003d00c11100c0b0b4448500503640840c810360004960750710741540c00e0103024220040c2001043c984001410240b41801007a0b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 307534100 1250 307532850 307532857
    0x110f031003020a090b1c0c0510030c03060b040303021905011d0610060e0117061503190b060408071a07020d030c14031e030703140c04030303061e031b0503030f 70
    0xb08450304100d140c0d43e01c111001381c861083d14564070003580b0342c600d03000314880703d60362281a125207040e80719244c0720b20004911040c4d01002c800020356803030700c10500c130750580300d0b21014014019080703040518580e0025600e00400d03c03140c4041e01000000010084250010000203a42d000341c850f90004800d561540c0d10021241006000442507000440324040d05074240d04200603511050012009005921624409040107801a80850112003240d22407030141d8050814a15a20a40c01d0f48404060542d200e000210780700e4902080308110001e40084d811044846980301c000202c1034150011507140141d040103900074180410f40420580c0c88486154440c1c0b040702c9040420808000d030f95500d01605940d0390b0702007070300f10050030340400d48000b841d07200b13002d8500410b60401015041c8696134060341e9425024038081024000c05425008040140c0070054640c5001d60f003d00b44903072006084c0c80054510040e00318880d000042684249000d42000f03001c890740d503100740c080310104d1360 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 307535350 1250 307534100 307534103
    0xe0301060b0d0605190b0c100f020304060e0d050d0b030309030304060908070611100504020d020a23031203070c1a04050304061b0f14010e07080d0f02060108060a110f031003 76
    0x180f9081000ca41c5103080f400c221808024181c445035030605002d1048250390161941c03080c58803030400451000c048900507030041c28080c1401517100c1c01d05240c00d2041c0e44034001c10009503007088030380d5426160700c10705840c090340c80a0710118905064001103425480744d01d92003501400f0000b03011034044d4025004d80c080f00e40c0301045a03015556010700300c5645808840110603a04403500011b0051a2034102036040360005020403600d850700e80c00030b00c1c0080e403540010b504503480c0810100341500c0030008054032406a000e004e0714068240d02400038800142003006000c44594404207022510400400c0003c1040d03018110b820941441562904a0b01c282c40004500c1c52001142406010816000503800743e40f01141d0341140d0b070380402c09a0300520300d009541d49c0b60f0111907800410090307c0014288030014015035001c20000501000c203061010f4203540c844801049003100004005a001c1401c14001800c1085000d00129a11561551009410000c01844000d4101080303610489 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 307536600 1250 307535350 307535377
    0xb04030506040b0601050c07030204150b0c060709080a0302100905030f03040606090f110a21110903100b09011502030f0309010c0936020408010504030c05060907030807030f0e0301060b 81
    0x10f44e81c1e000110b441d40304078040f0742815001054100010b081a800248204142182440069850b81070b9030160b90003917039600302241e0040003171101080d00101c00c040545150b03c003500c50040340e03440180d99181d0a1a1201c80f081c1d98a4185041c05024006d0b65445100782c00340564034100341c01c0100140086018041280303183ca80c0e0901c200c211849241c800d900081e01013410803c6c1508142c4101d01d8000041484500c3c09441d00c401e01d05130720070452480300c0f403e50f1540390a01381060525050001c0000a03040d8542814401a5a03490720480d04641c4540201c0200c603030030752030407400d5005007086105040808000c7c03001c01a419002500c0759101a910039030000d903520b552030329054200504040010510a00d1241078600948034460100316190141c585903070b4150703603421170f002124141d00148407441a081080b0003070110075003107a107100c01070204a00b1600d5101441c850044001e0600c00c203001c0544840e070161a130407400240080c020420345036190101b4116900c100303074000c1e00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 307537850 1250 307536600 307536623
    0x7140303070f0c0c03030503060d02102703020a0b0315030607082a041206060f08010504170c060c071b030c180e0d050c0a2405060409050c10090b0403050604 69
    0x3020300c40d01c0f240300c5040d0030500601c0041d14544081c1c640364400f41071035410162111011016880e1500110411003155448203e400c1000602032440800c5000c0040240960403040016035241e0221505844240c40706965940320038003003000340c2c800e441d11540c25000380307002c00c070045400c580740c6882542c0b8651640303043c002c00e24030300c030028245d000c01a9003500c0074402442007a042203c910215071246c03000094494403941024aa82c040e0f40c001c0740d017a9100c80402081189122060440c400260702c000c0c21704841c9800380d0f403a0480202110000c1d40007048000511400600001003400b0b4107083c0301c0700b9034603070078a142c6c3c5018502407500051040401c890343c2d06854030070280c50801e82000742a1000f200300c0b04030303281c0d40300800006862061007500008107100b002800f4140c0c00041505648010b40c090150541e40000c258030303c25850300342410b011a00114a000e00204116904040110122020b866003000380d0031603101d03860302040c040200701001030b116002d1800754400846 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 307539100 1250 307537850 307537877
    0x4032a0801021306110f010204032001021501060e040f0203040f11060a09050d0f05191109130605181b0405150a060c05030f160b060102010b061c020714030307 70
    0x280c0c0319003107450900c0080071404100c65803044c2e00f080c441483d1750040da95001c00c540d45007826a081a0004d681d42200f445044400701214401a01448000c2c005071107020300306040503891040500c500030600265981c03641c595030310740e4045920360300350035801c540300c1c20107003406800400581003c84480e0503814a070689032a10f4400d42c4d4100c00f03142e0703408280a0400040c40140e41c0c46000480d5441000d611540014501f0b0002d455008144c071022181b103400e40c10030b01d02d81a103170025180102140c1040c0506956050b2444201c2034000c2c8001c00d16450701900c1c001101601c40401045001e800e03c05e080010f00c0307800f41e07135036548216001d21898a40701040b40307905142d655a146e1113200b900d02041340900a1002c03c000b14015019603040a030240701010155116800700304050328044811410440f91030400d58110100b0310080020f0b02030000400c0151048201070150440e1407008120561200d8040f19a5194040301039a0014105109250b49800070b45050340070070120f40c84c008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 307540350 1250 307539100 307539103
    0xf0311150108120708090a27021201060c0201020a05010c030606080603030307050901200a0b04052103010b0d020d0603032d0206040b0a0b0d12020d0e0609011404032a08 74
    0x41c1600d0072000981012000c40c2d122450b503030f00580782256030500510a0345000d40e501d8281e00c0081445003864080c020048001d50711070058401401c11451061254400a40180c0c1030941516440c0c01c100300800c40301c2c001070303140c031403205d4006045608003014691010380c1a0085800c5407010b49070100c040d20344400701501c0780803c9039501c00040090150501a40c820304112050404a401402c00302541d101e0781414580e030340c3c9040c1c858603406824417007000002c210030700281008584201840e4650410101988010300c00e01d00d011002007090480d0a0443c1d04a5a40703136640e8904110a6559281c0684081580703a03245204038201441421510074000020b1000a515800b80040303989560f035882d52400d02a001580c0c0302d43e42da00000c42600c403c5620265517020300400c561448000340020f1a140b9039804020400441248040490b241c250940c0c501d100242001c00b0740c0d0b0a50503034011140501d52014020800181c0c0050700c840017400482004510041002541031b250706c9040d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 307541600 1250 307540350 307540393
    0x60b0a0f0308090603100824060904020102060c09011206090515010c0b010603051e04050c030706030e060420100320070b040f02041b1d032103070207030f0311 70
    0x741110a04102d43c3c400d52030710301e006540c41108000c2c007481c290384a008403441c020300d0000745c041041d4402020f01c3d0428107020f2040c1d0201088584021a01d0075900003501d9403c00782080384078980205559203180c2c042c1c44001a82e00c4101c40800c6465507600013600545000d60707415040f0406072800381070039446841e0407004190850704a5091341d00e0108214020400140800001c108880803081c800000600369801107020300e0007480c44216000416082c04640d42c8004103240ca02110035101800c040f4016602c160012064010322500c0085401081d42410131990301c0700520a48140c01d41e01a0b008027940310784001049a800400301c0010924803e141018001136803c400090000c0d00c6d445c07410306041d1000d00003050024000bc081d80310414207a070f5520104842403428400034030500e0010740005022402058200240c40495011054181100400d007000100044002d402001920000c49d8008100681c084450400a00c1c4010303031441e40e40c2c540145500c1d10703401d5500140300b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 307542850 1250 307541600 307541603
    0xc16050901060503040308131b03080a031b090608090c030a050715020309090a0e0f0303010623040b27031c02060601141801020a0204060b0a02190804032d060b0a0f03 73
    0x20100588c0b11130402d00703407100b00e0000444594141c2d0040d0a002124003101c10019403061303100586550450a020f002d0754a124a02500041c00aa021446541c00710440080310f5442c1041c402603101c12501c0c40c01c20300c40400e8160103100c0c0c800040f0400c5000a20341089400385507841191859440040382c6910844e510b1551000c00070f07010030021152035218081206039070088414024003542401c0c1103401c2648590085500c400f1071103031600d400200f03244c1c0024174501c2030b46405d0a00042c54020b0203181c09030f8036010f0042d03002440c00f01003181c035610840b02c01412181c488048180b850846000c04080c00c0c0180541d401103020f0b03500810f01e540440020300c05031803c140c003c1d1301c920072100c40c522131241180704007a08007025032601e104250141c400e5502c21699140700c2ca50191810110340000c584406501403142c020401c004d09032010340c0da0059801011100c81c1001890b09044105440c10f804000c404201c01c01c56903621003c401e8500791303140825285d03150310100300030140341310 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 307544100 1250 307542850 307542857
    0xe04050d09031a07170106050409061706181906050604060806060901090f1104090207030219150b210c090135030705070b070506060f1003110c160509010605030403 72
    0x100c0a242d00d8031443c055034810381601c1c014600c0840380300010b00d801d4080e4005008103800003020300c00c11049015100c0600322013890032081c8441c1c000201d0343d409000b40000c103c89502c4483d0004543c2c24000043e18918050342c0da1020342403803e10701c00810040c3c4595100310315066000030301f18400308019128600090107202140e20380361003003000e8000b030342c45010000d9481031041c41403210070000e40042d0850f440c0058946800303113000b900c0c0c80322384e9034154450126814004001440084071b81c5c00702510103004102d80d042c43c1d000c40c144410641e03405081d20810b2360091003c17240023303659400442103400010b81c0c3d80c2c418000d155070080c6005911542c0035030944c221030703099080401305043c0c1044100c0b0b240038400e0722100e00303001c0e0700d0300030032a041d100241040501c031040000c560010b5044400521000001c00082c2c840c0c240710300c5040925072100b0080d1034401c2d148080d9840c030910503042d14113020303403540740b004010380d80d0240c24410030f80c100012030180c0c400e0003940d118503070584 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 307545350 1250 307544100 307544123
    0x3121b050613050c04060803030f0705040b0708160f200a0506070b180a030207080c06210603210408060a0c02151b0d1b0f0909020d0212010e04050d0903 67
    0x320309032019902c4007042d80c0f1481841003152140d200c510030380e0000c0c43c6400c0950b499081c155803081000201810030010010103020a01c0519441c8046400c06580f0490040c0e44203018400e641e0100401c9a02404c401c402082ca0800e124801b0032500c00b0074543c2405851501a050411071312b50300d01d0040300d80049060008000082c1e564043c160403905d508094901c0b001190491494100c0d001e604400507080182c041002e40c030b00b00401020090100d0707000b802c0a10001034010141d86248404501c0649030000c41c406882c2400ba64806149111444c0c0300c2c15810603054849907c01c5c4140794551040720006aa8650144200c980d00110fa82c00340a40740704d208144400040050820100842031805c440b805428030401060810f0b031094010841501590003403c0c02c21585141c001800303183c0d00c62100d0325602445600540740780311001a203c2c02071002c0790300240514129006a44540c4001166031281e007661107200d2413190045680100c4d0140c0200e8100a19200c0241201700301c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 307546600 1250 307545350 307545361
    0xc06280309030f11190516060c0b0a05040203030703052107050c07080307020a0b030601090b0c0607030b01110d21020c01020c280803151008060906010c0812071803121b0506 76
    0x220242845c403401a4202c504411048050002c1c1a896901c418089400d0400320703010818054801e030b51002c40004c0800141c98143c01107901ca12030078400070304015000130022983d01450250b500c03901c00410350002c5074501200040c280b81d0145c1c01c041640d103c3c0c9440010100d1001007190002a809803440f5099817406560354070a82000d00b006043c00400d007008205118800050584400f5110060000f070500c0c10029044904990000e41040340d01c00318654540b8001034440c0030000186030048034182c00d241c40d01d0902c000031449904403400080d0b81300c0c1c0304505401401300d11f204401a1915861031000c00340007640d590440d40c080104009000002c664000051607104800c0b0098122145d040c800081d5802c0c900421381d4003049080007405440d0803d0100f841d88017400b030a110741c92a1440c0c507408100e000340280d011407010b8500c006012b407881007a050304c406401101d11840b031926481c0440c0f4502c6030701115800102d1a482c040300c14007254000d08800d68103c405400c181c1c8a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 307547850 1250 307546600 307546633
    0xf06011512020906120c09040b0f090f040c080307081c05041e0c05090f0423100908070b0f09010c020102040605030a05042402090102060a05090c06280309030f11 71
    0x84480f540d401441484001403802c001c91515100d0011100115a00c812450401084560120780d03140a04840da8402300305854207541a0380100110781c61000aa0f1546000c01400312550408401ca010214074a003c11022001030304d8182c00f007551503031910340602c070751001702c0314200c401400510f45110388500c440d0200844a50280c0a4500b1904141d100c0c00410361080c3d06907401c170038146003201007100703010400c0324902e8801211000d00f2184120001c500d5615080c0d01107250455644195502c00c2044240c120f40020751320a0f6030070124600842140d0000c0c80c101c4030300c2d040e0350801c41100344051040c0b0803501910f401d0307181c4a055440e03100c8110000c18000303108480c15025040d28080078079051002c032602558010000d6610841100024103000300076000c40c000d43c2c104010308c142a600401d0160b08002e0544210740c81d0b00c0789070407048840b035140c512003010160780702c1480040c55040d000030080074000c2c0c42c3c0800b000310720042260310700308484a00a498005240c01d0340c402e101d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 307549100 1250 307547850 307547857
    0x8070b0d0615272102030d0e0603180c0418050d050c07150224070f080108061816030c14060a170604020906210f040b01060e0117090f0601151202 64
    0x2440d5500c0800e15494002030740f101d2444040341020100c109403a04c0440c0341c1040441c2078182140f901544c00184100480d40c03601010780403181c0d00031614560403c85004000c03002084500920034088622200d806e454031111101707080d42c081c042d084940306042d000e0f000300e07040030103060020110140f0b00010748500c0f400d072079140340c1180100c5a09404011507000c417a0b08180350102c1c50107141c100b290004c1d08885040e41000c062184000041020100214116621900d01104582c01848001499003000d41103288005040845113003c814410030540000940d0700c0306450011151109041080c9401040038041c000b40c1340c00c009081a103441d0f411141c10400140003d410300000900283e80c6801240011484090140c0d8500c6402c101c903880300d802c803043c460741c040c0e1401e1680320a940410140245814031000d1010700013680d210b241d10546940483c80d40e0540f03820320400c6a500c841c042840c1c80c2c0c4600c81c010001c1190014004500011441619075034021782a44010030003940 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 307550350 1250 307549100 307549157
    0x20702120718050a0b10030606031a0604090504080403140c0f151b0c22060605040f031b090204080c031b01020c28060807030e16060507020a08070b0d0615 68
    0x60304d502c0151017035140c440e401d48100089071030129200307040210090841d21a548000c0110425a0440074144c943d0003c4900b0f0f910440c401040d140c0d1503007000c8802c2d105d2984018906407070300c0700d0a0450780c008100c800d50b81001700c8910142100090070000c050240b408403a940d80780c1040050244003280a0038220030b5110415943c0e80024a0f0001e1000d5410300400700703085c020b241184007100114814000030745250304046050a0902c07005d10b613220b03428000240803041408400e4803020002071400003c03c4080c0080d581c0b9a2204095a140c02c0f2104086d03020b0b02c2400d507070740801100080900304078801a80141001101c034002c1110105d90f0008450168240c07901c02001d41d84102008806001141c0700c1e0b40b041c1c105080c0040844510b2641c3e80c1286d040100b03140c0300854107602d600d08841c440d00e130098942e10309000048040c03002d039100c0c00e0b0300c1c0700341c1e80002682c0701d00e000580319290821a041007142c0da0341c1c03a0180303183e981e05103450014182080c82010030942c0d158041404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 307551600 1250 307550350 307550371
    0xd030c050a21090602030712060803070528060911010f110606011b0b010e04020907020106060f081806101706040203060a0221190f0216060c050f0d02070212071805 72
    0x1150345407118005c81e80705486400000f60152030700e0110303095500902c0000c1c00c0c0c5100852a02516856080d240c1c0302d01103400c80300707000c508e0100f905070b0001080b080e4566001718013040031603000d240101c1a6a404014a80403582c601c00c1079100d54010600f15082e488044082c1007507035150801140ca201d01d10b08400d80c0c01c1343d0f8102c02004240c026041c14042c01d003038001002a41800d0040000300f0a00400385000c681c100070091027204c0c0e02402e0301c41d1024240c1440070280e103850000d42c401504140364610320344070315810040d60400070b10441b003c481d204108a4104440074000f291140c1080314040e405900408c00328490160550050102e0100c84e4492000c0031810911907588490590b0010b400d1017203010b0002940c05180301d8158106401c41045282c00304054111200d003160041c09025503544403030840402e802030080300e90064859490303a03a03500d4164082c2c402508a008240c0c050300082c404c0000304000065500d069580101c520907040b4000e4000c080076200051052440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 307552850 1250 307551600 307551611
    0x3140310140409231504080901030504020a080a0c090e0a050303060f0f0607030504090f1b0f02070b04060306081608030409050c07171c0506060702041a120d030c050a21 74
    0x480e04419a2244080180000c9160100b13a0340045182482c01c210751070030905084140310015407410115401c1300000c3c20013048958a500000380e42481c070b513000207403a0258211000800110380f0840c0165407e074030040041d1642054113650f41d561081c0004e0165000700302003800f62410034403214007644020030510100040c4408103109400410048001c00e4011405204016042c052a0580b001c03043c0200a04c095007400000c2c001c03041c00410b0f080c0000b00d0b0b414030720544240a0500500080455995030365910b000c010004d01082c0300700080c90043c4c401505403031007030309412400c039228840110b0402d030400400100814014080c001400b40403c0b0003070000f078514060103c40709a14903590f8031005001e02142880e2032201031141464a030801301719882c0c1c2c039401071380e51460b01907800042103102035100c0010050480e028951005070b115281b10040000908000b0f100c07d507a03024000c00c00c661000382c076503009003200540890034110111400d60b40c0f46040611310308018001060 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 307553956 1106 307552850 307552853
    0xf031e040809090a1407020717010204081f091e1406070f0f020a0204052e0b040306021804050708010f05060c0c0409140709060303140310140409 64
    0x2180a00c000440c2854a6a030b0045e0f40b002c0e00c00c018a0032900304010f000e50359400702c1c410040b031984800c500104501301030080c0d40c211402d2900510b42c0301241040303038007801e140c5500360607641d0382c0e0510303540420060810b2080086041e0f0459102c3c1c086402c00401c16100c41c0c40b0b10906a000300140044070b680840080da06200b42e1070300740d00d544c000c09801c074101080300c18041e40c440c4c240004d0151000c005800300d01c6040d8441d402c4501502601400c407405d80c01ca22030f410000c04d052000f0000304032680c0040103059541a20f11035901079840002d421280180d0305200080c0142d8018081108040c5265002e020704891490822841800c016995031f4031001e568010b540b40c0c0d80f0340017001100c0b4003119034181c0c0c2c4c0342074401c02c544a00a80c001440c1c24481a000243e05c50400184881e4405c04c5070b001d211100c0888400b98188080110142072111040b40c100d41e030340d00d8210 = true := by decide +kernel

theorem cover : BRFrame.Cov 307374100 307553956 := by
  have h0 := BRFrame.cov_init 307374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 307374100 ≤ n) (h2 : n < 307553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
