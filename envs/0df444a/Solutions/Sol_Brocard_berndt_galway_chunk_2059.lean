-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2059
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:34:05.962991+00:00
-- url     : https://prove2.me/submissions/89ebecf1-9a03-47aa-9af7-bd25ebc43055

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 370143884 ≤ n < 370323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 370145134 1250 370143884 370143889
    0x11180a1208030f060d12050306030f061608180106032006070f0206030a0209040e010c0f14121012030201090615030506060f040207050a2a14041d0114060f 68
    0x80d0301030340204603090810006544010418401e43c1114002d8450440100c1950791265268491860f120020b94003108121151904110036416416190040c2c40f403414104080c846907841c5040b010240300351440400e040c1145541c0c003000c05420070000300000380c0c491030301d8000701c41c020086100300002d8200016240c9440c40c116081c4c1e9521044880451945a080c00301c0c60300006d07c07a0315829401c0c0031000c80780d100c601030b02c212000b00800014a601c0594030182611240150800c10003032240c0b246c5440c52440d4044850b924020340301074040750740b80f2030500400b8080e074100000701d0050343307040010540c0540000181600c24601888800e0300701c4410184190702c1d1001816540c0b0140100c2d4450030029030302008c90f58080c5c070151801030541c4035603143c0004401c00319010f12003207076030382898031a850076070400d40904045444003918203020076640e946800802e5100ea644d5540100d120340c07100f0400303084106404000c4c480144074544842c2c40d40d00803070f000d500480701003441c0482071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 370146384 1250 370145134 370145159
    0xc030e030f180d0f2003030a0f030204050d060506040f09260904020409051b0c0c0f310e031602010e24090f1002151503070b210108030a1211180a 64
    0x800098011820908d400000700c43d0400801a030006050f401c00c40840c658035508082c0c403243d405030f0004240360a0035000c0c00308848032035100348281d9141c60704280000e200300d54000701e0798600005c40300c20419108905481d51060300c140941c01480010000f40032510707034009a10469484482d68051981e200c11901c05115030403840c4844e4119200700c0c091498a4040c0a42030305005d84002540021000780c0580040b80001c4d84048180e0a8417070700b03035801203000b5800c00030710280c0a10300b4281490700507510074440e03070b000a060040c0c1101500c015144c0842c41a40c24958060500a02e0041035070b01c1c0e002e50100e407000b4091442d0000320390701820056214912692070394014000d00e007050420020801010f0803031b0075019450414078586a0b0100b0010010b800d4400d2900d903103214000d01c0000400d001d4480d14208086c420041000c00000300540b881003145090154681c0b10009003400200b200015900240741e000c598000c1c6031551101403003100c00d0648001c0c8402c1c1d11040c010180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 370147634 1250 370146384 370146443
    0x70b0108010e0c1f030207050a080306100e09041101030902030703060c0e03070e011202060d020309070e0901050610030c0909050f01060f021b010c0f0816060c030e030f180d0f 77
    0x41000c2a0310b0801c4c1100010b040b40001a55180041c1000703040e42d5080d041101c0d9130700540301070030044144043c0303240941700d44d00342c0c01c030310b0508001010000010a01c0da1070002d001500141c00c0481a81c4180d001ea0001142950b0043c1955000d50722480c1640082809981c04400149500400b441504000030f0301425540c00242e89007103a0704e4980f00303000da8076a454080f03801c008140f0402c0502141d6001560140003118080e15100e811f0150303208103e0f03001407690b42c59a050070107019041d100d0016182180c0d0561401165050305024261201807060348040420342ca0041086000081c1d124518103840e42035448010700400100200d9aa043c40b401032105c100705002510341c0e541c000c0c40baa01d103c6200f05501c4203407032070544459400b50040071245020702040105101004020300c140c2d200c41119040402224403640c4446a60340501c200c10314070b204000554600688103405415200c2034010f00707102102c100c0386000080e031080c5030000c584034542011911a002c2205000918 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 370148884 1250 370147634 370147639
    0x31203110301120f0b0406050105041a060901030c090f24020f0d0c0c031a09010b091005090a020408030307210507050f03040303060b0c031c02090d02060307050f070b0108010e0c 78
    0x46900b080290740b00c2d000c1c3c0d444200d903030782600e1075440c0020f605940c01910072401440009442e6150005000c140d496071000213220101c41d4110300c0c90756031130710140d508034030b028a4001545140340c44261082c41082e006440c0f40749192200003140105000e00c440816802541034254101c8510143c1e59150304a200c030b803054014188202d82503204464001d0020f0092401082d40e40d900c0d2141410340c00000402c2002410070b000b00500c007042405071007003241c0b0541d040c1039a454003030000f5034042250301555225120210209a0003251601601c01334601002036075030383d00381100c0241103c0102140025103039454400c1e004a480d00d441914800d21103504d070940b03011126030b0410040e501c0284201c1c1410758a001c04500702d2510f90141c82910b403403500660f035034184051031900810f00c692010112500400c003001c075070340301c0001201e592941030712010384989482d08280d40031302640340d0802c000d02003c2060001d0058000c000b40c100c9100c84020040d0305a013260940d11104289040754 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 370150134 1250 370148884 370148887
    0x21e090603010e04030212040f0806090d090611030903060c0a08180a0f030201020c0f2a1003200f0403020405090c100e01022b171509040c05120703120311 68
    0x10642c40c0040701368054402e20564048505090403c901030f045a00400103016411703000f40010202084040e4028003550b0003049481412071000f042c0005a000324004c109503240c00306003080040090702c40311000101910180d00e41200b1065480e00614843da001401c2c00740462007114100c489200d88944500c050190a01c880d11441c07425489070798100c04640d070801c0188001c080038040480d222000b5005007000c400c00b2440c8001d0090003c15426040c1d41491a40206950392aa1147d21022905010502111141e00c0003a10b08114164501066000a51250380c0120000400a981c4200c40810494661045040d03a541c001c0c204a40c000b000b0381c046043d10750048a8401050724144100c03600480f081c41c030101200445880142c298502c60500b9690507048901700e14080050031001a4a280c044182c20f4510603100300a40138468540c003048c10711400d0700103200078010240c0040642d5160b100303003954901a510043e9400342440b14007584040c400c1c06003808040c03490b040395 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 370151384 1250 370150134 370150139
    0x803091216060504020a03080703232d07080307050c010f0207020f0f060405040603050604060c0e06040312030f020a020a03031415090a0f1404050706020307170903010603050709021e09060301 84
    0x1c02054050030990f401b0088100001c0041c42e880c00a21150f48681c1c0c80441100303107071003a403240156800290300c6144042c080640b5051030079100324222030348032800020409190741140d026109800d000f600d0080700104114100350844020310b445421140200107a610719000b40049014501c4000d6014098080b0002e01c0d00c0d121503802c1c0c90901c010561480c02c0c0d92000060100c1d01c4a84c004c640d030350000c80801052040381d1207810307407920143c1000120001c000001862706c0c40350340801801018880031541042d84a5446682c0256401004542e0380340c428070040e40c0c3c1c0090b8041140000d0800c00880010b80144a0f80d07805420316102000c42d403c3c0000800c10101c400a02c0b00400035075800c2908a42840c6010783e100b10043e1f03201203c410f05107410914104401c6420210a6500400803100042d48400b03402c003510100485070ba4952a10a0002e405820035920103816885044000b04c0d240d03030b09900a03c0340c900c1c40d0711850075074010759070020480c2c05519480382d402981030004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 370152634 1250 370151384 370151393
    0xe0a050601051f0e0a090e0c041112010308130f06110105090d050306010e03150718060212030c03070201090b0403030f0c030608030405060901090329090105330604030803091216 78
    0xe5109158001704025816602d841244007180c160a8082d44a54480c0c080f0340b5107403c05200b00e500030a21039003110f1821b0100c04550105a40600c4002c15445000071003a098100e0b403421040600f1481c143c50070060750310040203014403045140e0030195407800010500100001511002104450b00e032a4116542c240040d5241c448040c0e503140c0600409200c004060111404a442503046807507040680c61b11340c0c910200c18072076030403400030b640c80441c0300c501a212000541368440042d007441c6a480e41e0341c83c1c0880c05081142c0c002414081224113100070036806401000100300a65820015600000e1007102503d0042c865406a40c000304014072a50502c0b600418140c54181401c248543d035030780e519a20031549c00c00821740c451400d480301440118203801c203a0094805c100a102d18284004586084050010501030300c1c6014043c08641c0305a070b1012648002c4010401c98079076a8a060050300c82d072084a03800824060407500102c182030580a5a9544400315100b41c841c02e0503039a03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 370153884 1250 370152634 370152647
    0xc061003110913080f0706060b041505041d0c0c06040b04030e040b0108010e0703150b0a020607080c0d0b03010e010f0203010f08060103030210270302010212060a21020609040e0a050601051f 83
    0x170b500c10742e000070400c000128003503014980050010449590b82c1e03600c0c0c035401c1c905503190100000f08000d4108010898142e59440814446101080102580d1100c4010442d18828102c54200a0080008000a1107150304106200b0390182d262450000c2500081104070740c0c00100c0e550100d141c2c2d40040c030100f00d40300c440550007034090a00041d96150304201c0d0a42881542c09012081d03000207180c04500c0d4180592504580c0d242040001414866007140c446e024010344402c03007660b244012452560250041c2c0030b200c40c1000200810000d541070a0080d6009028880c0002450480011344603400240ba0b81260f4041c1d000d04148100c544c40300c00900b13070300400507041010302c0c0c42210000e0101109100070340e220750001030740e54000c03103d55200f1050003040d09106e5078080300c3c200104055020008080d28013465060a4140700740300150716030059031030700d80e003151070050350740344200300041c4c0204181d024074100c0303005a1740c0394204002003030071103030103510340d00307000c00c0c030301e8010301819 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 370155134 1250 370153884 370153897
    0x303050a1a011407020d02030a0b240a0b07061407120e03030408190c0215070b25030b0301020f030907030201090915271b0f030605090f06060c06100311091308 70
    0x180404c18070032003a0000382c54201c9d010b1040e603d10407400148000254044125520017203000c0c907011144800300000b840700007003486811910200002c1c01000c0040320703403151001081e14142d10201e81841003009100d03010303c00c400741a8a250003042e031210f410000560b0f21482d80044c0042c5804c46980c1c481202c168004455021312040c3d11500e40180e94007040704045d841841c4400343c0324000c90405180300f490250180300104c2c2c41c2c3c540100b1a03003007038070304d01e0038040d090501040b8000c1c1d0402207070091164810032003c6c039202100780404404003048000849000366501082d00740c85044010844402070f0124091402004081101010903030800208030b076064080b0b640400003220b40020f03141036052000400c4690f801d003038021a04200700100088243c5000c0140c0b90600021440b4444050035200c0741030ac5400001d906079580360b04a81900581c201a2181414220702845080c0c8181c0401c079510030850007042061b061900110f80318411104c420440d04490f07485803a9036601c1b08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 370156384 1250 370155134 370155139
    0xf03161a0705010e06040b06010c0c03030503091509030903011b1d0a031a07020607090e040b0619030302030a0e010e240d0606170a09170d020904090303050a1a01140702 74
    0x34050384002c144280700c3c40140010200c044e100524061401c2d45098400505d41418007402e140220041040a5100c402362503140c02c2059030b0740c860404d51840c05a9040043c20005d80040401c5092000071000d4508880154000c0c072280454444210030003c1444c410f000094107010802d41801d6950684c410040000c0d0903004080e03201e4884444d81c00c1d103801150350129203a020b22440d03543c10004c1580c450707420300c2c080d81034a003001c100000601c0c002d4805000b01c0c0501c030208049640d100556000c41c1c001480180080d40d0b81d03d8081d40b02d4020800203404030710f24a80e0ba400700e5000307101c3d0b0030140c80e008118110b941c07104074401042070001c0d06d4405c0044c0c410700c00c1d1300844034113204601c0540500e49846000844c0307110000e401345c8000308482e0620381807000000001d05404a070803243e449071842d15403608240229540280903051715554400c1c1085003050506030164406406003400300401d022076500f4441456030103266019a500040580803210041502e01d406066000d200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 370157634 1250 370156384 370156387
    0x30c02041b031508010204081203100b03100f0902031e0702071e030c080d0206040201080432060702010603031e050d150e090a0c0501050c030c0610050f03161a 70
    0x11803100107404441060103001c40c1d5203948050400c100004200018034946000b586003d040400351900c5094040390315012002c040040717003407040003800040107803039400c04554591821481e120780f60303402d5200d024804282c0c03000205107100c0d54000ca0f8400d6000c0020703038420300084550701e8041e0400034203030001c40c0039030880803460540c50042c030b489584011040c0742009055003080110980280d21452143d0700c04003104d4991900458500d0b072092702401c26a82c40e6441c0d00701500e12200e02c900424010252543d04130181124608140070551214100c44065a442e8802d9080700c00601003d004240d081101d6540c1e81e689000d00a01966245011400c140300704145609542e507682a0754581c903e0360400340728144010310034903404500f0070014a94031216840b004107120f101c0c0a0541001000245680458000c004131079508007030030104c071000d00c0c00c2c80da06021a00c2c54000d49101c0c60032a9480800c82c0f07000110307012a810035840e0701c00b086140542004132500c0307844055072030000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 370158884 1250 370157634 370157651
    0x90510091b210210050d0c03020904060902030411101b1a070e0904170c0102070b150a030b010905250e03070914130609050313030c0905010e06040908040906060c0506180a030c0204 79
    0x20300d004404c0b407454191000741e1500ac41700104802d4032929000a41035a02c18401c120205100c001e042160500c280c441c0348001c101e440c2d048805014044148004e1059810b50700c0410103448a40e45418046040303880490300d039040c1c04c44104412101d06a4043d450002003000b00c0d0804400e001c01c40504258645400891404503003aa00040401d481a040700700c10042e000302e20b40c64400c3c2000048880302007140c2141d6401d0401c0006015811202e5640c03400250602d03c9404207000030036000070f40fa651440c0c1200000e29480441103a94080c3c05806000075050400d401100789801c412240035a580e82d90039a00c5018505a0f0b105885460301c4090a6000ca50140010285450b0ba0840b04070f21174154100280c041c860b5a1080c031045141900400c80e1130003010742d49800070411180031070502007a0a0060090045421203a2454642140040c2c5181c200940d1035800c0d100340c081d03c14540c4c1d0314900200030114040c5090f91508100400d0000178420038141907568402440000c1c18030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 370160134 1250 370158884 370158907
    0xa050f01121508010e011a0114030a09140f0d030c020d21050108060106140f04090b130c020c010206060d0209062206090204061707050a03090510091b21021005 70
    0x810950148030311340d6442c5e12500d0741c0742c1c00f8003030f6503d001c1c1421444942c5000c0c542c0020500601d00d4822807d100f00840480c03c50a615000312000a401c001b2980e0049030f06841c540c0c96030051002d034242846416010002c4a010703000d000c600c1c83c25034010b404c9503074101070240c078030001d00d05101c049805694500340b4402841d1140c540038090410040400d07604140340a0606410720000d02031000c03003032094a1284244400b22400d40310306440110342100b2b098040303410710b07503c1d8074075640f01400c141c0150103190740020b043c004d5003400da00f140c0c90ba0301c81c030042c0901a2490b80c00650040720b40800680326040070381a4406444021200524903800d01c00c0c40800c179125034000c80d24264000800300801c0b5840089031010b4812002081d80d6814050000b41c05413095502c030b03000345601d40320742d401888024003007800d419804540522081c0f20924116106030307060b00015064028000300031814a2002420500c00c044156640c2140e00040c0c0802aa81c1c100c2454407040090821243c980308 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 370161384 1250 370160134 370160171
    0xe0708060a02031806060603180c12061609080a03030207051002070c0f06021c0f0c0c080c0a172802040c080601021c0e060703030b06070f060b0a050f0112 68
    0xd0750502401602c0c2d0600c54030b155035103e0b070000c0d1000341c0d9005c1d50500401e0340ea4042100d420510491010030089429241c075414805501900e640c0903e00d039031910140b00000c10601d00ca00e6604940e204030015014054981d142d050003814040d601c00100c60300007034040c0d0b0052400c1c0d4001c17811103030100e00c241d00d0354044c5d03408030200301c2c1c884840900400480340b04003000d0b00a0f08181c000f1300b0348804548408668000408200b20400400c00e0405910500405400102540003000030441c3c03919125101c1d80d801c0c080000030b0142103403c1e4000340707910344510452040c10620002c1c082d0034202c840e01c00354070341000004c2002c1140d120308040060303540d481046200101c41d01c6070030b000e1500e10006800d02400b0005046901e0030300144108003640134281c50121a01101d0b4103440b0801c1d0304044000305585425590010300002c2c0d0700051180440782c1c1c204080c403c41050044020050600c08141580e10410b5045400054801708940c0213000d0302888070b40c090000182c8441002d00b22155 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 370162634 1250 370161384 370161391
    0x305040b0d020d0c0e0d030c02060d1103061507050d0e0a05100309050c010306050a0b070f120513080c06310b070302010501080601080307030807030b091501120605130e070806 77
    0x80da41c00550031400c80000d000311140030100f41004518101c0102c00b1a00c1c820600600504102369601200c04660311103050741c50b5084d0383c18080040f00c22540780c0d10b1a6500544581c1c0c8180000b05918224030103039000c80c4c400643c0840031f4001030441c0340c42642c03404c40c6005c10b0394ac40801c407e00801c5984800d901e6010010840e900401d0790b92103400d01c1d41c00c080000d8012410941050800d20094603400700c45001c40d400440c03e90307560700803418081d80d03400c582d09004011001010010b1603040c1e01c2070151040c0003002e03d00d1220203549000182d51140700340382060300028140052222040120b01188000c00c0020004c20040c1c0e41060340340000703e42d5000540d480388049421340c14140e0910425024140140c01080e195040c4044143e0700d02903614010300b0406403000040717040b0301c039401c9a400004040c0c90361842d810051070001c2c420034043c0c071140c0011020380c9841004051400360604a81c0c01401c1d59946066955240010700284200703068140b1546500060b920300c100000f520 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 370163884 1250 370162634 370162657
    0x50a020705030a08030f070e0a2106090b0402090903040f0b030705071b06030e010515090402030712111201050f071103070c03060605040e15061014030412090503010e03070b040305040b 81
    0x45d01e01d801040e0783c940030750140800302000315504207140142c41e55000401035400000703503c0c814040003446446000c1040c180148030a04020030035041005149487d4001d6200b03d52031840e40d40c40e481c00c2d03a628000c5100d51010341c0b4100d001004000800c01c02540c00124520f041860a9482e4072520020000c4005003458002c2c01c80c0100f00060341442841d0080c0b440500922183c1402d80e2140c0c40303c90700d02c070960b00c0781604202040465804000c0c201c010019191003c1c19070b8030728248586012880071005018000c0c0c64141e1803071003010f20656101e00d80109604146854894003165100d18144a0701c9171440200041070109200003020001140318520204145052000b80b0003610607000c01d89826920114038944100e03000071185602000540705103621a1070028101e03103401c030f81810807945a42c00002d101c1400380082d41c1c03004246203504c0d05084240d88801341030881b08207040d2101d0b90f80041c40401c0000d400c2d40400e5130410b000e490414109610341c02ca840060748000c03100701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 370165134 1250 370163884 370163887
    0x60c031305010305060d02030c130b0a0b0d0b01050307020a14070b0c0105090106140607060b0409061802040b0306010605040920031e070516141c0f18080d050a020705030a08 76
    0x1c96580d01d401103540c880c4c82950301618070010399020070f41e20742181120b140f00f070240c6400c1203640c1d070355a4850398114000410050140e0f5842c0546051580840c0d25090702900b07180380750090794002c078100e078090806580280802e480a480760900801c0c452100f810600030b20340009800c0f6086409049811181400091356007003500c40346007100c0107540300c40204084110f005520780c0d94107041c0d5040c0c81d08080c0108081040b180010018610040000c00d0b642c50480c402c150040c04802100349203200765402c0020800390420580d8405003445140700203a803c00080c0031040382d94001c034001810036400081e4062071509180c41d40c2d0411582d85200c0403201003001c4400c0702c80c18165400005504040346443e60310f00d654002c10f146150050a080c4090300b00000c10700c030030041100e107104541300d80c00c0220981c3d84c0091100f4100002000028002c42851038030ba90040525003c5a08100050600107051803056036503400510421055006501c0c00044a48043c0301d6078000a02c1440e006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 370166384 1250 370165134 370165139
    0xf0114031f09060806060607050106030506070c1b0308030115030b030a080c15010b07021e130b1809060a18050d09061b030e090a090c170d05070f030c02060c0313 71
    0x949218441d61200c0142810b1140821002070041074042c0c02c121b05840c10740c2e0300c3e0f4403420024090646940010214421030040000c1250b00c0000600c0e99403040c801a494081c00342d4104003c0000b900000e000c1d16000c02c010018024403003908040c80b1454200403c01400200009050180500b81034904800c0000c48005854082c415201114951520f462455040801e1011140a05580240075001c05d10450803010403900e150107140c04020310600b0000d9110a041e0003500c0300c11241c82c010813803032800b66454940c1c1d1421520031061400244400d41d034021146010345034100a81880b030340940382d4540420701c184601000300c0d05944401000c586850030050041515400e0382c07038090008500400002e6200c1c1000d00500320440e0400645d45510315440010042c1e240c0040000002d01c0e00010611883c00e10011081c410105442c1c4190b00c440007a100c1e4420354800820038102d5007142e41c0000d01a2500b54402800039054600340f55480703c41d5860341e40031903080c0241e5280742c0002c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 370167634 1250 370166384 370166431
    0x1d04050a060f0b07021801061e0908010219033e070c09020307091202130e0304050a03050106140d2105191d010e0a0b1602041b090b16020f011403 64
    0xd1448000ca001e01b40143c540c900b0704010510061047e0940d001590a01c030b1a2080c1c0c0f243d8642405015143e00840d40d503c1102e02d1141d0215500c00c00c90301207400d21094203c00c500340032409281c07401c407031080c0700707542d003122120b901a5800d0308a01e00c034881c050144801092a181c45d1001030701105400582d039007000c01d406040c1a446a10603101d1410013101440182c8444903404c1201c824100046140788800c02054210b00a6400c150741203580820004284001500701e070049410441121a40c8050030b020302c2404108104003401c4484214550035040401003401080b110203864101c2c02e001241c07040c98240a139003140f0100081c01c4802c0240c2c07400110f0022001410242000d030596089031012401c180f1640c0b24040c261100828911444203c23128803010803540100204070b035070101c01a0303e52488c0185d0001d00010002c090108071a030007a4111801c88a200b94448841c004e641d08203c0d41420302c5250034100400c002251100d0a080d00185004d078800c40c034074064440d8100341 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 370168884 1250 370167634 370167649
    0x50a11040603080a05070f05060c070b0a06080d11010b03060717090a020f0409050c090f041202030315100c0b040804290304110d050312060109061d04050a060f0b0702 73
    0x49648a1440d01400704002801602112803900b40c82c00c210b600c03640c040c00c0c10344890004020180c00d0b405070408000d050106880100300c0b140c4a44d190024548864007a44205c4815008101844c1e00048015540d5402001e00913030741c24410002041007200c4101107402e0041c191452030119420701c40c42c212680c4c10000b4254020416002005036450315000101c10f54000c001282c0125a2602010203100d01840320202244019122032f605051100001520380f000312025035424400d084a503e151b440070040b03e00885101c80c41c070707901e802007008010040d04a00c10703142c1401014070040c400070351550120b6100d68003071040d0030f440318036181201406003240c0c01924000c5440d50030f0000d070440c121040d030360401c1c0c20280407407241128101050480d00352240240c101e00c40458420500d60071302c4181440385a080c3d8031444c070185d072460706540c00c0b101128051410300c11a42c0c1d500c218103150740000c1d44100520030104d045540d804090030b0900e02e41d0480592030100180b04000e600781100b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 370170134 1250 370168884 370168913
    0x717161401090c290d02070b0103050c12070602070b030c04050301151806061b170c0606041503030203190917010207051510030f0f0b01080f0705010815120102070f050a 74
    0x1080030070854110340401140c80c2c07819036200158134040f443d404141d45540c1075811042e480040341e0755950712420308503624010107088138490304810090031a0a00003083c40c0b400c41e030164004200e0b25080c05540c5105410042101c6582e60b0709110000746a0340034090400e240745070030303c10821241001d2080c01c480d00f15070300c50303190942031a000704221940400300041e4807891708280ba00e12145031407c4045070a2006200c1280c030740108061490407000708855004903000c4608001c540d104a0f280d0b41c04200a21025001d41c0040c0711544140c01c50001301d0b200070700c039894001059038503a512940500d4040803030b24003980d40801c516082020400802e0243c152070248001ca03880e01d0f440104942c91640801418000301c00019010440c0300b02c500140950f029061420568440700301c0d0f99219417500aa00d5607216100000500e9405010321500946c8440f2808041991680503c07400c0315018050140d071750741c2049800003069501c0c4031801001d206402030038500c5881e08000b1000b00c00007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 370171384 1250 370170134 370170149
    0x2030c1f02250302010309020a1d09010e0d050f0702010e0604080d080903192111090405130210030c0c05070305060f0106032307170108031c020717161401090c 70
    0x400030030750108603581c44541101d82c2485d000c21f5460b56031011440c81d15059125045415030041200d900d00544540e140c80f404039000208492120740c0b1070307543c2d03a5600c000b41c0030221701d041040c00000711b0000002d18200e070041c100380d404230031040d012a00e90345c010341c4400803640141c00e28003a17040d404124250024016170003103040c14440110740c071000c0c2c0d00301c07014411b102d600f00940c0115064040440d010a0420710304120241040c02001c60781e500c41101544140d1400b1b00080102d1408a01c480f80b2940180101c044003420a000768020288204400107100c049000000041d204018034400386100310090002c40c00c00d0301c6d110301c04c44d006030440028503003800d4503030304440860700340803c0a9505001c403070b459454029060358400c9044500e1480e5076503860022038103881c004010028550880005400310304080800d100b01d008040006110581010b0b0103261100c81c84013800244604902c0c0d00320b03080075680c81040b8000740c9902c510302030f510303010006d05100c0060850b01c01407004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 370172634 1250 370171384 370171423
    0xa050103092102120705070315140606090103020d0f06090e03030c03040320010f06064a06030a050702101406190b0a1d030111070b0402030c1f02 64
    0x19507070308800c544550b80c144025950902c201d82068402c000b0643d511000341c0e90150384400c80e06181e6201c03102ca0100faa081c1040d4914503460000785e100d100141411252862501d48521f010040168008900345040607002d0243c0b18070640b0910810351a55000200000e40c24a020007047c281e41040d09802515001402040b48105014013103d6002ea4180782120b038490208107400707045100c0300e09032a5690300e07100c02100c4000581d03015009403045600d5010f00040c0046084080d0941c074020708003503052408040c0c0c5003074082903002c2d1030f604e00c40e2080002007140402088440e002203400820040e110070600036902d40600081200341c030000300c18022403c05900e650203d480180406005800e103c006680189400c82c00038098280052000d650749807111008100142d08205500b02000e21840e03500c1c1440d05128102c2c641031041c000a085c44e050b92268050214018801da805000c0c16640605655841a4143c0c603000c821000c220103030001d190081c54030f0348140240c10030100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 370173884 1250 370172634 370172651
    0x9090703060605181f020d08060a050d1103101b09060c1110090810021c1506050315090c0d0e06040b1306140a0b1201090c05061b0706020c0a050103 65
    0x20302c0b80842e101c064040d04c0042c001042000840d41428588000810b55159001411285603001c5404004000c2943e00c05001e40c03600b00802140c2c45240c070841380d02607a103028400006441001d2410029402000d480c04010190444800c0e03900420502450f180c002d1419443d40d600000003034054051b615040000080d9075032441204078844031410702c6105c401100082c114400c401e0a00501510800d540c940c2c003403041240080d40190320920842c2d02544c1d404111440380e44101e021041003101c11503099450403000f95070a62010705150344004a80000c0c80094590703000103402010700c220510740c1c40315040d1400040700c0c07000000403602c1c0c01c01000c0c80081100302400729000326410340100a01c3c1c1c2d0742e01d803110061880c4400c1c80b810420001c200703d203100da40c1c5d000c03255059068420003c60740070008a10700b20744400c24010f11015243c14103000c1820804003074584010890740c1c018503000540305035440c100d899804035005074064142003030181000704081004020a080500c410700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 370175134 1250 370173884 370173887
    0x60c030f02010606050301120f02130f0608151f090207081e0705070608150a030b07080702160b07060e030712030b040b0a050d0302030712050703030c08130609050f12090907030606 79
    0x1006202381d40d41e51544a060f441402250f0845040c80d0741c0c020300200c6130000034848031002e4013044050041881ca88000013070610b6001c261590303654a00000105255110b101e0089102c03042c01082016641c0300740041100b440c640300038400c41d40900d40b0151105034034824685501c220019101c1c0400b01403086100103140010b05000740d034401e0510a50a680318851038001d11040807603542d10400c4000000b0034005801a068010030072580e07040d01d04d07500e12000b03aa462076180e2111400c0c5105260030000104070401401c0c640b0702ca80000704541520840007455038101314800d407103c0440c2128800314a41601c42c4403030085050318148601004800054008051440303454000c410b4005401300b00361080c011030300416441840050303080c0c07120100400580140741e00f100813918007070707010051900984440d88035100628030b24a09854039a104005030829110480d46031258401681002c5014400c080c145895080d0241c0c0740c0001408000c00d0b5100039008006041c5070410a2004030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 370176384 1250 370175134 370175137
    0x6110405061606110d06080c010203072102030d05151e030307200301140f0a050609070c020409081b0c040501030b01031412070303290306010515040b0301060c030f0201060605 77
    0x19a612002100c03004550030300304042c240c003194413162800700042541c020ba125a0000080c0c0301c00004440c803da442c840103a94a2113102e00c01f030710000c01c1c80c1030044804a0b20300c640e03207c4030144c419a801d080c0303031f2103005050740d01c15140c890310f4a10a090050141c1040d0780b4961003007045030005144a9507120100c0d03101c0c031843c400a000100c00c00f0302100175003120020b006000c1c9018000704508110100c00c0c400910069400120712400f04010600c0d02d9083d0003414051178000b8a99000c1e501e6541c000c0c2c0d0343e10300c0e08000f00d800540f0b995030300300401c401c500940b114010882d80e09180c447d140703440c1c5043c1468404114880c601d45030040c004150b1000d240d5054941c0031201c00c13003c04500e80454601501440801e48003d00001e07550100f5615801c00201d50945100391080c41d10b072142c42c140f40811000800780c055005000401c410320f800845c001000341b0700030105192540364011150180d01c240c1101c0081000159194105030b8428480782e503d03290b910081089a040038030003000f5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 370177634 1250 370176384 370176397
    0xd0206010b03150613030f0308070302040503030405041a0901030b0115180b0c030f16021201050f0402040203070e0918071508041502090d0c0905100303020309120a120305040611040506 81
    0x203100307094001036054844004417684c5d01c2081c3c000400d281e5591810900f4125840f44c00c500046440d408542540c1c0240241c0d030903100010055401c090801e01440002c045420000c00c8817078035143c84080340e0311407248a070f000e18001c00c000d040329810604800c2030395040fa180981080300100518041125411210080d11403a400107a038403e01140740c245107004003040c000021400080401114421454162a0701c0c801c5d02d0165084007400045400c03a0340c2200c40700d80b0780d07203070400140040c030b8940d00466002c00c441c1060501c1d5042000440d004e9242100d00707000c0c10b003014280340c1285000304881c100804020850000650b020f08004040c0f50019000502410106034112141460742c3c040d2031480c01c000d402841e030740305a07060107504094148200751481e440c00f804101d003820703240084001e494140d00110f2030801c00c0d10038043d107035003203182c0940c8a004480b0468006010a480008812036a643c00700b614281401c055080303840604041055900800007042561640d0703003030f24003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 370178884 1250 370177634 370177651
    0x6090209151f0908030f04050102070504020a0f0c08040b04060e1c02030d05070c1d0411040c020c0f030705041b0e030606010e06031509011d06090708060d0c03050a03030b030d0206010b03 82
    0x5180c01c8608180d0b9000c401303810014580c0000708104003d030540070043c00444109034211150b0700d96640902081744280103040c00003448414650300c3c0140145c4600d01210b01c6500340c0ea15003035a030700c8052019002508120002280f51075000e000d441c0c450f410071802816941000402c244990002c0d40d41d2810b01790070130034441e01080380c4080c8124002d00a000b484800c070a81d0069034000c00d41d420901c0d003294200c411802608800c281400c1034480d40540305030540007420446404410400328611459035168144180ba0010906486501600d010314116800000310298030050140062142c0c0c01c0007802503010000308841c03a030b40050030303801c588000d0340c41540d04e4407140740c41703842510424111500424200d0001400c0d81c4540c9941880d030047c005103074083c2d10b500b03041040c01c44040da0740303070001500c8501003211441c0807503201d1f038820b01c030f50b407942c000507a40c0d07403000e0900c03500c40c0701603012030f03640c01000140c0c0c1010f00c42d803100c1581c10b1024291a6040601800b10f0740006081c010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 370180134 1250 370178884 370178929
    0x60616050f0a0b06131103060402090a030203010906092010030c020f1213090e030d151802031801020306011d04060b1909080a03050a0e0a09090609020915 68
    0x2003409000c0c02007003100161001541d070420342505000da03446600b40c074480c0c0208000c0403441000d04181c401c2d02400c50080103c145141c4401c420807020303400020318164421310500000005030740920903110014810311000c0b03440a110304001001c030050388118504001d1000702c1c4003d90381c83d10010350302d070701c400c0c1800175084080c0d1504a14058000c84003010a10455102515007030307054010f40f0b0000d208008a40d05145c07034450900680d1400781c49070079103910500c02d041410030160402e18030b81070149080070041d555102c0501d464181644020b586d1540041401803c94071810080f1010460b04002c2d455420f0400000b4005040b08803501c64078101c03040c28100d10f0f80c035500204010b00a0910300d507200c1080816101c03d6040350701204e008146181e00020b420103001c12080742c2250503448403030402901c80016141122440c4c04583c0c004044000131500814511800c031160703000d540300185845891040c4490b0000c05801c110aa94040b01050116074641052014500140c682d91 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 370181384 1250 370180134 370180177
    0x1203010515091c02030c0105040305060f0403020a0b070801090c0903080306090c1309151e0605130f080318032a21062a0703050306190617010e0606 65
    0x110450268074401c1e54070640c07001e40d02103c040c2d2481c038181114002c4040e1025404210015a814401c5110050058001f8070004620154240c000355105000b401a00c070001056503a02c00390550407585040400c1080c0014060b5102504c900301b00c42205080035281c0a0868403088200d020090906101d2044040003801d42074105066900b15002601c0300c40102e5121030800c1e0251044011000d1610120000068180341581034001c0c2c0201440c400d600150070a00100d90032b034088010003102000c240340002d4141400c4d50420001c09501d805940c460941d8005482000c04034140c040c03080d449842a03800c0003007402094094407070407a490007100380c0180042500140208490354602e03011031a02c0c2c9410b000441c0c4644500c0b801e83e620f0341d03d030090078841141681e51083c1c1e080300040600c030080000e4010002103802010003410a40b42c1181c0ca112070a01c182c040d04940c0014480c0300c102c40c1411501108180035143c0110b41b01802e10744400441c07120300822809509030000c90240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 370182634 1250 370181384 370181419
    0xa110d020103062408150a050603220c05090a0c05220e01090e0601091a040207031106040606140d02030a0303020310090f150501020303150f18090106090b0312030105 73
    0x941d000304090b28125074400d2054204d4072086140329115001300304001e00040c00d0b104010341d030740c007420001801c000c003c50401c000e009864000a1030785000360120030440ca600c0c1400c4a1001502d440741391700d41d804034185400d120401c1c0300604601017050408075180d00080d0408260361055200e4010b46100d1080260200100c8a155120000411030139001283e03000e0355410840300000d0150071a084c0b641d99078a5001150038980b00180305401c1d010515403503207460740003081e100e402498a500c10385003100c145030808800b41c03022519141d90301c800301b1a49054040c00400c501c000c492003d049100ba07008a81c860049480040c20140d00100040e10035041d0036102d07001d445144010400c100c0500c035244c00611540d118002d89160900340040e1640c80001141c0c80b441c0a0480707004081c40d14024052082c41c07031007035103078000706030b900ba0202c4000c9214010710404400002184a5203480d0318507040781c0c03000c1c04d414000c2d00444000c0b013090031104211b80c111001541c2da803004223042c191 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 370183884 1250 370182634 370182641
    0x1e0102070b0f0c070e0103030903080d09140a06060602070e06090703110406020c01021005270c0312070b07050a05070b1308070f020406210201031e15170a110d020103 73
    0x44030510003054081140c100000a00840d41414040314403503501c5d084401140d107424440100060100758050000642903c01f0302240c444241d4081030300710007651900250075892030000456405074402c0b40a00c501401041c00400090000d440214107260303e00c0b05510f4024046c82c01003131007401003822544664050342c0300b1512080255201e58035048000e450700e154107656801803080e41295480d200d40340c411140a480c000348415040034018070b40e012080c80c81850100340f40a0380c515118580c8044c0142c19502c8080a00c882d5030341c600c0d1911114050700603198004114041c4880c10307460b41c11200b203a0f0980d03001840d102c060341d2400d005051841003068010596140441c410003008013034110100000d2080b80d05120154a030010b002041a410364000055804400f0700001f41d4021b41c01250a04055240c20002190b1502e02209841440380f0200307629141c11410059025550648203860b0340c000b010303111004268070b500e9401c1011183e1144240210100b600c11a07005c1d60 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 370185134 1250 370183884 370183889
    0x706081504051927020f040f18020306090a050c0603090712030c0501050a05040c0515070204090b041502090d030806060c060907140d17130803030c0d0b01030b1e010207 74
    0x700103001e90320388041ca000d419000d1114550742c1c04e0814040c601062130751481c10703804801c10401021040c1c016001c000106552094864105981d21031058421400d0b01030490041e000740c0007900419801d01c1498902400241842816080761301c18000041e40401e54040c3c007281150500d0f146d886107051142407130307501d5201c45200e4021910704420503801051481540f40500002c0000e0fa44041400302a0740085800620312003d090b0b05220394a001c62800075403441009007103041c00155404502111284001601d034098110108010052902d08500710090852819810100c02c90301280b41d03000c2441c0e0040612400ba070010f40d00d51515802d03192084548000c89006040820060b916003085004109a103010b11401950341d00381400b4290316150711002441290103010b1507840c46400c181015a00c015015070001741e0040b040025500074101505140d6840720103807000c80c1290850b4004a052604015a0340322942e9045490811085041041c03100c0d0103003800102d0401c003031078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 370186384 1250 370185134 370185139
    0xf03030a05040b0106020f0705090a0f0905010e0609190816020402070309060806221a0a0303020106180506030a02040b06090d03180603051b0708040e010902090103140907060815 78
    0x22003000040c410a0304414000d6001d4860408181d884100885e103540d00c1040d80404c56105000c10004c50800418080d4082040c240001329441d04008110076900c5201003030b25169116145100c4840c0c090107681d402501c004000c00c9080001c1c00131540c4481c0060780509448804604a1141142c504584003541c0d0f0051003199584002d240140c1074003824040c08001980c01c400044c25401e00300210207800b140c240d00c0d10b03401c8103016580005000d099122000303807240050302d894540c03166051749020318804d80001c110f02e801d117121880c25051901c1007001c001e0900c02400803030f883c0030507404c00a079010386011800d2000b201c081142d07807090f240c030260040780682484040c958850100204c120840f000380c0003080d6142411001d07108261032000c800d20000d000b170841ea5681d2001044101d100c8e400d25820241d0b101c040c00c0c100e0070242e00c2081d046400140c220b805690500c580c0d1a1948942c0c80d4031040e0614000f4076070b8610725405008184224000880d9481540070b07180f50014100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 370187634 1250 370186384 370186387
    0xb1006080702120a051e07050d0f02120d0b0604081e06040210080402030a0804090c030608062e0503060708070e1e0d030e060307050c0d0c050a02010509041508010b01170402030a080c0f03 82
    0xd44105040550240e0f00584060081d0301c103100d040e5114851100b1101c004bd801001810105000e10b07160b0360126108032440390f80c0e0b030f211616503110500a80010614580548408403662078203e1800c0000103512906030000000c03c00166034140a184051300c1070300d0038001a50b91403010903d0003910040203170545001060004060b0204d4020a80419540e0381c20700c15a076403a04003e5698005840362950307040401c640804203940190b441d003050708850750142e4000e5990002c00d092070400c3d01c0e0f0100043c851800c1010b05034005041120700f04059480a00d11540f0201010703407170f100440094410789441325a60149071291052000c0300c00d005000c15540c2c10080303030190069020983c0300b44c0c50300890343c514130460b006040c51414103411001400400a486d80112199404942c840d0f5100d5640c101c0100ad0146a4042a000c0c0840000000380c6030a84000036142160141c0d14034041180f070000c01c070060320041000c400701c96102e00d10316110000701d2145800c1030640400300000344030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 370188884 1250 370187634 370187677
    0x70c080a030c021603200d0b0c0f1209060a0b061c050702010e01020d0e0607110703081c0912020609030408072c07030609060f0b031513090b1006080702120a05 70
    0x441b140464a55052641d40c4d021140b0f10020b200c01401d4800c0c0150130045203400080e107908940004044203021401030600e01403407050402c18000058502010036032000c01089162811403050107200107080303900742c1c14004502240c3d4400040b89100382030040d15000800e00c00b0b030003508141d00c40a0554005d640324400c45200da0000e0444010400f514414000440c41185c0a0003208500401c01c00162504c581075448081ca694401d1410317651010b8804100740a0141910845001c00d10800000c400d0628414000345404805801c5880d503401c10442000040707000185041180c0b050740320803e0f8002461000000c450f81003119807404048001040650790703250f03011a0546001c064208501030311851401c0000500d402464071002082012505098401a820340303404001402809804034203181e040a0300c80d40300003143c403e12106c0502c0f0031100110a0980a4110f0b072802040924007444020742c0c9110000805980602c005507849055200b8011100308030015400941000b5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 370190134 1250 370188884 370188893
    0x1d0309040e011503200d0201050a1103040504020342090405070504110d0c030b09040308060f10021b060a08010e0705040807120510091728050c06070c080a030c021603 73
    0x179a40c0c409649955100501180c841c80c00c030444c0c03602540c042e503805080034544641500c043c1010240b21842d44020701002415543e2400150320804c0e6081c005900c0c034401141c84200141e0001018042c0003440342c0c8074482d03101c03004082d080200c045545024070349a5040050030209180c004075081820800c644511015140c014074141e500c4103030400c00920640e10442c2250b01003825203922040040214000c00d01c5282c030b50350072200040091003c00c0e2402c00042c0301060a00240000d6000441054512410ba034440b2240000550b81103180c4201004002c1c41725405010703141034060b228006c0342819209074150b501821140c000c036400582c83e00c0405200b190002d10803125803103000303000b1000715010301400301500d9002c140e1021503240c000c203002480d04903040036600c4511140000c000a012103039079603d40c46043d210103650382220001b9608100d80105080d003844003401c4041c00284424048616810b8540f80009807181c00c040103c1c14503404071403550390210322542c00300a12 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 370191384 1250 370190134 370190153
    0xe061b030a0801061b020901060e2d100c082b02070506010f0902120601051b1b1c24020c0109030206090d02010605090612190c08011d0309040e011503 66
    0xe504070f41301c8801c090030915600d05c440c018200001e402c000c0c20401000414015a4862142900100b4808000350740781c100c044040c11800c1301c02d520021a079032030000740c10400c2d80454003003910720300080b580c2015210000c1621070f407040c590a9800c1c0300362400d0802e52141084401022101b820f5542e807080b410810350314070080c0250b0f80315202050000501c151140b003180d01c40d03060040348002c0749d65440019641d5403c528180c4907038854180302080182001e0103031020150350101d5481c803640041d42400521055844560300090581800c4400303c1c181e60402150041c141d01c000d807442c4140785203440680288051400f40d0741c00c1581043c04c064003c24030700d220b6500325003118005c440700c0100700c1c281c072000d00c585500700b111080810110304003e942138041c0c24415048072404072071802c02500c08907171121b09450444440c602841491802e000f505840e82c055102c846c0c1824425094980320711410410a100325076a042044c0070309429000074556070007600512507204d9503810841904e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 370192634 1250 370191384 370191389
    0x709210224071b090b010c020405060102120706050906150d26030103030f020111031302010e0301020f0c0f010e01110a0c050f1e0c04110a1202040b030c0a0e010905010e061b030a0801 80
    0x141c1c43c030b0040108681403d84240b40d0b028205030341d00c0103034044a80a2000801015001d681107018840000140d04051001400041c6c481c440c0040c6c1454107110060a04d070b0b024044030100e1007010644d00240d59500104d805c8190091990710340310120b03c2603400300341c0d0301003001c0031030310404400002419006512011454019002800320308841001000da512040381c5e5844010345001d22140994410760310f44903038400250005181103000c030825036003a0881c2c1803803251540310700410020141c0a0080801400110000340015815001514502c1c041c0d4001c07003041100d080c03040002e00004011850030000908103441050380e20800084a0851030000c08005104000240400d0308041c81892502c8030118841c9040074030700042203452203400900c54001603001c0c0300200d05503014100444c0075006404845a8940718804060a8821070b490907505001c2c0c060000c010998014a101e0394860703046a805640e22421040001040c10045e80c064140c800411500201c0d0b400c4000300d0705 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 370193884 1250 370192634 370192673
    0x11030c1b070527070905031e10150f060201020307050301210c0e0703062c090304150c0c06030e0604081308071814160318080a020105070921022407 65
    0x445030f032a04c900f6074084000e40b01c1c07a034241d4032036140034401c491902901c42c000d1042105135800c0781c1e030351b50040d41a80c030560550010369560400c100a000e440b0246500105428002503045292010740501540414420600100700310a40e00c050307405c00b10042412140d010f030028074030b42d4036400c400b035501504952000c0841d21303154001c1001e2440b00c2040c0c418101d000301c600d036a010804960509108090001d0341548400d00c070210b40a041c3c002e0100d01a00d840d640c90890000904084a80c04869031180f014503240150340b4000d41c402090a079842070b000310040da44c410b8201c0682c00040a5a40800054001d000001c61f000c0b800303519070100c100c40500e09000010030f00100c802c800c00107550b44480c52204045824025000383c0128140c0c3d03800303038042c024281d243e0711008001d9002454040042c0d54400401802607000340c005400790a42c101200c04451449041e40c01603e51207001038450203004400d1400522240c18100c4a0300c890741e04251155014980741c100d020302040140e8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 370195134 1250 370193884 370193959
    0x9050109050609130213151706040c0e0d050304080d02070f150219110607081c1803201c02010e0a0206040b03040201030f1b020111030c1b0705 63
    0x8041c5480b82c207940c1e201a0050100078540405010740000354064040c0c14070129585800042c0d611551000c1c5034205071a4950001550a4524480c4952402011544030304c0c507000d2507020707450348184602800c0740103031560208a525030410924600031948030451314072402c1038455450364003041e00001c40d040319245280341a1500b000c0c0d00c001001210740c00040c1d01c140c28420300c170300070003c0c40050780340074901800c0b1702840c00e4080b55450340300b48010303126500001540540414580f11044541c403400e0700820111a0001281344555000c20015007000443c0a40980340c03401422000c0325100c02c001110503500c40307510110015401e140c4400e003d540707085603601d41c4580200d45006c600b039000780703c24030b45424141004620382000d441079041654858842c914100c01d88140c0441c0094030602d01c2424051010081c01c0d140030780d609500f0a44103000384018140c161054403c1c6107444800009588501c08040d8540a42a4000c9520402c030f121244100f804d2050f80c41c4c03d070541c004801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 370196384 1250 370195134 370195139
    0x503060c030c0316050903100501060e030a030e0114040807170d05030105150a02010b030a0605061c080a0e01230a1704030e100903060603060e1504050601050103090c03020d0309050109 81
    0x3006030104981810b005901000000d81404a07040340c145203030320340c1c1081814852036801083ca0044072080040046076034000600925400c0045001c0c4e88034114000e000303c1e0002d80d0001c02041202581034103001d000c10b40801f0028034102545c01034401c2500b100d01e155270320f030100b45001411030031120907402907507001e608403441041128141d0741d01134030091040307444000d0103519501c1585050219562080407503503690341400614102c07801a81d002c00da5052860800c81c10f840c1000300751814802403a1303050005041d42090f120041c00da41032100322025044016140130200440c0d0385c600c26006d80086140340c1985014052000060f41c030ba4200c20003013041140001c0c030a40b40178010884100d4480e059180c03410038641149454a080c0da5940d660b5555070b0f06035490b64004032090360b15030149141d0810308010240340d000076000f8404c030b2400d054075011b8032058180120b078105510341e1175800c18089ca200d100030080d68003600c42e0014002c02c2c28001d01d0b800303450044500092408200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 370197634 1250 370196384 370196401
    0xb091b030610060804060e030a0c060b04090203120d0e150a0f09021309060605061c0f29063f010b0406080901110f12060114040603020d1d07050306 65
    0x244a02ea40300580710b5842d080240079035800300010006c950007a103810070b910300d20409101901c0d142010b40c076040800c065030301d0001c00340ca400323843c4580900c1c070f02078140c1d000da0b400181400c1c0c0d18070051929076481c04800c1c100405407403002e030102da80b03200322203280e400a01007201c80ca20440f90003108101c6607152049682c151120f2400c041c0d0b01c031601101006040d6a940c0c08590080c0c40741100250141d40c1c0d001144c42908640340d01c03006500d00300017003d03c00030f4a000304aa0000c00600c200002c501411a0300d5030207040281c1c411340c07a42e2084985807682c44d145c007121800700f0008824050840164800120300e4042030010510a81010707071000c50030410030140b03060707880200c805030800e030404034212803c3c0d0300200b50000c15902c403245040518680300050000046c424105590341424156132461103202420650403c600402c1c004c0350000c1c0c0c8801d69054540364503026a0310002005040050007140243c6c14075207406404400380d942000031218100d6070141d0507542c0603610b0001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 370198884 1250 370197634 370197643
    0x7050109050121110c1c0c170c101b0e01080c130f0b0408060106050a050901030504110916030c0c02210a0503180f190b03060a030b091b03 61
    0x150a000ca640d803201441598000d000f114102440c081c41c2074000042e5030910010fa0340d2511003640d407002e0000d0007641002051201880d0110592134800e2451200c0500500390182030034040c1c1040340051030740c0402950901121800d690000486d14424920440c00307005080041c282c00303980c8806600070400c1c5c0d000e005400810307801615400c3d0310340e0300e1604507400d9a0000c0800c02c1c5d100c203032410106060080e010401d01610041900680769420f010b1818542001030f0846000d2010501928441c036070b002d4111049603000f8a0017045545642c43c000782140004800d40d40d20900c100c00304000414005001c0c1c070011b4803603805000e08003d058058400c440e183c0340103904a1a903c2e0004803110000280c085980b00210072035454204070b4541e64215080018012480300301480c6c01071481c40c002c00c2c240780c5070714211101000c04030490341d0000c032400b0303a20a1003805000400090301503516040d880d801141c12080304040d51070000c040d00d032101c1d1025401c503600c2c01c500007044818140003a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 370200134 1250 370198884 370198889
    0x3050706350403050f0708030406050603010b150a21021813060b0706020703110d0909060b040501020a17090a0f05180621030f041d0901110f0f190f0e0307 68
    0x240da4951140c3d20708540c01e0f071040c1c0006820344801c020b6040041c4841005620582c02032100103118280710007010b0075103901819040c42580030400c603a82072000b103400c40d00080e40506041d001400340108680c0c440207040c010010703080c40815a52003008900c0c901411b01117040766070920540f24001c0e54811920315001c1d06400450500044002604941c01811018080d090800d81c20800c242d000b8600790814900ca40041c0c42410f007001415280d01901c0040c01404036030a04160400b00002d50352060058040c119140804d042000d40c15000f0450f11000c50250a4491207a01e40400b030a00410038420309000d55884890000c1c046040d903161400b03904001e00c43d4945251201d94561007200407005541035000c00c110300444400007000920041170320700807110030340c560030342c0d0b41c07107410002048000c09074100100304801380800360450304080711140920b0f4442c00c00d08580c14140c09000d0b132002071090041c80800985400801d401c00c907003650f545a81c0c001700c50400b807589682562 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 370201384 1250 370200134 370200227
    0x20a03030503100b0a0905210a080d060b07150510030209070c150e1e010f1401090e0a050d140903010606050c0d020a02180a0e0a060b010f0314150a03050706 69
    0x403a014031280c5041521108ca04040368210300103885010443c1e81045001c0c01c00310b40e01d01d000a440c40203007045001c0c0000030800b982c082410141a6195203108401100080c025107544100003045403d0031480c41000e0b68010f050f98020b4a00f00f1701c060900c10990302c06a4401c41003010551544500e405058054041d0310041c1001589c03410140c040900b510428003500e54075100304c00602400781c480c071281212400340c034807a154500050101110348040640c078141c1c2000e40800080b43e000500c520b0484801d20f4000e0056403909445034081c00340690b840d44c1075082c02400111940d110015207080040a804d0310070b8541800400d903900d000603500203402013986403d4481040022900b00d41c4922690004180424000840741c146a11414112201c5588507502070742544d00c1580645c1c036401a05082002c8805050195403070300009041517041e1294204415582d100c0640920040d50311604030358099440b004080c09550300d001d8158488008809607450009950041e4050040d21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 370202634 1250 370201384 370201397
    0x4091101031d060405071d130213091b080d02030a0f120e0d02010509060604060b040b0d020c07120b0c030c0306090903090339010206011401020a020a03030503100b0a 73
    0x5140154060186a808010341038100da2186149510600c4a58404d601c200080d0540c181401e450a2040051900006a50320300800700000c030b41e50701c201c80308400e4040b2441e45002e000c003010746000d0408104000e181990300c5820300c1010582d42c924400791814401510091824450201d81d00d003d1030f00d201c0005440c0e08101e0b100e160041310b0261030001d0504011850218100516103130800e03034606140141c0d528000c001542906001081d04040c003103809001c10343c0b81112040440c05240030b0607540c4400040c000c00c2004190307040310301c1c44c0d1544043d60100c0c1d540302100c2900c4040c002d400e0b105000c80e500010206402e107070480740700e00701100c120f80c15611414140103803504020001032041c44100302404c10369070100180c0e4080201c0b2203100c00d8550408031000c2003001e084c200c412001d2555005501c85a0b0013140145c1903c00742c220704255451090300403440e105003400c0c081e4010003030400200526510070011480727628080a101110f560303e065190b454030840c003005000444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 370203884 1250 370202634 370202663
    0x4060b04110304051501050906060a08130f0f050601080307020a0e06030703080d15091a060f0d06030b010e0708010510050c150c0c100b0d0f061503050102180409 71
    0x165211922451029000056400c1c900d0720000140c0d00a403020f951990040e49030200c000e880400c007602411303050303515620347e080010200d060b82c061510100203000c050400685031500c080c051034441c1760043c11182c01506e02c2d0508440000d0034036815501c41c05080000704d03124030000b045030010355000d00301510041c9840c1c110700500c54060725440e81400307003031000408104608050a600e409a16001403c1d1850700c1a00e903e003a4590b10200307680b401c01c0c103505600c6128001117608460252402c5da40c60301a202c1c0a09039100315104440034070700d4014040144003080001e54142c9010565880c1d00340ca238203a040e14900001d206035680041d1180c4d03081b182c144a94050500804ca800403951110610100300561050898a5944007500422000e0904208001422155403c08020000b84070f041d8045a000c400d03000014000303000e1200c46200f0000194490038001003013051b001042c40d100d140c064080d40c081c11690003c030f491010042d02500d4188038400266600c121640301d03040c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 370205134 1250 370203884 370203893
    0x3070315140d082d090a0f0b0f1c060f1401030212010501051c06140a0e0405032d0c060a0506030c01020a02190e070203040e0f070507060f0605060f070210021504 71
    0x80c44003100c40100310713080b80b01c03602d4002031402e5102d240740000c0243c3c0c0c40300c10f220240504845154000c1941c0021034004001d403107038034022910300c4014002ca0556440d6110805e17151360908035001b16101c2d26146002a81c0c1a0305581e41080d10b21406550040e1709207180114146c0c0207220100580e03040715401040158002c600802c50220348120045403e0458132401045039010362110b40b9103c0c03500680d0255103441d0079614094940180f0411070b600302901c8850f0f4a00070808034040104080d14070426088450741c0031249600700c2c0c407107259210a41e1103100e07100c25041d41c100100905000c041141c922700445c6220310b104069000700490f20542c2c080010703035100a0b5200b171409a142002054120304036100500c500708036001566030314540104003040f002e0041005466007201e406000a081d80f010032204203130741105c4003065101d1071200700d800400c100d600c110303031021001a841c0b074190b03480009000014001c48840340034508800d0166102d6030395082a1503490031300c20002d000107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 370206384 1250 370205134 370205137
    0x60a02090f0108042a03060b0301140a05040c0f14100203091503060402040b030f04050c030304050f01110f011505010905030606090112060b06070f1b05030d0c1703070315140d08 78
    0x2034062184000d4840a040020301d17840d01c3c2060503d03d05801881c14014805580154960600141c1c004c1000540e102649000403402030f01542985e502c8501040900091194040107090b80000b5000011703600c8107030305104411910b01500800400c42c1c0304001c81c0c0003000b60b581c0c2c45000f03460084c0707410030f0084440c403542c801050640d005a0900c03001c114071400a002e18810901e00011610358101401c0c02840c2c012191081882a80100014413441c0c540040e18011078400307003010715130f9001000c501e500300969090890718540c40c00b181d0303048110003000c03da401c03105d080c0c0754144a1922042819158030080f201e150300f0040c4800108038000d0100c201d400c4060081000254810b583c0380001e130701ba032106d501031710854080c18040c0e0511850910315000802d04d0000c04070301514000c04240c50f88042551042800f10b25103a01e0148070680482000600340c41d04820359a141c44c00002c5c006150b071032405100b000c0800c1d00811426030b101603810b0000d000a041002280c0c45a071034039001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 370207634 1250 370206384 370206391
    0x140709150201061a04030302060c070510020c1903350114060c060106120522080f04081e010e0d020307080a12020d2909160c0507090905060a02090f0108 67
    0x1159a00c00c80007038652040f030054442e481354070f001680c1d144d1031824000d282c240090041002d0709010000c00000500018200d42a084070308409612030007040305081c184a1144010f00c16140d16804445c00c055000c00e020080704005c5410340c0070340c4030b400010444180e818001f07088481c0c06030014041001108c00e43c00d11108010400d600e4550343e4000a070078183c1c01e80c884404036030a4291864108200e00403c2c0d03000700e841c912280c0c1c00030504400d072010805d200021700381400c00200d0a020003120030407130313000d8000309003240c4007031110701131490343c18480c0c200e07550f9254030b413640a8101c2c050104104001e200e49900450401e549620f408080354400c03a40d03402400003100c280200782580b40090014189411000a40200000340b100e0900c4171402003080001d0015000e007040d680d50b04010f13900403c00034401e20030408a02c03030030703240d0451000010b4420b1050308000640c01c0038640000598510a10944005484600c50b44d4140d0040310311260f80200c45022000d0554801c4544950 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 370208884 1250 370207634 370207637
    0x8030a05040c03120201050118090b060f12010207080309010e19080f1c0e0c10090e09070e01030b1509070c0209071403090a031e080105060a0210110d14070915 70
    0x1000e0f40c070358071035440d92008281da40160751140c0c010480b200700010340b200b81c0e880300c5c481480310309240e9803686400c8000405251040c600003a01e07416945440c102c900d07103690820000c40d581c030014201095140c2080313a00c841e1a6080c4180c03c1e96601000c584c2e1840d4044403c0c804041040655507580590071803a603091502e117061010132100440400031480d00d0015940001e26107441e040c86900b00248400000d014558030424980610391200109045484880c220102620342244a41c20b00c0d40036171002c0070482034040040b0501c258000c45c41e00030f8000146201c80416180c05000001d07100300c5130b1101058401c1300b400c01504142c404983e00074030f149480080818141e4448559410507940c020b09684a0601b40c82010340080c04030030541542c08070200d084641c2c550003082d0006c1409508e0080001082c840c001a000300945a50b61070b9090041c03101c1080441a1030440c0c1019000089160070200300f058812010b8405034005c00300e0b075079204030907400c01e03c5108003550408810720 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 370210134 1250 370208884 370208903
    0x1080406140f0601020606090f0118180501020901080a05041208091009080d15290706050106030b09010b122e0e0103030e011814060f0c0c0a060c08030a0504 69
    0x5040c072040c600d10a1152600d15051041820701400080c6482c42c01052540a455942c044c00030081c0100361950450341c0408003081142c0900712000041c00105100301480881d0300c00000070400103401400300b2050a9030380105c180d81e603421010589005039800f500d926081c40b0075441c0d00b4425040340c0c0d4801e10360002c40e011400d10040c40c41c2165003131402528018000316014030b6120550003a07039840421300c40007078138980c14030b0f00281000070b07e00850381c4002d18010b0120107080e0b03950709450006030099404c00c11507035519070150240c8510702d1990300c02d054101c00400d044810320195001d41c820a400c0202d80e5481c5c4d10303501a551901000d040c4080015070554a41210700074004005c2c1191940d000c4003549186000f90205140020b002d05008440b41120100d8000c183e0b840300325649400348a95840c42c043c08640d96204520040312010340019090006010020302e0340b16010082e03074400340d9030b40d5800040302c104c40b031100300504006003000072031500d209a030801c9800501032001207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 370211384 1250 370210134 370210151
    0x70303020912060a05060307031e0c1805150105070803070e06130902091206011203050a0e0907030b011d011b0c0b0a17010f050a060f20010e0c0f030c01080406 70
    0x44685078420302d84552580b00c40304000030f80c042805280c0d0032140907402001c045045990b56201040c036201000164000351424209006407050322600414034002c000d448002c0a50720003005e004100e400a4400503040c01e800134a5114030125a0480d81086d125825901c0d110801ca80302102022070990108050210607040000138680c90003c3c4050f410040c0c0d20030b036400070720048610090f5184a207400c214010032002c400300441010181d4140751441d6616903409058030700c1142030300f0039500602e0f001c00700314503d50140d00070704403040262190680c503180f00740f03a607a031501c030107071a01c1c0014084441c607102d40d004200e01d1480b15101781c0c1080805507e60841d45a1b5411411070100015854440342c80c0d6810541c201c5c0c0e000d0311810038261451810b05010901d9080c0c2880703a030b01081300c030800c0c2c8a02640b04456090440844c42400480c803071035220554040c00b00b035010691103006000d0400c82c90720b45a1181447d9071809400340044035102c07001505c14460081003500d000d81c454410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 370212634 1250 370211384 370211389
    0x80411030609030d14060303071b030b151f02070b0702030c0d0803180705030312151008090708010e10020c0703060216060f05040f29040503030a0c02031e0703030209 73
    0x2e1096150400441e03d82824101c084181d80f03a1041c07206100c46008103103c0d86803408001c84d0207050300310190900c0b0307441c9400c020310306d01465030000d40010090b009201c0003040b00d140445142c10704541d04c508500f00070659010301c100c0c050252016178064482001581e42d4500a80320b2039000174140d84900b441100843d044101d0131800325003c004c000300b0010040c050040e60028004400000d2141d070f8200303400302c2d5507407003580052540100c118000801c00c10260100e401c4090b8080d050700c1000c2e40d21000540240b0054a41c00d50b68054440003040d403110521402c00405003010062074a040c01000f6070001758040d0320b03948004d0155480220100f5800d00003050120160782d0358800d24100390411008480c1c460a109181c00c1c20581403001088020b80b8420381282c02c500001c4460500a108030686084544c0c03e000c2941c54808000c14000048055485241070000c00c1c08140310b40b5900f26203070310030402441c00c0c0d80c080c80034140a210400c0041c0c47c20790f21a0038014507282c0c04000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 370213884 1250 370212634 370212643
    0x30e06010f03051c09060305280f0e19150e070308130605070803041b150207080f060103080a08090a0204020f0a0e01030b1e0310020c0a110d03090608041103 69
    0x812001a80708007000c00400c14100719030741c0800003c1030700a800c0d0300041ca00806041d840d1040390105511440810f42900804450250000f203411031030500c1880e16660901500c200f941a50f4084d2400c1d60b00d4000c54408142040d01e68500300c4291000f641ca44c2e02c0240d2034003031900104186030740343c102030203018003008044d02441c080d10342c0c652214100c0d040154106500e03084402081410b009e910001000c0c20f0a89801c20391003810301d0444081c4800d03010700c401c4182d11140f04941d82c100b450101d00d0700401c2100580701040d05440f05524a202202e6680e5000c3c03000501e01c0004000399024148982c1d801a007159075501655111002500000d00b40d80201042103145807002581000044e0080c0340400e40d80d00a0805003c4c0e083c1c400001041040e03115040c0070001c00040f40f8040c107039020302652182c000c00c00b20840d00c0321801001c0550b10000100201c0c1c4a0404580e2800586080c9080001c0164540d030b03205481410603000303e43c0810003800490380c1c1b4441c079070a0405540c0600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 370215134 1250 370213884 370213889
    0x703022e14090d030908040e040813090204051f12051008060609060102031c0b030327031b0f040f05040602070c06050c0d0c02010c0c080606030d03150506031315020307080a05060d12030e0601 84
    0x202b015444881c400b034101e0b42c0714481da02807005144100b1040002d41c44461000c84100c1c0e401c03915010305180c190003618a4040466012242440c0904100b100ea80310b80c580c4041e203000d4412501c0c1903030740c2000e101c0008400c1c1d5005001d07034002d206000c1d0b80107401c68540320f52a00b030750300850290030a50200c1e10710703080305510703098a101c2d000c140b19203501c6081100803a468220010b02000c240c801c200800c114108000c0c40c0261205251406951a50b800001903520070343d104103d00e00e07003800d01400035000070f002140c00c80d14000340011132500c1034094410521004008d03000fa00c140c194182c03403e15205204074140f049801c500c0700070440341706009000307021341e50240c01075140800030503050400c01c91800080c1440c2801039661081c1058541040d50002d45a9940e6600c6414070007880c250b0030f200040110f5407580e03000c03603010311a0b00a50b0080c021900d03410400d4640e04404000d8a0b0111440c54000f0b010800701c501290700c0c0344500d42128183c1c03c0004220380040400e0f4113282098 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 370216384 1250 370215134 370215143
    0x80c04110f2b0902010e12010b0904060f060501090614030a0902030303040c0504061a07110a0513090c050103060302060d09060e011a030c03160b0703022e14090d030908040e04 77
    0x2c0407400082c00c801e4602e00314a8500c0700d803c1140c2402503002914a180c0c5903017050141d800301140c0c441d1f0710025408640c00b03182c02011b048692910340f4280303024002e640c40b406103179402c11400043d25406105803906850564841c0309450341103080d82c4001d0f400040001c0a80d649622164015840620046004601400007100c1d201d0800060006850f02580720021103540c98480c003420380c0080c1c0030749075080e07409442a0540c030311280009410310081d40010b940b000c1e003038400e01d070b41c4d55590303114100c038a121365a130065041d40d0f04019812a4000c0c4406500138000300160b01010140368400c1c00c40705e201d0310b00001c43d82e01254004e070071a041403042c409080c2c6040e00c60030b443c0c80c04014244451200320020501000c100004101e550b1261203a09644140801c508007014001e00030507171070300e10001c450040c10030002c010418001059000c01c080500c1c1104038807845059003061072041410f00011301140042c034000710000c01e80d0800c184c9040c2e400340008a42c0745070380244140101e024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 370217634 1250 370216384 370216417
    0xc060d020c062508091c08100605031603020304170c0109020325061803060f0203061309030f0c020109030c030b04150c020a110d0b0c1306020304080c04110f 69
    0x80401c0078607200b00544201c1c070002040012071098140c00b4050b0701e99032034a00d81003d030398943c9916940303020904031004080f0030b001c195564450780d00038401845000c100b070340701042a540e0b07082504c2d140300c203458240e40c0d038210201441d14a4000c0e0003c541045c41800302c80c0605203903408000d01138004250644460351a40003070350551508008034800031459040319030b0039003d811014020b43c00785120341018000c03251550100700390030010740d42c0250340050307061060100311806200294411130304a8450100d40d038010541c1c1c150b61040000d000e5142d12442022002550141c481c00003d0004904000c0e50147c0071002580c0307048040c00442c4138802645503801c0602e010b0f08410782c62010082803520b04041c0e40d0314503070b002aa80e2440c035089044079019655075004140c501072a0140030f0020340c0401d090041040c00540140403000c0c0000e0b0f10301e4450340b242c1040340c591003039204030344055108680403842c078509680901c08148110340c0039860144101c1144181e03400465041604007038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 370218884 1250 370217634 370217647
    0x4051c020f010e060c1e040909050a0201091d01061d04140403090e161d0301020c0601060e0a030503090402091f02030915091003090c05180412030213170c060d02 71
    0x400d020f030500142d05140078184916149403408400d01030700031000f4400341200340d161480c04401048401810302c5034014440043c440c10099038510000390100d00203104402c000030441a8554200164112441c01105507480c0c960125160000c0c00c82001c025020450707520420f0303403244203983ea04032070103408a10916190034094000302d080e90040440c6400c4101704800c0c98582804c202a120150030200082c1188011b43c164060760b031050f9540642c40050341000d090b1001910a040b02c00f42d40d202e50790740e5603017028072451014038030009010364024841e1aa9600d4103401410b145907000c1c02101582104c81c101c810503003030465170100581c20000c0d0402072401c0149541c3da181d04441012803400320038502080d480030b03206411004042c3d0340d0b030400081102c244106401041c1c024021404882302c4200c282c0000b909442c2205d01070043d0384040d400c1c40c024001c2c3e48814150348968800c5a190151280c08010b0240c80e04c0005e0207444020005a41c4010107020711700d440c00b1006803240b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 370220134 1250 370218884 370218913
    0x8150a030606150c050a06020a03061809021002010b1e0f060f12070f09030f03170106090e090c010c020607051606050c0c120c0409020a03170304020a090605090c0304051c02 76
    0x40e0050f10140400201c618980c0104000151104185030300100059450f909440110001e043c50f401081c0580c0318120099042c1c8656007014040d81d00850781d407400810590401d82c01c84400b00441da402c06054560f000f40f1100d088600181d10001401c0310750b0080503140021078580c054000714100c0301d408110041186030041c0c0242c0c0c00003540c02c010858070403c000c007900a01c05844014144102d5905440406120b15580c0500000300d4810f5210b0b0b585862000e0000d00250043ca07110119500c001140c8500020b1803946030360060b1100c0940382100e40910043c2e9000351700645072442030408105018401c602c1ba680104200da90b2680c880c10301042d418103044001590b144200e128403000040c0940100d0359035400901103c00291440c81840412110303007443e8405030407440e01c62501c1c14044001c1d002584218030841c0e11048150b21035112034201d031854003c03035800124000c0043c42030b003150340046803c14014421240045218000c00400c042820034000050700045140011003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 370221384 1250 370220134 370220159
    0x34140c1e030717030a0b0a061211070f0308040321060e0106170a0b03150f0406140103080313020a12031206090e0c041d0604030305150906010f08150a030606 69
    0xc0410014500e050002d0300c1c0e54002c0c0c80c18107802580350340004007040038054540c0c0501702e083c1010f080c400d2896560003002c0c0138216408100a007050030001164075407140c0f5000c031400d0b594007040300351420010342c404542c00c0030014421800e201051200c90842c40144161a585500d0b10390003040c000d05080407142c000e00186d00010500c0595041c518016401e2404541d100d94210400a140e24414000900d4100d02d0a40320800801050600c448001d480da00b09105500446040c051400c00046c1c1c0e0307141920910008c0c3c1400005c0c004034106400496803111194001030140e404641c58000d40311070449940000c80100d00d8050181c00304034030318000d200040c1a030000030000c0c0510a41c840b5102d8540001243c0704968401c80b86401c060654031100c542e03004502165101d00d030514014006210903155904801003003103040b0550b15145811910600060b5285102003000300820780d042d4101918507580c0b00500445441c1c00c0e111911910f00540c0112004103031540340031000c02c1007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 370222634 1250 370221384 370221433
    0x90224030402010215060603070f09090c02030d05070207060c080304020604030b0f0f06041a0f400209100806040e1b19051513120c08010534140c 64
    0x1a03030450b10801c4110f41d0341006480e80a1030600306182c84000c801d00450303040040f50010b4420340cdc03410000c002d4266001010f00703400b40c5003d20801640d114603006076902c0d01c1e61301c0784e00006120f015002001600ea03601654101d4400340c05281020380347e030340f00100308108954454401851004000300419444245a0800f42c2070310100710301c00d510081211100b0803a50014050000d2030b080b039030280c90300120602001c0045a1003259545504003581420060140110500d68010346401442d41580300b02e075989180188800201c48000c0d02c1032b190004000c08669001d47d8404800040c01020300c400303151451603400c400c02000c105010001052511344605c4000003071807406201a0700c500c150042c00c414184c0030704d91150482150081180203507006041d80c0d10f24048404208020000300d001684c1301400248026a613000c1d501c4071448454400c810f06080e86511001454140f4000080382c54691400398080780c07840c800c80140d540020795a50055100d552a05c481400d10a0b07442071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 370223884 1250 370222634 370222663
    0x6030c0f080606040501230c07060f140306010318060c08180a02061806070c06080604060b0c10110d02040f080d050703050a081003050a0f060e01020c0a060902240304020102 76
    0x210b041407070200780c8a010750300a040c14032039401c66024407049403488000c184200011055038070311076518902d41355101c030b1040307201140141c00e03030f045607034081d1040034244510341e04100e00b541c1d1441c00450252101011580320450a00102e10101c0c005004240a100f0700d51528892406c240c442102c42d52030f20f821200e2180c10640700080185d42e024110b40d450f102501001d008a25480b000a14501c1460401001e00c400420009001034008504030310a8104a07800c0101c241c1c3c40350958428070801d070340000302d500f000090f80b0240d07186a1007440020701c03054089040c4006040348000f00d91240e000030424840500c4e040140030010009a101c2c4182c0b440c2540c14040290307005840c038040c4040c0401071050580c0000c915030344081300344000710307081812200003010b182406040070003144010f80340f003418410b10311902d080500031290701d80c030701a008080110240e150700c001405c194800702d0740071000042c81c89080e103004100400051030600125541d091910000e49408401419600c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 370225134 1250 370223884 370223897
    0x806040213030605040614090106050f100215101e03060b060f040b09061e090415060c06020f0f040f06020f190b190c0c0627120207090606030c0f 64
    0x181c50181810107101201e41c80302001ca8103031110700c0e00300301030309500141804014182080040e0044150400c4044400648040b040034401600380007880701035206041c00340e4080364440000c03004c4040001d500c0f0130005415540281c6404034290356a201310728000054207420014010f00402d0f106210b00903c0407240107241030088620400d0500075482101124040481d50080c41d842d90000c6450808040c03200d080c03403079010090124181c20014150740500d10300040070b5000b800012080040d90b0640e1a0750404842e45e58558000c2e61252460f031102c510705000d80880030b4103d101030006801d8001000048905028009241a503062300c2c40010394000101041c1042500d41c1240c01310707801c01d1184015a0b2442d403002c0d031040b002955584100c1c9402050451240c2c05a59074074003070310903541071001a206a44154104a40040135a0480035040488e000121120005010030001d40191030300d40342d039520a1030440c0c000c0d03071005000c04d480d450340c1c070310260f484400c014400a2504000c2d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 370226384 1250 370225134 370225147
    0xc1205070803120c03070306090203010b07151512050c0901141306060804030c2f0f010212300901060918030c030806030c15120105090f1614030901060608060402 71
    0x1c3c0e21800040d00c00703080d00c2000808120620f100781c21031030140480440555a9523544c0d10116401d6100d11400c2e14065500c40100860300114000c555100c41d0744008004080c1c10080002e80c81900114100e8007031255040c2010240c440b0003450b402400e580c11200c15800c00842402502008607410410341840c055003031107145d4000304900c0e08a60903151204404000d4074100000030000d201540303c86041c2c040302c0e02041501000040c40c0c280076101a0800380d0018016a41c07409121000780851406018503120f48046103146005111146120500d40c00f0548104142c40b0060380c41200d50f03516100306001080c6039004030440100040d00400c050601d949005014820000300241049410004100e09990410064520004c0207100480d030940200500445a1110031440c200402020000800c6c1c50a070800502c1514021034019807a03440c05500068800c032080020280040c2108000c100c40c20031000c2c600c03c90a4900010b21503082c410b001d800001300400d0540b04a0041105 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 370227634 1250 370226384 370226407
    0xa060b0306071112090a08010e0d021e0c040b0f0d140118050c040510080d1d030106230a0e07030b18070f050c1c080109050a021314010c0c1205070803 66
    0x1d604c02c10100c810720544416100c40002c01c1002c55034013101c0251301340b0005074000200810300d103454080d107808440016001c003c001307607548a25005218581c000704001c4490342800d4200c0341c070a2b60000c0000e524001b6410025407403603401c82044c6d800001d0a168520142d000340f10f40e041e000c603190707502824070032180d40302903489210921a41c043c60310750300450800102860400f002c2c10a01054402d17117520204010401588102000360116210b40005114241840b1741c806840421000640c03806100c901c0d2800c000e0310390386c1c1581209410308006075400e070203015a40185221f503030200794031111200b04001ca4158084040c0320100c02814454008e40240c010400b4a400c0d00308182c540c00203101060801789001d518151b219034044550a00c00e5000024034181d030030003e010011900c403042014224003441050020a628100c000d2080ca0603840c05114040320501d40b400c0c1c0342c0c0e9580c3c0c2d1400ca0703041d1944a0505811000c190408000c0c2c00d100f20f001810380c0000550824500545 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 370228884 1250 370227634 370227643
    0x5120703080a140408070203340f08030403080c0307050613050d08070f0e120d0305010e090105060f0906030c0a1e0e06090708040519050705131a0609010306080a060b03060711 77
    0x1004041c4c1707600107100310440d2424002d0411101031032a00d445503691003801004018030051400703400c01c81a00d0003041d075404c0c482da08c0d020f40382c41c8401981414119075810150b548a84000713011403006200410002ea4100440c904c18000d014100010082a03d0501c0c90400c614082c081845025410802c01552050106811761080d11385442250041c501090000c01040007004c034a0159000418560ba09604910f04941d50041c090500c0d5603002190790880706c096031140c0d8002e602141045883c94031070035098001c10010141c1303200c2d00c1c0c03600c0010400400707940045800c6102203820804c90940b0403100008041c52000a11076107024000110b10190092800080c0310200703022030107101c020000c1c00d9060000c0a16039207100c190f81040d50b610140351040500c80c52140000c080e41c0c5240c1e001d911a9110841c1100214900960402019810107080a41015070316080054070f02e800b082000511400380400103034800d004028182000360041034030040c0f103020212140b80180024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 370230134 1250 370228884 370228891
    0x60203190513030b180c03060f040803041e030e120102120f04060e0a0305070203010501051008040308061212030f010501050405030d1d060a0f020f0609250305120703080a14 76
    0x6002035a4900758500b15440381203a410240040d46142c0801070100490460f40e00e05a450008a484a000c2c0004040ea01c0c0c0c6c0032185409003c0b000000b0a0005a0b0440510b400500c1a41c0000d40a4000749030a099200d80280550005200c0c0f0500c84081c200076490a0a00b40e90400a61a110041030f42425060b0007034505a01b042401001505001c4258013902c1d40c40084025144500c02c5030030f004103280c200c440160320179441c040c0009400c0c0b9195450494010064a601c40c095840d500d003500d488000414440d00600b41281c9800c995001344a1611805da120a0039a00e900300240542902c0c7c505030802c42c14410100001e00c1955400550028a8409480c1103022030031602a03540034207001c140401c1c1c01100c0841c503010513913080416084101404d42c21036101c512141e810b1640e1300c1055440f14000d03006034034407029a10b0070951080100f000f0403001e5582c0c40d900d661f01880c0c01e90803c220250101d0204990b020594484122074111141c5e200c140040a010041440c40103000b5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 370231384 1250 370230134 370230137
    0x10f050f041a071d0d12050309070801020301030b07030b01111f0b0301060501020307081309050a0207031b0818180405010e07140a06120f0c02070914041a07230d0606020319 76
    0x4130301031815030340d6912081300c0c0a03901400d842888000040d001d0310311740003500d240b91513019256004c90302110500c01d8904072a040407040e1100d0b142c8a4055000304400c000c203a04206030ba0507800060801040f41c01e98059488a4031440c10400d111620102c80505070391a11990402d0020405a83c0c0002994074a5411510066842c895488050741000c070b154440c841315410003080000300fa4095001d0050140a5211423180c1e8545040750b40a0304a0440300500c441024011058501d5001e00580b1480e40058500c4001a403041c81841c91400300300e5040301c2c2a911107104403900d200038040040180b40f42031165115186860000382c40104500510302003056545940100340344e26000700741e98180f9260100008040c84000a455140c1400748410032801c001011407c0700c0542d100e02d104035040300005001c0080b0a00c0308600040142c00032081180c880180b181c004521146101c004400b00100d55580107448140b10076117900740c9c0480103542060002d0000100c00b01d50064807031205 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 370232634 1250 370231384 370231427
    0x3011b21060e0106081911072a031704090f090210020607020a03080c1b010912052104050a020a0f030c0f150e01030609020d1a090105031e010f050f041a07 68
    0x441e080306d42070220808004020360700b01481c864652019400074182e15000e00e40e02038000004060340307644140032074030081451060500420110700220f0442201c0d280810040c0e2500c2c0c1d44000e0301050741d0070b00f04400c072220307940c202c00c0d0118544070f01c1e05841000c850010308214901031101a444400e05000901400b185070006202e62010380100c5541411181c51000d1844103501494002c00031000111420380700307020074922041c0035409480e6403500700e41d010301c6240010007807070f151508040c2040341d0324881da48500c00181d50f0740070000080e100c1c14409c01c400c1451414110408011580000100082c0302c0050000940240200e10504a9428864905850000102c0040174650300140020788045040304521419412584d25071000d04010444518141c0c10004040002e10071158941e00541e42030079a40c0c0c82d001d40402410b541400024840031210340b0a081e10012601d400c001505031080204000c020109442610848440d007810f0f458801c0014010f10480c01c040c1081051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 370233884 1250 370232634 370232641
    0x140c0a0b030727030605070f0206060a0605220b0715091a190c091a0a0512070c0c060807021605090619030503040b030709060e03190203011b21060e010608 68
    0x120040140314194a10709081419996810310100421042d0303020360004123040324221010740300113000d60248000410031a081071920500b5182e640c0817030030100c1002110600148003200406401c80240107080d9185e65039038881c6001c010045080080a21107880e05120102165685e840f42d400300c01004004180d685510f28401d8100c0707030950040c800203040c4183c0b6800954420f4501c0704454002d900e048400c1e41500075010701e0b0007034800f56400504184224404a002e004125030003501038206650b0850154440030301d03c0840740c00c5003002c9050a01889400386d81084444024250310b001100d80c2c0c0d0611002420502d0b000e01540d10980344144400e0101d040c1046d1600110350045c1225a00e42c1c4d03d11155026400480d001000300b0108400080c000d4000da100d402c64001c0140036110f007100c1c41c203503040011907101c41070760107650303a10004c0b04541c05140703607034207041c015107a0103104010f080f03219500b4228802400030300c506202080161000f1a40340074103503001ea00b04600d6942c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 370235134 1250 370233884 370233917
    0x207050a2102040203070509040516020708030301030b1f09091101120e06010311030c0d050705010806010f022a0402130306051006020715020102130b0405210c040e010b030109140c0a0b0307 83
    0x3d001003d59200342b801050104100d02d00b01140c449401d0360b0240e030380b1250343e004070350303100d0100b4880544000301a0b0b0020790070214001030340003903400031600480d61b25111004d4804488100078101c070342150384a402078007580c20160080b04d04c1035004062240e4271102c0802e545805062000501d1490759805480310fa039800d010380c543c0c912018107584002c10060411035600c45941c400c06002c111020041400743d4420304d02d030504000b441d00100b0420b000390455405000da18420002c608550018200c4199254001060700740181d00000d4222800c608018044800c05400c103d091070a4ac6410050385030003241c910101c80080410350300300800d0303000590183c454590601c1d02c84455240102d1007039a80c90240c03040d15400c0d9038034840c071400001c100080404c0c442d42c5030f56035840040d900b803032441c0540204840c945000008281201040d0100e82912503a0004841281c02806070300d401420402c10200200411200700410a01c0c0490100c0588400390050040040d085080e1001d41c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 370236384 1250 370235134 370235137
    0xa0305030d0f111201090c02030903030403030f090512061b18010815090403050406020d0504241707110c0405060108010b0c0703050706080403020d032018100207050a21020402030705 80
    0x788800031a40c0d5000c4c613541c11800c1800c24001d2040007031412030080141c4c1e2002080d111403150113001185058150348094800c680e075220241c0c2082088400403505868207042d440340308103440b0041100f410b02c0403142072031103500101080d90581c14400205001541d01500544a100b82030940c1a41c481030701500c400c5444c10811904203200c001400200b66000c4000c0c07040350500d83c240c84640c4a00801102c0503c01c174815104280d044145e8210201c07051600282c03078020906010071403001341500c1c4800c240c000c81c1c10101184411030320441090741440070241c2c81104442c01c1190b46804000a004001d044c01411450000810702c807840140410000c4041c0d81c000701128007190b520f00c4002d0500070100d400320010f0003404450100d06029000d0301040f018259107001c1c105080a5242d10b6030781100114080c014010041c1501a480702d00c1c6034087c000c00750340a0701d816402c00050100901090740010b00201708001e803030b240d06840b150305c0c80c080766041368056900c0d152102d00311050b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 370237634 1250 370236384 370236401
    0x172802040b07050705030706110303011a12010602070f0b0309070e041a040503092815090e010b0903010c080708070c0c0308270612040b07020708070305010204140a0305030d0f 77
    0x1d0350001e000e0040c84800122441120340031411118010340f280d00c220384202e403078890000030764000d0005001c50402000e8407070068041041c0182850f820b100d444004030b6080c0c1c04000580c00070142840001c03d9038107014040cac4950000303c3d241d4105022815501d00441c4100b0302c6422062000c40e0800c210b00b680c3d20800d0342c82e405141410705081c00c01948903400034406038411a0084031029804144a0081100341c4001540c00c0c2810324041c2003800c900d407043c1d20310301004001e002c0030911048800429001c0c0c1083d81c0e40381d8644100078189801c403140800300c203082c0000c0008106032a039100000b1540b00b05149040c2446600d586080321004085400042199402003090343d886110500c01e42c820001ca5503c0c1107910769031400303000d1207110f001841e9201001c0c10000401150503030b00850781024485c4110388940b03985001003820618150400c0354140d400050401c00d02440c40152000ca100489050f40ea41c0c0c45e50f41d4842c1d89100d041980120b582e121503484141504603071000d40c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 370238884 1250 370237634 370237649
    0x902061602010e0303070c0608060a03050c04090204182603040b04120507080424030615081806010b0a030b040b0f01080a1b0e090901090206040522020a0e0117280204 73
    0x1140c803107600c0e0041c07d07807095004040010703040302c0004480c2c3c901400700d00101c030341180192050309070800c1031102800704c0501c140d8000340c130b540500c200e0700c6440b00f403000c50500070000440d0042403d4944459039011a11761805d031607041c010f010102c0c0c071500c41a600320341c0c0a0700c0801e00c203c030842c05585c07900560130f003e00071300c2c00801c0000d224001e1206151028080304e402c3c055110a64805500301e50480c003400102e04001000b810140303001c1e0302d00c6a040445030461041c1440d40d400324500d0034200f40c002e10901c05011600c1c40c51142c05008601000800b200c0501084640401041803034180300d080074104890b180110301001c9040e0710a1021220388000135094001200c80544030340c10161501e402030308401d00203200808184958070b880740d401401103203014038190800c800b20518047c039209074521300480c2400202507100601003800540c54440e1210180710000d40f4002c0441e03200406569a50300b04403500c1020000003c5201461910840d1b4002d404084002401113421400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 370240134 1250 370238884 370238887
    0x9010f0203040c0e091c030c0c0501110720010816120c0e031b03060103030e1203160c140315100305070e010e06060a0c0618150605010e01030902061602010e0303 71
    0x700f40b0043e01c40600940d0100e020342e50407500e0b450085566200d40088004000380e084000e5042d1910075046038001420034904140485c5007a00c8980c2110f42c5814900119000004c4001c208100c1c03000601c1800316640080140141040000e07042104c0101707500c0c011110181441c2403039000e07940c0e0f00c031840760440c420040100b44003009818a840b40704024441c0c0b1810b0b91b2619200c03403010b10010700740300103070241c038240e40307941c2d000e03140b001c4000407613a40301441d1001001651800c00191044a050042004082149082103012000c943e040205146941e515540c029100015018403c1c400625001c1c55641e4211a50010303440a0b00014814080c3c1000014448600c164041c10307203694140421690320f4690400c8580c1c864881030f800480c509995480c08160581e1050041510700340b9442050409a0340e860080c0c001c0144160f43c140d500c3c82c0c18002540c2c401d00710303a0040820301782006000303400c1d00017030200d025031a0251000c84844030300d030045900c6480310301700c552400380840c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 370241384 1250 370240134 370240141
    0x3020f0a02010501030b1518090307080a050301050f0a0509060d05100e0309090a0507170a060b04030303090b0a0513020f04060302060c1c02071a030a060f06020a110a03080306060309010f0203 84
    0x1d020b03110a05c02560882444008541e00441c1692032041c2d8002c01855000c40c0b8545202424000c4030050040f01103020a00454010480c440001c20004001e40d84150303607581000204071031100b809082074020700c903880b001c0c13000382c8030009690703040503044a1021907000c0526043e49081e43d8091050307a100d003400d004100650001000c0c003094101114014100e96030300040204403034080380c001000802400708080d07880c61511900c0d410200080001c03d2041d00c88a49a0155219600440001c2d82e5004000140400a00060f40041450109101c1c03420305040d661020000590040d01c2000000d0403083d0b0f55507136a0242000350341c05403009483d01e22080009840d003110001c00c80104508140d6580c4c058804554a400c0c0c6011058461011450501001d4076030402055400c0f1680d5821005c02c0032005120780000030b2000798000c040708003542c50504003400326400744c140120341034141440066140c0302940d500c090140d50403601c1c2daa903200030b0342c090031148040313254581c400400d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 370242634 1250 370241384 370241387
    0x20f040c09061b03020c01120608060708012607090f020c011a03060a0c08071b0c03061e060b070204050c160803071710091802040f0e010606050f0a0f03020f0a 70
    0x41e00407903609440d0030f450803d250071840c3e0010403036000100140c100e52241c05080d03008455219140c81001000258152074030340c00d41c03802c80141e618501089100780104403030030304400c40c80304024140d0100c1c44031113440c7c8a00742d51000c1c9801038080a684440c64050184069815a07228039071080c000e0000c003240408000c0c001c0d40080255000380194400a80003e56a005940f9079800594031208260707079009080301c0e5080983c801001d908131507401d0b0800f29507803420070300c05035001d020700040c4420b0040e0ba460085c0703402018003e11a0401900b00311003038009007560041601624003003081c1e907503040321141c01d220310300c00c0045c00200c240c0b134041401070f5030015500c01c0e155030320740d45a6001110b02800032504101c40c0410800038860f4280610265600b011500300c0040d14080103001450b070002d4103507500c040311000c0c1195101c10010581c0b00c05d01800c0010082424414500103c01c5450303201449030030950014000813150039902c3e18401ea040b201035200c0440c40070744030003070742030b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 370243884 1250 370242634 370242647
    0x705061c020415030c1106130c1d0f060a030b011205030c0718060501080402060d0b03010b031b1e0310050c0712050c0d090f030303051f03290403090b07020f040c 71
    0x504500291400c020201c81c0340c0603010b0070002c1200300700200129618008c402c014805c40200c01c81d580441c00200050199000024980000e656140c036440307450841b0146150140040c142071260012041c2000400c0d80b9900107415102c0104034640400e029080c0145035224400000661344a009000941407101031074140c0c40000c981c10900c030303140d56400112465101a00d02a51251007008003400c0058998490101100040d001240d140c0704200000e00340040f54008d81c48000c0c0d80c00001442e803400e071032074011407c11010665020b00700c02011a580d0316038000c880221540c2d803804a1090755928040c0d551941c1d00443da00e855001180c2d0050103074200c002d030b0500500c10485d844c000c00340a1000b1205842e07515402d003e81500d551000c4010707103c0030742134000440d0b07102d005240801c9040059000f550040111143c01c03900000015000440c01c501559000c1c2a14280400a030740415a1000c1300da6555041d51501154000544203040c0c1d12111a0700510703004080200540202 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 370245134 1250 370243884 370243919
    0xc0c010c0302040e0c0c070e0138070308040f0c120b0f011406070c051306150309020604051e09240102070f03230d03020403061802030705061c0204 65
    0x40092001040006054041e40241d00404426000f004c002a0107049860054601310a011048a01d02d5036150403041051000fa00000141c128407040c04041c140254024184035518081440c00704510405034001d5008240d4028104154903000c2014444030072081c01089030003411150030155a24000c0c0503040c46002d048030f00c1800840010038040d00700225a041f555152005082d00d030b50b00b8100096a80004000c80c1c010034188070205082e22040002c07004245040d400088190515003907848045550b1041c0c020035040510200041e1a0301c020b0300e003141c00c180d485c40b284105030a0b40f034080c0b410302640140c03c640440100b0448046102903000b120800d44040340211031351100482e01c8154601810600840c1c0303030810030004041d0b0015001c0d064100d12000010070510b07403054140005202c10b103000a1300032401f072041c860b4503c60720002e00c44020440e0040c00480c5d000c41d881c0c52007842180d100e4040401d0311070315452040006894100044000c541c0c407600d488000c45888040f1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 370246384 1250 370245134 370245157
    0x7060e0a060804030c06110d060308070b09070b180a080f0a0201080106020a020a182903160e0a1109030109051c0323040503090d05011d0613080309150c 67
    0xc0009a264000e1440600403a05583c0340c070b1020b000c40e103845001e080900381581e00c3e0314081040341000c582c03500c1000d01442c440e002c07044d03803800582800142d504000c0c0c610500343d044a0000c02c219004507003111841e0480b1007000c0c0c008001d60000407000d19240d030024585000b1498008042e01000c03821741c1d4444e100b601c6088035640c032104100d954400e0803500a4008000d41414041001c42c4030b800d442800c10000b000c90501341d00d01d00c40b07690001600c00840800c80030601086186020301040d00310800703203070f2410482454050081c10010024041c080016a00c2c1c1440d00d41e0a526800c4900b46100a4001c2c00025943e10f401641d41012401d01441034100c00340c14622184a40101d18903440d111301001460441c0152000702484083c1c401c4840340300401030102c8035290749013501c3c034941c020000050340b180d800c640301c85c20810010015210342c00160070030240d58600408080c1c0070b90096502074490b0b0302e01030b14910300b030680310b0f640b003051456508020500004800905122528 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 370247634 1250 370246384 370246399
    0x41509150e01110408121308030c030c060a05042a032001030e0f0c1c050706030509060a0b01050a0309030e09090604021c171c0f060602010b030c0319080c07060e 71
    0x42e0003c0d2201d80c0298000c0b0070403600110791115819802c1405040755041a2280d040f540c0c3d40d51039007a2640c0c0c046039101c03000d0740010038007501002042c000540c0c80b2111207002d0040b0f05e0555107400001040a48100c103806101d50980e0081410a00034000343d9070080d04041e20000f540e2102c0c0d00092104c03550750019007016100c290070880450704644515842008250508900c0b041141080500409002c595810005c6501040c01000450010019918006101e0502c00c10040c28100d00400c03514035182090440704446e40d10904490854980307260025040b40c041c074045404541c510316803640b00303209106010383d031b09000c01c06501441c421030302030954080300c1040c100c441c500c49402400c0392010f10340d000f0b1f032004000001c100c1c40b00c0803856000e0a00c480440541114401d0102c442c0301c9540300b00910900d5024440c0c0c81c203060303040300142100e810b110006079843c10000603802d4411001000c0c00204407040c420b07545400380e018151050551500f10042c1001c88e081c0080b032003003c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 370248884 1250 370247634 370247651
    0xe09090106080c0d150b061c050a0b060a080412030e010f02130e0408040b0a0509060d0b090604060f140a050901030b0a1a061b07050a030f1203020901020303041509150e01 75
    0x1400d41074000f40c550300038040c5c0303080b414005035240146115250a03400a03170400488180350005881e09012100340b180000706030500c00309400841c0e40c4000c0d524012103007003100e11001c503000501140e011341d0200702c81c81d0405209504038058442181009025805e21041050084c03264014010190201581c0400f10f0741d11038039005882c2d4141c0f00941040340402c0140b00c40754403c00241070365083c03401c1c80f0389804000c01c00726603243c0c00051040700c007603681c0408620b5490200f10780b51708040219820700c0031398100020100095110701c1007010131a02c915942d601030b05c80d200f030200100f200601c54034070b541c7d403400c00c2c4210382ca04035811800c80d80b90a00c0308400540072003e1004c0040003034401401c2600c4060034400c2c0448000c8070715241d1184640010f200e543d10340d035400117148100040303110200e980c6080e91039144005806001e042c014011140c803641d0003c103480e4400c0d00030346c42102800c40054440c00400c0b84690241c188100340c142130000607001e400504050f0b0311080200078040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 370250134 1250 370248884 370248889
    0x5010b0604230a030f050f01060b0307091e05090c0c0606010c17071505190e060114100311181309152705060907090504210e09090106080c 61
    0x803450181c1072100c0901001d407071070302c80d10340154018507002804121070940c482d142d01c00c0007045603004076400e50109104001c12a000e015000042c0b01300140d01d0b08504208001402c4c41001d4041c0d03a0170a00450408403208002521400081c40702070110f4205003813000001440ba0f00085641c10340c0d1140c040400c2c615441007040c1c005040e0400c0706108890007143d088410b0368400c08090300c4482d580c001851010200b44240c500a107440c81c1141c45140b001c0c0300031029900d064040c0c00c9660032800041100305170045250ac61601c00315941c28208250b8031045e4000c0101244880c0d031140701055804002032000e50305501c03980200c0703401c600c103c2d2003207410050710007800d40200300c81c0d56003002103403041c0d058108000030324115000a00b17010344000e41c0980c4071000c16080d96503a01103c10300c9000c5c0400d0001001078001e0080501c903c0c6882d45074800e92a400301142c021124205030b11151446c40390000c20008a80100030f8411800d001c003d00b8041d00c814010205603018000300d440c003a1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 370251384 1250 370250134 370250137
    0x8120708070e1516150b010318020f060a050f0a08040b0c0a020d030b030f01050903030f0112080306060702010306050415180e0604111c08040f061d041a1201020705010b06 75
    0xc0380140010000c0f03ca04034116190707000203031a103032004c040f0710703074030340003412288407100c40e840c98640003d01d035406140010300740d0b04100042c8141600ea80013003070150300c2e0301a00108100d0192003c1d580c408071603804032910710070303011003010402001c1480b9824650000d005401503002d128000100e4171941a5441d0314800c2c14003903030140c2d02001129403120b00a810a100d000340040548010003040303041c042c2036580072110480207402c00420407400c06000b0000e140034000028440360241c10903a669402071002070100746c49040041140011a07100703401503009494040d00a0161000c02c41d003500c4818410701401001c07004000c010300c0002403070710601e00459003410042996446940300e84082c0d4000f050307a1908140e450106000ca0b000140c0d24480841c41004015a281d02d0a418501a80041c1d00b2910402010070050040c1401031104074010080855000804e484040e19401109080301c0b00160030010709050621005410b41c081c181c4140200003e01c03010b20030f4030401003103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 370252634 1250 370251384 370251407
    0x50105060108070503070f0207080d1e0905150d02090a060e030d0e01140c03070615030c08150606090f03100f14010614030702100504080a1206032004090812070807 72
    0x381c005d00006881c80e100d01003460307030394406005991500341c0300c91031181440004400040031400f140c140720305120580ca42134032440c4203407401c1141581410001917600c60000c503d41003444011540c88a0006507604607654850b00400072840c45a541c4009001250f03101e00543c0310380903040e0300b180c54034060900100e111034140d540c1c0405007101358071013026410490041343d2610083c000c031030018441c1e11640703480185100ca240d0a071440c0d0710701400d600700c0c0381d0045081c80d00804010000900983c0c2400d402020840d151611080000081415001c0003184070f5454458030390a07000f485910f0f0300007010010440824131079500c140c1421800702c0702c284100703000205010001c00c0c05001040141d40c21406a206880021612548240c25140103803015142d4400009028403055008a51045030174241101441414915240d031641d088003070480c44104006804007140380d035115400070001c0e6910084440e01c2d005000e5250f4000141120300f0360205d0b540c64040703003120b07000c0c0242460 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 370253884 1250 370252634 370252637
    0x7090506030a0c020c0604061106011d182a0406170303060405130c0e160f0905060c030f03010b12010f1a090d0519331a0d05060405010506010807 64
    0x80c5032618038000700104240c00c030600850107010000c5d200c035510385c00104010a001ea8130002100c800c3c001150038104180d0100006500f12621000c107040d210551030b81c030505400c0600d82903650001e006060049101440c3c03042c841c07046050043c1c05520f0542603240200f46c07010040940c032002c24840c443c1d030342d180100d102c0d407041c40001c1091426402007588076081c1e840003002e5072003641d1902040e10b01904200e4416800e0020402d41d00030300b81140c0c2b04141c10b450050141410000e02a0141140740035260240340c000410390308040d010412558582c21b105199650396035102d107152540d803c006211004c8001d00c0d800003c0000040d55460151038003a800700810402d03001e44000da5901502d0100e400044040ca450701140d414001e62119001a500100089190b840d00800e001d4010907800f10303092114a20251070200854400100c2c425090002000625403c6480d03a00003945010b55100003075190707a40c00c1020210f581405180314100920aa8582100649402c0d038102c50f080b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 370255134 1250 370253884 370253887
    0x1d010c0903032f0a0f1509031d121b041505030d051809150301061a0f07140a0c091b0509100306051504080c0d05030316020f150f07090506 61
    0x41901e007100240f00440500c1a00715007201491034a000d040c422007070405d64074180710f0900102400981034108040391101d5008000d040229a0003a181c80c40310701d2450a914230f1182101407949a40c0c8101c90805002003c68803030b48082c500480a0303001b040b0044d4042c40c100300500b420442d84811001c2607a03801800b07041c09030111001150541c11400ba045100c280170400c001581d00d9401c0b03030034000c940c074000b0322181c02c1c2c880082c5420341d52558406d0300c0d120701d4030001c0c00000c8040c00503100c09210030640103544403000c3c105640305001141212109000307000b0041e0800c92511a202c0884111040034050101512a00c8440008150400700070032400c200c80e602510348084021400403090030001100380c2c031840802c185040316442c082503907070000b0f0280104041080302c0008440e0440b00c22034161400d54500f0385900002d0000d9803091001002c84005600030700103040e01000302d000703e4038065100a1405007032441036442d071071021602e101113400d0505c181c0580341610005000d1030b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 370256384 1250 370255134 370255157
    0x11e09021f05040b0c01090f150b03060408220302030d0801080d09080601030623010608060f120c0603061807020a030e0d02030a0201140d02070f020f090403090e0411041d010c090303 80
    0xc52096001445c85c2d0069544c030f0310903900085440031030400c0280a454814025002070103600101d0f50081940b52103640b1003020400095503c1007110140506500321400c440045050301101500b03a400095150042d07400445007141c0c4807103034038125002d100480c2e14110f084002a80c002c0c0250103044a1a000340d0014404141143c0000000602c251a081c48004001c2402e00142401381c0140d80054154006c1c02403d24140501602400c000c403103031681d468408444603600c054a542d018003901d8081f000801c543d548031240200c0301407400026650740b40c9228000d48500ca0048104d0204044298401260400c4140081c940782d014008204010546c0c0040d03405800e8282c44c00442c07081000141201d80890014090452040c1807144c80111380340304109440c2c0000c000a17010310178400400021a80c4506420110b500d144074072000f40c5c403542460007801d04101c0b14941c1013820300c0c800c1406c1c002030103124034124845400800c000f004040e802c8031841411b00c4058000f840c910b070350 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 370257634 1250 370256384 370256399
    0xc0603070f0c020a1e1a041206051f09090309090b010c0318051e090105040203040209161e0c1202121c180c06082203080702011e09021f0504 62
    0x742c80e0500043c43c900100755100c901400c1c8046800000305011482c003810000210300c5241d1032020024242040e04003800c0001c503c0350310741c030790b078025205a4840c000b049002c00c0d0f00d9030300000070300490511018580c84501c41009428120700440c000f5104810004c5e8400d0359102707280d421907050b5103d1450360b05a80301115007146607110f0308902d914500001450741e070383c82c118550f040398407080d0724050011394081082c0642c0580c8018020f0f4010800c0000680d40c409866030301803407290001004600007941151100c24035010050180c01c1101e40703201180e000038840340325a1080c00c45142d540a40e90b42203031101024400d01d80070810512002c00e654511103c8056182c0c3d070340030700081071440c450100e2003d40488078107840100d0f20100610815510820b030651107040001030034000522441454241008048054100319250f0041a103040c801e400c610a601e60fa943c000f0900100ca80c645001441d01003401c0b84a681c04c407281000101c0402c1c00625495129100c030340c14140f03031800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 370258884 1250 370257634 370257647
    0x80402120312041115070f1a090c010306080c09010303050d06080a08280516021c06020301170a02030c01050c01021e030106020705010201110d0b0303040e0f06090105031f1a0301050f04050c0603070f 87
    0x18115038008d00d002d640080144038141861042c4070306401045142d200e10009401c81c3e846070408e002c2ca402c0a041d000485e03d8982c0000c2c110f990501d04140e03940c0d000d22848000301119041080d65004680051050081c000090815a1a81d2a80b20000610500c50b60508040c0002c2d040c0410ba05002107400004d80110346201d543c0040c1407009091138040d1010046507031078004542042c2e0200051146418402c01202040c02440091200c030901f03400180c0e07510503100125041210000b08622003450030b40568a15106a0b041500c8101c910176040640360024081e1703d0040c40380e10380c00102907205028140c00007482440c01480c014003014500c2c003400d203480c1d42c6901444100000034071208170040c3d00d840b03030440102100e084c0c1800d004000c282041a40034500c20f52140f03505e40c00040810f040e800000f086482c0002e03074520303808450040c1d0340c150080103505501c1c100421034400002ca24880c1701c0c0e40328a00740d410120740310741003000d0b502064800c1c01c00542d005400c50032683c010340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 370260134 1250 370258884 370258913
    0x3060711011119110a15050c0d0e0d14040e15010c02120102041a270310060b180d080301090b2214061f08040212031204111507 56
    0xc0c004120b51081d0066101e550344140d1059050002001e046080c8070350000020550000300400f500c4e01c03c0e07154545c4812024502849400303903a403100130806005800003240c03440000341005005600c0d9400c9015260341b582e01c40d03030000c120407007803003030300c0601040488003544c10140c038009450721400200c5003030f01b08004105061045101c420000f5941e80c42200c0442d00781d507000940e542c1e05141a031211901444e10b94520340d0030500450600c011411010f2545100540c0c1007010a41c65000092800c07500348000340c0ba96107030160200f03142e00100001c041c081450001c10421401c1101840b81003074168002816050081c00103200c440d5180c0c0242c940e6040c01006d40c14001a000900564081036100d025429556501104807a616104801e070740802e080302c2c108070361100c0300e1a1003c080f140942c0b82c410061408001411561425020080c12406204503a145d410030075448015160a0b40d041c1c82240e46482ea902103845c000c00c1810004540c60440e500f00403060703680940102144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 370261384 1250 370260134 370260167
    0x11070620010b090112170405090402010c03030908030901140108030f040e040503040b0f040801050906060303180619030522050d0c0312050f0a150f150504150906030c0e030607 77
    0x488100b01c15541d240c01c002d0103013030480c00c801d030303441001c0c07070402d1440c1c061801d22881b0f014180003c01c12551102d9405a1090302130a04600080d0a03250890081c1525100146129404003d01c001f2080551080102200998101d100c0343d8803440915600d02a6060704040c14108120a020144003880071940040c4240c3c12039052544a440481c860307040108015121203020a041001c00001d0040c180c002031460003518003170400030702080c1c0b00c2c400c1d1500c84800c8116401503550a1b11908121200c15000c0303115885582c01b0104010090310b02078030455070a40c270b81d418500d2030560601d500014694003c00400c00344109240a4543e090361120550030300050582c4006022224050903200703120f190a851440d1514440004c112203161040760b0441107815003d110502c9140302d5503081c0e40d6103c0090b031080070544012580d034031845d00290b500170300341510f410740301c0d030480781d00c4d019a18036031001d01209100400468040150030391003641984054041081540030f0205000c000181 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 370262634 1250 370261384 370261391
    0x1c030e0f01020705012009130b060403080f090306070215010311210a020301061703040e0619060206040c12030f210e03040f0b032703070209010b07031107062001 71
    0x40c0c800050898001d5402500c40b40d4680c9486442c00019280d00400c452801e4446d0b4244400c800114901ca074a4040600c4182c1d580e00d083c68480d507482c0c0c00c0e50000e5902021242d950345580225100d150841050640240304a0340030448a5001180041180c01c4054001d10710f40c0c81c0d502c074840061401200035030482003070144038000c54610a40820022520b074020017a0a031548141821540d0310780c0b1001c00b0f00300e83c41070042d440700044110b078122008140c0404258a6031000a61900300444c104241560a40800640c0c00c0e00810218401ca000302c1e80c1f81080d076500c00300d100540d4002140107000400c520401100c9500450320340b0050040100c119800c015101ca8090172100a80c088501c182e00100b010441c545841000101414100d4500c50860420716070801c20f00c030840000d8224003076000001c0d035101004006482c0f4982e0018a680d0032569a1924040258032040055000441421508100100003d1044215a5980e5880f40700901043d050000c47c1e9202d162540e16548 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 370263884 1250 370262634 370262653
    0x3090d0804110603240604061407061d070e1303090509180706090f051005030609180a0b010513060609140310060609061101090312110c0f01020a111c030e 68
    0x8480c0c011318825000095408402660014508807181228000030302c41c000c100014848180c1c000c03072010880100d5111940c88121614000002d003844a1380b600d5602d4103070145101c41100002e01c002114a201c001c0304a9440700b40000218030b5800c000900480c4d60444c08101a042500d500caa0007520002c0d6940300c0d500380080310741081480d0380030000069968409009449220b0304400080c00d0480341b00d03441705406d40b8043c00030301004042d0740c480c40c82c04001414100100c58040706114801e0182e1300c3d508001d2400010070042800b82c1e41c000d486202d440f030040d0700103101da081034a60a840e400f440600e81110702080c0f00000403c550035004140c81b400201c4070300d004400180226441ea000b440d0f04060008062040c094030fa107880b0307810038041c100070a130401c2c41e0103060014020301080130720751100c0010080c071910784107003110320983ca250002c00d0419400340c0304007051941d40c0c5001c070070303c4000d559036500c0c9080c44000141442c5035064180d40207034001c45540c510315050f03944102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 370265134 1250 370263884 370263889
    0x5030c07081605010506010f02070302100302090a15051c090f0212030708030406060317030f0c0915070c0302090c0a1706040e1f1d0d030c03110a1707020303090d080411 74
    0x2d52031401215580e440380203006140d03170000e0101070125220f100810308245550001030704014612201014941d000442070419104c0080d03d40107400001c50b405040c007060000203010340d00441d01c86055802c600d44201c009e400e03034010400b0080d0002c981c68510711154003040041d8900401212043c0b004001c441c0014a4a0004d5131007107024002c00074200d469414000842e4200000301c0020742e10800802c0000054110240d410a0088091035140d152050124803081144014004500000700700d940030425446a185c1c150780c1300352200c1220fa1200c0090321094042c0c2c0740d4a0300070428428003021070002c029440c3c0e07131140c00280081840c1d001400c09a04014056103e41c0081c503036100c18884070082d500a0070004080d00c411503090358000700c0308071b0311103101030f003018101911610b00042d040d1180e0085540034188a0034190785412066000d88260038070b00d1001e901541100008010302c0c004800c1d02c0c41101d29001400c002d4000c424100e0b00000d004104840342c0034400360040700c58 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 370266384 1250 370265134 370265167
    0x60f08010504120201140703090503120103061b0e0a09020f040e19150e01050904020409171b0d1704170f09011205010503070510110102220b090105030c0708 69
    0x50044000006003400c15043c05444141c0703121042d025a0304194810702c01450101049600c5101c5250004012915140203401c5100350704800e4440c403e108004028000d00c0c0c0e01204a0000c440c01114428500c03e0060b90300c00c5c00764080da64415040720040102202e2500100001114040c000303203441d032140404030142c682074900758192411201d400008a1062181a02000c10542601c41031468200f0f400b1004a050058900494442c0046021505d0b143c2080c0e11007a884620036506452100049165801001c000714000140c900240070301480451440ea160015940b00d2100442c440242e005e12100a082144d04004000b1071204100e040c030042e00011140864095480b2405030004088072054a080c50a4601c1e000042006581c0024010110703030090b07a400c1c8142c40d948500b0344050003010700c806415400020309611014500105e003e92140910528000503204d0300d0700189401284861400300d1001c001044401c0781400c040c0c440c03580704c0e00c00280780041d00703a05910741317 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 370267634 1250 370266384 370266389
    0xc1b0a0210090305060106050c071202030321151e0409080c010c0e090603030306010f0318020301060b0d0507020f07120809030d0305041106090d1103070b120a1d0c13060f 75
    0x24100c40b20501c2004014840e040c0100300600d84075041104140d84a600d64059200d40e4500e00c43d510030801c2152814000d44044910f02240c2d1001c28601040f0702e4295201103400e40c50740311490036010350914124180b025468213a2144a40b9540075800f800700401c040501501c0c141c4003413004078003142007400303195203450041d0303105003107806100140140d0100161445100c0c0c0c00070702c104060b50341c1c013424011801c4200c0c500450020dc003401100320240303104001070b40550030114049019040380380140150046008100721f99602d0000803616649050b10f240c00ca03400c5940204640507000511521403070080b100c8510f406040c40000380343c080b071101601c000c2074945007000184142407034440f07809501078a62038a0022054005140203140c242c1c01420910456071410302ea441c100154805424206003803035440000c2010300810b018115004c045060408400100b46000a10294481c0d00803000804080120303504100c164808110002c10480e42c400c1d0004840c18595a880c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 370268884 1250 370267634 370267637
    0x14061c15030b190f0c0206070311040906030c051801080a0f02061b0f0c03010b010207050108180105040506041e0b06090a11040603091406010e01030f050f0d030b180c1b0a0210 77
    0x20700e25800c40039105132a400c0042ca4070f03d034640400302c82c07000d4003c103481e0b500c044903103400030307007610414110201030081e500030641c0949005004020412103540a20a9800c100c0f882c1e21150a000592070340c11100340141d9140e87c00008203040065500c1c15441c01040c030090043c2e091100c214401590502004982c03001031f8001000103120340380602003c4001c00003a0001c0c0302040030705001039511005480b0b8a41001a424002060800301000d02d940c203620303c0d002400241028100303960317103507410340b4240c1e02d211a0015803099502d43c2401c80804070b0313001b104e0506c90740c0c5082c00c101008800508001c405605c40030003801d030740c8503940200301509440e280059010300c141002d148048034211a601c00d80d01140c01444011816407419044942c00000307044800124900306040103840e07a5510340d544075410aa42445030940c002480c104c8058446005400c2c0100c00b1121444094409042c2c0010400c18280e801c09101c0700803100755041d8048650748102c03903000c02c0000d96070055800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 370270134 1250 370268884 370268911
    0x206070f0b060103060e0c21010e250c020114090904050304151817070f03030e04050c0a0f2010022508040510030908120114061c15030b 60
    0x10400041c1d480242e0081000c4c030302080710a0500720303013a80a020280481601010118143c2c040010314071048520f8440c648442c8a256922144100d052400361442540f81c81040d240318925001e180e0f401c1c1526209030b8621000d00b840d60015200058416061070034003000700300c04541d03074a0b0060307001d014501c541c0c02556264a8070403040d4602c1ca80c225000200724015080c075818000500b01c0301c0540d01c400494540b01e07450700207114503044050740030034122600354500100307058010800038214403003601c06000325074424034005c0e0b6522039907070424003148943e4000301009110f800d403c0c034890003100810b14640b4101550914080c3c80070703d842401500041c1c1d94082006a03a01030080120200c0f0440c3e06512969420398140210f010791805804041444d0280c2413082d00900d211a802a942942d91440005406d42d140d20074001c40841d01035101d180c100d06d00742001290301a601ca10340c40c0c0c08001e55280144094035400f150303070481c400f042401102185000c0707401401190828401c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 370271384 1250 370270134 370270163
    0x13050a0b06010e01030b0109050f040608070f050f0604061d12070e150f130903051308011401080d0e0d05030415050c06060108070807031503060606030209031e0721020607 75
    0x43c9000b00390503440341018100b8a2641c1c0b02c0e6005042c410a4980031035091001c1c030f4500e03001c00d0040a0a42c05640f06101b19240087c07c030f680c0bd000384040d19000e680e003c481500010502c030403031045104000019192003505000c0040303400c3c0d440074010005000e11010702080303003a186820405d0304088610348620061020300034040c0e211180c0c03c83c1c00e80d60401d8903400b0400140c3d41030381041d038440318a5103684640c0304140c895421101d200204130032143e546a283c000c003900030450003c141118542140000ca10b01038009681c0e4540c4000d5036824200501c0c4906101050062038806c80300c610080c4808603011010a42030128101940d40301904e03082e000c40300c2e070729240c03005d0101414800890113101406034444400c3d035114045081c04075804403840400c400304083d60307001400c000d24000c0045521035064005000e1440b04504491907204a038010361040004420500d066500100d4104010b41a030300f4954282100703007411000741d035201d4011804c2548940c40849103c081c03480c2c803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 370272634 1250 370271384 370271387
    0x213030206040603150e100b03090c040501060c14060c0d0c030906091a0c03010302030a020607050c1216080328140d200c070e06030a1b0501030b01140304060513050a0b0601 76
    0x30900400040c861b00203036043c0294107041c810010f0040c51508900080002d00d00c0c001003110180316070002d00200025031755100010698001128221015804480c02a4421100084041c024a0941c10486c40d010b1007100c0c0e40c00a1160104c854241500c540d03a401c0842d0091081801460003034159008602c1095804d5001d058010310368688820203000500240e18000f44c1c144a60341c0c10384209030b0715003a40c18104e15000490b0b01503035010200008070f0b10554030108410551488400080d060380740c6540aa030744030301034002a4016140707156842c075040b20810464407011081803c10303005180301c1004120895001628000c16140c64200280b5100716400c00742d11079030180c1c00c2c0f80c0c2c00e1441d041280c50301c03079001d8481c1c8016003102c0380116a103030b5403d006e4206603d9105401c1c0f03100682c0312444094040880c0300e000d01280c50031182c0501d0303500815420311a184545012807441d66640d44035030060001911000c1e00383c0c85004100000740d0108403c0201c0c601501e44801c091624000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 370273884 1250 370272634 370272671
    0xc030b010504030b040602090f041a01020c030a02062a060406020901080a09030507060506010509030a110405010e04020d060c14070809030106060519081801021b0c01020604150213030206040603 85
    0x16000d0412908001c10000b240140c200503420540c00840940c1d60318103000003401621210400580c018a45501c60b4950040100719440b5840c0a800342e84052401d102015181d020ba020041e410403020003c41d060011180c3c9c002102c0b885409500040f41c02c420070f01ca24185048400b103800c5680020725a03055a0054151b5605c12038070802440340b074145550051060050b664000c0582e51620049005680940c0644203a44000b804a07401d011550030f002100003500360210f8051460b04002080400e120306540e40700356009030181032100001c2e501c03103004020004c0361000300f01c00840740907450800d020003445004d010709041611b070408901010b0848429030300190a02400700f01c0c01400c5203100d10305041c10710303190410305016500c1481c0304074207012121600815500c0040c044030140003070015440155038900441da103034503d0400680c1e448070155006440f0107040004840e0101442d00180610104103030031182c2969603a0210302c203034200f17403c4440841e4442d00701c2d45051802c6030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 370275134 1250 370273884 370273901
    0x5010f08211603091a2821200309030a050a170406091103010b01090b0a0e0a0308030906010e09060105091504090602031f18050414100605090a1415011107090c03 71
    0x2079800f03213011b401c00000003409015103403042c00d00610040380c070582400f1720400d40204a41c0c001c1110036211b0b08248100824104078030604084c2d0401c410707032018410b030003a00e100b820040e004601e8420f08090035034032500407a80410030001f02c01012040c0e0076840c01070a0050344180f6001c40e404005d4a4016000403843c8900d500031380c5004000074650fa480082c0004540f460440150342d003480310000c83c0d111784003602407900614008000020800003500661080c607220069071a16600d0703c0d64082501c0c0c050350f0800a5503c0035005010601d131100d41d01e6000030f00001546e00b42040940803805a13842201c080d034005902004100c00a07034018040041c14070701411000341141001a000c05904d582c440a9007095511400681080860340382044c08905035421981c2204420320707240050155030240c14064500d04012514009090207450482c1c03c1d10303103520403e5a1a840c18482c80c920000c0705c1d504000d1100340700300b8600401d0100d00041d02a881010508038000500903080d5041074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 370276384 1250 370275134 370275179
    0x60405060319060f020c0303011401020c010503010e0c03190c02060405010501060e09181f06030c1a0730030501030b0105062b09060c020307020405010f0821160309 72
    0x14070b0408819400b014003264900e40c00800020b490700344100000080c050240c20102030310000001203802144584524100c400903403c0700c422440080044a6034042031003420070694019000c6418409001c0285912100035a0b0201c04500c80c8560b001c142c50300d10062102503048802404207000b000c0c05064050321543c206600c10f92290710102d904040f0044c016055051b246681e500c43c2c2e031003400396200d9922805944641e811003135400c1030090001340701c110354068001c10f00040302808614415002185500380ba818400542c41780c0b0300200c8115868640d0034004090241c440600070a04411a402d0b41c1e40007826605616000d00601c8048c1c001038800c3d9000c0c8291002c0ca803074410700d0100320300007030100e00b681d000303080b1031401811070190004c011606000300c500c0c0042d400000f50448a001304d80500199a070340402031108240e5004090b52600881e041041000703e20342e41044002c4a0104545003030000855114a040d80704811000240700c00020084071000500e80d10301c12124 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 370277634 1250 370276384 370276393
    0xa08100504110909040f0b0c041410210f020f09040f09020a030311160e22080306010e15030106091d0121060212070206070f0305010b0a050702150a05030604050603 72
    0x1070700070b1140e075004a0140b1031145503a200050708010b04102290190743d407208603022181048404001281c015005481740020b040749415228501140b6001031901952140650901511040240082900144d107000e0f078031980300031600507092008180c901131810f5000d80341c0003110100020744402c80400000380342000d00490159540c3c01d003e0040766414140340c1200080701c0e0b051400d000b04034030320302c0040011850000303000202100c03881c0700ea15205c0502c0502451120700d800010019003016082c200107000150b4294009e800c002101d42c8000c0403000e02081c0403442d00a0365000360441c0c4005a1010401c1084441d642c1440c0f2045050b45003800c1d1645c10101c0c4d0500621140010411181c4e4015001003405403541c1240d0411400020210b01860310240c069901d0718161480c8001030403c00116000910900c11141030340c2002c0641c510340018020210382541001d041a80e0000901e0a10404000420000c0116201d1a281e0b640c071703490120200401c640004011b42e0081c0c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 370278884 1250 370277634 370277651
    0x27060606171b031008060405011a10021b03010b060706232503090614071206030c0b1806040306050601080c07031718010603110910060c0f0201140a08100504 69
    0x22014a10390b6115040c4002c80c0e126940c41c0100b2072040841d44c8414514050203007484280003040d08900d05003840106401c0900b4288000d100302130401d0410600160010846411480c01621a00c2c604035002000450900c9040002604903070002c4d0f000c0700d10300c1c0d036501440030f1060f5651071804203038000841e60b45103240442600c5002003903e0110020a40c42221078070030300b8002d601901085400c0203003001114415100b50744000420b4920002023500c1000c9030f115044540180403d41358441350400c4098503121034800030703400c509010014018503904100280e200d0384094002903014240108040c01d03c000050075440c809004207040500400c20000800e030000c0e03000140c441c1c0c182007010103640d800d2629a02d00d41110781202c643d424044004284241c842c0c1c10310b401c020440e01d003240342c2c40b001008050108a0711807071f004200420301c0300e03020a2035400340c2d0380564018101004035029640080c0410f9010074004808174001034140b1801c1c500ca0800400175100070350b0b00f00000507 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 370280134 1250 370278884 370278901
    0x9051201060e0708100b0a120e0607022104031e051c0306050a050109120614072307020312031806010e04031d0a171606110d020613062706060617 64
    0x4446006d454402000043ea1804003845850001d009244140080001c0807402160b00e8580304103984106c01403040c400a03150350202d44851031752100540303098502c2c051940d90f42c118140d43d081206a0305240400c10480800c000340500301c1d1242002c82d6082030346130341d40009001c1710601d03003180d40030300d0640005005598020b8840410b55403000308500c24804280ba05102a02c1c00116800c00d9070b070814103104256070008a000c401814140d0080c01c110f24000e24410f0074020a103010b5495840003001e44010440c240056411200110742d168005014003081860301000784d004007d1104c402040000341903001c0318003001c400c0602c0d40020300c000004009030102c500c43c0100d41900002d090b404034a00c0c0100255400c01c00c000c0c1c003402c48103a5403500901820002d000b0001c10b030089412405400c0c0c0b000c20f02501c50f000d04004031b9050442c031f40303034072000308007507003020745a50441c544051022002191310140988a07480100e02c203401d03c034000340490300c0c8824011075010080c06105401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 370281384 1250 370280134 370280161
    0x213080a020d061107020312040f050616032a0c150810090213180b040b03150a050c040914040201021c08040809010903020a0303260103020d110109051201060e0708 72
    0xe81e003000010030a440340c0004150744d482082402981407007030355000600781c414080903008591581c0441c110441e0b80e0000d00c0107038403c44002c0308062450f01c908400182c081d0300c445030407503400c400307103401c0145011104d01285078403882540c4d0103c2c2910100921041d11b02107a5035441c441c80c0440441c1840503540b1a4588640aa0110360380c002c901c0001c8041340e0803001c0000c0100340810a070501010615070700a05a00002c0c82c0610308140c0c181c101410000707a1707800095180034610b003290f0354090b41c036802050b0182006924000812000401d001c090044410352907031070400c40698201440003914003038090294141400307449038401007031038101d2407076540300390400d60031036a42481c80c0049810180c9a007000b5400070605101106042d4400020a01d0581807050b4a0300249107410603113415100748002507000901a0b842c40005001a44542e940e4406050045040b6114000070b82c48400c441000c40c610781d9a14020002c0303082803400b668000381c603410511828105169641e0782c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 370282634 1250 370281384 370281409
    0x20c0309012001020a0905030105061503070e0103020d0606020d030c0f090e06040603050f0709060b0702090114180c13050d0c0308030c191d0a060e120f010c030213080a02 75
    0x14071018002c41c00e00d2524121640400340042070003155540e86900380a01558a41e0250b140a58603001c0040c000b8204032245080d1450051003980c251b5507400812101021003c160604060f000e11507540808a1070050001614040c2c0103081c0006500300c3c010308507002e0516000421130700350f4076001e486800040c400103654418420411654550000c500501b409620050081c0b044030a14041200c01084803c103880c0009010301256603a10309569282c02245006507011507641c004100c11014401520345074000640049800c64282031040700c3e000048801101d9031900040c24880c40203d0320005010b0f1004843c8080070190644508084540c2030000400c40d54002010603460f55102043d6490210100040078103014001c40003400105442e002074403110308402c4241c80343c64241d00d10010360350300d17035a42e00132220f010040004144281241c41c8680c001c0d402680c0040b402070150a240c00081d49000d82e4600c541081040c40720119400380285400559420005940d480d191200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 370283884 1250 370282634 370282637
    0x1b090703020c150106090501020f0d0215060d14010c14040f0b070c08070b1e0306010e150403020607081b0613060507032301140109030c0909050a082b020c030901 71
    0x215994400011450100042c0f403210001280200008040d41d00c04403070000d40d10700313900b900e01c91000c04106666541c6180304043c0075800910100c50f4500244000d07940c4040002c2c030304003600038036442d10100b5000f074070030300321840c1d44072030454a080350400d00090711003d04c02c8401703140524086403204103848078003803541d9000b40003a00c00b050180f4035929001500404042d0341c80542d550883e107455500c80c6010000e094500078034a4501d90f44041507a20404042c0c4855040481480801032410300d2089a020081414400480540c5550002d011038900c00d03440c0039950550054400104000300c0600007040c0d010384100101110f480b506083d055034040c0f03010465486000058002d000d50319a10300c6501960070840800c100e18400050480315070700f4084040c800d010b401164550391500000d8120f114042c800c00052280b90b0000f80401d00590954010b04250355840025601070b03812440001e0910780384604541d100c800c8140c000a00341401c511f00b1220350a00d0341c80340600340c01c150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 370285134 1250 370283884 370283887
    0xd0302060a020304081e030601120522080f040f1805130305030903070b0c0304020405090120071505090f060a09020117060a321c120525051b09070302 66
    0x1405c00c2000c400342c441c8410701829540d02040c26120300c2200fa04120b03141400207401d07180300d40103808244030300d601940c02e000b1a20b09074001410702a4498814803011505044100610310801d044800030304042c0c0344200c940e002403490528415400a08486880491071a110030701c9580a0582d0480c540c40d0b0b4141401034495031030002d001d0960041460140040e0040c10030000c9000000005601c1a0b01c00c032803c215503184c00115608941da040040c03501010f032000d0320240a08420060030b0803500c5400400400c401d000c240c0d00680d00c066900500a81c4103802400c5016018880c1640c40802c501c0d04011f280c0c440c0d0002010b85440340b80800441d0414404036034503840e43c501d91000303000d02d40c0007841100242c510141c00c800180103203040c40740039119404030500e0611040450452019844a080e4813192a6014584061500b4406008080000ea0b28542d03280e03000303122882c401a100141e0200a0515608104040b1a150604800048030b01880d03941c4501e0300f90490701501d03006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 370286384 1250 370285134 370285141
    0xf0412030c05060703060905091b0f03010f0e030306090a11030705090102010e1f0f050613020a09030f061e15090f14010b0904110c030403032d030506040b0d0302060a0203 75
    0x580e240740340080701030118015030041002c040d4044e000302c1d080303810001c4c042101d643c7d990603d60721500c0d004010b02c1a003005880701441ca00d4100301c481003200c80140001010001082c10500f16034071106030341d002d07402c04000c02c0001d160805003103030720040800c801d000c01c100c000c08100484c8001402e00c030500c4008140524103174800d40c8052044000501201c42e141d60001e001000d40e10400c20b080032a90900c500c44401030302501031203001742030180030080703200d003110030303020203034001d040c0c880100314030b03c0000004102c0250b80e03810038a0040700000713100003018480f04e100c203000520340080380f41091300480f07404c503405034000d04881c01410005407172581009008041d003000f00030103508120300000030031010716541c003d100390785007140c00b004403203890040c0111501680f44032082d01c3c3c01c01e0104001083c09244040940100041c0e02440340c2805502c00c2e28509a041603080000c0d6a00b082143c07074142445984c40c50074045410254820b40b07917500a541c5c00c0f00034030803100c80c0d4022010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 370287634 1250 370286384 370286387
    0x70c0213091208101215090203030f030c030f010e04020108160908030403060b03010c0e010c08070c05040207080d0e0309060a1b0f0305030a060e010b0a0c050c030601081b03030f041203 81
    0x6091607540408451061a503042004000f042c003681c0c05552086400383c00101d0081807802c030745201d07a0101011414034802034800c40204140d246c20703600360104111255210014034011882400341e095078945a00b004d4a100f03000000580180d282203480c2004d10000d0303070300724036096440621030184001e89480381c0d40881d140300c070940c4140f59900c00850701208000094100d8401e0345005d500800c101448201e00700c424002e2040494086941400c4404c045000c0038000e091203401b400900c4411aa110042801c81c1e00c0408140d40440c0301041650049100e40120b000c1c04103003c004508000c003060008015110304c0c104802480f040f01c040020800070800000703810398000141182e19055410054102d038401c40762070425528115006c205d484a80c1c120340d06880ea030480d4a03040c000da0380d0003560140382c9400c040c1c90701c0c03003581515143e0385c0d001c1002c04c2c040d120600c06440c0031020f0030368003030180b030700141d049102e500144400c071410000082550100c52540c400e24110386c115050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 370288884 1250 370287634 370287641
    0x405010e0f03040302120d0816141201080c04092a030f06050f07110a02040c0e0d1202011a030a020d021c0516060e0a0302012a2108070c0213 62
    0x80d0818502401401e45104407001c070203002160300a844045202e103844c4a869210304854039520302080c840c2000c10840c200ca0820940c981c5130506180008901c200c40564050b0000000000d400200c0e10045c01001f13020b200602107200141d4041c03141516a9640c02150b903041400307050484402701c035009210a851f18901d00460b04031415460100d514148140606811124014146407450105a085119440007003190101038040c0080b00d085500304406003400141c8101008080b10503048543d50707800d200c0c07182d81e100740108070200c0800b280180c250f80e040c82d0307030345500e0850101d60b4843e9180810700b101080c0d41143c54103030b044050303c0001e22401c00c0c1109001400e030456036010800400003005c0302e1124038028a91030f120b0f51500e003110060300c00801075820148a4100304011b5000350540301d04a060890304025074060711a079810003644209060383d0521030001414403003900c246150b1080a114604209180341081c1e001e048400c20030402801408081d401040b642800d030f1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 370290134 1250 370288884 370288901
    0xf02120c090414010909020f0a080303161e0f02010608010c05030103110a080307050c0a05090910050604110d140609160c06140103050109031e17090c09070c140c0604050405040501 79
    0x49000c041945c40e24190340042013a08000ca02888824120b03002601c0d102002c10121020380009600d1540c400c11000052581140258140641d0800b540808544011300444807100c5589806e440340e000f0f44000d00b950302c10352120031142d24100a01103003d80c0a030843e41900c0d0081396881c1000f07031400126103000b5480c2d218009901020449100700000400d01d0101c85c6400ca4664080507110800c20182e2007085c0c1da006800e5000394101580581300340c0210360701c104000c02c00181074402c4151000503034002c148480c1001e9940e507444601c0051685100d40150040c0c4946486103404d8103000451030b441c405000520205560660404c0181d41101c080d51034503560341412540e5914126000e07042628049000c102c040d0280d0b114030000b2040c00300341c0c0009580d0040c00314074046440c606048050310250443c02040c1284010761119940c42e03003e03032031507030340c1749480401070a20810800c080c1104035143c0d04048411711039a0740d464284c60658004a900080c00e07165440e01e1401003072003c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 370291384 1250 370290134 370290161
    0x71419030e10020f18090f0a090609050d050c15130813121101120b100f1205090d02160302062b05040303020406020c04050f0c0307090b19030f02120c0904 68
    0x2240e120304400310700504942c5c0e907814840d29010200c3c0c41004640201252850000c04021000400e15040d58214812840c018071001900f602c06031242410a651305807001c2c0030410004a0041c0704100b00130045a0046907804082141001b028204107a81192405080c042010881502444a030f07247d40c0300030000c40c0c04079801c0f808c403454103001104040b10b54030b01260307010600c1e0f035501c070960040d0820100c004010300109000b5120550300352610381d0a62080102c00c1000118802041c446c3c10b0240150400400c8210603005000b4500703040e00b0071124490141c101c00b040162100b02c02c1e00c420030044c0c121240341c4845140c141c4c50b2950090040300c1d519040074180804d054041e4001c000b5280d656081e07a8031b4000c41003d02003a030740c040d20101d9152007030343c00041074416424003468201095140c0014155900c480303e10107608000c0000900b0111210340c1c3c00d040da014450070f0f14041024a043d800e08007012078140840c500189030500c41c200009400040303075100c3c0d1181d0300c41c0844 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 370292634 1250 370291384 370291387
    0x4170301060c11060717030a0f0908030108060907081209040e0d080703110711090402030f0d180f03031205040c0f0f05130b030d1209020405070206071419030e1002 72
    0x15908010705803071205400f907688400b071003040c800d1414904112007410350004d4840b44181c024250078106544003d240040c01c642c0c4207a40310040e0000e004040c0124000c105542c1c5950424028030b040038005045500103901620040281c200c0c041074940e00801210316107611008010b0204002c0c003021090800b4501840100d03821598000f840d540c02000d040d64100035a40c1c07902d000c40707264820200098400642e01811254920b46414500d030300600c045c00b0782d1450a02040210302c1c0051030416003020031503084001007400f070030940c8a40104080590710404902c0c40c0c901802e4000d0706039040030102d40710400034043c0910480d04000030074400b01c11207661342d542c40008040c0c84076800380602c120640c45050348901d8035400703a00d180d2000180a020803071520300050780d202065920403c0c3c090384800c02c29026940b28480c49204a00c2c0c1e030080e1900d40f5100030010a0a402d41c1600c1011400921075001c18003847c0d81e00d51610451400d0010300c514042c4036403032070180200d0442082a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 370293884 1250 370292634 370292639
    0x62d030f120915120e030403020402030f0103031b08040603090f210e030312071d0301020f0a030518191704090603020a080601081506061c0b0a14130504170301 70
    0x208410814100e100700e41e90051925202e0350318250301c1002e150038400090719194a003003101e1072035000e041c1120102048030328040e900e502141c10303608102c0b040002d840341c1c0c80040041c19004043c0c90800844455100d081d100155070b80c0409000340d0080b841010360301c6038a00f040241e5144110300303094010b6082543c28010118042c00d815078401410005007500f0409502410300000340c40e11a00004401049956604c60445650400040c071301c42888000305240300584080c80184130003001070800a559001080300601507400c050550203400e029038615012030007020a004491204058100030f0000c4603043c90304a846104076198030001c1c000400003422192a40a042181c0c401c0d91a0070020b40d442420b030343c03650000d1141d0480c0341c2240d401d0414103044424401d81c000001411503050242a01c0c040394050a42c04101064543ea00c101154600d04000c0c000010044d030000014a09142c00200300200380c035508089280d03848030003003010842107082a803000703440c06015640342e40e07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 370295134 1250 370293884 370293893
    0x103110325050f0a36020d051512070b1803030c071412060105040c140309010b010908010216110117041506090b0f19090f09060609062d030f 62
    0x181d0358462203110300e00584888180341021107010b000c6500005010007013148a0000d00d052240106a00c082075244640584803c150b92014081c0d40b25a0f106c000380394501900241e9136641c5d0100704d14840c4060140303488404c8000074502c03091b981c4030a0b20940301c1841c40d8404080b02030030000b0681c1800046030104c45428001415011036149100c50b80d80d807085a0203001c00d41a001c008504103821007030042c031032400c01d83c004c0c03080621685800070303045032010724a0545030420b0340c018159945500c0d02d00015030348038800201a118a0f802145812442100e071113142141e0080281000d00d82d80c0a080160f01030103440903c0c4c0c00031046c0806500e0207142443c443c10348801a403611a18050000c2508202c0744075000008a004d070041110620740b5041040d4089004141d0a042494000201e421401e074000c8000d0f0120660003c5400720051510342e056424070307008048140c0ca060410002c0780d011007000c0c0900c2185055580110034044042c2c0110016500080d1442c2c00705c0d1072000412 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 370296384 1250 370295134 370295203
    0x50105030c160318080a0606060f09150c02180f0a0605030c0409020f030102071202240402061615060f0510091809021507030e090c0d0c2f061303050301031103 70
    0x1c0c0d100b011f04000035070b2580c10655400308a00c0e41e000010311040018081041540440c01c48000c583c10108400440ca81c0040d03c88440440e170290340d440604240841d05441241032030300000940f4040c800c0341d00b0240460b546800301104644160b8654a28100b5034494074800000581c1c05002035540c0c1c030031410000d004401c000300030700c010b10a00c2030242a03512007241c425442060000d119070a91526020403419801080c20340d8032258480c6118000112580007130011100e2084022501d545488031091b0703800c5d6150300081c000d4000000c040c4070541d0004185041d00d000c03e03040a1003400c51416030380184041700009410820040300380170507121900203008054820383d0b0341403400ca009402c2c400c4000c001d6601015005003480f140030000740e0b81d0400340c028044da01e0000144070141b03c4070700002c031460130381081c000d0701c00c0c511000051040c0704040d030080d2240c1407000c800a165500401500c0144805070201c0880305214919035010303c01142c0d160001010104401420032002541 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 370297634 1250 370296384 370296403
    0x120102070309090b0a060c05030c01050106020d020c0d1211150c09040b03010b030c01120e16030c060503100501142205041d33071107050105030c16031808 68
    0x450802040068840d00134080e60040010240c07000040a103008000d551168244008680300c1c0010301070140440c20900c15030340205160340c02816450032040010341400d0005003c580905200840040130400031124107400282c18603000191940703005000b4141407880c03102207880000082401030b03510b840b902400300e00200b00d408100c1c0000a50816088801403001160540c01c50001a403840d8004d02d04810f0042880b02c1c08218140c07071541041c1050b00901c403003402503090002c1030051013807140301c0d8005000c050400c545103003409a81501c520394035200741030400002c1054031035a0360403841911300210401c1c998088010b07040703106500080d800d02941c4e0042c0e1500b60445140e00050b913810300641c4401e4054050800301008501c42e511403038801c1c0b44403190144602c0884602e600007188589250341d1040700a904119406041100640c4000c3c1044801e0081c4440021f54034120cc00c0004400c5a01c0001c0003507142c01c0c1c824102c078000811424544a0000403030040203e680380703d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 370298884 1250 370297634 370297637
    0x5030c04021c05041509530f030112110114040608180607020604050105010905060603010b07050f010e030c2406060d0e100c170103150f0204051201020703 68
    0x144418091000728012120400402e9000208040c40211a540f0154015014a22009500c24080680800d0b511030f420110b60818400d540d01594003e112000511081c60355105d0480740c0d00c001c0021404e051185004410159414019400c0e90b01982103460241c41c610b1501d03140c2da510319413240741454114041d6440041295198565881003a10201400300149a41c0c241401c0003412290104001c0c80c600d01c145021018100c886400c010311031180b45154000c0070716240c40c2c5082ca007922010703405552402e00306000c0c4074140d620182683c0c1501c01a0414030b4640d0040e041440c90a111620030b1905940307083d000062046020004251039850713101110407000947c416001c2404521400c881042007400200e02185030190040800365100100030805041182a850070038510b07201c00203c1c3e65807441d28050454201007144c89481107020416013941c910f46400007042e082d6458800f0b0150380e1541d403202c00007aa03042e17070007524016005410240ea2101d40500035405920190f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 370300134 1250 370298884 370298893
    0xc03020c0103200915161703090307030f0c0606060e180105060703180e0a150e15090a0e1609052a130504020d0605090c0a0903020d0503160c0503 64
    0x980c0c03540640200c40030002da0350004007605400d15000a4150412081507910041701d082085000360034001800300b1241500e01006207461034509170b50b00c0c120315540d195200c0740070300400c200d0a00c04000c1c5d82030150141451031040d50a19002c940d05842d0940c01082140b8015002c40c4541c0d00402c0048408003c0d038000c400c141c109411220f00e50400d115003036100703a0401144000a00c06c00b001100700249241f10f4071241d4039440c1c0d0b40c1044204450503001c9aa030b07081d030100c0303c0700c1101c440c90081000c07080c00501401c04220010070454003001f1755000700b80000108050748110b52090401003c51003e41d0b241a02d540c10360b09010782c043c45002e654a0801c40890b0300c1c045503000c040e001c0060300c4180c0002c8596084c404900b078100f80080d0321030401003c0001190348941c0010511703045400360014446060100308550000c001d882c04640c00e8003031100032401a00184501c0c281c036012511241707210641d00d0007910b107102e00e800d140f404c000591b02c03550411412541803000d41d0300c128242ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 370301384 1250 370300134 370300153
    0x304030e040513020913230303060a1d060108091905030304120819110f030a0b040e1f0209030322210b01031112010e0309041415010f120603030c0302 66
    0xc060f00000700040d6024440401013000c240920014904032881441c502c411003244810302c074030402c02c00944500b40c0d0000000c01c035035071070700c5800c1a000d003d09541514140075503c51017904070304000e08035810300c5428404a00028020007001d07012080c540804240d4203c107140c5291240c10690301150320402d80c124541c541e5010b42c1324075119401031110034400910030344494019021116158410190030401640c482e10440001e42c0f048100007400f02d40742c140c0d01d09000c100c80350240604000d4100c0da5141c0665030f403180f0308000001030b400025840d081c82100080c111b100b034410809100752040080b616440c0d4803003401c01250a05040f90343d601028000300404131640a00042415000400500020f00c40190998151038041c0581c0c1440584161460848008500c50151030b400031441e06100d00d414025408091403136641d04c1001d00f480300010041d4482c42c000c1c1c0d414400d01407141110b4a220f442d4500800c40c07001e0081c000c40d41c0c0c07410f01400003034043c9400d900500418810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 370302634 1250 370301384 370301401
    0xb0105060412080a1106010e09060702010e0d0c06021201120c0603020702030604020622032a050a09050613050c07200d020103051305070f050907020d0509090a0609020304030e0405 79
    0x260703401c0361498500e036044030845030790f903202e04d5010015003403d12032100200c1075600300801030f540c080d028610001c885424904002480c01500802901c2160304107007042e4004900491880c0b0090458100f003c9d5805482c03034030700d01900400b803030800381e68001d00001440400300c044102c0c0840c0544104409240c44800407000e0348500000a03405a01c5180810300604240d0003c002c80b00d2100b203802010b11100380710b980c1040c0943c1c01580c2d944034095156102041d0704040c2caa040080450000c0c0a5140c080403070300c03c0503140718865005569030001941503d809081d21021415440f08014504e042a02c1c040e4540000354240c0b210800051159405900640050411103004010b1100b246035030340118043c040051001c00126841803101c40024010001900504000d00c05100b1140c28981400452800104841300315400044007511164114040f01c0e0a11015100040f2541c0c03140001c0f0003070120740d0702000f1080e10000402c010b242c2e0085110005090842d410300c8a43c503030040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 370303884 1250 370302634 370302637
    0x30b01170112020a05031b03070801140a0903091548020102031e070615052206051807080f150d110901121a0c0a050a020c06160b010506 60
    0x45030124208030018850046450562046184020016406a500c98010904141c1000c0291405403110703441002e440c581448510b01a1680b0781c000c21140b1080000e000007448050040700f0701d90741d5000500107240c41169400c010700101c4801c0100141e00b03540003084803080c4440c0740d0320f400d0150034054075801041c5001d000c8091603070410490000c1200c0041e003840c4031030001ca040d40300821100e01181c010081c96041001e03516201511001203081071819070754101034040301160709076810b1000c0d07592951081c490b5031440810040e04d0141243c040001c0c00fa0360000c542c41340d552a41c5503503640b02030340c03454454107440d030311540540c44009000c06c1c0c0003801e540c0381d1600802c0500506250401600d08039800340a9080b06844036240750105071240c00a800c2100701428251100c2d0130702840458121003860041a644540d140c54502c440450086001c4c2104001e400600e1648103032081003080052400140001d035250314a007110010036450340b50803509074a114000044070f1800d0720 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 370305134 1250 370303884 370303907
    0x3180902160816050d0507060b0a0302030604080d0605030601090e0d08040302030a0c08072010020312073501050a060207080d050f070804090f0e01090f021005120c0703030b01 77
    0x1038404400c880c0e03452240d181c2100040f0303201d91014000381c3e0081282003000300c94451490b00c6041e51980c1500704a400d8411000050340107010314007007000141c4000500a41c0250070403070090300c41881d45143c0000d03200a500259140c1f003020004203600705680c4c0286500007085c012103814000015041c1c3e92100c0440c0c0140c00341c3c00074422169030601035105070080398460401d062511105607600e051800300440d04003070136942d18a484d00c0c68240003a10320202c4c40d1500085041100c0c004019695550040021080000014404503121030828410b0120003600b48041400c0410080c3c661444809200c0d65218851202e40084e1f21400400d080041d1490b000c042d040840040e40d050350160300c098590b01d0007140400900c80443c07400f00182c0042c108075a008a038016250b030302a000d9a06031410301c00c42c0d0740b51400140000e0341d030740c02e8003a84681c10b03a40310b40409400b510543d05801040d0341940c5114905040102c40c1d07200302c000301801440790301c0070852504036400440b110550f00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 370306384 1250 370305134 370305157
    0x160311130b0a051e150a0306080703111e120a0506131502280c0510060e0402090a020c01020d0509060a0c1407080409110904050c09061b010f05010303180902 69
    0xb21010302c0301e41405080000168851107600131200d0418010501d11180700c0400603030f425001c64494101981070150360010f14140000306046803c41d2620008200c03050b030413911602c1840060301032002ca00510942c0c642d00104138403040d02409039096201c1c4100307103085039a0b00031035000844507104509615901600010011003440d03641500d00000e610120103804400c00c00c441a0300b080041141c2200280813030758814540c4001440d06a04e000305c201814800e1f0340c103141c400d20000380601c10031544150110342940301501c0b4007050754024402c20890a960354000a10302108035031a4003d14001ca0820044803416070b140b1845c02e0449002c2d000c14030000d0040b1810340c240007080d0002d406002d0051114a2400f0360366442e0300100c9115180c64604a040071a0540f114a8188100b079800315081408518152000d0005070f0584585076900107001d85051404818510940c0b1a02007500344400c2080203507100e00780501143d00c0c180186951910201d07022030381031818025101c0c1c96021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 370307634 1250 370306384 370306399
    0xc17040803160f1b150311310815010504050903072d0b180a021f0c0b0c04030b07050a1d1917070b0306030c0d05160311130b 55
    0x400300d02c941140d10302c00c07058070400c100004500101d55100310740000d80480c0c00848104500e460a0039070751031070100f07901e000d151410391500d202d545484102c4a4181040d0041101111501c403240d41ca20305020000c2c414891302c0c080410056400202c000e640200c01c1f602030500e80e65a0100000c1d11001c071036008882e041404054001200c0e400c94900060394102a01c40850101c940b00c001c0d010303c9074054a441d4200740621480740e2144001880110061016050014558002c22030208001c00800c24441620095800142c45501134126445c1e1264075203642d414000e10010180e041400142c0b201074841001c00c0f4080c1c051780441d80c4542180e01d440c00c0c40001b111038241d5014002041d01e40000116054807420404003d4140142100b01d40e51000c1d1444c001c50389161510540081c039040780100140079103036500081d94280034004450401900805203021707820828010042c0c001d11038114000b004001d48401024030f00b40041d40c804100401d0045554151031850400c560010b21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 370308884 1250 370307634 370307647
    0x1a18060304080705060f06101b0305160618060507050c070b030705070b04260a021c090302030601060801030201080a050103030c061116080d05011401120c09150c17040803 75
    0x5065024540c06801101c0580c1410b01c1525403e061600440b0144032501b2541c0801c8043d1034003d642030b541e03030042d01d04030184401410b5a81031030210f6417030250602c2404241da04055200035001050035502813018444e002d054405042803002a801c01c075407980c109030004104034402c20540d103c06614600510809182c94807036811948050030038002c120f410050080802d00c80d050351400703503201e40c01c25500c0d100140c200001c2d01c00f8643c1e0010361305804000c0100340c1540019030b01030a0340c41c1c540d000c00310800340e401529aa086580000e4050041d1800060016002038005040324001e89801c44155a01c9624001700d0307009010007400308c0c02c0d0b41010404100c45501001628440c1c8a86c1441c08d0f9401c4c0c00d0314858a46001c08850704107000804210b001c16500641f40180768401d03802d1030150035078002074686038030101a00646030342d800030803800f135118080c10320040c00500e0448903002e100c448010154003491101f170340c502218070140a1808118021901110340880c0510304190 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 370310134 1250 370308884 370308889
    0x409090606080a02011b02030312160305160e04050c040503070b030a06050a030c0909030e0406080c150339130302040b0d02010203030a0f0e0f010b0109060801030506011205031209071a18 82
    0x51008000d2340c042c8418040130840700809288a80290580600f031050794001880060940f41c0041201c440425091182051160401008480c940c800c50b00031401da5100c02107000d440c01154400359041c070a454000990205880003140940200c0c0b005101c260745600500c9111203003440b0042c40350114600030001600182d001210b441c2c440d00d0b10310720200c10000020161540c2e0b03040030880d80c0220304402a07600d0308401c400175004000342020305502d0503031072941102815240206140d0b10404006111100c060407000c04007038103e00c03d6441d00b940c56010522000140004c1703000340e18043c5650034130720740480c1840c0300c960b05a00651542d92a40019400b81440494007000e441e20303000000c070029428040c0e0700880600e00b000042503140c0500040585450383e0020342031050103001400400e101041190541d2024001c91081540610789585540720301244c0b45807d01c040401c1c40305064003c10207400b11124910080715002c3c0d1040c1032001441108800100440a40030754132150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 370311384 1250 370310134 370310177
    0x507110105130b030709090908070f02130c260f0a0f060902040b090a210303090206070b0f060a0801140103060e030c10140a180204090212030409090606080a0201 71
    0x255040c03601c1820181c0b980c01482c0581c6541d0000e20418a000c000c00100340d920550240080200c0380c0e0500030880c00749c581001a20a0380d030003422803408540d00400b95110f2915440042e6540ca10400c0903003030003840200507001c820303a003c9450082015881c500a01e4003d07a5006810711440081d407610341d0b120040c010005018100f800da07440d1100058030b030500c0c5c80030b0b000522202c418a81c4e904828000c0100005040d001f1041e5079445a10300a10090740c2c0003200080c0f5454140060360300058000200603001d030b0900140320040350010010181c0f40281058014041503452028140d2079511132400d85858031100380750031711071000420124000340c00203840c410007682503a01d82051600304034148030510130120a6207842e00342c04800f41c2c000407a40c1c0e80c880102c4404202d1514803614401703503c003141c040031744516201ea82034019551030070544180c2c08030900849554569481c400360150003540000d5440901d895800100004081241d103800317581651080c2012105541d00d981c0c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 370312634 1250 370311384 370311413
    0x6030c040515040603050c130c0807050711060a0314070806010f05130902030f180106050607082b092109060c060204050303040b0c1605150d090f0b0f0c0a0507 70
    0x3401802c10070002151150700c60003024501440240c141051081d0138030402c03525600b0104c40c12480c183d000f0036040d500918103600980e4500d002c03a99010141041c80d90f615601d412654800c1c000a0328065a80c1c01d41d2040c0c01c1780100c3c5503080c4255458500a4404000490b0628046603083d100380c00c2d62407042008010aa0380441c40c0e800d850340302e03d130810481e0421a06c10034500144401e000c1c41107070f0040115403001500d4024059903044c04007085060044000040050f0b50100780751217240c03400c0b10b40381d17401c03509c0001c03e44001d4030342c03918030001c0d28416034250303101d03440007841000b02d60030800424a45800c070703162441081c0c078010046600c0502c8040a944440e401d00002c0b84640c0d007440184020a5508005510b4100c900807aa003071410b0000301c4440c5c0504c80da0100410317203c0945a1840c101040561034a074400802600d02034150410010a0064070340844820894080c65050094800c0590002e0580d100303031204003584240030162011950901c0381400003144000320085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 370313884 1250 370312634 370312651
    0x60e1e041112070201140c03070e010305060f300120090a03050d0f0f0503100302011407020a1d0705071a0a0605100207030308090313050f010302130e070206070806030c0405 76
    0xc2c0500d520121901c5020903248000181d4590072082c11a4a03840c0c1d440f03400294000c001c1e440c2d4103203090003804844445084078141501d5200003021595604844405804003815290094160080000500d04403954900c2c0703e0700c20507590030040005226110a0241041c584140c1842100354403071190802e95503a6441171101101000083e4140141c2595010907140c1035072550b80b0890180100403072b101c0070010410705004220b00000d01c801c0c0803088030740a00700b181002c280105002114400c3c20030203508803c4043c80081c2c9080c2d46114003512004080d11101035490304d81044a60303200b150409000090710203810315449003164003454010054400c001074566581d40400d0403413002404400c0941c06c050420418103800601450f40700450601a61900141c03030038101c26a1828061b00d805041c9903460008164069411214410051485805500d0381c0e00e6144038403030004c80d080001400340e080414000c0340a002e01c240101001001780c40c42034080e006010050100a08814 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 370315134 1250 370313884 370313887
    0x70501090b0108061320040227010305070c0209040f0302031e1902010902060301170709050708090f1204030f06060915080120121e16021b1f0306030602040f060e1e0411 74
    0x2e291140540c03000c0101e102700c04a040c00740a80310000741c2104d00080c92007080c06070300c17204140183d0700d44c0210b0380d00541c845000075003812942401c81c554058004d2429002c1009000042e500803070310045e0a40704031040a080b54046120412030980310200c0c0c1c0207400490500041c0000300f013001300f01200881b41000c6a071001c1d40c55400d5419600190b40c044040b0f110f0340309200b4500c60900100e01da26881e40000c0c1004551505007543c90b108500c40a442c0d00054103100f010000360b030b084a0028412603505000c0c09840c0c0c800000c65800c0392003290304540c40c2c00045445840440000401c00c02d80000560410100a0808101d00c00092003401c90240c01d00c00d0241011106400c1c5c6e02035008030f5141c5040544002020345000f444940700040c0400c040e0301140580c0d103c50f40da069145a02000022400e075140c000d80142480c0e8000900d00341c00410045422919083c1c040100ca4070740d41c605070036011800c1400013849482c028843e00340490885100c039400c1c6500044c6030865501341c0075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 370316384 1250 370315134 370315147
    0xb2b09060207030e1e01020706050a0e0901030302150a0e060411010e1003230405280503030405100c05031506130e0903030429010e0c070501090b01080613200402 71
    0xa80881e0b20010003100841c5540200f8100e506200001e6035190361900c0c114400c002c10400045c2d074401c9136100d9030040041c000340b509030a922521051641d030314068034020b000d58407031402946903110203148000e1907080c04001030b90740e201801140108024030010b4071a81d2903c0d21181c0320301010142d5103041c05000300b0f417101c1c2602d440c19108001c07090365400092031480d1403a041c155070754003240f440d00c0c0d4007040240004560081503202c00c05010744a0940341151030b014000781150104400390480c000482080203000022545040450400d031003040300713000a20701600e940c007064640d0207004070307100443c0b001d6043c441d0042c03d01ca69601443d1078071668036820141101d034100c9155021350000b100307020800605520a12041082d0780b01400301800050f00c3c41c4840034141701d514071096801c070200c1c00081c003240072600c0b030701e8229001344590342c25030610800303030701d030a103c0d115a52041c000080d0808481c6640110180d42c40055211540444895080159415480346070b10903420420b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 370317634 1250 370316384 370316393
    0x206040b031302100e03120c01110a030c02060717070f110106060203180a0509040b070c02060a0206040b091f05100914040629040203090c1002010b03070b2b09 70
    0x1952240c26401010b0700b800040e441407010103c400ca1024052241100120180e0355000c0b51041100c0c88a40481303485142d1031078a2809014035000e15903501d4000a46440340700da160300031404000c1c03140c0840b459038660311001c890200e0034140181e440442103003c01c1c10f00348990350046105025181c56500128211041401c42c0c40316840030307005d41e200050005003004022015040d1141c225180c0c03602515040100d4036851008000619066412000514540c0030710324010100d9005840c41d074807080381c408003a541781c2043c0d13030585411070600e002031404180001c4035aa8400003900540279030f00c400415801074000a450080d4441c1e4409020800700c0c210b00c1507520605c02c0401c40710203410302c1c0c01c10008035010b488140b1700246401306140404200680d00c2e02c00b00f4410759005a0726a90030200c507041902103000701760703c580460381c0508a50784c150040c06041c0b2084040e80c420a503507202c0707544c4130701c1002d600702ca40c0140d02c039407403034040d03244a502107000302f5526002c5900d0095a60b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 370318884 1250 370317634 370317637
    0x30a0801380c010509012c030d06030b01030219061e02012406110f0318010309150e07090219080403020709020319061d011406040f090911011d0d0206040b 68
    0x11224a6490110700b02012840034040d2941158100d0000c0007480ca98031525459000150017000907110801882142a6000c00884141803a00b0303004001d05500ca103850b122100080c402a44107549a1268610660440c0700c41c5045810980b5400c2556168104608100c0c488107040020b5542c8c40c03184101c981c400107a00f1a102500c001d0f0704440ca814480060600d0f0119051106250301c5180305034040e280010486000c01d000000018051802c040120060322650340014440ca02403400074140340b030582c118299004c01c40c01030741d5095445a580104030700503520000c00000300e60301c0d507008140c02441030741d070060302910580d21126110407500c0d080c0d074015141c00b081035450408003009541c2a00c07800300580200c40c0c1c5402c80c58050100221040410300a42e081d2068a19102e003203903481204881c000d1983c405003200c004d5031140164003c2800403030603600448109445640d030340c45040e60507509403e5000d40007010b081c1c5024800002030402049070000c1c0d003041b01245402c01d020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 370320134 1250 370318884 370318979
    0x504051e04050604020111070e0c0f04080d020d2c060706090515010f0e09060a0507030b0d060b091803041404090c0e06030d02010e0c0d15060b1308030a0801 69
    0x8001c2c0fa95043c140300040080341c0d80000340c0d02d50b40101c18107018880751507031a147c12602c0c0740360903500c07102c8000380d402c0d41c3c1c401ca034820001c034405d0f03d02140069402141b21040c1400681360780f11003580d201c1809180f81010b02000480c40c1d182c400d01341d050320305100a404618020b02c0b000407a810603588403443c21032092596022100d0607001008058580d41e40d0f4406000c2580001803030b410812180c2e03690384c90107440b051180b5141c0740000e0615100303521500302404010071815203440030f0304000d0028191412410b000758500c00010710040c1588008040000849008500d000d203405070411b5000f02e040f060b903034015102c14808003c00c100203900d03000b800c0d40255034121400e2801c101850240f080b03c0c89015641801c0c03070920400b002040000403440140e07003141d001d960301d1130020031a140c0c9503000303030502d032a005000c80c1d0a44454003034044070380c48822180700f0f07035150f040030340e600e0051040307141c009080c20f001400002c405450b5508641a910700404030441d41c0704001c40b4056a00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 370321384 1250 370320134 370320143
    0x20a0f09050601020a200301090209070c0303150503031b0312010902030105040506010e032109030303011d01081207112e0f030509120a050d050a0b040f150504051e04 73
    0x22014840403805201d5503400620074001840c8a030145d83c1c03030780250806081d040c51005154100c210f5a40c40031740048403156030091681201e031070140809081e54422032405d40000e40380c21500d0481e558004c0c0310a094400003001035007440c142281e02c01c004040000c0c02e030744500050040c44440c208070781090380a84001c805c00350309c960400041c00102ca02c020040d5040101140410440c0d403008681d0100500810710b607000ca0250180100740103208005c0041d0309480000000140344201c1d09078020040030942c490803240c0d03a11046280e5900e0780ca1800010a003080001c00d0005607990300008148170b01501d1b00740c07a08100681c0d64090b01d020814500318031403215406070f003d9885002954442280e0078100114144101c115030354000781c00102c88484d80015000028a001f03106490708482d0f40c0f030040c089854103000c0900500b1281240714003590030040d081884103140d0240c2c6940646004070386c8601c40c5080100405001c0150404503c544610701450b0381440c5140c9640c07286014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 370322634 1250 370321384 370321409
    0x30c040e07021e03070b0a1a030604050a050d0c0b070e0a05040f0609060b07050a0206070212030d060e0a020403050d140408010c0320161b15210203100b07060603020a 73
    0xe010411400c0c002e80c1841c3c00194108011600005004000490b00594400700000e515443c01400001e0260741d040c01590511416040000b00040000d0880700140b1480c04d03148004540c120684005058141c02020b00382c40b000040d000a1003404500b44020000f005890705554860110301160044007000c1001d9448130000e1088880c240240750042c40101651841d00c9060344074551181d0000704020310a14000400c1801c0d0755542c0c142d2001c0c41000003c1e00c0d5524042441d8030000c010a02c103840803c0182d00001e903140881c1d2080d01c0859410402904d27056602c100e040b200b02e88135094454900c1c40501002c0340b550024030a5503e0980f10f5100051007507821140c0d0796594a5840001580388403c00c0380c040309050340038003034046940c00300e50f40340041281c141c00c0f00710708901d80198521040c407000d83c4020030780c0460030461040e0a100b2145002904200100a900c0211090380c1c05208140d02009104040c1006002c600d004041c0016004d880384d00040710301c209075000d908103021 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 370323741 1107 370322634 370322653
    0x17060d06050c130e01180c050406031d03031008061510050f0c01020f071203050103031b0c03050106090219020c0906010e0409390806010b030c040e0702 67
    0xb0f010551203100380c43e01561845103909205001020107020070b00280a4268412021030501039660f10703241c10305140b000d5002c4c00d0404001800d05207842980c00a2800502c00755018140c00c211a507455880c10819034505030010782001c0d44480a480d04038040d0342d8800d60b61031481e0307090806076184d000d248500c80705400350000101080d40006500c0546244403002458018480d00c021150721200100850446009000040c00f0601e4009064050240310740c0a202d824880e4800004454491b0386541c2520036990003000d0351500400c8401140700303080c01013401c3c44401d200401440c8883c0000640869000d0401ca042c1f021549401c1074a40740c0c0e40080030b601d50032102d2910008088100200c0201001c0c040340c01c0c1c0c19001c00d01003120342d4510086021070b4030000040c4101d07400d00c4c3c0e5040f0036520141031032000f09402c000c00100044240c45a83c07046042c0d8000d40306056 = true := by decide +kernel

theorem cover : BRFrame.Cov 370143884 370323741 := by
  have h0 := BRFrame.cov_init 370143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 370143884 ≤ n) (h2 : n < 370323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
