-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4615
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:11:17.041973+00:00
-- url     : https://prove2.me/submissions/1af2b365-06e7-47d5-871e-14859860b08b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 829856115 ≤ n < 830035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 829857365 1250 829856115 829856119
    0x150801110d050a110409021e09030a14010b041517010605060a05070c0527070906020a0f020411070516230111330c0705030a080919121d 60
    0x840c04995501c48401004002c050403011551840c0400b44406900c2c0240014420100d016842d111200e2001c0c082c0c0345804034082d1035403000c01805403961400b10346d01007000d40005882e111800c4200460780940032000026078480d1501c4554010145020005030644a01c115a0b285150b14030b00303110300700c03101d42c040c1315032204003070140e011018403c5008000c468841c1c540074000c01c1d030b04c801084542245900309503a004000303003071420080c3c054244c240c2c014170178507120182d580340a20203501c0d10b06001000d05055240030300d0205540311900981410035400450598a0314242401510307038402003288100300361200000078111480c005000284001440c0c40d004c800300740001900c03d000b5010072645203000300c078880c18500c40a1040700c41c2e0701f0b0716420b0180300669004d00300071081030020052200d5507030521503040132035400002c0d80d4000c0040d003400b00302611003002d00380c80c1c40044000740e500f4a0072340c41d29000300904445041152040d68a5841002448100000e480c040c0c46010766 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 829858615 1250 829857365 829857367
    0xe0307050a17040812030601170103150207020402070b0a05060108090a0230070321051c0507051611010806090f0403030b1302040308130512101d010c0315080111 71
    0x20881e109000014103060305442c602e003540d15002e55042080001c1d00c90034214000c41002215600b0082c002d445154414030b5000c20740c1565103000800e41c4058020020941c04640320046485550440704c100d43c00031043c20140c50f090603090041d00f0b0894100740001e0700940030601e542d000141000c1c070035a00800c6042c01044005840140400140d10020400d858850400b9644800d10114004d14042c09025540c4408444070042c248034403d0700c0c00410004104844403c0980b201148200e9081c28000c03410b925110800c54040c001c003010703403159204c6506804108060340c2015008a103081e200d01070309a403480300f0803107540c031304403003001c84400700d8000180024170a030700070199140002c20b03140d203981403d04450101e80158104807140d070000a10103000c400d0707910070100181022185880c6207225001000c0d1980b40c02c815500c10140c650502c3c45030240a08040452100d03604002c015007828180300034041c0000000780728031f00f0800140070032400410b001d9004c190351840400303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 829859865 1250 829858615 829858633
    0x5060a1b02030a120b18010509010b091c03050f1201080d03090302060a09020a080a0c080106080609120c0309060d0906050601020c0604030b04020d0209040b100510120c090503061006030e030705 85
    0x2528400c0c1d0303d40307a0040285d560340000c01255a001c1d500d054010b401e24040311250b04050078468200410303000100050028080c0c0c200325a00c68480c006400900c0500b0000004103140036126409050b00c0c418000001091180d42c1c0030703090414038121011841110084440c1800980403500c25003800380c01a084040020701000b45074001c1002140b0240c08902d4030b135a00c40a09080540c100011901c40200f49800c00000000740252009440c205002d4645410035140c000d56a00f035101250070200000b05240c88541d505000b44c030b000720000f51996945220300c0c3d9244009048071801243c001c4c1c5003101040481d48002541c10341c2d03110183ca450b151074210b4803000030199009000301d0b44102a11203120040c3c51701c1c507100340510f105060a5580f418180e012080b6140103402a40c002d00408084640c4184e0020941c00c2c0d48244800c0010030300f0141c00c007154074100320f401c05600b40c41400e060115500300304507140c0403035416540400c01c0c41301240031640c9900c00e180001d0420742c411008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 829861115 1250 829859865 829859867
    0xf0207020a0323030327010501081c0201020906030415152106060b0d050906090a050304060503130204060602100b0a0f033008010f08030a021f0605090405060a1b02030a 74
    0x101c0d00c1030f100d40d000503042c000e80c40409626540c000c0340d00b1541d14060250700060212810600c06403245100000d0046604000134240d503040c41050808a10451030031030b0004070f000f941194501a00904400d0752407405003411000039009507240a0b40928003041e444048a80c0c40c1805c051381d80003040d4003840350109003032040306c5110708801c4d14400e5603036400040c50f580b171400601032248200800315051900c0c0b14900e05020300100400400e0300454625000144007208440540e0100d0030b0160b00c07500c1d280e500102104034000300942041c6003a0303000c1103064000410454806440344c040c080c4581d95010302011003014402c143c15441044020b00018049007a24071280e40da240080380082f041c250300c0700c0da003904405d640e000b280c21140107102c804503d42e2590094450f0382c000358504010484000c3d91034021811031a6132015445c1560110301003500250010b00d0014551265400c140c105251698000d80e19100040c2c50404c00c8100d01c2210100382a201400760013a5041041c9240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 829862365 1250 829861115 829861133
    0x9060305100b0a030b130f0501150e040504140d08090d0f120f0908040b0c0c0d031d120106030c08010e0f1b1f02060f09210d14070c05010f0207020a03 66
    0x8020f007031645945104055031219056640064179440000c10321003034081280c0119401a004504080981242c1c2e12220750081d28500004000781c600080c140c1c0d44c2e017400340d403000000781030810074000e89840382001544440854002d1701c0d1401615040101d201094890304240c620040100e49115544c490300c0005902c001030507400d80c64041050101c9641d021030302c1d8090340100d0100034010030070562250003000100d41081c000da4000300010801e480c09000490800c8a02912700000b00c46029070f03444441ca14415490150300920a42c0e80b245004201d03030060b4003e904880d07103820300441ca44000000c88071710700102c2d4805050800005100711001c0060a650160840302840841181354180e40621000c085607601804071401c00c034040501e081c101512400050341f100842c0759402c0c081c444007030040b1114054081d9908004112003021b0180d03250b001040603120320801401702d4100c061000303254820b000800640c551342c0d81c071100700c0c02070031806500301c65203100a00000d14800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 829863615 1250 829862365 829862377
    0x10050a030609151701110403030207030c1a1b0a0503271917010207021302180d08030a0c020c03010203101a07081b01020c0a0302100f0e03120c0403120f09060305100b 73
    0x1400221b4000050000300c0c0840d4041c0e88101c0c010380c0496002c00030303c0394866200700075118407926180c001003464102030071801400e070404484900703800b400c070088000704105e061880c0d1007410741e0780b250601d035080011000da10030300325025040c140109665180041d0705895120305002650045030601d10f41c4e100b2052140300c1d00382c141d035081041c04050b03a01c2c901c2a04e8403911001c0013582d5103115024490b0f0f03ea80c44865140607100d82250800000c0345201500d52000038650002900705000000301e20703010760401e030319400d94400010301c4611007000a0020a0f02e903030101441031846400e41481103480380322005000420184403440c80c0c0a0002424070054000d500050304101d121000c00c0d040503a180c2003103000d40c0c003c1d040900d800c1c0890056120138944c126042150000c0d8080b007686078800c22030b502c80343e40030641c00120780000340402c0c1c60146401c84072811500c4241500500740090814522001c286d680b000050180e00c240140340c8100c0815030440041c40c544010b800303a6400035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 829864865 1250 829863615 829863659
    0xd0509040e010b092e090f060603090c0311041d0303060f090705040504110d020c0609010516050702040903030912022b1e0306090e030319020903060f060d0210050a03060915 76
    0x1171105465811400c800c810203404503040c0052000e43c03492030302080350456032000c03081c5400e01040501083c3c00c03100c07610413290001307001001e03001271400003001414406540e00e8100c00035800c110784110008051071050f0400d46600d20342c58507503020881000c004680100000c1e000f00010b0141c0d0905801c041c1a00d0ba48000c42401c144000d0702d004103a0b007010542801c90b40c07001c1c04210302d00c0400d008103078206099010041001610714002403840c410710001074081c580f510b0340702042610907400051a1070700b1800040384444a0800251921303011200203e4007012458007807001d11003514010328081c40d039220345017011001000010110b2400000c4014140c0d2114009100292409010066005400655924508580783c54190280c002004083e20320611840030700d502d00240c1143c11159115240c03600ba50f03802c1c0055107042404100075003100f5850014804541c01401030540180603480c18489640c0b2410804115030380f01c01c82500d280c003c10010820411026560401c1101c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 829866115 1250 829864865 829864921
    0x31329120a11160b0f251404080d0807021002031e060f0301050a060f0b040f051323180c0a0b2206020c010f08010b19020f0d0509040e010b09 62
    0x1d001d40e0414020068401e0300c54035079004c10040d50806203510f055100120544034951482440c4e482c1011603140d84d610018801e14006a01e050100e002c107960003000460104e5403401c00c080002040e161007954200003502c03880060b40000801c900030f882c820011251001c940a202403621000310002070485500b00c14403800d0000f6907242070160034420f140700280460483e26114080c861b00c949030f402a0f0030280c09020500404030380c510340344100e40c0d0481d80e030f418828460078034000508003000c079946d164014921002c25060b442411910075811503180d904124808200303540c4030075211141a5018100c2c07074061008044070750160410012400719070303010641030b1081201020f4142c11a5016a1011f003100034150b9014011100600d520b00d415803055140280c14200c5000720384002c0781103081c2c100c110500174420020a26602e0500d4100d0f030340703001d05000203455075000141080c01039003044420f040700e6105000318640010040c6c484400783e0f03100c0f520707605842d010000820410304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 829867365 1250 829866115 829866127
    0x19050904090b01050f0603090d030c05040909030810081c030c05070203010f02030103140f0c062107120b01020d050715090b090c0406060c080702040c02031329120a11 73
    0x21144075504410344105050415541071000700000c3c003005220300e9214850410400208036400304503241c00c503100341000300d50200e0700345090350300e070046810403902145018880800d0640c4582d03594000c880948918115644484c443ea1703c030b180034090056941e0310300d4201e400320762203540100c42a4249140c1142001c5c19a4000ba0945006825400180750048010301c11300c42c86042800e0381c200c0d80d4004201281c03294000036217070038000d5040c600c80c60f00810b00f000c081c403044040c51140184002825070910701200c2c090a10140005401a11858585100b6055000041d03440003d0312644800307040904540d901d400c041c1c02988500441915400c0d100000b50b01c0d40036203409034103600090450444810180011034025a10160030002c801c0f0304040030034610421124a00d070140c030082603c80511400303074514071484c0c0b01c00307a20825a1000189440700e01d8040c80303440b0744051140c101044038000c2c2c0c3d9071500851008075030007100c28000c1607454a00d07a10102034010450340c180e007050307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 829868615 1250 829867365 829867369
    0xc06071d0a0b03011401030203060d1401140403020114090f030909190c170618070c05010b03160503070e01060e01050703031e1e1b110a05070821030103020303190509 73
    0x1034066400b514a00d60084014001e02214030400d8401802c00e1804504600d045400541d1049203481c0c00b50101400d00141c0a14070020b40025114003400243c0110500341450001c0c020013207050050725910a10001c16012140420f40c0441c412415000314100b0414404000405c040a490401102e4041a00000814107406541c2c40d21459868080c0f4954034003203143c051881c000c1030240b1030003005044040e401d4400f5462070300245245450076856030145002801800212005503151086001007000c044a04022500780c42003078064075031450383d0303a111030602c84c0c080c000c55000c00d4440075982000c0d4825000340c42d24501038900814040d10603070412018460552094800648810a146140d00c0315000c6804181c006d2008004940504909020100000100008100c210240f595003180100080343c0c030250040c1c156100389550f1002143d0300c0e0001300f640100a4076241c401e0440007444010380c1c1c100c07600a0051850102090420800300c110003000d04107000b01401030070915 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 829869865 1250 829868615 829868629
    0x5040c11011b080a02040506040311040207021e01020d021b090702030d02030a0603031407122f01322d09011e091110090519030210050c06071d 63
    0xc044004180035000c80440b00601c518401492510a00e004000410042d11207904440442c0c0c1c1285010403110710400004000c0c1c03194007400307544000308050080c50003000420480c240c010907021074035154150601a030300c0740d411000c5c1d80101d55000b151802c050504d544000d80c4022684142c1b4584030708180d01004982094030304a04141c0d49440900805410101041a10300260a8a403c040d1969580f40c940d00008a04030b0070040333884c1e0b40701408044d0045a03c62030006a00904070008a07240c20f500a10100d2038509102c0b500310000600100d04035164414500e00d030054500380e5507054050318110214240c120740d92004c0d040f00c0025a251343e5030060150076007100100c2c2e038200046291010b1059820a10861441c0c410702c10b001500c4080030030340c0840c2c01e9038059001c02030110f042e14110b00c65400160400044501c1002500201c0b00601c142c3e48200e84c1802041103140c000c03200ca000b50240c800b083e03404030001c40c041d54090b0006044017280000128046581000400d02c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 829871115 1250 829869865 829869881
    0xd0506031b0a0b16050601030f0c050409200105040f080a020f090402090a150e090d0f020c220609060b0418110a050c0f070f0611030a0f0f030603021816080408030105040c1101 77
    0x1120041184a270030400d00c004440700820b002c89081c415080191103005450745419104000c0000300303094520680d014009a5000304a0b020429501c543e8503d401919040e142c40304031300c10241c510600240b86049603c80e801541c001d024a2902d82d1500c00c01c034010424242d0841c00001c41140018520300d0304c025844c41450001d0240209500498010342190300d00c0003414255003000c41d808006803613030601004400000074a0f60320a480f04402900106141d400c5150300302d060150100e400300c549002441102c1a0207a105003980c2d001c140c40d001c440700c40c03410071641e0030f0820007040c10602c908094800d1841250641e0501c6039803445142c030f00f44842d031065203811240c010030428160451141c07964212200041c600e02161444010280e0034407943c08800d10030f4200016281920a0f440000a0344d80945482000001d41c402c1c1380414034200c1e039002480d00042c442c8210385109080042c0180ea20035003080c29a403d000c104005041c1c00e45c03a0404001c820000803001070824064524 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 829872365 1250 829871115 829871123
    0x711090c090a030c0905070f0e060a0c050105090109120c0803040305071b030b1006090e160207120809130b01081b2511090c0f030c040801020d0506031b0a0b1605060103 74
    0x291356854400210142d81c03008103500203004c07604412060341c5800030407900176180111442a544c0800f00d80c1584c4d103480c1010007410740e41c40c1400704a240c6070150300445034180650801d1004050781b031002c598071049880010310040c000d0011500080c00f82000d0914144103040340100d41d07103000c01c1241c0c01c04455100b40e0302600482c050018480300e80110102401e03440c41d080b1015800d081c0320107070310500a00b10f4088041800b0002200d103202703200e86c0f809081d540c1c419400150b15420107200c9034010850951041d00c030040c0b40051100d0078883c81e454024103071034081460707503200c1c5019100c0c4106039001440060400204549641c2d002e0748240b03444c550506140b40f86a00d0900c80c140e185040a4540121a698240041c0b08400400d07500a0b540b03510440350b0b640c1d610302daa01d019001d2507012692660000c1001300d11660160840c0703102e007105800710b035540b40300d9080e05d2501d01000b100e40c030740102e4110002c2c0403110b4098010000e103800c0300450310030383d120396403141e19003602603205036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 829873615 1250 829872365 829872383
    0xc070506040f020a0803090306131b080a06050a02030f13110d0b0f07030b030a0f030903080d0c02010b030c0607060b04060e01080d1403070e100e100509030c04020711090c090a03 78
    0x110441c13620100c00c5000c0c0010000039400c101760a008260b50750340250554880f000000320320320070000d54081504480050845060040742c0c3c2d1039403a955901440700c11500340c2d0525000510f40704c0c1c00e200341c034030640d110030306207000d5100c08441c002901400311084e1030314001010781c1c1625494116104a0441c032906400c0158a852000b1100415019000408050500d6980d60050380d0015074078007142e420001240b0481c40d50300c0c056540c003140360710003411080045002070440e040d82c1c1c4210200c2c98543c0017030120b040c16004168803014081203030b0b54050418050346000c1075480d80a0800c60364050000141c20780c88071300001c40c0782c0090b400382089900807201349502a0703120b007004e074200503030065140c218244030780c0c05440e950603600990300901d1202200e0440b50f2003003140d8105000b01402030350a45801d2000207105601649105011f84282801c0c00207034100391003200c0000c2d42101000c144901d0720780401c001c10030301911030b040605081c0001d2880d680d44d400b40c24015441a2442 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 829874865 1250 829873615 829873643
    0x801021b10020307081f0f03030509090a050f01181401080c10020607120c02100914011d030d1104080114061003090c180f0e3409050c07050604 63
    0x1103161440700100001601c0c014000c3c000c0b010b030004400c54120300c001034002214000480740e40b900490507401a840f0350820b540c00014940c200e401421644402d5801c00c025907100800502070307640582d1841816806400100003140040d03180c440f44400c00900440d41d01c0742c12019417617202d02131f04023401d240c21035030b00e49070b40c0e18100d4403142d403500b0580082e01e21442c0080300a484c0342c130032141800500352604540322949209224081d80700342282c2003000f41c070566080c401c8452030702a20a032042c2d0304c0c00c10110b81000140c080c000b0a0b442d010011031404c0400c0c05403d01901030301d0a40301d43d980d428007006c40c2502d02030103210380074070340400210003d00d401070403c6401c43d03010a01c01d003071503d0030f00350801040d80c2407046010340d000204091911124844440000c1c046d0b00c0581808901c0d25410304c41c40503000c900105081e50b1f0001c24481e400d104603016032810800b8040b1a260403808404216042150308901e42c0304114511702c504043c02c0384c999078104003048404550590484ca40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 829876115 1250 829874865 829874917
    0x210f0702030f0639070309050310050a0e190206160f03080411010305040f170d0e06010503060603030c06010311010c06020d0b0a290f04081603120302031b07020a080102 74
    0x110803c0d104882c4d00f900005004142d100200c41303005401245180b400180e001c24103028901d0000245009002c07900444500414240140340a8034210704c802d0509904004034500080e0180c00e0402a40304030b80f00d48015070070071525503c00c038098070a8101190409012905138030801e2030145c0a502c400c1014580f174a400035010403003450042c18180340c1000d0002148c2d03001814045c00d9401501c1031007185107402614510300560720070340d0495040c10082180404003044440c100d43d4140c0498040d034a808040507140e0048080f09129a40460010004145c140b10001c00c2004e041c1400e0481c05055120f100c1079a00112064500308d0b25900c00c0409800c045041c01c004109500e2080790303075124648030814810a0038159a8001800301c0c03201d032210107a508481c02000070104441d64204c0001004d1300185c1503100c00d40d0304c000703080714455040e800790085901c5009402d004400764205800c05440700e070018070f016031300030f5400900031034009800d2008091800500c92400c00c46406400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 829877365 1250 829876115 829876141
    0x90604060516120c090b0c070501030b03060121030314071d0102070e1b09130608121312061b030509070b130b09191202040b03210f0702030f06 63
    0x2118565003400320040c2440c5a42c00540c240345000f5074400403443c90600f003000c40c2c0d140300a400c0f10107108400100d0b1b0014100c0001e0356001c8840c20788050000400e62420141c03100301c24800c1810480700c061004404400e0044d00c8036000e807081c240012100740c203c0070003001c08000c071001d07008200603100d254004008034543e0300f2104824401001e9246c02c00a481c1c608d0341c005050140e1303171511070840402031070078201500c034610000b4000424008032a142d04c400341110b13124580050044107150710092001c13200716030240e60840c0c03c01d10300e40d01e4680d80d034004031910482540c0b540c1c0c0c3c4101c00a0701040d6140c841004400e6a607010405007894540681050b44540c002880c9070030070840020148001009a001c4030504801a512160120041520314650300540719400c1c10742c2c0d4001c00d41c407080e002085c1c0a2402990304001d00304181c01415941c00e104004ce1003107400804c108002c85800790020060701141c1c02040b400c024150f40840d160480280901e8510742040c030800400c015288 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 829878615 1250 829877365 829877371
    0x130501060c1e02030c091305060a1b050a020c0607110d0b07020601081b2e0f0f0c1e082101051c031b0204090b0109092a06031d0102030906040605 64
    0x1400103101c800c0b5940025030751200c50508a02400d000303000a100c020480400d02c0d0816003000940f0075a00e002c05860300208426214080000441c00d42e42842d24808c505603400e0281c0c98000300806006a81080201d420030281220032200c403203a5207070340b030b180c1300071890408d032144590203814201010060b040c03550507080704003694004001d0411021006d5689890848195104081c1500244858140c4c89c0090208202c00207090b815401c842e9104180d18017191b03280c1d42c0d140c081401e00704102ca10030026000134101c5a9040100c41403010b005080c1c100c00c6208130869403800c1504e110180b165241da610982c801500d840c0104502d091031031143c500340c0401c1144140d003140c3d80d0f5002d007003004200200000486900d5503941103448680c0138484107504440c00400035a0340d149900058001c0000446c2d100200841d00102202d0900591740300d0205c82d02545204c50400400b10700030241f00400c1ca4070700c0850141c00070304141c280300441c001e10500015114500c5e10b0b0400e9401c0c1d441c0a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 829879865 1250 829878615 829878653
    0xa0b060a050703023315120709050112080406052a030717040b030c030408090316080c0307030302060a15033207180203060315101d06030705010e130501060c 69
    0x1500a602c1c0002640e03903107103221450340d207040c525101c40206c0407140c1009185680c100c0c5414040840e141c100107012403c075048504c0901c01a0b881c0d40515a506200c400004d001010920003400064001c030080c02c0c030414001142c544400901c001e6410580d400240c04803076400001c0c05c0e000b448031206500d40c0d0503120403a03241ca814648000a5050300c001840950172440101c086020000107608407102480c00030112900c03012007482d100f0641c0c52134803c180340c40c0300304a1a94031a04003c070f840c8040702c0d0150040e10039275a8010120000c2c14032026030701d0b258800b118000c400520b01c05032156801518042d43c1c240c0003659900501480c4005801c1c011560024070108030541c0303000382211456681900258803900c81401113840d1480c0703807003040e4211803604200b00d01c02c0d4185204c036046a0351105103d004a0a082074079842860030341e0300c15055041001c06001c1540a00f0080c0d605a0340500950842c1c1c105c0300ba442c045583c282c12101c0000d0038a2900746c20f000135220007072412050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 829881115 1250 829879865 829879903
    0x92a1502010207020607030f021609050114030109020f010813060e0f0c06040e0412030905010f2013031106041701050109110f07020d0203030d0c080f010e0405030406080a0b060a05070302 82
    0x83d40c00050302801132000050800c00781105001000d48240100781c1c1860001981c03a02850315540c1c0540900401d01480b160300305244240b44070307890140509210a03070080e0844070001031040c01122a000010b1041040e1054401c40c0c4002812522400049080c1d01020b8802e800e00825001c0c102420b001d2860b21802003484248201070300100055041036114800512040000d402503007e826a481d015003e5441c1020003480c8106680100c01102c080100c43c481c500e0703910002c1c0001d40164010020340d5a2041403d00c0000c000545d0b070b081055000303040b0390601c1ea40d03540005a81d00214442d284a075150350040010319458042c4200c4210805061810001c07440203800d0700340119507010703100740030702e06002042d0745041c001c45101e420241030502424401d408040e00e908025a040c1ca0740d01d08140001640d25080c400030790166038014040c5103494903052088035100d01c080c01010b0394a94a04180302140e640b00010154013000b0740758642c0fa0f040c0c1d0b003800b90078001c50f10803004d28004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 829882365 1250 829881115 829881127
    0xb0d230f01020c15190b03071a03060a060306080c060304020616030f0906050f09060901110f0d11030f03190e01060f06031a06091c060213180207080904092a15020102 73
    0x34142100b030b11500082e41c4c3c005106e4000d000024036055450780510700f03d2250965070b1880e0f41c00c1c14001c504c00c0c0c1c0d0039240d1400365a40d6142c1202110800e2054040540160b0f1540c6c2d040e180840055421900040ca01420701000d1900c14984005016049010840c81c00103804c00ca500071516200904c10b03070800c81d04220424040c0da03101d1040560462187c01c000614484581c042c08440418550000440f142d90742214940d13a511a40406803a0119004139801040c007080001102d00078084020305034110f07114000c0c54988400e10f0410006055210400810042c1c0c0902c140001880220507c10281d40b40200283c119031024600d403100f40c0f02d0801220305510b07450102e8459240644208400c0d40f540c002d0340e20b618074100c00081084d40001030f08000351000400c00c0303050310103020700358020311a901c0085c4200c0c861844020004075042c41056260f18203680318020282c041c1c6c20404c0303c201c00065640001055400c85003d6040001091015200d44800d030b03940700c401400214a022 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 829883615 1250 829882365 829882381
    0x1206030d050a020a12110f0d022802060f160605010611011b05030601030603080414150c060f060a0e070309060b030f0705060c12070309080606040b0d230f01020c15 72
    0x21300301101c081c110f512030b080c07070414035482442d58900103c6404161203074480d20b01c08990703d8003c03a81100700140b00b00f100602080c0312489103201840071f5485040008112a4240142030704144085280d0f494248a8440301d00240807092802c80c4c49144002a00e40c1031075809404c108a928005000386e14280f8081e980c081c030784912036100c401a042950300c03030352070800480c007401c1950001000300b81302003000981d201c195a00320148803012140741c0700b0102000b190803194080c80342d008043c0c0d40304401080044401e05043c50300510040d0030070188584038014580d000c6420303110400000d590703602110901009104000c0450801c6001e400354640d034410b0705a0300d04c81030150034890903001811341403a40c8100302c0007001e140c580b0b0106440c1d4501d82000380209255100784140f5008140004001e403a29110302d00e21840c0042c014850400e80d41c42d840011040c1030031404803540c034000d40da40c50311020001c02401d20480c0f000035984100386140907041c1555440c1c3c89a42e030041c81d090107111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 829884865 1250 829883615 829883623
    0x2090315040203011811010804050c04090f021302030c031807050a06080f0a060501090515121e1b0a0c030e04051008070b1204080309070b0a1214060105040b09010c081206030d050a02 80
    0x91082403a08c50340726102c90403c01d00b420b1070017011540c41840d2882084c1081120211002700c01c0c02150200c00c000c2d03032a072021050f031004031fa054a2a0008000140c141c3d910329000807410401c071400c4a50440d169004200c0e14021074100701d01058100c020442c1000c1c0e10301c1840d6000883c1c26007804014640f00000c0c0007080d150050600c1044182c2c400501400407106403804900080e1100c1034a003462001e000084034032001541d02c00c5140d1001603100d41001028070031818143c02400d2400410b09800c440800145c2d004404105082d62000c59a55440c0600e80c00b50300d10564901c0c140d89400006882c0c4205540108442c0b14140011211717596a541d505e948503810000480e941d40c0d8101e8180c1c00c3c075140d40c0200c8207903040441c5a00d4042e6000380c03000c0e40b04922000810094580c013070000700d015030072140ba40c000f49081200b4480e2070b40c030001401d8003a1040c103081d40408039580e82e25040c5d0b045120340900c080399400810005240420607800c101280d409c101c0e1611040e84030003034035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 829886115 1250 829884865 829884893
    0x1080d0207060918020d091a1e0f07031407020105061c111507060905010f1d0a03110c0405010914060a0315201215011103120a020903150402030118 65
    0x9040510005184c1c60103085c2c04a0b004903d640c1c504004080d0545005220324080340d0303088010400e03a02c005000000c154400f01d0844c0e044903d80c465981e20420f8902d025000100342c0c400301521021074484182500b242213000d1340c120380011910349418002d00105d840924510900440500c54050100e001140c10600580c01030b14813801121019080d0b1510b403045100c02814286000041024480194403822400d680244107000c11002281500710980c20000c10310720f590851250b090010317020b98500320310002c144003511102d900072000101260001d9000d1a2101e07107941d100f0380c12440650280e940000125a03491502d801c5456401034081c81488613003002d913403110900c165059004088000742005100c055488541c125924aa101d0603a02201c0d0388c1909041001c0b150300840e1005a064000f000550030203500b10b503e0076400c0d038098480300030182d0801c152034098800344918020fa0f000c96895240506082c07044c5400c42c1e0b4010628141210b200300d9590010302da0204441e6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 829887365 1250 829886115 829886129
    0x311270601030917030a050c04051f09080a0308040203060c03010f0b0705101e050c1602040b040b2808160902070c05040e0c03240106082a0301080d02070609 69
    0x825550300c00182c004140818001c0c100c1030300da800c148010051400113512420700c0c0481805151541812184e5a020f10b004480d1710807100701c503281c2c1c0a081c902e0000d407458903901e0000c010b956102d081e076007011640a000c3d0300058402d8100300a6040402409400c0f44615841a145600d0130941c0b5001c02a00c0c0120602d0f035000280c1002070100c204a960b03403c605d280740401494441a9904516000300066924140c0c18000062000c60380704095802c101c0d02c0c0c400b0108c08201c076500f088020040aa81c080d40103580300200e48064458103c0200c00d102c0240b10b2072112909400000050300b025801000a54040c3c0d042e144070004080c5868111142e02401684902603031038181d005011580026402c9803900c0780e04c030001d03540000c5a030030587c0c2c19405d540c3e0403803100c114a0910308a0115518400800030b0040085034030449081c2e610014503106040d18185100c54120341c1a82032400305488240031005100f070541c10f101464040700341d4002061601d1402501903c03406241c07003040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 829888615 1250 829887365 829887439
    0x12010f0b061905130f12060b0102010504030f110102070803092a0d03111509030d11090906090c0705011a040c020f0a06020912010e0d020d050f0409092a0311 69
    0x1070390b80300030001303060301401c0c40d40c41d4092902d440b0310b146203114240c1c5100b541c0b03035414909482d00d5540180700b0743c0e00860301581d8850b0700117070300401643e43e109042d40140e031640d401c0040c070000c9100c500155004002c540080c203200035007200b201c4055100c5c500c03030210708148c0089180c01591032006ca02d0071941c0c5400c1c05440650b492003024104019194a02005c44282c8104a940380c0302100604200e210007204112001a11107000024040c080e55030341c20007941804118070b868403007807035640442d6800307145160002c0c81d50f41c1e6084d5201e004074501c0a203010003100c5030728502802024500c0c0443d02c0100f400c0c10400c00d0650340e0790320060016021680c00a4480b40944138505a601e640c85801c5c001e000100165110650300c260303030b61030000103004a80c182101c0790303c158201c903404030348100c0450409003010703419001808405c80496100400302078505d031036601d90a0074403058805850200f000c62a42c14080708810400c0d4486100c6c0e10111b01d0b039920140c0031405100000d041003034038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 829889865 1250 829888615 829888627
    0x1050114150f181f08010302150a020601090b031609060810050405030d090501200403060b010903030c08210408031008060603070608040c0e010e070201060f060806040f090212010f0b061905 83
    0x8264008100d1001d102104d03c0d607408100710b25004130840b81241c0c406e40b40c0159000e04d00c000080d85001d64081c040c0144c000c18010003008219420021610600a0076501e541c44505c83c1107800403500d9000b11009511040d0401000302c0034400b2800030800c880e4144020b04d000c1e03071440d459200e1600d00340c500303580d551521018000701754000c4c004001500d001409881c8000151202c46e08540310856585003854032829195204101c0442240e03490780700c0810040c071540d10002d16810400034146403030700c01c62158030210724611345140180c0c0200a0155a0b003050136401c8005450b6030003020036584040c0900003203413000180c41044800d24984040c44d501d0740d1600c0098a070182c3c0c805003400c550f0400100d003080301201c20b41d00403055a0000c000242e03a6049900d03001485104a101240603900042e90743c1c1055000241490b14030703a000203600e42a6400543c24400e0740c1840c02040c0e54528800c245101c442c4988a20401c2c11542c0ca41004660010942c84031240f0581c50104040400c032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 829891115 1250 829889865 829889869
    0x10e0c03091515031908040630090303050f06060f0d020906070b01051806090403140c0a1103160b0304020d140114190c0807030203060d020301050114150f18 69
    0x5007040c260b4440401c0e045800c19186240c0046440c15500d8807a0082c403c1c420110380c100014041d2581e44600d81078206403900a084d85d0171015451440a08800070003e440c206021103460150082038104c0022001c5d17181c00c0040880320700404501260b40b101c070a12550765541070568002602010b11959144056298140680620681c1d15000000843e0f444100021680c849042c0c0e0000d584140680c4218020080e02444c2913800c0380d000701001c1c0115011030b2082c40c81d51454100b10b40414580034038082c40500c1c0c02c82501302030710081e5000051075100d28050103007080c404038850015250038206004c0b04254800a1310080c0301d040241100c1d0100030401104184524410000300311001513490304c280c004030221840940c4d000c0c01d0219207000003040c800c0c60401502550b8003802a965610241d00a5102614103540509405101401664240200c2c0c0c0a05000c0d05103c1a00c0b130324005000e0f0501000a444500a1040c85003049101300c1900b503582480325404004106505400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 829892365 1250 829891115 829891123
    0x15160905100309020303120a0c02031840051311040209221506051206040c0e150d110906121e070f080601020313050f1f0207080d0305010e0c0309 64
    0x60021740502010442d0703200044a001c84a00c2558841b609200d0500a044100d0716881070401e000700d9544000780f8080c06061003001c1034a08810611071900e00c070f90b5140800f07021180c6c201c40d6441c042c0241c03a02d01030031949004541c0c00c09a4900706407080850350390382400c80001c80c0a01c1740a207502180d002d40720b903110826450018035004105a90320342c07204c42c1030054600131440c0c00d8054041440001c80900c12811501050325140b00b1001036200c00c010040580450f1255008114401c202a69150b8902c8140380765044100103140d9170700000e201100030781b01c03c0d4404205400b010310580c00c003500c480d000c4031903150304035a5040031695102d020290300803028158404040074102000203060b0420784001000810f5121200184c0d112001241d4900c90603c80d0540707111200010006070400b42c0443c022010b0080c0803106842c89041c1c0c192403008045036020041e07014003800c00c00c5110078420f550510241d03180500181d07040500401c280c0c60060442c07005048004005540c90740144 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 829893615 1250 829892365 829892381
    0x905150411121303051c091403040303080112030503010b0c01020c16030201080a0b060406030b06071505040b0a0504080307050702011e02010b04060807031208090717151609051003 79
    0x5000700061510003403007030034a03000b05600c0c03105180c6090218040d01c1036440015415541507982d107142050b9503100d901d410b1420803400100949612a4000096441091030841e108850003192120702c0c1d401c5c020403c0d081a0300c10350480307070040d0400300865030050499042d90031404c40b640c0e1b00e8048096441c0284681c510074603a81c060400c8145046030041300341000c0301d0003640e0f410110b0b00c40501240071078040451440e40700030204800c01c44503000f50003507000c1304802003005080503682e48a0248500d011030140109036503903010041009513001c10203401401140040110f0318040e034490505100290004003404404222403045a01c107180032030b04500950103080d0158000301010b4042d000d5901d0561003a801c000c00805c04102c00145481244d800040f0002200d0303200e081502c48150280210305940114a408218417294004d56104044000020804614454080000e190f0068859203015220403082d00c1107a41c0072031070b03070152001150400e032000e4800800758002c00f521 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 829894865 1250 829893615 829893619
    0x60609080d0f110f030706060e090d0e0f1c060606050a0c02013605030118030c200613060e011d1302190804060e070312141e13080706020304090515 65
    0x5138064006100b0200142c58250f1161005020301ca443d100c0c40d4481d550200c40d110310036400201884d12181c850010025140400380603050a08106030209014000c80b030002850424401002020040c0b10703c02c1344018000f51804500b032004506004200b032600380c0e006030420001804107200300350140d0402032080715401c01c1400c0e2083d407281010740c220042c440d00e44a9445c02c4688840030404009072403000e681a40c1740d072203401c0241c0d0fa9000c0c030310107904110360041503900f0242c91625004e0003401d04050802d08014081c6c601f42d401081c103d0400d24590400210490400540c0c2c2000260035038038004a0756400004d000031030300002400360b050311350004101c030034006400c00c0d08003d800780114024402400032100c2c078640c00c0d59030080c07440010a056480c0c042c0300c0042d880340980880c07124600031030b9071900014a03208660a1000582c02c04040800920803200ca4541401d110082c900540a06007040c9081400307034890155110388190f06885000041c18546004403800d102400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 829896115 1250 829894865 829894873
    0x5070b150d030815090606071e05070e0a0f0b0625080a0c020310091109040312050c0306040b09040305040b090409050d1701060302180d05100519060609080d0f11 71
    0xc1420b000702401002d5400e9081103815002411003801c084080d9440340001a01544c6403101a40c0c45c1000004186c020248040f00c100352103000032401d0002c2c03402803407514150070507810000880c0049a5072800385807011807030040d00d00c01e992590000e481140038800d00740c01d1005045c46040d030f403041e181c6c500103104440008040ea111900b20314040c82d490300a60850342520050782c650b40c12126000d001403c2078116004a120519000e003009500a2192609040701c400701103454003601e50070f45141e160b62a0100400c402401c5c2072064072401082120204080d04082e100a0b002e03205030300540400c0ba0700050204004d454039001001901e80c07090498840303032403000006082c001680803c20010b596070000140503403113070003034030070407110b10b0000340a40b5000c41c02c0003004a83d414044940b4009d03a41c2c2014120b0051141e14031a600c15141a2441c0d0082e2441c402140c40303d8000c601400101601400702d408001141500d1400038240550709046c204401e0303c1501c08203030b403100b0301e1007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 829897365 1250 829896115 829896139
    0x15101211030a0609020c06010905091507020601210f1b051201020406030b03070e0f071202030f041202120702060906070b0403171005060702092e08060a02040605070b15 74
    0x4034000d40c841c54507940c040203065240c01d0414164414081031041d140d0201c40140102034503a4042608801d26808407104500034616889541d6000c490410250300090010807001e02940044982da155030000046e540c0815903481c0c21f00c094501b000341c0000703241020140302c2d2404114242c0a4100100080042e03250404954080d51150240c1c000080c10301003c84240d082c005003100c20784404690301d40055851160000307030084001d20980c01c11040d4090a400c040d074510003140250380c0d4101d000800e1810781000824200308202c002c0455001d102503514031044002a01d14103641122110342d1600b100002803844d0003200c10150503000784005000c201508502a101c51902941100190365900040b13852002594030541c1e80100d010809400140751002d0b996510140b516150720544810a8205182100b0f0b4941690036202038101440684010001190f0002e41d01c18154501030420000034040d01603444000c1540b0b1030000410802c2e80110111f03d00018050084403c5038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 829898615 1250 829897365 829897391
    0x4060c050418060f0b120411060d06080a03090605130b0304140f0a03030b240d0f18031e05040b07080435280611070524151012 56
    0x1091030721800480e2030b850304002507040500c500340e62030311030507090480e0a030b47c90f62101c0f410f401d510040e10703901c007004000390180103010784a20302c041d01a0300c0c001c0c2804005482e01503c86056a002841845001e1140720000c044194804003652803900300300d0703100d4440380303054003003000c900d1402c454500914606001c1d00200242203d0514025601484010000000d006107080d14650580b0317000d000c601100302e2a03020310020450210044000140b19480c807100d0400c6810b0400001c0c49c051158000c0300601d1f911040c2c00a140000c0c5941503090900c401d0041c205100720721850440e0480480d90101303000d4204280c1c0d00400c81c00a22003004440110440152080004110004010118007458400300011082070340c011000301d03035180d200f5815208010240714901250f0072501d4030102400303112500041d007402c074441e1004100308043e43d0300b012501040b403590720180c5007a0701d0411450300c0d071204207111140b80c103543c4030107007900076001140d1350241020428001360034003400040314 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 829899865 1250 829898615 829898621
    0x2309031911100b10050901020304260604050c03100203130f0c170a0201030f020903420708061c020103020a110316021201060506030103140a0b070203070501050f060904060c050418 79
    0x1140112404c280c80d840c4003501756524065000c1d214016130003404140404004004001080d8002c2807202102211050340701c0e04c0c1080885084840707400c07605501f402c605041010032425000c0d58415401c42c901994410407044003400b010700250080d039049400d20900390b0409024201c0c2d01c043c00008084060001e640b03151255041b40042e00d851000c850100e02803098400c0d20720010064803142c94651459414090703a409028541100310718080440403140500514851000d070101a140c507190700060403208004002502580f501d16042800e40680e10f80b032010780e03509080060b00e4036014101190440c2c0c03454070110842c44009842d41d0310700c13402410112068130032903188100140c0000103500740c036003910038180c1150b000e00050000800408180b11030070741c10000c840388442c4a4a542c42451000c1c2c3d8044096000014407105024080c09600c0e440074500309160214100f01c0c0214490803030003400541015918183d0280d15413064044900402c0900c1c2010340c0c00045200c01e0f001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 829901115 1250 829899865 829899881
    0x2181f03121b080a0f0207080d1709191e0b04241b0c080d0507050301090506010c113d08060301050402010207050909070e0a230903191110 61
    0xc2800614403140d0b4442007072180c00815800b110450400c40381120640d580c40504030302106501919101244a0504001385000da02c9030b07a070790804420300c010340c0f2159214040c2905d00e19402000000822107031907a08110b440e035004405602d0303203200c0c07103400007401180718004000d90181c2c002d20060107984096585550f15401441019400706c1c80d1a0088800c60320a110314800f244d5180003000c2d01808081e29031a010303001c2c05140036008a01d420442d1000ca88440100d130010005000804962007500d60003402030a0018100c03c054403400500140320380414070410441005800c592074030041010400c25141031200061440d81d000310802c00c0f50401e24000800c50400038000b841c050288501644d0181c001e41051401c4c402880544400148203404a10501300009035881c0d400c029a4030680f030324240015003210301000c0000f4911582c40e9444002c04030014041d0045001c42103455103c01c0300c11101035019501425503401c402c014001100780201607840d10301003e10303000300724 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 829902365 1250 829901115 829901117
    0x151314030307091706040308011203021203180709090b06040e0118121818050c1303051c0f09142206030302010e0a1208070e10090e060d02181f0312 65
    0x950f900c0d02500e91740d2400c0c119400340c001607003100100001c05110320049006406881a00d071501c02101d40351156500544808019120465560a18120510100014103407810007071208081710b850307100c46010041d090602c1541d9036490b8080a0400f544203240c0d0503020046040b80c2078460074080b00ba22075140e26a00414210070240700b81000c040500e0b02560401d0048600031a00c807059000200001007100d200c0d964104100000900d5410401c001140b050700240382c1ca031030b080e101a21084880074500c041c02101ca84a0449540001300741d000d0301d640303c603902e1303180c82c10100082c0d095a030f41c4c0c04205a045a02000700c07003905990410005c0c0ea010360001c0c0f113004000c8040b10754a688600b0b0142400300744510030380c1428420100d01e03030420054900501015030920002e451154500380b49004148098000c004000314826201c0d84039404645554681815402040c0a000c0f2580d00408100c0340704005514507102168005182409031584042e0715241d140c81c101141d09414118 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 829903615 1250 829902365 829902389
    0x20306100e0121060c1b0803010503070f05030a2a090f110903120d06050604060c0c0609080d0827030414060a050d09030e1f09050315131403030709 65
    0x2044405040310f50140824070044807101c1c01c0340c107498a200400380c0c1d44258003005145044203101680d0702852030791490080400036582e524001c00c1500c4d04403d64072034104507405107020032440d5000724604142d19004010b81030408541820807840c00098106002504c0b001c200101c1c44000301e5105000306602c01c4c0082000c01100940b08001340540c89074154503a0100d00090215a40100a001c88412160b07010400350b07180c000180003600a600300c0000115424403076424811007112041c004c0040381040a58982841d01054031580340045907024071601c0c0021a400040304002200e800440811410b0092044c684482d140e5005209101045130815074801140c038003882103503c00074032500e80c80d10b00b1230200315900251030851001c1e024010040c034414480c0d05c60800866031583e810b41182e04036441c5070406401c0041580009019a1001940390340f4142401c07d0160030481c00000e5481d80c0d041440d205c254260302d6036003490240408014090b140d50456492030540d0512200c1c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 829904865 1250 829903615 829903619
    0x2030d0e06010302030c150702060f0c1501151d150910050a050702040c020312250801030c030314070c09051006051204060c120203010f1d0108030307120603020306100e01 75
    0x4141e4500e02800080c0d85500050b032081c072545020320151403030b024052502414011107800107642e64101040e0342c1030070140000d403408504401c3c0402074505803100d004440a5050089481c0ea016040d0104818810341d10004403035180c2d8480000c400a10041010060300000e030444c1a1136000403400c6170040c0e41114052018034054019203050703000d02d61702d45003020b005408001c080c00991a034402540803c20600707a890b651404001d00c031b9070000440d8140031854050714001c40d0320b030300f10703160400c90300c40b005200042800b1507040880c0d41602d840784094003109501449486444002002014902d00c00141505140c220318032843d81301d4890303440e45075608010359480c89001c20f03200080402c03500080c0040c4065008100c000340314030749103c01e40c4081c40758000300d92003038108010700311404404129101002c0d0345845200c25400d445091540b409051030360701e020141c8141c1c20702c00e200c03403907106141441d44624000e5400604407039286c204958a15514645400b0380c4103154160800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 829906115 1250 829904865 829904891
    0xc1507061806230604021c1d0c0406051305070306150201060608060a1214030412060b10020309090411010e0a03031e030b01020c2e050307030f091703190c02030d 71
    0x1200d1000b10300f4070340c8100740da500c10800000390710444400713086944406030007038030602030300c02da503440000c0c070700f100700030014480341e00740380040788042184154285407041c00280c03280d010f500071800f4243c00c0882c19499501c015005040b9582080903007242c00c0d6240e148055054001c40c084888586919030540c4443c0144447c0070034500400f50003e40310724a84c1e0008200b801040111420304080da410326440c0e44d030b01c250784080c140007600c0c801e4462120080c1d0303103880ca480c1000e5070241d00055180202c1e903004140007100040001c0e090039500e2050407101c0c0d000300c0b4854001c0c10020035202c0210307264540a0110000c002400001c054910200381d4454003034407903903440c02d1058004049d41d10740395040054690901042a00e444059941d14000c0c42d8803441001038022a07480d940e031645840c51008046030790032544403994a00702141007001c59070741c0036a0290301c072910b0301190362a0b0718241003880c2c010005003a034031844d1501101d5240705502001800c0c01900b007003801d101200c0d01c404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 829907365 1250 829906115 829906151
    0x1305010807090b07210e04050c0301050a050d05010603050102030a020d0513021e0f040e0105091204050901050f040212010e090d05030c03011203090b0c060f0112050c1507061806 78
    0x1441c4000c01c0e540041030160319810300240c00c2d25482040e8484901d070310007449920900d4040f102801040e0701c56040c2e6003d1506001e0300c1d60090b60342c20784c5411036140c0000102c0d100350603c1005d009a003585148014000203400050295070003000a40d41d03410040e06120095009000b0010918a0000481d46560215080e4250342e50014030314051074003c01100f00c048090b03010b80a610141500c0c00000d1511107018083d41c0c2600b0000014081c030340148000d0402011411004c980e01c002c0105000a40ea44550b060540e00c0580d804000e600300200490000e11807410110041609440002a0f043c1c06401151082201c40203440500390a403e05988a0205441d14000108113000600414955400b103031202c50091a080080f65580c0b690114035070b101451100003074001c10200301751341d10f0002c04c0d5801001d450120843d80c0b00701d603e80030744844000101714401d461112450406030300000550301842d402c0300c410049112072218007000c41c0401c0c00700303e0f081401c207103110358a00c290311 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 829908615 1250 829907365 829907371
    0x6040332090906041a12240103110303040303020a030503150d0b0103020f040c0804020f031606020114071b0b040305090a08010207051506210703080f03151e0f0d1713050108 76
    0x1d03007071708501814070400800500704000c1820134410342c00540c01d41445800c01503603d0103000c4818150794154205100c403148501c04107170181c0d00811040000036030015502c0341e220380500d404e580300d0b00d5408110549040b1700311180e502891400324007041c400030485d0141249d10072540600c111000206000a450000001c4000309003214000740140c2050542480c0107070f17008042d107100307100b41002c0f00b1910403141c106c9070060395991446804000d802e903505801004a042c40c1d00c1c80d09a600280309110f80c1440018035800c62500410b003014040c109032100f07400c006001d00001da4903550054001e411680c0140c0703d9100d103402c07412403201034046c0903014140242c041c20700145201c0d41c110307600518421140480c42209800400b04c0d4007040a0203422880703070482641c034140500420b810391540e0046520980c0081c103080400084105030110704a800d0320b00e6000d044100001134031125215001500d12a43c0007042598282d0980081024940454854880c00d81310801101c201c2022 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 829909865 1250 829908615 829908641
    0xc17070507211d10230702030a080a170f0420030d020f0c0603130201080711030a080105011206080631051608010203060a0b0d1d0705040606110604033209090604 71
    0x50b1000005048441c01e10111194003040850300c6c014482c0e011900e000740b541c800340e032648400304142201075032055103030702404410004104ca40c2400b060b1a0a0580054402403401c0f407054021f891401c203e602803c50903c000301a40c0155440c0710010352107030100015000349000b08030701d2440318644441545d008614100b40c03a00d40310020f40c010340788000c001c0e108005010400300c080da032175102040101001070442c0e41d079100c2c65160400140c0581140203025000500340a001d00004100164466010030720050b844100c021410054100905071034029141800c0380c2401410b000000032481440ca070700704541e5100355a100c0d640c070f00700c1c0401c0d40d103035030b003c10144c1c410170481e680c0c04c2c040d1400b24814900041ea5010b960705818000b1256131000c40780340c12508040050703250510442c1c0c001d0000e0701b401a800c5180203001c80d1280e400800c001c1c14425644a150b07107040c42d030000c81c0d100204601e604440303aa000e01c4070900c03503040000d40078072490404001441d641001c0c05080010144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 829911115 1250 829909865 829909877
    0x30f02120408120918010311010905030d020a0b060112110408120c0706030b0103060b0307030c1b020102062d0702031e04030206030a0b041514040c17070507211d10 72
    0x619020440d41d601c0011001c5d405041c11442000b207401d041075290007107210301e0040c00240d90001c0090a800400d62120744a9040300741c002401580200e007071510b0f1607204074240c1407681d030280160f0b60750a210409440380d40c600b8044124210f4114010020360303802400300c0c1d1144030706c021806014803c0d1041541c25070810302c1c04100240c004c2d040004645414140400e0700b585075000303461180c04c201c0b040c10005e501d40b14001134048c1c020030407030311041403940c0300042c2002e1030700045e54812000d0154502d80000c0b00304858078008100d0301c0300303600802c8540c90a19040a8000a64982200c0340340c0d03001c049030004c14010300c3c0e00278044800310381d805802d480c00c555411441c500204002c45490303030016102c40c03010340480da90346071040180c105047c0509198045809000807110341011410034424650780d41d01c3c40f5003260400b982e002440d840c1c0603603552aa46844803c0c03c040418030f01070300c5d81100540c514640c2001100485440291154803a1140c0300c00300001002110340d80c0000c521 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 829912365 1250 829911115 829911133
    0x606120a0803060105210601120b180414030304140609060103110d050f100218101b0507051903060507090e06040b01170f0618010b1c18030f02120408 66
    0x4605800382d80e000005040440c2080b01c101208020711031020080c15104489500304505136802c46010303a1040d4656400704078000c0c1c103201050710030300d040c00d03010f50358600740000500b00400444020003000d2031005903901c1e0304107440e1070021101541d40c1d00240e401080f0009000c1000003420a0480343c2204800b140b02601c50103208200464480503100c2d40100c0028000d018010064181c204107100001a07480b00c0100d07070402680d20740a419449600020318900003c0e50101c0004001e032030407013000c608440b46142907850011507030302c455000303008201e014210200d0310075200100c0b80039103001d10031680c41d0501124160210f008101144203001c1c04a0240e060a074000b582c401018140f0107480700c090000704841d013204448100a00010604000c5141066511446030304181001c9d01300d25410a07000c46224000e22004e03c400c803079110421648100650031654a002200d170400341e111065040090913507040b80c0e0504050701c0341048662641000d04222001c80c0d810744080c01d1039207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 829913615 1250 829912365 829912373
    0x90b1017060604051320100509371202010e090f071101060e0f090f151902190e0907090810020d060e130516061d0411070b01080606120a 60
    0x42409400c0074017007a260310b200740008100300e26105410055150400b070485624003000802c40c9603001003070030030200b0700021000e500c42580718158050080113856010350740d9030174003164230301040324000242c03800440099810040041207070a68001ea9409a489000606000c10136005443e90480d0700800400603207568800c0740d07540c104070641d00000c0f0309242d0340c29503142c0c240c40648040c10341c00c0503442800f4034208200131078603942125201406954003c00c07420042c0000c01405045802040407080040c86810382c115070010400e450b40c4004001e000310012f2407100c1c00450a40a5480c04003c0380076107000f5409417041300c2c1300c640204622690386141601070f401c080d990f07400080c3c5902000c01c0c401e5102d9401403007000846440d81c12601c5604000d490040400a0030390b03039404824040c44502d82c020300740031031100c0071050030a80031801004240146009180741c0c6d1b00c0d000109420701003182c7c40500d54100c0d1200400c45032103848640810a40c40c0101020116907880654070340006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 829914865 1250 829913615 829913621
    0xb010305091b19140906040c0206011701060b040801051005040506062209110c0607050f040308090a09020d0e1c0509011107031205071209030c05040902060706090b1017060604 77
    0x30b03003000d0240188141c1c02c1d1045054100300b500001090800100012040c1c2420300b0341d260b02000c01c48003440f405005031006510b400c810301a007a00c0c840c00200614204500350441030041201d8a6501e58907039641844500901d004c1da0680028110a81c001801d85440e0084901520b00208100d24007869030b8212600035140c412100ca0031030000e4000640008107204001480c00040d48a56a0f00400104113040500040144040c48000e11600c01c01c4c00c01132040d10190b03548890626540d0b040800000c843c48410f900564109000050380c2e198000c032500102501c160580c1291244200300c090b441d0450726220030032000803418020f6002c1c5600c143c008a02482ea80420303140368640707030b40b161900c503035201d088400400c0001030100c0030042a00c0d2104404034070f51900d60300581c19a41c4015036404940b00b024030598030313461090190340c1d54500b26250140d1000040054200030319140c04010000c403842418801c450100040d20441400c1400000800002510495490000700401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 829916115 1250 829914865 829914913
    0xc030606060f210c17090a030212030907120311011104081b030c06072405150111060f090f031c0e030a05190504030609050606090601050403050604080f1c0f0b01030509 74
    0x3088052030405d81d03100ca051181c20f002c0c0740a0809400b10043c20b00300030f0714050340740780004141c100400800416440c08034088003a209110b10440361800c240c1803c6507040c1d041003000f8001c1d40f0703114081052001c0380004000f00c0c0c2e102e0080d540480341e00c0808582050306440c050f501504900c15100321072801500411500c2d100f034009041d00100d00c0c0084c4204140074034203030540d40e940d405010030707100030304d690400c00b07071091070104007a030102c0260a44420b40030700561340b0400000d010501c40f0070f003408242800600f110403680c81d0040c544a000718200342d10a941240740c90805003e4245101001312510b1103030750703101d481c41c1200000d0780c85180d20705071000c1c804022b014000400000c080d400703490740c05800349004195a061840400060800181210341400001c1008000082c0089202a401501318501c2c6448528800e01740c003c9110b0451320f00701558080400558401071603001d049900036130341c1d081004104c000015000c880040d5462403455019000803500c0010300800004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 829917365 1250 829916115 829916117
    0x40f152c07030e0a0303020a0e0904230f0f03120108060105030615180c2107021e0c06040b04031502040b04140102120f0c0f1204061103070c030606060f210c 69
    0x90702c00001d030443d03007001d101d11000c4000a400088058245030b00251401491604440c42c180504013aa511748282040180700084c60901d0700c8140140c00081c0000b10351425941c041e691903070064001d4035100c2c1c0c029030181284884000c000f149444000551905132900a0000c2c4025114401070300038142c42c031440c80b0f1744000c134240b4140c0b4615956840a01035264004020f4032500052400d020074040720184121120714001002030240d03000511074244060f0030340d027642e40708841306070700e09259413100801d07007101c00020b0015401840c1c030000e004884c090181800e1342030418140300140d21540c4605021141d0500c02071180d40c0306580003541d82034050040b5100100d40e031800318010307004040300c58031924000c41e201100000900c510f0f02e00489a80c0a410441081d00031280e07140214002c460070004e0004482c2c011100410440b1109600042d210300076642c2d91070040b01428603406080e00140e81c00e00078826441c0a401d5042101d02d07803a2894400200c0040c0020050840744c038407030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 829918615 1250 829917365 829917371
    0x190c12050411033426031c02041403010b220204030803130b070306050d06050a0f06030507060905012c010507201005070b0c0a090b0d02040e0c0c03040e15040f152c0703 74
    0x1855840161f007000c504900104000da00c03a45004d81075107a00c080210014000d9042c20a54406c0e50b84001c010a0462070300c050240c1501c2c1040c0d02da000030700031500000c2000d9000010300185241500c4550484c500c038601c1c1e9003040d9a8840105d00351000c520a00b6040a85d02d480074000039520f8020a078402e286100002d030f00b0032080c1602c41956a154819200307500003c109005007030f800000b92018200c00e0170a1601c08d420322500002e10702c1c0140002001d6202454400000d030701c204111a400f0b904161304242c2044143c014030307151840140c2591140c0c60314200409205e015201355482d1a4202c4e48070380d4103036a40e5840e04a44c0c0d2142501004002d044500401c5640044020348580072640b0001a2a5400c200701c1d0b020246010f00401008003080c03180300510341001049400b03544000044914588030000340d4244610a5440a0b030b0044c180042c2130410701640e8000c125070355040c240701340b0055440001d0500d40c0a048101200c0c03400350300300c42c2d01a030f150200f880d8008140d85400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 829919865 1250 829918615 829918627
    0x150e2a12101805060f041d010f0e0703110a05100806100f080a09060e0312160810172b020601050603070c03110a020a030803190c1205041103342603 65
    0x40441d454010104110240c04040c015900000d21271020203a24220080140711600b040d40b80c0d540186100003482002c000d800144280c0700e545940008040103012102c00c14070103080a40304410413143d25000d610f44010400311076107c1c030114980b6044584410400d0317115492910007620703d4003400d5500c1c58403010201d21071001040108583c0c040810b40c50740700d013006100c5c2c546803400084450104101072003400190456070110800b00d0b41002502e015840c0c0ca401071b98106010a14070602046200c0100c0c00c7e254840c03c83d0f0303145000703d642510100c3e03032039100f04019400300350742540000e218a014000020b000798000c50b8039480e80340c100c9144803000c0d4001a419445a0821584d0b881c021051060619044513500c07000c614601040c803200003889001000241d01e0480d0140c1c0b5a15100440c0c00d216441e8030302d030015100030741910607000c07175280d0642d0308095a1640b206d4030002404c2e40b65210180075101c0054540105403804141da002c002020300e540500c200780d00302d01080040c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 829921115 1250 829919865 829919869
    0xc03021e0c01090c09020d05010905150618060d0f0b01020a030818010605040e0f06010e01030b07050a1b200a030f060c050f0a0804110301150e2a12101805060f 70
    0x1140024041200c006d69102c5500101100740c48040e8450384e801d504101c20b001442180003c0c15120fa00706484250319800b13070841d084601103000c0380290f0003481c009881001d030300254210038010380c4441e009010350f0140500482c0d481865071000390020b1484004689503079400f1507210741d252040000840d409481d00d000070100c07040010034035416070000f0001d404501d001d0010900504803010382c200558556181c070784001070700400c800100440002c0283c02c09000c0c0d05c4040c0b01482c814100619141036241002c00c1a0b09200c01d0983e81d5030380c1c11407407500d01c4c0c50806107003a0b9510610081c5c10581c180d0b0f8507030185c170b400e81c2900c00707006040c8100100d00ca101c1002e0912161560340d14186400d260400c80c11142600203414041d904120104070001d020f16015001c80303c2c0c01c1320301c044aa40700b2607451003c44501c580210b102c59101405e10760002c540c0064034113001d110500c15003d4903000d41c801c105079254440e141541c2e14184511031100141d0340115800700028043c1044400300c030b80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 829922365 1250 829921115 829921133
    0xf010303181d01030b01080703080901050322140c0301060b040902090f0d1104050a020f190516030e0f01030606022104322d270a0c03021e0c0109 64
    0x7900b81e005142000100240b14442d20810300400306076000e0810320703095840c0c1c1d85c5035118000380641880300000102d0076808075094075200340d04500088200f401224500110034054681e2040924403420007000c82d540303810303c2100304a0700308503105071800f4a44140b25010307405c06144a40d200c644104840e2044d19603000d01c403003140c490409104641e841c030b0100411950b000e00288542c03403043c0040b0458000c4103085800c0b6000c14141200c03203102480c2d04441c3c0b84141d46007111001d00110031a070425030040c03048100b031032080713030805007400c540700c0110215100340c0301c0c140043c2c1c001d2401740405e14042c12500c40d200d0789180307800d14044d2500304500403c1901240591350105104038001320702d910107082c0450010440380100910000b0f103011200d004140c0070260207101c3d484107094a83d643c4840c43c00109510760b01d0050480c2041240c000c410380450f145002a82000038440303031a403082c401c07514424486088140884c80c215101c40c111341201c10401095036031881c450001c40c02c081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 829923615 1250 829922365 829922399
    0xa0605030a12020114010302090411030a050d09091a030703120c02190819021e0f040501091e1b05070311070902031e0f0601032f0405040608060f01030318 68
    0xd40a00540b8107803040282110b100380310000030761030340034010300c011394510781c503980c2103500038000b00101700e18100000d00348600c24030014400c0c400c1c80701c06005560882640405c490001c0b038204101c10b005012103107028019802d680d45908017100a0001980d00207142590003a41e1a19010091171540401d580c03c0d1211824015821038000401c203940d820004100c4084114427404540003440d03012a001400010142140c8000c940e0020781c81e40311076031945101500104180442e50b50713402441c2c01001540e0303042c040405170f4a00d42c0710307882c55406110401282d003078035550340121408003181d2507080144c0880410040640303d20385075008014600113003000c098016540c2c01c10600a00d12141038031200038451440704100203110035800e034460390002003820081000b01c0500200210f03c10900c3daa83c1c40548011070a8070308400e014007030400d0b2542038030b00300a940d880b540c142d039696608661010204400300018030000340703d1891001d8a400d407999001d0016125070b59030a0140c004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 829924865 1250 829923615 829923623
    0x408071406010e0f070c0317070e04020301030602130602030f03012304020c1c0f050f03070c05150f0a0207110f15042408010e070c050a0215030415051e0a0605030a 72
    0x40c024005045400d444e4103420440a04004035941e242e5540035045480c10700c10b11070b82240080000702440e0154a600d40f000b44001e01c11960b941c0c41e482d01e01c000f90032803800612f0003001c0c1180410346034000021900b00910140090b42160b00c3e05401c23149121111000303006000b016041c2c180b00362030700d00103400e09140240117003a144020030074811000c0e40d1114100200041031810000050b04441181e00c5262065110303983c0361742c0c0507401e88181c0707007a00000f84248203d840780038030b4008481c1103900420700248082e9140e1100080d01069004074500908a00860f08030170b4100d00d09000712504001c0040c010000039140054040c80a8000d5031080e4056910a0a1803002e10079072051415544030904242c03810b541003a0300040c0010008040b0014002055244800d00a007006001d90040d401400c0a8500d10b1104604c400b0707030820b0303070101d440101450601d0b842c95140e0103094402c02d501c1c3c9624450380008102c0038a6088050504a0b499580da0700104103611300b840307428241da0207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 829926115 1250 829924865 829924889
    0xa0306180f0f17210907030c0e10061805060703020c030f0106050f06030c030106120908072d0803220c0807170606030304030609241a09040b040807140601 68
    0x26090440d8078210301d40243e20402410491948031220030001e8102a1144c40340e100744503130319202c11381d04c1c000e5641c1000e4036200c03202000207030000408509510820314044050140c5581c0c00082d01c10b40d529040102e0390040001003882030f41407180140110034042d02c1200e480400040202e42414040c4009800ca6511003405104500f850b08010740c80c003c00707881c400c1c69450251202070742d900060040b46c007000342d07000320420300e0700b0b01d5006003000319001a41203517a18114a041c070344010900e0340b81895a00710300002d190461540c1100d60440d50401c0c121841c1d0783d114402e404541c0c54904e0407002d101c80c41100b8002180300e241240000d0141c01c802002c1250401b9400840c1c02920003031401e440d40010200701440c0c4022003a0303411a80c0c89080400c8230850340c03906140200e030311380c03c2c4648040d24408401250069411134080c901041010300540e031000001e20100d40000c480140103c03c112000c140011b034003400038141103020b003509140b8045103c0905007085001e901014011035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 829927365 1250 829926115 829926143
    0x40302011b0c08100b0102190f150f0507030b03031801030b0d0510090203120a1b0c1d070e0411160218010e0610030c0e0d060f020d15060206060a0306180f 68
    0x4c03180c8240400039100340010840b0145043d000100210003080040000d1000369030391040003c11071880303c00500c5032409010000400030405d0040c202103501d03800290500b0702c080f100342000310450780503001c3c81a03220348804864006401800000c04442d03003201da24004000030400c140002c0600c40b40c400004198842036004241c034108541c4420390a0b030004000e40300321a80c0050a030204e805e140c550002e0140c9041c1000030040303801d544904000310041161840d104e1407428402d10550b01500c2c1e040c4610903a03020f2000701d8149048010b0400d10401020450701c0d0050b190340011031008094044044100b1140c83c11450280c1c0455100040103040c041719181081f003040d01010540b5080146c0380844038018443c0ca070124100c0c0c042c075203010302601400540d4000000d0600c0c0c1102c10b5540b1646240d02800400d0710f0803030785400020185000c9880c80c0b0215100e401550020698840e181c190303100c10009041e80e004510701d1f000d0940d0f42c0800075030080b0b03403079002b0b41c0901d0090f12588 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 829928615 1250 829927365 829927393
    0x6190603022101120b130b04060b0901171f0b0418060b0409030c060f0f051f0f0f051e03010c080405150f0c091206161b0503040302011b0c08 62
    0xd01481d07007403845501c001408204d8000c203d0134141a080048951180c65044400c41010714801001d4102c5000c0010881880b209400917203131080107513010417241c3c4c0e881404c44890a13401150803010782104426941c07000055001032320604641400040429030751000a089642c03c00342e50040581034400d05060206900c901c0c0070302c00050710148102540c6541c001d100d158084801400c1c1c554888c208441540756502c43c0469030340890007005035040c0303003002c0c68075445254109009070b03512020101d0345d044511088401c0f10340d1404450319050603e170801001407510800652008201400704041e940d090103008512107186e2a450340d281810b08006041200000c20150000e40c2001804801e0040d60310b0301ea4048084c0380629145c01440700016880f0808000341c114a100c0c070350070700220401d148011400002642c031040d040268074151444561307030007a0094403d4100740700420140d40070b0b4000b480d01002c1e004112103280d0321651484406103054001c0011a407000b0178402c048 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 829929865 1250 829928615 829928647
    0xf010309020316300b0a0507050d150515040f05010e060d0c051b0a0309210213051501110606060f041203030f0c021902061e0f130e19050619060302 65
    0x203071902c601000c61346407030780f83c0b070300c0b000f0014118000003555480001c1c80e49110380103880010b00b14100074418451064a021000409801090303c90450080c41d810031045840480381214404212006a02d24107001074a80000e810a80d581020081220b04080312003417080c220b82a41c0d50712044e403030360344441c40300800141d16420021a43e000340d0018000c6a00034005204030b9420710b1a04456400480c4203540384142201c000b13400403e41808841a090f4507000f030383c4560009030180f003c04940c54011160080601c4443c030164000b24082045428540c0040c90200c1e050550280341503901c1040d84d031100d103800ca0130760000e0b554000900303010842e405001c6d2001d010388014100312881e4030f42c0005002801800034869480003400500d54015042c501030b500044a808980303c0301c40c50028281a07104100d071943c1703030154030310101740f1226460303407076000c2c003406d090f05069861030240800082c240035007000d91140c4c203c562400e41d8411214414064403240d0303009a11818000310914403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 829931115 1250 829929865 829929929
    0x12010e010506071509170f030109050a050103020105161a180601090626010f02031e0105062701030912030c08180a03081306090803090d0e0f010309020316 68
    0x4502e07820852580851345000f04040c0d85040f0f818000358141261403e030300b04030301000e007450060502141032082c2c061440081c5040300c0d090f0750103001c6039a900541d80f003102e00900009000c140d0600000940020009048810700d100d501c42c0c22841c1d240715a40c1c0c3e107202003140c1c02c800c0c985126000e0a4040d0082c01000d0040905c1d400070301c20581898440c041c02201c0d1b201e0344410342c071141605240907400350070034064440c0c4804115901e00b001541c042c00e8054080c41e8155048440c07000103084c0c05d0640444030058281c00e185894000da0f920000c0d40e010f842c0740441d0400d61141880c1c004248810f40c5007140080d185c500040071900350a019218a40041c0703641d00c4004414004601c1d4a0041020340c076250340342c6000880c59548000802107c8c440c1307100603098900d072015003000c21148100860040e400c0c00c0890780d1056400f0000c65000c030508528540101120300f14008650003031700154441c900c01400d4a4040b0602c80352100d81d40402e07481044580344249d401c801280c22010340c0c40c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 829932365 1250 829931115 829931119
    0x21090801052511071404090c06030b031504030906031d0d02010219140a18080d02030d111303061802030a0807020406050603040302071505040b0a090609060e09160e030312010e0105 79
    0x80f004951101507840b00c1403071040c040b04098030080890180e072240d001d0060aa80039102001d616200c1350300070010320103180310a0080c440d000808050301c4030110050710456056540d44c90040c2468021030281030521000d0320842000d030826a81810107001e0000c03070060365070005807a00002e40d21101d400c40e08080c0d0000340043e2441d0125607864200440340e4040990400900082c0e40b4a0400c40d1072100c0e034054443c0380540c940c02420994080b00410309081c2c00c020a0002c00721600c00b4000070b10070348104000c180d0201904000045241d0089424090b000c013184180703200da90042424000e0221084400d43c40c00a0300c8421031815120301806480c081c1c41040c21071405a074042c3d664559030042d409401ca500b940d0041c2d907131003402114054000314a45a44421b0040c402507c0440c03140500710101d003103000003183e041e11a0600301d000c1702c00200900401c0e142c0485400d0307106140d4950004105001d010f5800c2500e0420042c0310220490020400940c502a40c480601d10181c200034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 829933615 1250 829932365 829932377
    0xf0f110604030816020a17071a1204030309111e0405091522150906050a1a04020705150c0d0506011403070e0a15030609060b0403210908010525 63
    0x8000b043e210026140c4014004840040b001d010740002541041c60307510102d9914600310081071500d80126441d8210b96006031040c80401d44100709507118017441e6403100c5c1c1c10a00c50000340100e446500b050302c4850080030210704500410000c242e44081c1c00c590390070300c00d000225030700b5241030074481d5a030709c0040c0001900c491014006080c0d203001015103882c050001e440e09586007440301c403a8050702190300c032400c0c00000c003100c44101c0c0a40400340c03054480702e14000001d6000e07001c2e80501000d5a01d840c03129860610072404110003904104420b45407407081d9816091900c074140002402001e4602e0700d652103480000102044e6100280741604029403049541018880b103400c1e0380d00b0860b5800c00e030449107440b0002c2400801142e1002c44006a004005c142d40d9826500c1101502c41030340043c4082525018800c0c42031046110042c10b0030203003010480ca0700020516961020341510301180307625a222640c40c03d554080d00d65a29603141910404440034007082d180e903806216080070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 829934865 1250 829933615 829933619
    0x1a031009050c04080c040b2d130b1201090305040909050c03120c060a1109090c1608030a060b04080607050c0f0106080c101e030b0301180f1e0b1308070f0f110604 71
    0x1040d000d5490042981c0700303044200c441c1230300d10232641001c04080030103891650b00208440040000c4c090805610740241840c45c10303a5164030044c020801080c1d010f449141c9070525041d0350000a10b00c202040e501ca00605030070803401e41d424040d400c6420350b805c1055448030f9080448a00b007a10207000c00d00039034540041c41c110302c8000810703210302d0041160740001d5956242c8840000d40706034160210001e03c103440030002c1085480c040c42c000ca0086c80100495500c0780b0000030f07644a2402040d0709640322100040b015446000209a80050102501c1450380303c60541801d42e152604500e655820000d0b202009043c034607c0903030551000d19050b11100c041810740c116600d44c17080070200b01074031a060035080d40c80940002082d143d845c14940013414290420400583c15031808441d00142c00340500b88803003003045421542c1e608018190180c0d2921070500c00ca0a4090104031030180e0103111840100c0c598004054a4034050110075500301018070780810034043c01410b580c4284814481 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 829936115 1250 829934865 829934869
    0xf24091202012303040c080f07030503070b071812060c030501050112051b0c0309040f02131229060109080f0703081c0e030c0d03061a031009050c04080c040b 69
    0x21100000340c0a00700044100c000345061400000c020070744243c90400002070104001c44809210101c6200c0c5003600c1d40e80f0038000001d5200d085501c40a02107a03c240300c2000400d00c801607203070b00030010b07080c01c204003041e58588002820b40361f803144590003003035125102807000a00401904180390f1038100318640c100000178000094985005040b03a90340c0b4006014102111406802a18400ca01d83d4540c1d00f50365282d5070340d40c054104107000d6804d001c0c8c800c0c030740055402070310301c002940d4010f03100b0282088200140340a80c15800c0d9602601c0200b4020030300c52540040c4000400f401542d42c851809100251424500354406071007030380480002600c008002c590042543c1d4008030840c0c1d41e241509940c2a0284031a00e0200420304d0003030f400c13009250020061043c0c00e21202565084103c0c0381054003204c4040c814a41050715160001841045c00030040d0303401156098030a0940d92240d1703050080b00c00031100c03450302142c00582031001910811400c61414400c49007884141c54143c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 829937365 1250 829936115 829936139
    0x50c042d05030607050a11160b0a0e0306060a0b03070201140726061e120f0f071415030a15030605060a0506180910090c0507021503070221040f2409 65
    0x42c0540c1045454080c0287c0400d0030700201c5c8058040c8442856040d8035242000e0940d40150203200c04504820825941420007061880c49400c0041021102c14941644240703141d100802580455607144010001b00400c1c040060203905540c0d20107040c4824021207010785030328560035404a03025a410001d03542d55a050181c0c034010003050303558071205d494012840d032299903804107491b4021740209003031800307000982d200f840f01148100c3e06401d030f6030214a800081020007581d04414070400b000700982c4000002c541016008400048061403521f00340c0040120b600101c402c65151400c0c8102443c14000c10300c007400c011200d5528040c0d2380e043c010070f042160800d1a010f416040300003503058107030302e6018005081c20311091020160740c42d4000c0496200c003104078419022000300ca5590130840d015030f881194290014074401c4032211210045101c0561041090310040201091142d01e011158005094201c02c00007110340003101e854202106003513080400441d00c3d401c000c2448008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 829938615 1250 829937365 829937377
    0x6040e06061f14041d0708090a0204051506070c0608070201150302120c0303040b030115030902030c0409020a1a0702090a090c120203011d031801021c03050c042d0503060705 76
    0x440b65141258552040c0e03103001e6105180c85500502060006501c0c42c8800c4030741d1500c41c4820464400c1d0b88061050750700035000c0e5042c605035840303004000012b08044d0321040d00f000045042143c40400d0500140441e80207290032100708140c59000c00c002e68200da103954010b401400240700c0301c00014010405075540d40710180c480d160002e0001403800d0305100c070340d90102e005820b40f907441d500c600406005600c203200f0100802007c009602c1e08078420301c10355034403942c01005010140520010040a004200e5080c1c1c0d01802c06400040d548402044aa04050a8890032515202a80100110300500805480d42c590604007010001184200b114083d907485000c5000c5003c0c680c0080390040101e2a4085510a02c0034a02040b00000002a007102a4841001149070480c803004a031100109900c401441030304c0c50900341c0c050b010390410bd038401e0607001c1a40c20295515400c0b46020101403280c0c0c02a84c5e00d001003543e03600c0d4888000081c00090380100381a081c40d05009100303216103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 829939865 1250 829938615 829938649
    0x1205040f201c02040f0228260a1d01090c09050112030f02010f060e060f010f1e120c08060a09060602120307170106120e071206092906040e0606 63
    0x902800045544030781c0304001e8001d072a03030119200d480c0d10900f1600400c00100e4900190305100c00f481f6441c1c81040248400b0381c50b4142c0ba41c8200201030718061501c000f80080150075282d0800c6011076081e44520000111075100108030745c2400e080030b42182400340c00101e140c609010050108041501c4601d82d174650602d007242000d41045000c900401e01c50400103091070400c00001072a0202001284c040e04003201c0c410003001c8080c0054030701d415070200e81d6010a00f441c0d402108444181c20042010400e41072880c26800410808022114461100030100301503409103c403900381400003901408680000304007017805e00c10040c6d9290030300c56449030100d40010000760403e110315150070544080c00900c00c130035612150080c02e528000454500c0ca0b51401e0350b900301940c0c0020300b2000301c3d000c511002100e08825101c92018042107801a1044079140c0864000111000c021285c0000c2d11622030b041d90409404102c00e658441c2c42c450724683c070080c140104c0d540c54100c02c21104640c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 829941115 1250 829939865 829939909
    0xb0906250f1b081c182705010b030910050c0705031c0c092103030f0c0206040b0c070308130807150204050406090504121809090b060301050a0c0503040b071205040f20 73
    0x920b0300d4258031780d00f061464200303020341d8140800307030620307155a109000b00040c085680c8400301c034499400300316408841d66101382d0002d441c22440350b0155030071107a410f19461078111240c0383c0c14516403040a0149200c82082c0e1501241d40b03c0d031080108200c024508240054542122218014002c0c05031844c00c400f274030b080008150080e406881a02c009070300c28040410035a0b80a515940225000e4800c11441c070300040480005404480c0c810381d142e2551003c41d142d028070601501c1114204482c10002000a0350109900000d1421a8041c0c8000542e9882c200800d010a8443d10ba01c5628528207090a020000e04043d4000c0714044207031404040034210080c40c0c111100030765011407100d600e4941c2c171b401840f80c07152035984142000c0e402441151600c10032882200d52201041300091014008a8005043d007505580c1040007890002c00c2c1031040c2d58035508455068400b00c410441c6003240c2d108101c019081003140354074124208d458041703100d000c6035440200803030030030340380c08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 829942365 1250 829941115 829941137
    0x210020a080301180f06030305031f18050c070206030103050d12110901030b030c041118030705152817150a05040e01060812090306010b0906250f1b081c 67
    0x4c0c1c19806082e644101907000d0105690380c0c10041c22552041d0f48050604c00d40078403d215084940c0f5181c0100e80407840003045441110580e41e005001c042d100380c264000030441200075a403100c000e0750186004d400645110a80301e00e001c0d00b000750380c0142810150404506103d505203d00c15681140703020308006c41c0c1903840c100007a0500104404080d40b0500e0020f00122025850340500002c1e900084580c0001d8001c000701070352072840384201da0303100e00a04034035424031240c0c030047c2c41000b81002d46d4080c0346030729942c412060318034200c80000081c000400c8403091501d582c0c00301d40248080d0200d047c1401c40300c0c0070a10300c08040c0a0a80156140c48480e080071400354400340c02005010181c030820501d2802000b40d503072103503000e00c0c482d10800c00045070032400c1c18201c803404032005140c81d21f0200300900306401280d22100c0e0f1802509034000c1000030800d105040d662a510428503e4080d0308144a8294000c0081e0000c000503803102d107046025440c0152627000c207102034104448000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 829943615 1250 829942365 829942409
    0x60909051e07020c03010507032910030b0a0306090b0601030b0d03080621031818070215280e010c09030f080f04080d02010c081b180f030d05070210020a080301 70
    0x2072441041315010f42c605010030030019030581c01515042c804c40c88100e16080c2c2040d41c084241101541d45510074049220f004485000ea40540190040502100d0520759240c1ba00400c56006000c00c1c1da4032403040082102c15a894458941c0c400b0b0704603202054610305880082034840d00070921400351031b40841d070703181c01c84110074080c46c0103c05208407680d91580c440b410300303411a04a001401286604600d0340b064142c03800d09441107480e54002c000c80b004080c250381d1202009081d0418201400340111425080260402203070900964081001140750b018982140c42e81e0f0958002c11203608401d10005aa400c85100c40d9600246c83c56200c200c5118920078038072a1340d21020f036030b108159011702c1068040d00308041035a601e840c2c5401c00e5440c2d62407054600c80c0700c00c60f03444001d420030a2074000403051400c04503490f0090180b5440d040603102107454000f400c81a2408250302040301402c51610f07034880c6070350340020f1000d84901c81c50780d0b803551041c2c04107000b22050800031000046c3d00e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 829944865 1250 829943615 829943623
    0x30c0a080604110619030608071502030f0d020714060f010504051501082203170a1b050d061809050f0a0f1203200304142a0301111201060909051e0702 66
    0x6045a04969191070741750b54003e00248014403c02520b40155000020407204104004005501540140d480d103481c031170040e207040e4003e10940180540c00d118500100e219141c44080d810a111300030034840c10f01102c02480040141e001700d20940c01c1c03004003c07403c045a15503d0300034001b07080044090715040c900c4465050080000c04984480c08039034400d242d408002c0c094030300b489084000c540d40b075031380380320781030754515034030009403c0076841c40030700301c0d4400d4008200345c8030728000024016440304444019200204120302010703407203440c9801031000500030b5062001d4510014100c42d0010f5450b402c0200c121107025099070640d10303910041d0350081d0001609081d01d8504403140301d0380480d000b03500390005d80d801c0d180100040070820010600040841c2040515a1804100348200601c000c62403030740302030301d500f40d520390035144168500c2c800030342a601801d030092480b5605042c00280044061360001184c0c0f0308100601412441e0a1001e200e059202004410207545400c4140e06d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 829946115 1250 829944865 829944877
    0x50319050c100306050909030306120106051e180702100608160b0c0307060c0c0b0a140f1e090a03030b0a0f050409240c030513020109170c030f030405030c0a0806041106 74
    0x42644c6c0100324608502000031031180300e044400d502031240709860f860882d00350f4014075401c000050b4015103151141210075103404002494403658455040b0408052902030b00c1c136a0169001141c1e0f08001d950501405014012140c0102060428005c0e2014a0444d42c81401842000050240c0610170b042c42100d0f071054004006100c0c0483c028002450950286e0781a80c1d00540712011403070303000c400d0064040c403a0001c02c43c0035540e00c4645442c03400a00c0508411450b03030803070140c0d8804107000d5401d6403140380300310301038030540b078441c00c1c01380a560241550ba413064200740010b0002c5c8814090f1001075400c150307400154020315140080c1c0340c00310480c0714000074910070010f011006060b0000c2c44040d4596909210726141e01002c84088103032180020b0100304030040c03d00ca40848098520704400c09641107c00718640e0101090410390341c065003510540001230180100d082c108018080719806071081d0405525001c00135450b0f0101510003081803026400d0361515030b861030b00380d0f10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 829947365 1250 829946115 829946119
    0x1c05030a02130b120a0b040e03031f1a09041a091513060b1801051903151716050307140415090e0f010f11070f0c0b070804050319050c10030605 63
    0x6035407041206150842e4a0440e07405c0714442c1010030301e0005080a0194410614102000b14150740710000040356800b4400034403005d10f444081c00103088035111404007500083d000d10a50f031800c040060109454a08940913180200c1e071a2841c0c454131490819039015860030030302244041008005071501c0c0c29803541d0781d00d07582402c801007147c0e03a0600007408140d0030742419022440410005440c01e004080000703038808030320300c150304a941c080e8020000c80001840302d0035205480701c10060045143c0c0003e4413040e8880c1c500010040c2c600001d03035010301011401880403d18240c0e101c00740801a1018900403601c51180b01501c0d00c44403a218041e10210350103003c1e0314490081140d40d8554503c440256608080e490b81900806120303d078400004001c40511f0014291102c031004c0315034403c00c071004030f801e2500040d00d4901e02e0117400c03041c2c8505881342da50380c686001c06240c50f0484e21094618002800203000190300050008210101542c5841c00d585c0120000d40082a4543c007241e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 829948615 1250 829947365 829947367
    0x3020f0d0b030c0411090f0303040f0b070b01080712061a0d050c03150c0d150b0a051206030606010c0312020405060c0604020a0b0c070605091309050f1c05030a02130b 73
    0x4011800c0d01e40003403000d020300380d00300e8840140010800c003d0313031104c07002e03225038160801c00b501d0300741040c0c140368580071000307021a8038281c1d0b41c1ca2065659611a805240d0104000c990001084400f0820f6030041101400400e15982009505102951144030052401d592001208511410142000c3c2820b000420604110400e400d1546c3c80e60004646980f1034007640362420110f02a070031000d8099000103000604001800103201d0050503ca41c02000010850200040c1d07100440c000781707543d98483d40c40301d40b6034182e070500494111025201c14481d8009500300107590360b1082503813032600d4151800040c4881b00901d0302c0024850790700250b41012000800d80003070b210000d4040d01492003075503042c0d0203540d40c004011a80c0181540101d030390f041290b00f003226601c960050604562f00401c80342c0310032010038401044a03000d01003140d01c1e0b003014180c0c100514042c05015040c0f01c10780031010481c166210014001d10000b44a607140c56400b0a004001d41e02d8804081d000e040d02140ca5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 829949865 1250 829948615 829948627
    0x11040c020f060702010c0819090b010b1e0c0606040914030a050c0c01091512141f30290a0b0307050607020609040b0301110a0e09040b0708040303020f 66
    0x751101d0340029400d0307003881a0307000b048280303205101e103a000f224569100c00050301c4011003410f20703154050100410a441d54045004210720b00003207402410f4a00c841a41c40e4501004000d0700241005000d15104043c404d400c0403d50120301642e00c0241141c001520843c0c0c0e20344010044c4401903045a10300c00407401a5846400000800c040f9480c40c046814488003070f001100e04036003d001741c0810603c4d11202e000c040d03003d00c55980d44502c503008082405000ba20b6001a84041100d035140c0321400032078102400c05c4240c003000e0140910b40e010264540c2d03030180c1c141c080b0346003009840c07101c141d500941003808001d00140c84000464001c04074008103084044403850f0007510382d0031807140303400d134014668038000a41c58115980608207a091010a4080142c0e980180140680042d112181804150b50038030841d2030100c00c148a0548030058404020526001074032214000c00d035000c18080410403030b8140300c0c0c0c00724480c500071005a4907441c0c118068010003d00c51040d03003003c144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 829951115 1250 829949865 829949867
    0x516080c010206011e060503091207060c0305070305100b0a09080a060b1207060906121e0c270e0c122d1b0307050c0303130605060a08030405060711040c 67
    0x16010044500340d00f26030031a42c0b20309a9080c0200c0d113054207018003481072810030041d80108040e5612102c1c4c4000d5440701c4200c03d070403a045600109044540c1d60b0b807070702c140750303426018070a4030740003902d5140820540c5012013008000c2d206a000c0e82400c02c4010030042c214078400e03102e81e009004d1400036241003000e9440d0000103403401840e40c44c070400d611600f52102d0030001600c8070407182c056803884211403030300100359281030b544c12508490300d440c1c5c0703404800204204034040105d450800c000503400c02c2c1070002000401c020445003d0340441e103240b401c1400c808400002036980e10101c9050680f200c0340d01003c5807040b0700a00540c40790790020044510203004080044e0740d5001c0c0d0078200c0000032210301406510880d6455503c0d02c8004c00c004806002c4009180c1c4081d0034180300d494007030506021f0346150003c07160101100c08081046080007814041c2e01e4000d841079445800c1181080040b03526400b03540500d500814000c40c00500340078010001c4201000e018000b0844000e80d000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 829952365 1250 829951115 829951123
    0x110a0204060b040e01051203220302060705100e030f09120a0f060f061a03040f0c1205100c02150c0d09060f02180a0501200102040b03190e0304050906060304051608 72
    0x3c01d8503c8644c91070000140c504042503c3c8035003c02010181d45032600d01030b4002e16a1501e4444807074900311081d0040016180c1030028103a007401100148100214440440190b072829101d140180c4c2083c00310312015900c14050300c3e00040300304c40712225201e41480d541d140c0303804120081c040a0340a41d10700d06224140d07101d030305070b149a50070078481c0b6602c0c0c1c0300c07080c4d07a0311450305030395050502000010b000c00c42a02d000c500c2780d40300b4801ca0001c40c0d603508e60886007414401080c2c0706504044600c40410b01c0504c10781119151a00141405c1c2c071014a44055242004261102185002406910190440d4400e402c0160301000400c280d203242c0c44400000d400000b6881c00e0201514071001c8589001a0400b0480d41d050f503070b6194407440204540384024081007a01c041e1340d024040419802d0075440a140b00d00ca50303a070722010070b0141816000c2511600d00c9a6040358000300404e1120352205181182c1c80003080c1da5442d681d40f11854060b1801c1400c500d0110128028200440d180308042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 829953615 1250 829952365 829952369
    0x30c1703102103050f0903010e100608070e0403090e0a090c060815040b0f0d03050c0d023301050603180115050117010e0703050705040e0108060403030e0319110a0204060b04 76
    0x208484400c00c1c00107a00c010b030b507262500c0140220b041484041c00c41d4258000510001002400101d520388604203000e10b480c030300d50f010028007511140d041c45140130801600300144246100d02d011800c250301c010308040102e003d07126a212580d800141814590703000948072591140c22850040e945007402041000b003500c9050410745a039403584070600e0103003d052260030000b82140d0030700b07061038108400c111034900100c040c054140044c5c0100d40341407040c40320100f410f8001d0b050810b4200042c0c00d0110074000d5914105600c046c500e04c2d000c0d070044036503041d110203590786903883d12640000d4000e0314480c50100c2c83c640c2820b8001001e0700c180c001c1c3c1001c0714020303240c000784041c1d240700c5004c009409001c2c0100c8078100d4400540c200f8420b0704031035008416403e050780740c1a02d405c921b0b20f4085090f040051030354004130500c810958140b0501c158501002c0145050009045108600503100b45480c0f04104400d020761981c00014029034007860350041041000960718801c4400343d070454 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 829954865 1250 829953615 829953629
    0x302040608010e0615031909080301080606060f180f0d0c0e010902070f110a23100807021b150d09120519110304030c17060601090b07030c170310 64
    0x118000050360452803c18900075200101211407001d040761000580c4c2d00014840780c20007a4445080405070107520501c5601400f8111003035507981080c3d0110310784075000d002c09029480c2005241984000101542c0b000020340d0040440a1940000241c401c2032035846c0a60007140c0c0415a4100f001c1f54100c81c3c1142c088054000840c0c0e03944001c0b0b0120f002d0050040d00e40340c0c01000741d10005500c81c0d031607403004200801d14000743d910340750134000700d150004503907001d000d01800540b503600e44810007100414991408250502d00b05400075190b2800510345100d5000030b640c0d0500c9030381e0ba03995450b0b0065401103410b8880c0c0f00c0031030a0001d0200d1231425035803442d841e520320000511030021240a40840056441111480e0000b00d80c2c0780502148e400c2280030600000c40040e588125400080400039650341c00307070444070721103800c11401074249810300c0040d035402c21541007080d080c0d560090301814007072440f212509007101c41094900c003005600387c0c000200301500d50190000401e440301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 829956115 1250 829954865 829954877
    0x18050c04180c110c010f1101060807081b06030420041113030215030c041215020d0b0910080d03090c0312090303020d030e0c041116060203150123030615030703020406 73
    0x83c0100150b11401071040d0346001400020f0303e241181c0c007030050500110702c0d150000034070719a90b502240c141145600105850780109100440c000b802c02c0000b0300d00e200032550780d495818955140c94804036603030101001d01c90813201e4000f0560713654ac000c0341c42010780c0303940a5691100402c020008080c50001302c4c440d00e403442541908500410541e841001c01034880380c0b41505080f007110724542c1c1904116a08446040303a140200a00e0018156426100d0710110b24120420700300b18642c2c800030000c4101103080001008601d000040c41400360002d403c00054250321800c000f018001d10b078201078403501c1c5400c000082c5552040b2605c2c00c8034000c0d42500c001e0f118080d011805e44040300355020302c41c0c0c820a1291524039180c0c0c01441d0007240c00c0e410516103010381810a08031411464140d50080d408420060b0b040301500ca9845400400d2070a1000d07502d030300c1481d010402c5007002c502c114036004000550551100b05441c050389000c43d0b9080e840303290824001f0080c3d8030500403c000510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 829957365 1250 829956115 829956137
    0x13050114120117070909020d0b0910090c181a09100e010f05040e030c06010e370605010e0303070f020d170c15070f08070302192718050c04180c 63
    0x8010b226031b0031004ea004240b200700388095201c0d03003540d0002610301880b030b0240440100e510300b020701c1814510761061210400040c90103248951030303500010b44003019414200080c01d00800040940c1c3c501c0d40844440205484940c4c070325400c017080740c210fa140004614008a0b4408240080d00c040b110112814440080401c0034103413a8040c00d00c01d070009520a01c0140010503d08246a80c020105041707401c00b81d080c0701541142c03401040301e84203008040884038401410502039900500001e0034454408088040400c1d9248244032000d00301e00398062003101159220340c1800f5415420103034401c00390312501c401e80d0751640302c1d030b03507000c0103100b4012441c2d007a45e001154584903480c0c5842d41c0d102c128281e501900c4d01c840080c072000c01c142d400c0220582192a07202c4403540c000d8540c0d038520a2080402c85204144440031141c2d9908000300d00411040282d038200400c910318030500481c41e91200c007480b0900c1e00942d0040741241030303403961007a40f01c040d81d489030b1400010356961080b815 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 829958615 1250 829957365 829957379
    0x3021e0307090207030513030b0f0f22020609030610090f051003030e010e030f0a0215181e10080a050601030519021602060c0604030909021305011412011707 69
    0x158a5050240c064200400400c858205680500790050080c2085407900710586445040c10059410032110040070405100c0a107c0001606030320035040c1081403058104091100c4440c2c0341e0100070440301c0ca103c41000300315110314041c0c030305403900034044414a00300746410400c58440c03070145031045403074502030040e201c9043c002c8a0080000c141007600943c15038600322019050500c1481c103201319688200707a9910104403103000303d0100c10141000310206d2040205d104084040d0f194121010301074003140c00c01d00240d640394020129107004a545030011810031518440700b03d650301802810304280f201e1b40103c0d4091141403100c20400450307941d1030054080b9002a1034016652500030380c004182c0c403030307036000b806100a4840c1c2c03554000c0e00350740080c1c003641c40040020310642241040c4410583c0240440c4041c01e411001503003131106090940200110318070440b0f0402c0755240e04c9036046020308003100c15003c403407030b42e003900c2d0340e12054254000b0134209403070b4020b4854914001810303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 829959865 1250 829958615 829958659
    0xc0703050d23090108041109040507170705031209030f010213032108074a030604050a02090705091216060203090d060207240603060b10051e09040606090302 69
    0x1602d079000c0558200010740c070044500100081c030868103a6032484601c4020f41d00d00400502c07070b40c42400200342d201d0601d401401e403980c020040000542c80000107200c3c0307a8004c05d80c8407a00e0480e400341c0740c13586501c4001070310f07007032458403c80115480010141aa09055000e00d815240514030100040c0106034140c4010769540c4c2001700000c0c81c003070115503203030321600e180c2d609180980d1001c080d0903804000804c0c42d83c04a030080002e0038418480c4040c0820140e021080302c0021030140c030349441c1644a40707448443d40e0b24001d01c203d010f04009104d140c050003d580900700007800c01c002000078102d000c0ea82c1c1c1080841d036070410b20395000004007548004112a048080034152a94800007581c900c000383d00244000c03541c50192240202251440440300f00828000900201c0c8a5146042c0340c1c0c12901000341440c041d90b001d0503240c40030303900070084481c100d00c210000b8a409045074000000e5006141d40d19a0013428000d0000d50990b01c9045881664000c03206584540060b002da80c402c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 829961115 1250 829959865 829959917
    0x1031a06010f080708090115060512060d05030a0c08190203071a0601050a1202040b070309150f0e06090f220501140102070b0a0e061605010b01020105100512030c0703050d 75
    0x35000f00000740b807988201507094100c606000085114840c0c40070700b20300b102664001c540041d4001c20060700c00a60510401d030440780903035040c1c45055007600e070310751240b151034104c80c1841641d0301244108202d030300444066107411600c400c9080712200009482ea8030962040e120045103d5000c07029400c5191824002d940503150689170251544081c0e8a21007500107800d4060303400e010006004c1b0181004000c02c611994810f410300c1c0c24071b4580b015880d0780e205d840c02042121298540c000307402c0150b0302d240e1902124010303115141400050281c80c0c000406607000a11b0010041401c0d0924036a0781c2c50341241031091005070f03203420380c3c5101595030080c140d0041e48002c00130031104803024004c1080380c0880c44c0c290754114100012400c075611402d050a40310200072020000e208080c82001e02ca06400d2009006500b48841d42e2081000ae9010b00b40c400c00b00c00c2c4442c0480c00d410002c030f51a0402c00300540f482c1d02c0d6641490b070b440705601d909000205145417401c0b52900380c0041000c0c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 829962365 1250 829961115 829961117
    0x30316030b09071e030e0607030203040c06030b1503091908090301240902210903090111150c0d0e100b03060c0310060503060f0409050705040f090803150402070b01031a06010f 77
    0xa032200d07100880c1410204900e0900170300d0342d038a4480b02e0044d803d1201606c540c00c507403405a60b0f400c1a1400d0740740c08010f5840702d4209483d0000c901481da0300c030307815105140c019501650302d039180d03c0303030160808405011070500d1440000c021420410100040e140c9075408030003c21000680700140329401140c90400d400495103224140000300e2a03074098080b0001c52116004061920716240c030b800709041c1d6600d0a9540082809009903a000205030040c0080201034420f002c00d640a1541410780900920400e2030041615040310006a0000c0071051451003100c01035504528140000c1a06001450003070050301700140051610b003080300c1c00340c11040141c001e032920f0a4022141500060201a804420042c190b00c16076614021030603e01d01900180200901c0d100801040714410300304000354606040d289800301e9810403e9980c802c0c0103606030b9145180703280000e002803041c0003009000a00036400807050050900307181d030803c2080112085203441e08801919101e04500c4850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 829963615 1250 829962365 829962377
    0x40f020406050405100e120606091501021f020c0a0b010f05040b030604140c1f020601062a08071b15140d200301090218040204150c080408030316030b0907 68
    0x80141070011040401c855241ba0000038121500e002955401c4d41960006080c0c1c001c03800d0041702d01d00307801110707084200003108003c003000e0080041d448604070409580070103043d20044491002c20b4048a04050703400064480080306032a11801c421401c1c0210402d005c0804008140d50070544100c94100790010000c0500c1d030707625a03d07841e4442000052038500e014803440c0e022180c56080d0301b00b440c070035128154285085180c030000d103400c1050f4420010018815510314401c0c803000812504002c10b02ca040c8448600c90510301181d22411100504000342d5840307080207640c0a41c8410107031941e000003180c042030801c2044810090b940010b80c48d4200401c0880e8501100d84d11074030f1071000601a1400c82c084560080180390800d0340484c007d560009101c2411040b64913941c0d103400c008903011402d2504040c8000002c0d001c4400c80f400b17009142d1088020b21004a09407002001c4041c11680d4070718101e085010401c544540704000b0a050103007408092034070a0066210f00341a590301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 829964865 1250 829963615 829963619
    0x240f0e01020717210a050601110a080a030f061e05030d17190b030d03060812070f030f0c060e0c10030e0c060d09080408060f0717010b07110607060605040f0204060504 73
    0x403d016070203181061007020b80d00f00c60040b8100c194490a2041819280004240c50000e00141c00e0401080d94140160041c0960000158a000c265031000945103000210542003200c410010907580d00712203468031040b0400c540174522510f11506550040d81590003018507080c1c195240450500c0c60b404995080340040c03e800e0980001c40210020b03200081403428521000c6420600160280c90001c2d80b246c0007405110010404416405500006c05103070481e507441e014116100e02d00c0003010018008890f4071203030702c2540d0950b900c54026104004800360a03040541e1104980642801061228100c00e540350184c410540030303c88040241000820800c1045250b0780a42c1c80201500d603150840d10203c0c6100010303001400c4802d00600c0e25003806140f80300c10b50700c001d10035002c1055110314140640b406120880c1100c80b1900701d15203c20007407601c1e51120560f42951500a43c5c041158030034030800b900300b0001c03180265010810204100105410380c8a40d01403039020800030001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 829966115 1250 829964865 829964903
    0x180b160206041806090501080d1710050a150201050709140112020d090b01050a050d052109040c030f050a18021e0a030309090e070f0b07240f0e010207 66
    0x12550018030081003145055125070144607038070b04200d0441e0303010f40d450718203002000451044d40d000d800f00300001c214141000900501210309170840d01d4248281402007024001025024030113044010078550303035152140d035040c00039200c00c0c581800560800c000318400368022807849064a5103401604100c4e00c0e202e0056805510b0107140e1f061040d070170403041e5140001ca00c50406014803403150000a540362a082104c01c945640125124130520405d010001c2e40029220701510342c01c0c44001540c0d604120034640f18010104429001810145580e180d20340c1a406040b901252640410046d143c4200f1082280c11006050342c00c01c5058101c14007515280b040181c455048c0c8003000380d01006400882c502ca540e40c0e1084010880000c0f00b4800000903000d4440f90000700401802360b80d280070084c1021401078401d110b16480002010024440b0b441c04821041a0f0140814102c00e0100e280400515904421880c0c05103060324a019144041c001c80b6569601328010602c0310700d00b000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 829967365 1250 829966115 829966147
    0x30206160e011b0c0801020f04030c080d200c150a08070816050f0d020409050106080106080c0313050a0209070810270b12060a1e0b0d06020904021e0703180b 69
    0x30b059903010891440003901000900007010f011a12010894540340340d460300090a8110b508000420b4119137102c594196000d6074100d220900905800c0c500c00303110a0b8103007000c4c02e100c00e944e0450070803030741d00062504240c01401104c3d1326549080c01a40c43c01000c079250207080c0e442c001620050500c0846162082d0082d004007840e079000f035454001400e030390ad000c80c0d00607485008455101c200403c612500408070500401403802e0100c01c03841c100300880c1c070520008140442198408141600b0b000302042141c48041d030190001015080c880000b0380310f6a403c6655914800d00322201050400d0851064142d80c0141310b0300d03100d42050030046002800031720b0a05500109609101c1580b1142000018025500040002042e0322440d00244002e82014400c561031810108a00170b29100c80c0c0c01c1308441500070302c0050302e40d00d108002401178428484010840c0f51b0100c08211040e48000007004c1c030520a45555080c40409156214007441c90b100780719000344184101d15000314140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 829968615 1250 829967365 829967417
    0x9160e01050c1905010606110a1205160f0f141f1107080d0c120605100c020609040204030c0e060913170708040b0a0f020f0d0e04060503010207030206160e01 69
    0x2105440001140c010310f060601a00241aa8241e4403248200403058110000d40b851403243c0e80507204040c242e0b213541e107080282c0350368030041140024280f03500255240400071200e5110410069800446c204400c480703282803030950302e4400c03615010b4410b4100040402c1c07501d0150390758024a6840c1900e000c000d0a08a88641054008002c94000503410303100401c00100d4003100018a4041000010900f444c440045c0c224149800700500c020742c2e41c3d8180f0441c0100514051011441c6072012403c9400b03138516064002d80049404030400c0325000800096819200e480902d980e1038004000c0400401d42d0043c81d07078002c01130184040b801d4460810500120421764500d0302e409551441107d42c800d82c80700420780d13404108110483d42c03211724400f02248500c0185110110804425292030007880e00101303000c0103045200040e03c454100c000202401030085403642e0050801030b480f08001c580d8101d50031191070340980f41900605090031010707010b95810f5a40045100008a2a140c4c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 829969865 1250 829968615 829968637
    0x5040804090c0f030e0c13020d06051f020613120c0609051b010f0801060504060c0312110a111603060c0201090b16022b18150c0209160e0105 62
    0x4110204140780c040c042d10684002c166034803440b0404111000f002c940300b0401c06a19600041c030110302c41e507158980b003100a030b403080006948941c05040311000300100da10407078000d050f1131848101004c1010300103a20000e6502a564966243d2484130a104228500148040c10350b01030642000d11680c7c5c2c0000b003d1207107200207003804a03500c0b107510f401c1299808200709244045405820f50b4080c40e544104040c5040404065040c44005051405140100b104109813904502d0a143c072404000403c081e110404000f54260798015280315804140070340042543d410004041040c0003d01004130702000e503001c1281815680c1e03100c060f081c0c59803600304542d219015400460002d0072041d0251b03081420040c0e0840c0c00b01c201905100f00100e01046580c1d0748511015062803841c50100c1e50b269500e0104010056800e180b0b1160102c2d400c042244418070321042d003207981020500b51400d001b00d400d112a0784c1d860116a0100010b0180500020b040e803002d00303120350052024220385c842c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 829971115 1250 829969865 829969867
    0x9080f03060a0f03110f04052505070602030a020a110d020d140408061009050603030a081b0f1912050919020a0503191e02091b1c0c0306050303130504050408 69
    0x1640e80304502d4000f45400907140307039014151100340d0f4030300808000301141d001e41c1c0c14400e92a01d40b0105080e120701c0e00740c40c0b20034008c1100c0411410302c1a0200c03100c0980c0304c0800c43d03c0e41002003100c0003c0d0001404400070070405c032100c607031950740090144100d015503801070058141d07040044644109018601889080a00021500c68014010300f403007003240344016030100c0e2a06807620187ca1002e00418081e8108000d524003176548462030a90100d90691510391280c40e900d01c4840d10b1082d4141d01522003070114441424030f05103002003900d4491a5180002e0030101c030620011030f5804d8a16080c5640300442c00d880300348174888480d49041c0010907405190755900042401c3c00c0c030040050320141040c507001c00401404e4204100c0f4030100754606009034495a01048441b00c0180920b515120006d030040303942d00c02d0204407150030300380e0030020003030520841060b805840d007940440003003801c10201180c2c900f0004140c600e40340300048a049000d1a00051000500c80034106480300c030740c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 829972365 1250 829971115 829971119
    0x3120219020a0203071a07020103110d0912020c031605010c0611130e130803040b09032104120f0203090d1a0f0f070503040302060601200601080d020d020109080f03060a 74
    0x140311100c034210522181c001c0c000941141c8100350034907000e40c110451030000b080e0a02c2d41031072910240c0ba91030b80d080c00d00140d8100c0541010180340210514096100e0814910304108001603540c0c80c8048001e03000c88401c0d4051030201074407124800d542c113644541c00d0408000643c030400506041c2c2d402101c0000d99070510500c42d000c00e6021401c10304440c800704c00100950112030f4041d03a40b1848a0040c82001c0c2c0e0560344e08045444041d0000d80074200541c08100681c07000c0c02128040159a054400c00110301500743e1100c0318200c9042d6030403a40b002c4150241405818030031660002580514913081c8030ba800c000306050803080603602281301c904004403540310011200d00603500803003802e20310b03e403800040300c00103001400c5d581088000e20511000a40014801c0d41081d42400d24034200d400315140c202140c0c91544a14091384a41000010740d8140454460f03984035282c6d090f1100c580c4080c01c00d03801d981094100910341c0740108400c81074462484061504884018546c162030340e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 829973615 1250 829972365 829972387
    0x1f05041110020c0a050d0803010909021908070e150d0312330b070302060f0a09050303070e0a081b0d03030e03300106120906200309060c16031202 64
    0x1140038101e01c00940c1c01010041064501246104000c120845141102e040d860362124600c0c00f061050021040d00c51000004550360204014013031000842900e0f0303c1503454a610303135202c0c124400e88014070b15200210f001800c0e44807014019030409840d480c030034222a64103d40d00d80c0b05217901c850880d55410403282e07d04040030201480350790380101c240c01c009862420005400d403548441d880200410900300080d0f0041249580081c9444000503942c0e00c04046030050425403000800f280800420072441c16081180030b02d00050550b801000d00d511072171440c6d07850514648144070b0f02d00c00d41d070300d12407841d10112a884d00b602c81d01e000b25440c007404082c1460342e0061101e4103a10342c10201d1030080070107034021210740072003038039502d02a5501d0401c01624038007108a04402e2152100c0905d02448130720740007050039403c2c3d01032076401100b40042e01d03040340d00b05848014080c06100c0c0414102c0460b8010ba883d10070030b8100081d02016190740541d9101e110001c200f4800d41c091104031111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 829974865 1250 829973615 829973629
    0xe0411040e0d0806120609120903070b030906070909060f05060702120d05070326340c0c0806070f1803170403060b040c0207090c0504030b1609081f050411 68
    0x7442e01500c419a150428408020070421885862141c60b8404810403804040c0060342e0b0201c109606a0142da415a41d00800e0510070030b40c22950b040c079400001d0003400d90002030058429650381e600d02e110a5241c840300c60540d111480ba4010400881009000a140400040c132045100400b1100c01ea24000015410007901e0a054400b091000c91045c0900d5004081114110f4000c50140b03c090250310070b1004240019107001030002c1d15031580c2d200e038078003c000003031604412001d4070440188030000425248061004503245900500700041ca1200050038500171205500c0e1807025007a202d1040f43e407884600c440d00041030b00c5c818000046002c601c0001400d085c0d14a010740e4a5055041c120192905135840601561038008414001d80c0d0100c1d45d0f00039a280e60744007042c0f9480f0040211b078180210340016081c440544180030700800c105140041c7c4da071a5031241b03102d5550b5903502c0360721511a4000081d11840440320700c801c540c40c0f58080c652107442600c1141203441000b0103e800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 829976115 1250 829974865 829974883
    0x308182e0f0f0606020f0a020a1223071703030c0306090603071203050703030b0f130509010b060c01020909063a1a100f0303120b01090b0a020601090f05010e0411040e 73
    0x30039070701c07141480a0703617042c03050b14002c080c401d0080000104a5010031003a5503140b095140300b0f103440c010350040118440927a0303144081c0e407810b5060051503105c0b040d1105114414841c8400404110200801021060303a00c2103800c40d02c580d00310394801c8144890142c0040c407071a494001c000000c0340e028010301504c034032a4041d40e900d5484010034a001b904940000e40313694460404100c50310403a0340d400147c400f80301c1c0e003420301054540301d1064880c0940304104150ba402a408175001504840c154094030801c0b10448030070589844070400e00034071402c1c556004000f00c002c2c02000c0303808081c2c2d1a01c0c404041c881c046002a00423180c68902540c80c90812002203014580b090201004006190001500744000c505c8991481d603070780a406030008038000940c440d100d000d140180d0f170040d400d5030300800c9101081c9586190419000f03440d42c0090003007502c0386142440e00c0e000e5142c5485600d058960030140c0c0500350f195500d42a601407107245489501603102c482070b40c44003a040c025442 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 829977365 1250 829976115 829976141
    0xf07171f11220f0504050411040f02091513060e030703080a09030c0b0d140915060a030c0e0f010602010c0512101a070201030f09050d0c15090308182e0f 67
    0x360b854100005060500419030290f44990301740420305c40410b852000c5145040c0d411600001d43c00030340c092a138040e0155140c1150722881d4001304c44400c0500d040100b0300303480b1558000c0074580d00d41c002922905201460a030b01503100d19410300001300060014071554540d810f0400711259a5034402210604a4005580c01e0038080759101e01d00319640150007a05540142074a080d01c0c00c0e008080d50764220b0341c0c0b207000d400390000201c1c4903500c8803d070318000f03550000802a44a034403006e900d1600e1a055501502040c0c4100c000504144184140503140a10b40e940e20f2a14000c0388000242c080c2c094400032645004103000106c5407040c0c10201c40303500d50785503000d0700e03460f0341d0001500f00d0710401000b1720014101918003000440200b0a6000000300d410300400c564500e040076aa262210700014023072501c0d19a00105064010341030700d11030dc014410b100d81200c01d041c0141d4884103031215a8040d030429401e503500b20020984040c150302d003c43c0c000118101100d0050055039100340c1110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 829978615 1250 829977365 829977427
    0xc120f02060645191802101218051c080c090937060821070317090a02040b061207120e150a05010605160303021602030f07171f11 57
    0x204901c1340307901402010402d048182c828546098011403175030b44000e4054004c000b601e120030845005c0942c402c81419101d2000355074400c00303920300103942c0c035103c40b50840364034040c80200445a1041d054144580458201d09040440b488213000078100040c0c601c5024140808041000354068465940000c2a0b1003901d00700070031301c82824080b40c000e40c000060701d8104824081e48198000026203692900d40c40043d503070800d40c1411200481000c014203182029541404019240001c480c031710903008603810001c006a4108001da644604500403d144030b000000070511070040d070301d40311003010031000441d074500802d40d0b050400002044e14002e10340000b0074001012118850313180900101d0400c1071820421420410780c030802c00100808058000408401d90184c0403070100c9010f034090304540e07480031040c00341900e0ba40b0354000da134203120501d03101c80041da100207039110054580300f5918003030780d07248102807001d0500ca0240405404041082a042103038004141030b100e00c0c204410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 829979865 1250 829978615 829978651
    0x5100807090b0c07120302190c08100506090a200d090c09110d150e040807050609061504091b0e1005010512160c120f02060645 56
    0x5424121560410205140d0520031840003d400040c40801d880348051900c84418161070308900d00000741003088a0000d080e011380c01000344020026055801d00e0301501e00512095100c80c080700c000b25030180e0b100d0040030100b031100e00030358031400701c0904a01540c40c032981e0407214080c140e4071503503007130310072940d945180010710489110000103006181014040c07206000d04103e4103000700220785084036520703691520b9031140c42d45410001c00a50b03204460501c2c041c204480b140d000004241d03002c2c024100010454000400c0b018420300c0455020308002409105105c001c00d101e40c0c0032550110280d000c4007000d4400c080000040c10350700314074070503454298402407036803c099105c941441020303c07413110900d40500845030b2150071411a8031520100010807141140d681c900980035260280003160295030100c071543c214081d940032106c00752a440e0500c40303500ca10300d441690340e800704400301c003018400220412440c0d000604480e0000e0744845040f6240c4415035507080b003000e1090720 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 829981115 1250 829979865 829979867
    0xa0606050406050303040513021e0d0b0a0f140a0302090f011e0302060d05070c1704060905180403260906010e07020a031d01030e0304090b040b060309030403110a05100807 75
    0x801015020075102809858548408696240114020103124010b600499041c0504550540d0361928101d280c2e90400168034007108444c0e40103203403e40e1228244200c4203114240116018201c0c0c0c044103204859030301d07042c08414019880c202c1c43e64004104480000980c0d58020305070b00894400340c1c41c00c0e00c3c1d498503001c1c04c40651007024a8060020740d010810240c1c0c0c40600740c500c1d0940c990300218541e69403603400c0350301c050060001032a0000c881007509240c240a40640169101b940354108079984070f04c10401080d90781c030100c2c1c220921410008001911500104806841c990058042208000f520003502003003190844400d0303026900420044c11072840c29030300600b0b54005406200040c0d1401444140c420a4070030340da04000d9190300346a41301e42e12030744504000350306807500d6640700c40d01d00000e0b0a10248484c0310301d040c42200701c1d440c603040c6d04136402072401d240214a414910358807020a08000710020750b02c013159000c0080e858035601044801c0354000e40d140c8811f40341c82d0070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 829982365 1250 829981115 829981121
    0x140c0a110306070807050a0c020a030212061f0b0702040207050307020909460201020f010e010f0c050f190905100c0213060501092106021303060b030c010e0d150501080a06 75
    0x440e260820080d1800e201045c3c1d0898225081c0c0300e2986000d2001e4111800880d40d03034038040d0700081d0800d040440c40060781e40c010a440e801100700e02060f0007021a048010f590031400b90046920494040140c600180350590041a0243c41001664181804c50f0000381954000316060070454000001c01d00c5e030300010801702515034078102c1001c0f500e00c202c1100084081000c181003e6103400d80350f0500b046da0300800414100c80c07203101c000e000c00c480c0140c505c0d01030011110103a0145040091450109024005860b560b00400300144e007081c5030743c40da00324002c1d00f2084030001d0120790f0001003096180c20404144112098441c1004a800e61042c00b0500b008202945d112a150020501c01c41c2c7e0300c1142d030001c90300c10768800c2011500c155812a4401404c0d000100f0452000580d0884a05001030040441e405007100b0031800080100745501e500d402903446000070701d5080d0f480d0480c5888400b880145014100c0103507241c01c2d20030361104441007a00701d6000c40c3c1c01402039104201d4540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 829983615 1250 829982365 829982371
    0x50303032505030c0708070201031b030f060e01030b0424060f0e100b090f0103020c01020705010608070b040608180f06010b03180304080a0b040f06110d0e0c0a0303140c0a110306 78
    0x1207489491413800303108924203401040ca000700000400981c8000303680c440c0d0003180c81110040c1410b80000d180c05006401401200030300c10142c2d04010001418461320b0500754100c035081074621056a0b40d030f41e41c000c80d43d550b404c40314480c4004003449030b092140b00e04c10035000d484110f8a034040c076410300310b155410310801410750040c40341001c000c0c014498201c0c26911002c0c2c0c02c0c1d8800b643d280503540160042c2c0a4260b5526a41d0310101d001d50034003005402070f10448145206549109498500c5014144154010308001c1000640801d20b02c2d140201c1c0c10303115211600944240501d08000c15040c51800e0b44aa00c120001206000c207444040d41c1400003043c484004500d0b00345840505500d1300b140da103002d0318241d2200d0024060240c1d8440490329030364040030400c03200030580010502a0080c40c03a80f88100d180581032403c83d2000107182080030310050602c4a000d18640d0100d0305050070100100c4d510400340034010b1801c10400001245a02c100c480c440c009600341c0c281403810b0001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 829984865 1250 829983615 829983617
    0xc030212070b04351602120106260a1b150206010612060806130807230105150d140f100f0b24030405031306030e0124050d05070503030325 61
    0xe400802510031002d41d0500400800307142d80c5d15102d00056050510781e104101039046034000400c44081081035111724141d40400888080400038071080c00541958051480600c1d4008100c2c80046908111040610030380c0d40700c890840e9866440501c064903007000c24401680c0510014099240c101c00641c0d65060480e00411a00b03160203285907640c2405010134524480520f02c50040c061038070121041d0b1034110722030b0f00c6680480b02261400c1d6040c40c02480e100d52030940440d1440540c01c5440494220082408540b0525511804082400442100b8251061038406448464144600014444c00b0f071f00018088146c00c0015043d24044421548100030707281c001d8032000c1c200b1f5107040824a482803440c0d2640e4492030711a1943c8200e442c3d062103a0051600052150303419000070703c041a11308024800f6902008188507030001c94621100018882c1c0b01c03d00081c10b21181500fa000d009500705c070821a600d03408281180e000752910701c0c1410101c039aa404010b142c5107524020703409 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 829986115 1250 829984865 829984913
    0x30503160203190311160804030c14090a020315030106080a051005071b1707061d0708060c160609030c0201022103240a0b180105070809010c030212070b04 68
    0x1003e0010034001082a01c4805043d51a25948034076002802a600010180429000880344904119040350014802111150520480031903030741c03140341d03611151034806803003440c0c03944848082c0e5020307400050910040700d4084d15565460b51b42400b8250040200c0030241000410509149040901d902d45e0f0602c6141072401b804509507100342422450f641004c48a24038038698034052240301d41417034006228070300100e03040d0b09000440d841510b601c2c1e400581c00d20039040c3c0a422075203d40307c0d8401c0d1455a0092000203018034640001440c2800080300300c00304030030315036507418200d038a1814150001030341881c181e0110b5804000e4030f8204d4400e90b800c0940145400d040103607521008007d06203034000046800022a0131003110119420010000d0a45503140c00d00114150030481001407104040c00921101c2d500682c1180d16540e0060002031400c251080199a0030710a84021811031250410000720180310201070441c90340320310003501076820f09050003654114640030303038103090003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 829987365 1250 829986115 829986127
    0x102252d030b0601020a06060f060e03011a060901030b0301020d020c06090a0c06050a0c0602031810140c03100807060503070915020d320408010c0302070c140a030609030503160203 79
    0x30498985404490303024901c01d40c03030356070080101c0c2004607a0100805490400304007143c99040742c1c40c120241c1d1460740d92469041c80078010542030b240c90346011180b602121868402901300b103c01001103440c18100864050050408a4220381c0000b000310203466002c503030194800418442c0e1a04401c81c240141182a0b95403106d18807100c041c4602c405201000491009131350240a488400e1074204004544900c1c1501d56030507071015034851642240151401d01c04c3c5194144200700358003524610042041e0ba52009040041d840500100001c11000c0f200161820007005600094000f503074443d42c8a00740010080d01c20712039030b000601071b40a40c480701c81c401d44c4c0c0054101984132041c54030405003403d0b0290a050084600c0740da030046017180101d601203240b041d00520495a41c1c0c0020000442140d00c03c13000c80c000c4420051003000191820080d080920088019111008041c00c448680d66035418003140c0c20b031003040300460004000c1044003c410720703510383c8005407400698a014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 829988615 1250 829987365 829987439
    0x4270606080c121902040e061201020c120c031204051501090203011202060a09241706090420030604030809010b010c0b07120e06010f0321120506010225 67
    0x80116107809510440390b0000400f13403041c901045084420b41c5104558850f100c00d01e2605880003214040d014002146192000707082c14801c407404404190081c203600c0805400c016003561000c810031400d8030040c80748c1816448810038003409140b00d100205044031840c0031b011002d0380c059000c41481403040c001045050b1558a8441860754120b03859540d510010906845100441d04005840140304507074104501c1c424501c1d00440354541c42c0c5a00c1c1076200910380090003003c84042c0d8001030341401080006004400e407c0318000003007140c518201003100401d1905004480590020b00e50100307101481c1802e125004070704c1d00a180c90708901e1000d49030b4a00c29003001e4040400c102280ba90401485000d0703200c203076280b0a0000391007d030b59540719502c2612007180401e6581800e503200406c00d003101c1c402600d001c0c0086031118049245204158002013000900e1746055015004604007036500d10b550b60030014030510301c90440c0e03900307208844500c0f0740c1d03219603c0005840081c8511544c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 829989865 1250 829988615 829988617
    0x203101b09060f0e220e0c0f0d02060307110d03091e1a06210f0d08190c0302120a0c030e030a08010b0a020109170901030b0d1a0a0204270606080c 64
    0x24160360b080c4001c134000c1800210764500008080340c0c00c401010441c501c03070500740d50042c441841c001e004541c1c040f411101003002e9401034141716a400700340d416a0a005040001c082c0d07510965a043c00b0443d41c0c50107000030b08010041c1d81c184002a900d80100c010003102c004c11902c02c92091600b504007d00c81d070fa03501442c5195003d2000614804800202c281c1d41705809460070b0b50f43c4001d51444051494442680d4441403c008559400b450301e41040091040317945510503400c940300d0f043c0f44c0071031100e03210040034460582c80803d90200009211030401e01112406089000b078001201e4444500041c115840c0c5600c02030150410050160013541c0619907a0540380b060741c940b961901002c00590050411900041280003800c803a2007179a032064000c0c004040080e2030510594102c6000c2045030f607004c1100820300d1034154507a090922411100780d910620400c3c00515003a200c152684c402c0d14003040120301040606203a05175200e09008410044c60242004000c43c18020301d49502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 829991115 1250 829989865 829989887
    0x2071e180e070b12061206041509030302091c05150106021e0304081f151203030902030111131d1501080a0b040617010c110613020d0203101b0906 64
    0x9054550641401004082c410308004040070500e2580d40e401002c031a4102900865116115801011140c207032a64081074081c03180740d03c00640c1c2181407003200c0590050000c00c000341c0425509000742a02c9807a44005680c0e0a000018884d030310740407a144c0b0710b141c41181074088003450304410040107003940000b0b603801c015030010b01041d101d45940340c4541c61401540e009000318880c0540c02c901d2050b031052460310003041c01c2010300c5071404840b0403a521020610509900800c4154143c01003442035002c0440700380b00400104400e840c0c00194880c42d00306e2603852a00000d03a0074200000f1074003454100c02e981c0604464101c601c2d0000f00c40403c000010209414802c4c9200000d405950b0788d400950a06c100038010000551250070740030310141ea41e11a25040d41c64120303040b610900a075843e16080b00420001c0c040c40c1d40e104020701c214403002c0800c0342c001000415490050b5000d12019081c4600b0140005910306c80b4003540542d403249606110500c80c40d440d060207555441044070308 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 829992365 1250 829991115 829991159
    0x19051f051005130e041502070203070911070c030302100b0301051501050a140412110612160509090f16050c1c14190810080c040b1f02071e 61
    0x118140484070103507442e2150260029850046240110b04610010b1255005074001c444030304100000080309804c80c4103d0030b01960560010004004845150b00500e510041c04c044060800740543d884985001c0b29410071009a04103404100802074680306505040340c00710024042800c10702e940b2100850000070060400400050791556075004128001d602142c60344010380d81d03036070703500c8074440d426100b0402c40341d40407502c0c00c0300072500e80f50b400e07100c20f000c00f800030010580341c0d080c1038201420454204014080c00740450801941e8000d00305100b218940002600c40c038010503403152102c110300d480700c180304050140003c2c044001418200d100007000c0f02040c2d58458100075604503094140703480030301000203840000076040c002003000010640d15501420345404620b03003424422806580003031b030700100942040745440d42001c81200c4002d844240304047e800003920956481141c48000b40c0e10590007001280040c00d11000d04884100e00d1040350303401c1054441c65658001c0a440c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 829993615 1250 829992365 829992379
    0x50603060121092109031218030c0302010f030b03030d090222020405090603010c0c0b06031e010903110601150311070c1211090609040209090f03030a060504050a0603030c03210519051f05 82
    0x201f00d07640100c001261020300021208c03a0a03503246803400c600550780c08100d0009210146011505009010320310100c1d90060266003003c6000726520300503d005103090f60300859400713004061001c42045e29000c0c00002c0f0000da43c0e941410240b146040300541038a000c0e0380740034030300312142da44480410b419540c04801183c923a150740c03000178a440c4200704c4107896170381c081c00c19070103d540545c840308c5518882c1e1117021000e003070b01d6501503c50780244070752201914079040b144000d81c800d80c0301d542800c08001c1e40310700b00102500d4100c5100b140d504065402880b4020050a002c1a042e200740000000c554850b10361401e94003184c2d81910141001303008003035280c0032810080007403100d5440b44d680d2404580d00e03890421002c40141080c0e20500c2d010f145801c000c640a00c15500852003030f285c0584401100318282d44d8122101d010203050050cd01c01d082030854a0121240034050080000920780c0c10f0750350654000c03104441015160400e0101600d400e10032028140c0b804804482003140c841e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 829994865 1250 829993615 829993643
    0x9031203100503061311043e0d140a051311040b13060603060605030c19050c0a060f0c18090e010e06010e10050303040f05060306012109210903 63
    0x958900349800c81903040c000d140030820a408842c064503a40ca02542140413006000070170b102c12601c43d003c06c2c40550840c0c1c03d4410300f4851680440701044980200c0340d400001c1823100401c00c1d040001e801030180c0c0c03070f0a4184a56000c0c0280f180d00a0003103d410842801d101c4400001e116080c4070080c14400c0c1440786d43c0d410368582e800400c210034003425028840d5243ca202e4002020180940030200c1d1a1060200d41c00e8882c8040d00c0c0304a0303031480700d0351503e00c5035000b0501d601c0e0041c01c0b90b410010101b040040b00b01081c07101c000303200d108580c045400b640410b81c00c2d041c1d4100707510380010411a045071b954400ca20401c0c0c001100e41070b002c0000c0005e907600409000d0521520044e085209000c0000781070998003c101d40300e81d0131600034080b2a62180e0415459202d01c0c828841e200040c071100b804a460070000540d0040d005050810001c4038a8090007482001820303400c012550b2a00a1001d01c0b0700d0b41c0440080050800030725500c80c500c1134000d011140540405440c4110400704 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 829996115 1250 829994865 829994881
    0x90f0d120906050a0f050a02041805060a150c060606050322051204030f060c020f0a110a09051608010501030c0903060209120618150402180a110a030f06050609031203 73
    0x21110820340c0002e02848030f80380644840000d0000f103108504624501000200704c6001c07407007074030155a0882847c01ca0b06c028901c07030308040c01d8054855036000003034500c00104650300013260708602c10070343c854034415032583c00c0601c1103590307581c00318086c41000c10411035480c140a1050007405080e400d80a48d854040c24510b1070b100f94214501c4405100180120a00802221030a402407041030f06118642d60310804a0b211b421084072078642d64410400b08000445100c1052114900030388104c6a10703a482c1c207030000780d5005a90000080c10410182416140d01c802d03840e024100a0906001d00c44116100515040c1581700117040254085102e036aa40d440176203080d80c8410340c1e4116000c500304418a41112131400201e01c52900c40c62998500038102c00a01900c21a0000d1020400c2c54903018000300d03c40004009202c00341d580d0400812402440002d8100803041e80d80008000000011600c120b40d070316041144680010702925240d9500028410808880c0403600b0b9241d448100e8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 829997365 1250 829996115 829996121
    0x9050621070801022a070e01030f05030c0d0e10020616180f0b0c060117030409020f13141002150c09060f040b0d1107030c02010e13150905090f0d12 65
    0x5906030750000030383e07540414405d08103404480194045248040c07500c41c110390307a0340c001e102c0c946044800750b004001040062075030503140380c0a00243ea1905070f00710041400e0400c04250a00402c2c1003540440f0385003070405c0070f407a100d040390000f404c0c0d40c10301d10801504050a455510704000c1c2014036034104140c9400014010300c885421845269183c060400b03194101c2681c0035818410b800000400410400b0540b0451030400090741c60141000b01f10000fa50081e1028100e440007084119401441300820340300070581402401011101c04041088014414140c0001c56001055000c242218a0308494118081d4541e036592a150740340402c107280501c0c82100c580307410120300021550903800040c8100340428030300300482d103117049101d0b405001c0c03902c01500160340241d01e503005500030140501c01540c01442d400c20f0764100300c08141541c220440800b504070b02c40c0c2040040c41c040d07008a0740c04c200c06501421405030680440c0303950381003080810781040000c981c4083c441c82c513a8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 829998615 1250 829997365 829997369
    0x10603180b1e0901051f0311040902010905061303030f020f0303150d02030607020106082b03050a0e010207081e09010f050a0504090c02012307090e1f1d010905062107 73
    0x152070355190786406140c06009040c00c4401a000c00c1c0759a4440001c585010102011f80c0e9214091020b044044401d0000070028a0412410300c0040321001c01c40303594003030160400020382a00d01404604500c4c3c000c0c0bc46030812400810755000008143c07800801100740d07035001d5148400d40c01401011400603410003d81c0d83c0194141c001c4a0500031798a506410003029503008204440505c020001e115500c0c070107440a8407103901d80704a400c0c02c45803003a040660051020305000c40c410700c0520040742240c0c0186402c540000e0001160300310303005010303513110b60118a400f005003400301103030028114030580c8804104200001a8850364075000d0b4058401602859004015400c40104040d00034180d900c294041d0070101c038080c0b0100d4841d141c4503849003c0701d030741d002c094528100c0c800c46800780280421070300001c0c14110303c4407081501e40183c0140031401e41091500400500e800e104281030b00404503444c240003c0000544035620740303121080030f080f8100c1c036000d47d483d50141841c0c915 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 829999865 1250 829998615 829998661
    0x3261312080702060a08010806090a03090e060307091b030b1507081605030a08010305100c0509010f050408010219080c03070c020d0212011104091406030d0509060f030c040e010603180b 81
    0x1060344e41d1700c0d40d0701c00807040c1030740d40c118100d44158541000c07103540c0b074102c4000207001400300d480c01d00c0040d0300055480e0f001000039048031768254a820341d81003542c003909a2507608010042e400e001c15a8140107a41c0d09080a541d180600118005103100034420f80fa4003030480300000403800300c503950f210f07180b03500541c12200340ea855081c51075004000d40000e100c240d0b0b15201d0303401107001c010400e1003060741d102280d4458525204410b00159180307001c4104140500c07509003c00107002c0400c0c0002d0200c0110003403009480703500210050720b2400041e000e08010030b1300f8400c200d641e83e000202d10100c00d130100e684901c1001075200007101c02080540070b020650034030740e2680c040310003c00500f040e65800c0c42c0600c100300042007001b019030344c1150815815404200141c0266004038020f00300b507607001c3c0c0700518000003400d881d015584107480035410381000003401c1054000e14520540580082c1c80c06110b01c4082c84480200758805040250400c169400031034440602011110182055 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 830001115 1250 829999865 829999867
    0x80301080d030b0306070903030f0e03120316051206062b050106030b041a090a09080c030705010b0a030b0612070f0e060a0f1a030702010f05010326131208070206 71
    0x114480280c0301c80c0d40c803100c4030110341000c00c100943e140c08140301c1d204284503643c0e0301080c0c1ca552400c85884c49500f0403203051142044d801d010f01e4800780415650b040400b452940c0e01c1c200141c25807090100d82e6100e104210040c80307070b01c13103402c081102c040c2c21003011100c1984412410002d02c9425855155407203404520304203410841400ea0080e40c102c07a010749081103550f00e46c5090106840c2c03400c502d407a030000c020340344c42c081c0e00d405240300345c06c0f8414410000360754102d69036031015640981850401c0c0d0303101044c0340e0308000c024000d134141d0760030580781001c82d64907558500d0744018000c1c044a10500082c000c07400e12110810401005100c001c034810001a0780d18500c10310030030292601030055140c0c640100b41451080591070454003882401e640855007000c01c41ca054102070466000c40d5260340d0442c2441c5024020365000e98080c0880d010240040d0980070062213000e000a843c1c0c400a11100c889a00d9200c0148100c2c0c2c0b03a501030040190303140c0380c0b20281e03116040c002544010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 830002365 1250 830001115 830001119
    0xd050a030c030b100c0501050f060a030f140105070c0506250809010b09011202010801090b06040b0f070c17060906070e01050c0c09010b0301080d0c151d0601090f06050a0320030307080301 82
    0x80c3c00a0117040c1140144000c111540780c210b40a040c280d8112021900036000038810000582e40e41c1c41e41802d5030082030013641d2910034102d03090a4900580740480001c034002c0c21071090003410310101b5000201c0d8121012010300e5072800d42c0c125001c40021a091080c55000118400f038290840b511400005041c181c1540c1c40c1c405061607880002c0041c1c3c0015002400401c12804911032940a02c000411342402c2a02e800460038180d0700c1030000b060000d0050000c880042e0800f0780f5540540494546100a8031624482e540380c0480103021406603400030060190450708041254540303002860551b980b100e0041806260030000550a80c000650500004004003018082c41c180c4115009859104800440450b60421700c43c030041c01002c0150211201c00d04240d1101c1c011001c50b0741903003564024161010b090503000d9020440050b100c0103070502245040c801e1138044c080071a100c020381e0342107464120648551804030110f1483e80762105645680400607140e1582e40075080315501d40e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 830003615 1250 830002365 830002367
    0x10e030708030c0d0e090f100905040507050405241306081903110a3c140f210706060b07141b0d0b0402221d0d050a030c030b10 56
    0x1901103c200319260050903188265544200241020854010130484203611400818100039070080c0a240600314580f500156004031801020b01c40c03801600588003e0f40743c08140030641d01c009054205100025903804840c21101074441d00c59001605d41da40c00d00305074080d503030041480340c01c06980b03031098072602c00d03441002800124106200750f40b40c1c001140f40b0b100d1503545440317404008010f543d03208170704403540801c4280b055510007205548414100002c0c003102040c201c0e80000c0d10300341098111081980d0042004c0d6103c035070303064000c00214546e400014a017101c1449a06000000082c1c040240300a41e04040064035064501650b280c0030341c50881000f051100301040d2501449010001a000d4080030421140005d856050503440c1592041e410340002001207074000c455110355002c03000013407071602d0400780d488000680c41c822500007100903040c401603041203503c0329511500740da611500340d03401c0c0d48250401286541031103406070b0240c40c20000e050741200e5800c400d00c40d41c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 830004865 1250 830003615 830003617
    0x14090a08071707030b24040e03130f18020f071410050702010516050913061d0c030615161e060f060308090f0d0c030501090506010602060403020a060506010e03070803 73
    0x8460b00111422410808000540c452020303200141138148881c000130141340b00ca9501d039800702c0d01c1001c020300c100d00c03902c0004c2c101c0e000460900703030a5002080400318402e070035915070090101500052112458450300080c1980ca6042040c9880d40102d21501007841e03802c1554003072540711446224098a102c041540e40880304000e41c219402d08012412450040c807801c0e0250441680d109c50300c0325860401d0b1002d0740040ac4154101800000081104000344038500203071100c80e5a41145840c5141a01c6065001920b480610034007041400b82603a10000c0c01c509680380e4850207500c031a65921203c0e00912210000750550410240380241031070403a0134810810700c544420880b1014486404049561030301004015220420126411740b07040d246052451a00a02d002c00e8a0407581e214140c02290740e20890781e5a4640342e11000300003090022a014251a10081c4154a89034500960f5068805005400e169803100850380342d0340b05146040c800c0c040034007141c11441d038a425170355072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 830006115 1250 830004865 830004869
    0x3250c150b012307021f0f0c0213060806091006080714030708100902120109020d0803100b0403050106050307060f090306050a09080c0f0606010f020703110103020717041404060b0a14090a0807 84
    0x6c1042c1000358080c802c1c020b5901c80b0322144076503407180125003064000342d079507042c8100144e030720080400320070000401a004c2d410141401c80040c000d80d08140d1a01490901e00a0548040300d00308102400311550004603c2e04403560b10641020302240340000c80c0c20203240ea0801d42190081c5440c0b81184101a003150603507510a445802007075050540c52802c0320400800254418a0300c0c0126001c0b07000f5801468112002c548540079083c0c0d100e040301000c1e030242e40201c4041c3d440e81010461483c2c2400008010080e5091082c1d1040c44000c00a00ca2a51404020140c59650b404141d102c600d5a10032101d0a074000c44c0d555449000781501680e40613030701003644403449000005925948144401c80c41e00703600d50010035003242103564028076034028a03d06410150700344a8100492000e810700300c034208103100c400750348500300310f8120a4143d00c030401034050307070030440d04203c3c40400a0840b0740030040d0f4a0030702a600c0300c0781110400303445070305100d03a800102c02101080e042d10211319142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 830007365 1250 830006115 830006119
    0x1703010f0f0501170703150e01080105010603020901140d02070614060a0b0405010c02090a18031106131a06180108010b010e0f0603180c0603250c150b01230702 70
    0x840e030340e0380c03800744000501405442e00103207000c0346549116840001c0740c0d400c4115410007007642c00c55032507501c00040c02c036440344450010480040007114020311955000d4409443c06500e0030844800107421103001016003000e203800000c031083c4082155040c0c0b42d00070b5124809101d0b4410400e0316101140e01516114401c0700c0186000a010349400211011981d040e19003011880d101d4080281c41100101040a810749070810703840c41e200e80d0100400001d00ca501c07003050310394440040703031300d4580c1c0104102c0605401a0064000c20391040d072a40e40c16485110155903a901c00000c00c140d0b03442c0d0281e413419506a00004200120103400c001203001302a0f03540003412420504002e003004c02240c1c1907030840e01c100003040351004a0104620040141d804851440802da804209a03900495051048058102c82d0814556030100b960501440d2807070302641c03400c2c540e103920200c2c10010209000e065900c4480308101e07401080360b9410401e59940c2c4186043d00003241001a40c80071070102c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 830008615 1250 830007365 830007389
    0x913050304031226190f180602030f0106080702060c0c0c0a03051b0306010b0405060306281a0304030f1b05010e0a030e01080c030a091a04030c050d1715040603170301 73
    0x13082181030308485100f0002404200c06074039007000303404010240c1007226030100c0e46881d035101c145065040a650200c0c801c6400603928500561500038008048e0481401c002c3c8407810f0003804c5d94001390b1107821010389212150703181d5424000c03074985481c0488003608240c000300300006001c00401c0c041c0380003034111025090415003400b010380700c6400f4050b40c28945003d000030320503428000c002e59408500030f031a002a4900c0008847c65240c3c2e4a4180d01d1550302c4802d0130b1200040400c0f088210300b011452840c1182465a0060001c4056070f42803000c100702e241d09011076080806004240c10341250003000381490356600140c0310351300c1605c15000300f051101000318275482601c1003032044c0003c545550860301d400b140140a040b401400340d4640080740800341e0880407400485015034400d440b000701c00465460020309204060000c00f0a02841c0c5802e045490000c501c07403680503007030302d5011404400e6800024002d01d6035800c013403d000035078090300480c100001c000758103a568108120b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 830009865 1250 830008615 830008667
    0xc060906090d030608120a0903020901030b0a2d090c180207230d030b03010f020c030702010e0f0d020d080c2401080106151d030619050903070209130503040312 70
    0x1c3c3d094440714415845260700400c000c0d0600185103015012107201407130040c01e00c0c1d80e00d0300010303000740c420381040d50313400340c1b400034424510b045105124004943d0500111a4007807003010280041041e41039417165900c81c081c1c42c0810075100400b001a00c2908950000b4840c0082c0c050300940000d4012104c0d402e540d40b050a502c04070349010400e040c102402882e4034142c1c0c0c0d1003100502210140d40f0381640d200c019500340090980080c0404841d5500210b49510081c0001410440c100c0400c45c0100c0d00f06041100355281c0810000c0301c2d90301662503200000d090b00c2c0641543c49890034814440c003c02516078075403216040410000014040703215860b03601c4501143c202d4a10340f0810480302c0c041c000c1200c005003c0c455003052015a2907601010115640100342410030031185110081c241038440d090178074151250f1070304000540002d505102c000e81c04542c000e50302501001480f1514000d0008002c41082202e014644c00082d0045003640342e00c01525910340c100b00c2c5600c250b40031142d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 830011115 1250 830009865 830009867
    0x1e060112050933092b230a0807080f010504110d050408071703190506010203160305130905150f03100911090a02130905100807030524010e0105060f0c060906090d 71
    0x40814009000b8643d2240800c49071460210100c0607142800b4454154020100d0080a05074080d080e40031b211881d1703950700039400c000c2080390024201000d1100030350a01c02e01003a0304020b01e0565006071800602c1c001d86100405190003541c070713a01801424081000100510403010f402414801c0c0c0140c4407002035040000303103c0c04203c4078100b10556084050184400701e0700880e030806010b0069a24000f084014200f4220704014260302262000907420300c076002c036110403070042c0f4074160100400c0c205201d04100c1c08450b00d1040f40704120310041d00940d50f0302400041c400541c049010010b081007460070650118508020324860590790001134941d0700349000300c2c0c0e6000300d504413102e04641001d507000c005000140489280a090400c0400d128504005682c082e5004070300400300d021140041d0060207407208011642c50030600010000e42041040850540c0c804440090315090003241400c0300780602c1071141030501c17554042c0003a5420100d01a80152040c5003950281461100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 830012365 1250 830011115 830011123
    0x1f022b0c0c03020303060112060b1b06061903060b0a120f03020105070f32130f1401050315041506030b100305070e010c020a03050f061e06011205093309 67
    0x1010300542c000b0400242158030840311451650810080090a0b5449444592054101d51129041604200c1da2f070f00c0c1c500020003140e0341c0542c0071a2481d4001d41034056840e0606841c0c0710041051340c88498048443e560080c00401800884c5100c00a00000341040880448144019030255280001060388184201682d0602c1f000c1d0391540000c1d00c4040b0703030300c401d0120012162000c01c03040750300a9600c2004180107006c3e1150f40c11441c0740d40d0b4140055410a5007599129111061504038840102e98000050700d61001104820310b411092000224000d028600d441c60b58546002e00c0110701e15405030300000903c00180c0e650442101201410b508541003668a88042090030b0380d5400030b90310400c4c000c1502407014008002c101c3d5655903140c504100145000480d0304840100044040d110343c0900300d444000725102000d00304440081d0003040c00f22402502e964449000a03802c1004000510a42601a202942c1052028041664810300856801c005451800400c03050700b0001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 830013615 1250 830012365 830012387
    0x1005270a0614070512100305030c070e090307020312032a0a17010b0405040f0905010c03061a0f0405010f020c030f0115140307060503091513020901080105091f022b0c 73
    0x500c4c0c05180c080c0e074038a8403200c4080207102d151090031082c80440021780620191900504200050840a06280351010701200081c4604c4042d031082c40b007540580e0300041c40c0c82d160401045ca4039035036143c1810f030004131005074400030504d05400305a240740c10844070060a42c00c1c3c290381d40da82e8625076090309180c40003081c030602d8400d400600042c000791509a22184001c032140c41c0000b14080160344643c00c1d01c0d5100c1c3c611001c00e80ea804208114a034201c1c000481c203407070100391840e0500032000100f00f4000c60044604102105081c562101d00800c4429084003004044500060b207641109018050203001c2c401c54125806001139040c0021080e4501644000c01034071700281400ca04035265007000780b0304000c03407164150103e1000f0314009094041e00603c88950a0100d0702d00600040d588181c0c81203140d40e2500080009000307011400900c5440d8203150207040481040c83e55010303014407201801c44c0b020b244942a052401d0710801031408500a02c240101c00c10104d0568941580c0703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 830014865 1250 830013615 830013617
    0x19020a1e051b0c0a06030b0301020403020a0909111206220602030901050106020c0d03050301030602071e05062d1501050d0e0303060414060306040b041b17100606021005270a061407 79
    0x188005d0000c58001d800c41c01c0c1c0d000d0090001801c0c95070b01c5d00028502d90055114000c501d07910504441840710082009648000135a68001100020300712203540304002003440035080b115014013032a6428204448541640008003552641070201c0d610340280001c2c841c890142c80346020401150408800505a01d50580c503001d0943c3e2854680c030703010350301800c821034035006150110010303000d01654000d0300303601520040119151204804c5006424061400005944030401c0d02d100c500e00d030b2905500640c1004120b800b403034900c0050f070300360081c1500032400e5401c0c280d41143c2d505000014500c69001201d00740a41ca5945814000034141600c807141c01d0b4010700d000801080c454021150064420901008000080c44c001c40d804001070300240312254985d9850070402c0c0003040f8448441400314420405149800c00c0a2340d114509096400da4503111000591665141c0c500d0320962680c070307000780c8a0220101961038560224281c1103a01516001703a0703a11410000900700d10031101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 830016115 1250 830014865 830014879
    0x10051609090216050a03081605091003021804020a0f080105062802031306090303110708061501120e24190b030f1f1419020a1e051b0c 59
    0x104019400654403c560040181c0c2c0c0c0c05074403600041080100c80e102500964130502182803d00b644640300340101e6540080140600409085585040c52003820f41d00d242001a5501c0d2038904103081c50340e0041345141e101d440403400141c0190403040b03504400c011582c03812a180e80714010042a80501d0b1100441c441c070480c101d1031005190b0030300b40407071003850046070b042ca05400d1010365081030503000782c2d00250300e6074400c0003010703007103010b5036000004d003c05410414100218a0740d51000205940551580d04075034070081e0340240c8100d015061121024001e0903440404a41c1e1524854180070f130941c00102c500070602e900303a11943c0120170841c01c142c40c19600700410005003142d01120390703243c024901c680800c15010040300c481c2a050308642400020901818002c5480310b072003214840c02d5080c00c2203028a00c0c00b200f0b02d0461002c041c01615050044130456441c44031200701e44003034080d003111111301500310000d4a000600c03400300c6140f0640100d0070b983c45081c40b070403089d00401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 830017365 1250 830016115 830016119
    0x18050c1507080d2301031b15080610031107050d1e080f0a1d0601090605061309020f09031203090118080912011b17010906030b0424090510051609 64
    0x6901d03080400f6244035132501d41c0350030001c18000c00c0541001e034003c480480c5c900310305403070300c0104813440c10041510302d0090740b10558548010b007800800a10051181c1c188541c8400124060b50000c0c4a416221a049803105070a2a045035603902c4691040701007454800080260114120340800f4886540e440301050b44400350403003114500074003112452512080d0705200d415139414a89141c04204000b0030300795142007a144101c074015003003180182e5042025030050714803003d4040803078001210042c1e807003050070798140c1c0a01400e580f1aa05018940e40403a400c80c864000c2c0d401065003500801103801002031030f207001d440740900240b01002c1400306000034500705810340f0704106140b0000c02d010b80d21011400c840210400c080c40803400c3d00c104058109030120072940500301d001c4c42042813038207540310b224080c07800034401400081062030030b02d0480c0320b8541d5501c0304a51048184828400c45c80d0640e00c45022409180100b407802000a900d09210390401c4c045842d0354a9032030440e8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 830018615 1250 830017365 830017387
    0x5060f04061b02270c0c030405010e030102040f03231f0221071701090c32030408090306060a0e15043e0a170402030118050c150708 58
    0x85081e02c08820311400c4554100d000da101c45052915040d400b05031000440d200440c000e003654405001d644522109020350300314038400100715003c0e42c1c003d0910340302e4441c5a0000901921445d04101400340c55898008208100300c44840220140744c58104000108032018a980b07020348103d1078140300070900d000b01031001c0760340102070b4064003403810038501101280007240c02d1820f031209000142800c4070f0a03418841c0c050041e0240c60307986001c2c0080c03416024024001c0c480f101004440225109a288041c3c1d00202c415070800b22300f00b10282c607844d042c28080d44607000340003002d01074000d00001642ca4904080140c05980d00a90030146d583c071800c1211102c040b58000c500d41140ea583c080c1040b4070032902482000c00c418800c1d00706076101c540940030704940704019807000100c081c07010704c2c10359403c5802d14445c00d0b60818040b1660baa82d00002e8003400307140020100341c10b02c4c0c1011605002d008640689404000e9900800518041010008500c1505005030004805101d0212a8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 830019865 1250 830018615 830018627
    0x7030203071206170d05031b0325080a0e1f0b12060f100e010b04030807060f0e070812070c0e04020d021909150302010c030809030412061505060f0406 66
    0x714403140350900403540300500c540111003503604804e001c00c4c40f140c0780d00d6074101d041204501c82030951901302d003942010b40d01c0c2240b03201d050360201d0741200301100140121032081010101101c0f00b0540004101d65020081c000700342c20b0380c120000314148040f64500c071030001803428400361403140342c550310150002000c0c010201c40da6016400a25952000d103141400c006440c000c003040a04101c40b400e00300e06013468003140b0341c41146001c05d4040100a880b800c42c05680c1100e8201e0700807603440c1030340c1c0340100090140b000d0b00f501c854070304082d481000303070700084123003c0d24000c20440b0440300b560b05c4015042d004420300284010341100c03051021042030105039400c03d02c094245106545181d00003050460707490080001106540401c00c1070401c03d0155014544591a14100312401d5400003480c03e00c4010ac05810300c014800414000b01c02001207800078600005c03080004a0585001005860f81c40781040a1545003803002c034031403610508030f1b15001e0280840c98a0700303141580a07241 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 830021115 1250 830019865 830019871
    0xa020d0c05120c060a1401060c080f1b0a032c0d0c0b04061106060a0b0d0902031f1d01180f0c05060d09061a0a06110a0819110102070b07030203 63
    0x10030b0042440840455940070003078604500c400002d054035107001800e06044441c030740c0d18a044000b124004008060308a8141a05603400000301907070307a02c0c0c0703103540c0d90140309104a0740040740c54804d19808801000c102c851206100356101007450700b241c021041e40314201c55032220315038146028001a0711b00b0400c00e8413a140308080402e1250f13a5150003280c0368021783c1c46072000c100880c22140c000c1303a080c0125540080e0458030ba5850904051000105026501d50070301480c0e40d5030b582d00155030b410401c04044c10790030844041d10100800b80c2ca405441040c2031030002c1c01c2c0c19010450134140c18040da0480608102d010040907101c0d403195521008111004e840c850070030704000c51241c81f100d0080aa00341004000b06403d00a450003004852078100c0d414058040301140600d04e03035404a4440444465180a200d89002941c2c220308111514400070006e0700000340c0712400412a40e0001c803203082e0f07902c6401883c80d507410f003c0d00340d2042e000000c100311082000503c0890280d8007442d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 830022365 1250 830021115 830021123
    0x52503060f080606010f0309050a0206160203010e031b0c0f0103020f1e0a0f03090228230111060c04060f09080f070e011a0f0f09090115020d050a020d0c 67
    0xe05199070741e07041c01448207150025981c9402c0b1404000042d44c21111100d81c0d00300070328003040320346c6140c2c0318192240345c24500244a16400a100030442d41e001e0003030054550010020010841c01c1c0c044580d499014546c2102c1a4480715130120b804500414450400702001d072180c9085850000110029030112058038041c090902440d064082500c02c5c000503005402901e50783c1c3c00b10000d006c0c01590391102c070389041606010030030b001a180c00c65040c07140f200c2c1d0381104003000f035411403900c03003070210f50000d030345400d12801c2242641706580c4080030004000c0e201c1030303a050111f00d403a6440385802c50f03a100ca4103004100c100083e07440303005c0340e8448100d00c0c03400c2d0302c1d829201c03c0706c2410804500b0056803168031000d4140321800000311014010a03444030044240855040090503500506a248000c0c010100303024022098203002c544100030024407203d0f00350f844400c2d2180034181440004014401d8034142c054403401181103808070000d50b0000c2c40180602881101d4465000100325 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 830023615 1250 830022365 830022371
    0x80705010c02040c02010e0d230315040906063209090a0803060a030812040b0a0b0d06020702060918240a121103010219020609150403050a17040b010513052503 70
    0x402c009004d006500c290460b5540340c05540c10f1007200d05451019001c2c41c0343e12010204242f0901020200090018407019100401d040000d810050020483c40e8000110741035003103408040d8100c00381900d0065440204209070705041c00c4184043c00c20102d440c1055540031040400c0440d1140d0040c66101e6030044c0300003842038496030390b2512608001a2101000e0f62042800100100d05010b5a40304c099030700100160154a400900d00300d412010240c1461341c00900c0c0303800e41d150801218108800a0002e01c5000f01244507a0003008040f0342256013a04002400c55120440704182c801140004202c00c80d0507091000d066080403081c0d104403a80d4140b400104416103082c00a0a84000018480f80076405060b0010b400c02a00515104140d04071941407844048101003aa80203174040c600701c0d0f250840340e0703402d844400d00642000755031214402000100030841d445e80341651016a202c0600084812005e0151030059400580035040e030440c02100c1c812500314040f090060f45008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 830024865 1250 830023615 830023631
    0x6060c120706020a03050a090209070c0c0e070e0a080712080a2309030706020a121803060e03250f03030b06090621090a0b0a0f02040e0702010501030606080705010c02040c0201 77
    0x10300125406000200c5440b0f0b000300302000d105425103d5141d010081c0c040a11a0300c00715030010740d4440c0c006100710140084034207e8418400310801840240121071110051810300131005807420300c82d0319281d803041e41c41e48008a41d14201040b00c8040300c039882d181404000440c5d0701c9036010340140c00a82c00700300c41c01050083d9801084c0702d0031794580c284021b190351100c088080c1350400311150060003e40d1f110110841c00510440d101c544861b149107002184101400d2040c0008c2c6d64603403001e40f090782025070b03081c4140f0307000c0000c0014445180740040c15036501c4184116030500520003a03c0740d48400c40c1840428020707084468540030040c4031600d0007075008000750b520703000300390419040320070740c05e042013848105107034160130840e81001070004a8144c1d9464024000040503030410940740c1c0845943d90481d9015507010f482c15184090712894a240300a002304002d110544210341440e200148000010600328203845043e901c140c440c840d15000e100c05040429404c80441d940c0d50300d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 830026115 1250 830024865 830024893
    0x30506011712210a06030b0a0c080a021b0f070f091b0804150e010203060f151b1f0507020c100f0806060d090c0303180501080f13050304080c0a1203020606060c 70
    0x107884d1003007003000c00003d6681c1c114101422449001400031040620709074038540e03100d401504140c3c3c008005200940c4d0b500c2c0c580d400628142c0c0032000e1140398800c2c1c0e402114410320202d4140b06403009403c14403243c982d10042007040e120800c100c41c500070001240460703164401c0e4481e0f0b0f0310034001d101c107110300501c401401084404100000d142030758080140542d500d005c1c5100310503d00101c031342e50400c002c007055602c003d1040159402103240d0568140710081414000816440203004145120302d00810400010300401c6840c00b005014800d150440ca103402440003180c00340f00d81c1c4100e1f81e9822072030b0690300040050881984200e00780700035280540755000d1036800d184259228401d0502d1071034003811a2800149600d400c0101540600050743c3c807407015984000e1114004019444a080740710100d1807262000d042d5000c001000f141c0140d00050f0358120081c280c40110b4881d550b00303400b000b18001c1c08402401030308003e006c00e90b5032400f031015250345000c06003035402461040c51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 830027365 1250 830026115 830026177
    0xa0e0f060c0706060902040501050405090405070801050c22030803010b1c0e160b0328090b100512031215060c030a0e0f0d110103110d060807030506011712 68
    0x103a8030a450000050b00c40070003000b07000c0c8800600311040107509203820200083e209024500485008240c040002418880300700010b02c000c01640c402080b4500300004c1a4400d41e02c21361000c4503d07100e00160701d65006c04480814101c0785c02c40442e03401c69003445030503000c5a10849124080b40403c105031820000580706420a03507417683c0041068903207110ba402c010224a03402455541c01c1803040210f14a0700400000c03c0a8008160f10004070021074544020040044060050804601000001c01c03c0250603001e6450498125450442c8850300301da580c032400712851501500b20300030507403071100c0819410920b4401084a4140b04241045130319581080020f00000f80c8400c00302e00c120301703222101042c0410103981815a64500b6207c2d05040000c00c00d1150400d95a80c0401001350703114800c0c0c2d43d498200c52400d1000613900c1c20f045950340150300003900d081c01400c000280d241101000146560880740240514802404005400b0780081016074640c42040c0303d03010400308104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 830028615 1250 830027365 830027371
    0x140d140a02150408150115030c09030b160201240e090a022d0f0d0b0709080d030608010b030303070f08070306090c180501020304081b0f0a0e07170106080a0e0f06 71
    0x11854546151002030f5240440d10755117183d5004a900040c803560140380001c0109400908011800b04005001100d41620035400505038880a4051089034a5a4104515003502603402800000d2141031780e43d081450044202c0401450b03000d08101003000a41c019511510724002c0e100021101c1c0c0110790904206208401d601c003000801d612805121381000c2580a402c0c1d45040d440148440400c500220110b4064828004440081c414520406008003d0301018003941c84c00b10f1400310190107442d16001e4140c240d424031030035001a090000c10783e032090724140e54000d14620881002d8170382c0d0170050050010182c50b41e20104031450180640380c1c107182a50f80c0c0940120a90617082d4105000c1d4120a0440d00100420801d4180024091984241c02c0f540351500019400005942c24100c52855030007107141ea2001a24201e02c403030962007540581c46e16002d5100c191a07080c14450b003401960081102031001c505442d456070321229038010705008581519800007161403610701c0031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 830029865 1250 830028615 830028649
    0xb0d0509030424090f0e0a1a030d020a020f091e09010b0406030c06020f060403050405041503021306061b0803180102091504090e0c280b13050901140d140a02 69
    0x7590800035004d50100d4800000d0452622241005040c4941c0e00d0381070030b015245124003911a031852004184a2400700700d180c4008007280e280c0304606e417002c1c0d2601c40c007403010b80c468025252102254184000c3e207a101d142081c644440c920120004241840e01c0600b07002055917803540d2148581d1207902c44c4801450207081030451051400800030310345415903021102c0d9410141c2400000f9801c01c0c15039040d5141120301280c500020b5050100c0c400030340c5d10203503000303440903888400111b107a4000c400f078544070307519100c0300e03c020342558200000c000401450ba0004200060030800340d005a000c0c04004480094508000ca1002410003206c3c8652011038810005080202c20040d1103015842285400a00b400c1740c400000a07940d111a0040008429441c0d1200070409210f480100c000e011003e001a8590701e8502069841800d44e00030340d03000b111441c00108041e03192120341102c5d0000100100c18104095881e0aa80300900203400c0ca0341c842c00d03240c2001641c54411410079030402e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 830031115 1250 830029865 830029919
    0x30605010f0e060d020306041707080f0d0b1207030f080d020703080f090f0a0f020102031201060201020702240315030313030f0c15090306022b0c080702070b0d05090304 74
    0x4080102c100c2980240c8064844e60980f24444c006840100c1d007243e000c0d420082107d0b1210340c3c41042d5250b071060300001480060b0001d40421501100800b40881501c401e008001d9a0768030390520500076001d40440403c1d80c0186c00410004090f40c56010b8800e100d00141c605000103c0728400c180e070090307e01140415944010001024445000d00e58406c0440c80280f00d01c01c00d451045071a4224554041c00d11070819230103405690080040310f0011202680c22003280d0380d1400300038000c1d00108001c03489440c9a0020041c1782e140701c0360400080100266092a40c1c40703074031400b150311b8214414683c05000500c141c0d48c9003864002e0900003180079010810a10384bc2c1c1ca071968851000388c02c03041b1088040a0b50562895204144c0c7e4186d03a40120010380e94240c1900d00d02840314240b260100c078640c62208442c180646400240d02c00445403a182d08580701c8503003d80e02e5049274000c443e02d0a1040c0403400400107550031047d040440e9009481c034107502c80b9180d1008007551041e29420080c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 830032365 1250 830031115 830031119
    0x2060c09041e0c0e090c04170c03070f030b070815040e012913090b01030206180307030f0614060310020a03021603050c0723040c0e031c020106170309100504030605010f 74
    0x1402605070101c044c4122a000218a481040342c1c01c5070040d4000c14042c2000c518900250400820011003100703802822580943c3d500c03402000620014002141c0c0c54100c0d5003c543c805004161050103549409400c1c1d0a240c815024080207080b07558a246056417a10143d1107415041824402c4280207000000841070034142407107c000e20030405091420324260b203a0001c03501d00c416140c1544c0d8100d400541e00d481d20340a80c4102d1854882ca1941070107204030020401c1072103d80c0300d028501ca0070007400360b500d0203409504500c80403241c3c0c0d034040e00150750105103644254010503072005503080050500c040d668141040501c80381c070031004500c00080c4414048400c00241c001406601c5410700768803001030040404030205891640200e071680079003c0c40324014004109401c0d0003504803040041120700d11070003643c0000841e00554605040820120729900c0c00400301100d940045240c04509000e202c42446915409010072100b44404000191540549802400800d207105031040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 830033615 1250 830032365 830032367
    0xb0f072105070f020a080d0903110102030108031b0f0604080c10060f030204270611090607030201090b0603070803031f0f06030207031418040b030c041812020d02060c09041e0c 77
    0x402c2c111200d00640d401030041740b0004140c0001c50b20081e00c0e002d00406c6064840c50240c070102081c40182c0c1007540003100200d4540c000001a10549035040c0e04007400c0b051103800b4545800c0e0b503421501d00c5401c1000018003081d40749005141030008041200c009511403151402240d040b07401c81c0c1758100d2132407002c00a5241c40c0c01004071610420742c1c0e010312100c1540001d01c0070000b000c3c0041503c0d8840c0013056441c01444192914901d020380620b58800b03662800078028a0000c0c0c08403840360702000801c40038180000c05600761000800154555150703502000d0301314041c2c1d0310741c45080c15561000b06604020482803402805662400350b100c1c076062130060030f207040c0c120003045e603480f00340702076500020031000f10b5203021419240020b02030002001711f810030790591411034109080c4580e45480005000760074400740d01800a4034800c0c2803110f01283c50f02152031001c00103034810b0020500054140f001085041c400900001d444940e15075008850102d154090002d507990b102d00180f00e0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 830034865 1250 830033615 830033627
    0x91b0e19022a0a0611030417090a120c0312020a170906071407050306190e010e030901050d1509020a02010e1c0c03021501090e190b0f07210507 63
    0x9060040010350821903003800c1002070180502d0a0340c2004002000c4400c084000e01c40c40c0344030b58010034140031040340006403144662050318101d480e2040c0c40c1c44954118144070586060184c01004000203524141c2c40b0262110707500402c0c1d824524107000080051528a22003081100540242a03800c1c16820301c2c424000c40d40c0b600c1403238200100090082030780ca50040f512200e82c41400308107a0b8410700c4100d807401d54960004e5806104000034042302e40f40d03511090746a18092001071101c000c503c900b49083e54a2000802c480307030300901c2400c8266001d00013034080d90341040d100142149055200129104903640a0340300c0c5603000171501c0d80281d081c0600302d0069291002080170500c00d1104c1818180620011010000189401000c252092021240030fa0540f00701355050358480c0381c1d0744020a181005018244a0500e11003d007480d000e5010a10540182407842907030358500b5180b401c00c60007480e42e810401c1c0c0c0c030340713152034107083e00402c0f480031600c000006000d2030101405000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 830035971 1106 830034865 830034901
    0xc0810021608160c090501150e060d0905032b1a0a092705030c160f0b0a1e020c01030510050303030a1d030403080d110c060a091b0e 58
    0xc00030107504928142c0e618400c1c1a50001c98502301a9246507005945d103030410014460a4042e92030382c1e001c040401d00ad041a20710b8444070155418015104a8454480740d1281041c440d55212520844501d50f05105208642e5080807001946444661042e002401c2c1c4500b00340750b903155085991104403000600d8081164904d150550303c3e900a01c0d81c201841c81202008407225100e0035042d000c40f170381c01d0400b06001d030030300d04071f000d055125030810004d00030090307069010304040544900b0a0221a07000e06522000e07000018180c40001d00300c21b907000c0d1003072001c1c80159004000c984d00000c6456002a0815199001c0250b034080c10b100c0c08a2800046400401c0c4000341c07004090a40704100100035440c12034094009078050a405a40c0766840180020f100c0807155002c000d41030b00404041400040c05903400a0010417900040300440d101340170710038084651145e1002c = true := by decide +kernel

theorem cover : BRFrame.Cov 829856115 830035971 := by
  have h0 := BRFrame.cov_init 829856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 829856115 ≤ n) (h2 : n < 830035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
