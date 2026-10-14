-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2240
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:05:47.491456+00:00
-- url     : https://prove2.me/submissions/a9622ad3-2c85-4323-a1a5-0131bc131948

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 402697841 ≤ n < 402877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 402699091 1250 402697841 402697847
    0xc01050a1202030a1409010f0f020918070e0409200f01051e070c0e0a06080d020a02130e01051315020304030c14010f1104030302151b180d1103011b 65
    0x74114540e030030035000008036400b21314a503c00001c00c081022100c0c1a8104680068080c02c400c280340c208544c2840700c00d00359811a44200c440200005040c0320202c801407443c074018000042c01d2a0a11201131541a040e4031640590031081d40300b01c5011740060340c1c42106002034034689480754000e48045d20740d412140d820100302d841c118050718000c600c62859505528591082176402840c214405000240c1c41e4040c00d420750003144151802e02c039142d114031505544043c2500b5440069015a900e50007506055542c0e00400200e200f021884a041c009440e00b03441069940e8036802040c08131001c140f220149414511128030b40055242d42801c5c0c500038802116900094118040c0005100c0c443d4825442042c8018031040e040c000f00e002c002d84d0081e81c4d0004e110680140c0aa0103640e0705040e111035485214144a01d8485072940c1055030400558104103200e0100c020140090303852a81c0305001e04103458410912074101e080c03c5000c0c98251620019504000c0c01241015407405030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 402700341 1250 402699091 402699107
    0xa170c041a0c030d0f06081b03100f020919211104020d02071a010503070e1006050304080403080f0403110d051c031d0303010e1f0302060d06051806030c01050a 70
    0x3007428201d90b290241e10320040d0462080b4000c00b6842880e005001d4611982d540210f402c85000c0c4056410b20718451610f8000140000d41607030703058200360b164500e4070740366074403200300c44244500043c01c050440c3c1c0451b01082484800490301c516400013040f45c0f07040c840702d2409090003226000c188001c0c55035441c141000c042d00c03091056802048030301c07860741954151800c180d081034124603130944c032080c0c40d040b002d002e004447c000c0c002c4142c040703110350082001500403c010b00c0445101460000202d0b6281c0020700102d1340707580e04000003c0031406d04405802020700d40c00c81e15a0300c519529000b540c05d40c001c45003038040c8020654001c089100483c503071200b41c40d4003a04a4001d41c90381d1088004009107100c0d514912240001d41d21018000000307503058507450305200816481d43c4984941087c0850b0010307040c0ca4403042c0502c01814100302602d401c004044001c141583c403800002d403159503410218401c440c01600300000b501c1d040042c03d915003c00e080c982c1c40c1c9500c980f0000d107045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 402701591 1250 402700341 402700379
    0xc1110020a1b12030b06090307153f0905030901200304030b0a0e0616050a140f090a0b090a0e0c0d0c020a0b2d070201060b0a170c04 58
    0x40d038045899001c60380520392681d0040440180380815071407929120720004055030319280028030303107280c540c650709041c0304680d420000280101241c0e841d080191100071440e0b045201005100d61864208480c0b582e01081c480e511b503000b0813400184100502802445850310211403420070300d8020208074040102c0e000b030002842c21010016a0ba020422540d529207039442c2c0500c4001000424010350300c0c071082c0220111030040c03100300904080d6581d650825034650109004141d401054030b070003000109030003041820010503500c010720000c00e168000d0700020705240c10004400d011883d04100f0710000c0c0c142c070020075007402034500108144810718041d219503000304d8000308441050b13080a450511540f80000d000d00000214000d40711080848102c5018603410085455401241486011071b00c40711110902402081000042c0c0c01002c0c240005555940b4004100154410010441300c0c002c1d8460100341710180c4078190424000800c5101c01c00028002800315010852180c0644 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 402702841 1250 402701591 402701623
    0x4080901020f120d060f0807210203030d0c1e020d0f020708010c020705090c090105030402060a05070f0507060908030f04030f0302240114010c020d3302030405010c11 73
    0x18829510050380703802c0740c91a60450520403103200c1c041220b1040f000b4030020b05003c0040c811140d4650310101e21086600070000f140d00244001d1149000c0501c10013184404d00740c2019440f100c41e00840d00303581c00349882022a40d01e40f0010601103800151544144564400440c031081072504000c1d201c2042440160400c441d030107a414040f48200134042c0a813080c28003c110091400ca006552012184146405061840c0c002a0802030420680320002410b0f140c0034955030315542001200d074489502802800702c00e0040b200800c2023189400200c81c0f00c0c0f00103000c00c50602001a00240e41035018103600e900c10003d02d40b01001107002d1b102113991000601034410158a8140d0a00c84400c80c4042c41c0406010566010300321424454103e50042c0c480d003541980130401100c0041c44000069000000082c2000000d0b05024040204181501e44581c00300202060441da030307118642e00e006a25000301c24407040c04403c1c4a01141610f00d03081c50703594507084903034080c4c48080700c0b07250070f141b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 402704091 1250 402702841 402702847
    0xf06091e12031d0709150f080606091312020a050f03042129010f140306061306120302160503010603030f0c0501110a02011a041109040e030f03071e02060f0408 70
    0x892043d6030380f18016103201d1015269441d84034640e07140141095541810404400d10001507000129215002510341c0d2201a013110358500040c4640e41c0c00103450088103988900804001c00d402d9028001100202d90180003010700341e04140d440c2610940d0a4495078000300401c20608414900100020310740b449050104801810025100703e60f000d00750340c1081e0210b602c0c88800048001c0036060783d041c10b41200c44130380c0b80c0720301101030010078031015055030140c4007080e05490304580d100890440f0500c0807921a84940100f501c10450520032005607008080c80e6090402c80040200902415402009001c0c65500c1c000c0c0013021040121090060002824050202c2034002c83c03a40b44220400a07034814502100a000b0481d410307116082080c41c0301311035081c1ca801c0c001c000c3d40d00c80c0c452040d400c210060003000700401845c0800c051500c001c0020303002c2d071000c990146202da038941e284c071113a01201c0b58204000c02c00c20f070300c60b008540000007003004940360050140d8202d500f08403c2070b2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 402705341 1250 402704091 402704111
    0x1f06030e0c041503051203100909020a170a03140903150702010228110c130c0c0218160203030105060d0b0f09012409031509020d0f06091e1203 63
    0x10500c5034003119150028203000703a00e10001241c803c014100c03071051007200c0d07240300c024403444031500050320001c03c501c085010402c080c100355044000300701d00040c845000203030307500c0c00c480c20255484403401154000c580040c05040c1c001400c21501d084129103a85040d110304000303910340d803009210585030002c6102080e403a0b8403d50541c0d10398a13006282520b40300d582d84220264030b50081c1c0c030800243c1e814446016086000c6011281244040d0212118403d01080e402c082d2160603502070400081d8103950b0003503500c0b00700c080044402d2020301421070902546009a05130305416200640d4400c02c010021626004200c91000f140f210300018004000c10025000d41c0140721101d0340202c1d11400401c1306090780451840701844070304c1d441e45c130b614910030039140003400e8440548411006210101079184903000041040d100500c0b1480c0320804e55508040c2118900707041e0780c002c0e5191511802c0054640d100c1c0c01076050445550201138030b0303070746107609113003005010400c042d1141d403009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 402706591 1250 402705341 402705343
    0xc09080a0807030c05010606020309100f0c0803090a051005040302240112021f0f030e010c09050909030f0705031309020403020f13061d04210207060e012006040303051f06030e 77
    0x4c141c09138800020322180780d0702c076802542c80c7c00102c14103115494000360351070700da8052000e00b400c245c01a11090000700050703d9181440d0401001400e0300e000752413030140000c0003404003405020032510002160704160074024581020340e03d00006042d000800081c40b241e412080904582e0130220030010140c86201003400517841008101d00c00e40c10f4040c80b03400720703000034071111105051380d000c010090140c1c21442c20b86002445000c0890f08850f000d004a00340000700603400440441107903d00a504122080541c3c448401500d082d000410326150701001418218000c0859480550901d42960000340c0101042d90046204030840c072889044071a242c2c10050060021102955160719a61030140080030300f1135084902c5000d25a0702a201500d412841288000c998000d1402c1414603405481c080d0040c68128140044064540302104041c46095102d940d03070b82c090040b43c2814640034055070720241c01c21240c10240c505d12420380c400007000c541118503910780480c02401e000029 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 402707841 1250 402706591 402706607
    0x4181725110612070e0621090a02031501060305010801360b0106050903010e010e03030609150a030c030605070e01230409020310180509100506060d1d010c09080a080703 74
    0x269000b000c00b1030200b90100842040d28494a40d03078031107800e800e01203400c01c9224403d03d421154001d00926004040500101180e54410104c108a070020003160700001e19014075501e150b20b0021112005101b216413500070b2034010110704000340543e48951007581507040840011002004018403509020022010501c1e11607030000d0301c4980550315400010308951001031710502075800c009480e042e20a051240d041c0d0110014099030a58440b402000710000010b01107140300c04c03e204a0700c120369144009000112320880308404c1a42c07640c50700c00260f800051213041405100404020361381d8000440d00a503000e59404940000f034004079580440c0266006040f54910110030000d481a1138006902a1000c00d80194411364640c01007000b82c46084036011469001002c000551708100d80145030484001070280e810142e04407101412a00451500d0b607091543d01da0b00004000207100d1985052410f1030060442420a1545d640e5110300703900040400340f000400000f810700c10018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 402709091 1250 402707841 402707873
    0x50a031412010807091401080303010509180f060a0605041a060d0e58050417071a0a0203070852020319080904181725 52
    0x2800e0610b5071a20b0040d50340c3e0095001d0500f0162804502e25417580e104036066048404000085155030f0070303c2d042c0290000050310318003401e0800004aa6403000034400d51004040003401040c142c5003a108a905842c8180e1000b03018501d060401c03900b422030351910317049699081d144683c0d85c240c00c05e00203008208103001c00445014080d00300c0354400c014405201c8284040000c507404010100103680410344801c10f8411280691241c0d00754100c04119148801e080d0b400c245080c60350f00d4040d044100e09050010f0402d800400080c451140c0e030000c54a00450042c050f607007854698180a0b580b4820311902034051134011800202d03034030110003ca0f0f040350a00c03150301115a2000240349a000201325003900c101e08404035007030841060801c9140454009008002d030401c1600c24003e141940300064800b02420410809141c4940c098400316106881e15a8030f00c4869050181d25042080070340d840004081007440c020000d4000508810900030403000c00c2c6a0551504070010303c40304003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 402710341 1250 402709091 402709117
    0x309050316030506010f0608070f05160b060a0b040501020307110d120807090b0a0e0d0312020f07020418230c09040308090c0d0b0c0703030b0a081c020604050a0314 72
    0x19000030040c80181c540c1080760302ca40c04561a90f40ca805046002e803009001d010300182c0c3c440001070400344642180a20b035031040c00c005113000100500358003220768564041c0c6074503640b0014003c03113041001d4000f00500ea100741e00ca08050401c40001d480e1300c00c5950161004e0030f40f2003600c0f05940d402031110b040340d600c40c64898074002d005e90090810907084031311310089029181700051060840c022510b2114030740d80c40d8004441c412040013416011100c05034200990201d070f807004030b0010b10084c010400001d88841e01c900740b5104001c140d4454200e0ba1071016182480d000001c2e462081c0610903034011003820070300092030900f4034030701040312220543c0301d204501030209160b0065602da000700e0700d01c0d00350303801e91103030201b4420400c071008030051080c42143c0004800000d50f5010300402c5100303280c080303108204035000822031469034001d40b015030000c2c02e04111034000c902c030f0558034031200e00140643d07243c1500c640d511100122409010b100420100005003040d2030100c40079a41049 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 402711591 1250 402710341 402710353
    0x3010c02061806091009050c0405090c2704020607020112291c06021305130b040510120204050c070206030403020105072c150f0409051015080a0903090503 68
    0x450001e54400c03064401906079400300c0c180202070900410b00500c44c0c0c1c1164001c018185a583e408001807a052000362130500400b681d0003c55600c0e401081d0080b846100104110b0068100304900e000a03032000d14515040e4002d0013045201581e40745500a4048800035102c40c0f030703800180c9a070800529a1440c1d03030700d0550380202d0302c00c9000580600c1e40c01030300b802050f15007030300500904407050340007a000e1f0344d001031102c000522580c000b400c80844940c13011f81e040350384e8030104044c004000700d030303d1001e0348900440b84d8504061041d164450400740c1c0c1d40da0721925140c100c042a050048010340101e4075040010f86042c420000c946985901402159592405060090090000b40c0d9402e001482c90000a11140320401e030311001340891032501541c50041b4010807510200700701c0416401001403145403411039482c0054030050507042c502150360b20344607644142c45449074101c0e01680780d49492101c0c19540c002c080c6030f403014401d07000043c0c255443c202601c0c0b104559004030b0f4075200791 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 402712841 1250 402711591 402711611
    0x102090306130303090803010b0d0c090803090d140f011a01020304060c0f0302010908030a020c0d0e062203020607080a0e03011509180b07020106140d0512160c06030501170c0307090207050c0301 85
    0x418001d0030510741d00360040288242f0f41d50119841540b6200e5801d09034428414101c3ca46058408420014031904055140c84501c92801d42065011328040300a6551034100d00702c5100f00f562002d206070300c240302461410f424520040c1180c8040f41c40500950141c40031101090f00035803003050f20580000035561030340743c42e0412030042c1d4010742444d0990301406c03804004880c0240089075030803034014980e0717080c6800c5405072000038400340040c19404d03030703c4100003000d030303c90000620b00d590140301ca4075a01e40c0d1149024120580d4100b81e10700030780c54801440c0c420f0140090703d6055a140d0700307020846210300034461000c4007002c1e1000c0c005203104d02c24810074030340544c000c17000c480f0030781081840c9032415010882503643c03411014000360000000c500281044100400255816225083c94001030340c0702c100c8210301a802400100c0d50b110011303c106e407031a020920148400c18001e00601d600040401d86070702c0700744140c08505402190040402006000c009040d42c80603000b04140300728 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 402714091 1250 402712841 402712859
    0x50c0114010f03050d03111b0118030908060c130e0705130902030105010f090f030308071e0c0b0604020a0212180303070f1403030f06010f05070b1f0602010209030613030309080301 79
    0x715100c1183d0345e05c10300b0250200e0900034000c540c507070b44090b43c645080002e0750303201d810b03141020b000100407550f03103041c22281e41d8021880b15582ca400b0b6030b610744a007402c20f1441d42c07034900040e00301c440100f03017449044100458911000c040c2e40c4551040170713480d1221201034500e0b02401900e100d659030400340104070006d05a01031412580240da40c81c003800000030040d07500ea1900c1c0140344080c0c200c464180086030043c1116030308a402c80c80c0c101143c80c0d41000c0785251000b03480b0f00c02c00103003c4228240c01c2c40101050700350007140844003185000fa20a1002c0e40d0742000d0400040d0f00300c800b25600401405000c142c14500700d0240c180d07903644400c0d19040980b00c52001c4116512400c2c031050711210103000007903d1203652030b0856119035446203001509c403401e5070b003a640704001c0100f100000160f07509082c5401282203030a641c0b00007903201025190101242c2245085a10500038041203542c0000c403250040c038044e400ca10100f0b498201180501214140500000c00000c000149000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 402715341 1250 402714091 402714119
    0x7050a0c02100c0c060f020304150e060c0a200f22090309080609011b1b0f060504060e0609070b03040f12050c0c040b010903030809070e07020a06060f0303050703050c011401 76
    0x41314030014101c2c40d84804065581480c440c145800503441840188116103072880007540548190804242c241e12010000d603082d80480c030340c50903a8003e4100603041000c040f640c1082e200c02c070001200c0fa54008030101e0303011300000340702610030114090003007000540120008106034403000705000449041c1006080d44407584100320241c030943c00003403000704062140c082124500740c000c0042e400740d0181120f1029501d40350301c40440452404070000b0380088000e041c0315200e00c80200e4036240c2802d15200302c407002c03c84213106811400802c200904045000c03802d4500f030300c000c40d0700c0742c8590074072440b0b4030004c4500500c074003001580c000b420394008000d40038200607a403c0754003120600f130901c41600d42030b001250119270a41c84c280000390141d80324039406403440085803031056440c25002c802c00703005e0b1080009600040d07240381c01e0100700c0c05602c002e000c0314103501c44554070311faa0080591080400c0034040010100d0790300c0b0100c03c02e4116010035141800c078001156111303185207503440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 402716591 1250 402715341 402715343
    0x80f03070218130b10090230040206030613270c08010c0e040b01020a1b1a040806040b07180b0a0807021519091e060c110607050a0c02100c 61
    0x8456182c001041044842c110300ca90540c081000b41c20140d0381d980c3c22010380c041c10303260312030020980100b2244480d00c06807640040d81003102083c42c6004071341038180a188407183c0a0981804100000b40e1103e004807504501d00f1ba907881c1c0d00d0751141807410010440c03171915559100d100503038818400c0072041c140c40001d00404294001c190344050050803a4540f00d150000b0484500d60b020117850181d1040c2c02c1c0000600544400030000e90342c90303e015a81ea003440d4400d20318290103011420030a40382e000491070074401d880c907040c140306c01e5907601c042c000e000400742030303640c80003a900520499000c81020341242c8410302103502d4606c50b10b6190032000206001480641c0000d500e54800100c43c1d145540c0742c114800c01c0d0326640c1d0361118074010724000c00c4809407542c0070080014180c22440007040e9441199181d411141d18055094500090f1080c08100c101d074000d40c030008010400c25040b02203810120b42c2c0385031101c810b948205540c2800383d0320003150384e202080c0c1ca4001c03800d01a52 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 402717841 1250 402716591 402716599
    0x111c1505070e0105070c050f0112020a17060a060903060903050903030c28031b020a0b0408010213080c01051219050c07020301060906080c0d0c050616050c0a1815080f030702 76
    0x102c41000119a507015a01c0042c2c42508091410456400d001c8080d040c03100c4117140c01140d0142e082d103442d060703a000f12100c0000800c04c61814981060b2052141c2e040710007110702080c190b01d0000c00400c000b566000181c90b15940301c03107084c1018010f200b240c4010b44041c00344c070b40380c0c00008c40310f5848a243d01d01e41c0980074980c1600c80003401c982e40c0c107581017139450703110003071201204a0940c086206400b0b04a81204262402040010705200603000900710b0303000141e07403103203140e05a14184d00a64040d10860f40050010304150b038102d815145504030401c5074006c16074a00b0350188614200c1c8a402400741c4c40d14003071200503401da0000701036043c020760003402100c5d540d101907411905144540061130b0006003204005180425121580b81d008440810b4402c1d20ba01c0002c69650124814405500c04c51000b8802c10109000448008000312180c0b0f40369442d105004448121480b4400d8520381d940412081250500300403101500306441190740c0120440d890b0307070f41ca50042c0030907880b03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 402719091 1250 402717841 402717857
    0xe0c04120b0f1f2d09090201020c03030a0e060304030311030403082401140a0e030601060503100f0b0d02070201021f050109200d0504020a030b0906040605070804111c150507 76
    0x91a400c1500c2c4044240c01e0081c2240c440b4070f0041654810403e40300e40c11501c0481503d01319400042d000034602500b80e44000003050130481c4006441c140c00074030a2030103074100344440c810460b008500c0030310202064415681d03d545520701203008003008443c0d4280b9000200510050542c0101c41504c5580300400414690001c42249003002001703d200c00c1c00915110914504034103514044c10070745290b4209048001d885030002401c08009802013000500013004110b00e080322012031000a1112107600684207062a00360381c0035114250803220410740020f00442164401c02580b000050661141849641c0074115007020700740a210b4000c03468140000c001e89000081b010603070b046c0d403041c035081c41e044440d0b0154026003c018002c3c2d07030143c0071010003c003003100c0450061203000340b40003070591403800c2e1511008031400a89140d0802c030980c42000700040c00c55101903580d1608680e1803202c00445911408849480c0c80010a0060358488c200015241e98010a014540c65150201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 402720341 1250 402719091 402719101
    0x80a09051c02090c0d0609050103120e09090c09072105070e150d09050102190503070305071d0415091d070801090b0a020d060e040f020918070e0c04120b0f 68
    0x1410741c941c040180d0712154150100380114a0840105503080803290003180250b40d40b51650210f6200340e1050300c4102011043c035642690041c42c961803072804a90390803460a140d07002555580c44080c0b058010110040450102d03802108005040d840300c07450303000c404d94400d0303081000c1c14081d1040d0300420110310000019141c40b1a0ba00094104480c3c5103080c1503400300144041d1012102c10b840b655400c10110a040c1041410300c40d036144d042e1078490fa20708002d5001021500d005000d402008080c100101094040c544a880001c5040303501040751a41c10002d085403e0041e40a0004c451815030607200d0f0ba4446001d4150f01035001c800c4c2c0302026503031280a420b940050000030032414283d0f0000340d80801030f902526032003007801c40c001040e03070300c4600e00c10b1844400d44081e075400d0440b80020045140118006078407803550a4000c08000380518600c1d0b403602b80b801030842d803c144200040c0e22010348026100100180f580d104110640c60803c4017108506540c190110800400014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 402721591 1250 402720341 402720379
    0x30e0625030b0a0504060f0f090b0a03060c200f1c020703030c030315030b1f0509070c030e060d0518012c0c0a081605010309020a03120c080a0905 64
    0x4403150158000c410008429421801804550501d59200c1e654940205098035140b00c0c0c1d801504900c104110402d00b000480f5180035425482030308201d0401925064580342d001020048a031301c01c078041801548008140c1e0720303c0348400c9580304181215040805010001000c0c03129241100984540e40e40d851860440895001c0d10280980d00016082000a10a03182c0794900c40c0249400076003d014004980e51260b055442a238401c0408800d00614412615583d400b50340000300310001b0b54035240100b004010020414801e00120030041e0b0240742c010f0400461100001706480d41c0c402040c55014014002a140d00c038208128610903101000e05100320458103000c20b80a00c212002083d000342c0103182c040d01c015541c01000f407410040c8d241e049150000e0105100944086e114000190101d180c80d580924101418000b416015132a030120030802d503078000f6504242c0b0a048002500c4401a2040c002d04000c0c001032401c2030a07a00039120300582d0001c90344450f0181400b0700032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 402722841 1250 402721591 402721621
    0xa06051813030c0309150c0c140901090f0e0a060504060c020d02100f060b0d0e0d052d19020d0201060b040b121906060206010503012301060309150c030e06 68
    0x1111032024440c20100803d000d07420340d00c1e142d4845d26081c0401ca8842c04248803280d0742c003000c4c0f0701003154840d00c02c2c10003442c2072481e00500902885001d07030366683c100043c0c40301030600c6641002d660700d5980c4640c1d078400d80c00010744445404101c440e100028508503000f48022102680c0326031a00204100e018400300f94518032a10b9a4000c1081804656902c001800c2c60540450f0f0b1961782c01e8002044840d24014103200d66102c240000c4114050b540c060810300c0e148100310800c00700304078a0040d04c0c00d001e0080b4072030000c0b0302d80040f4030301c0c030806448c072512900c000304010702003d5440030402513001404043c0080158002d10103141d03a16020041c9020301c1c01005803a01c0107110654a01244450381a880346560809030251060304040104840d80e5400c9240140c11039401407295007024010b840448017041b041480200c6030304140d203072a10040c0500010561200c041005001c0c00c21030b46892010f041d08100000340c03030348501074010009805055042c0c0907201c00a000d680c000303002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 402724091 1250 402722841 402722851
    0x1110d2301140f040608060a0e03030606041e0308031311030c090c03040203160b04061b2f06040e0a140c030612030c0105040b06090a09050c0105090402120a060518 72
    0x9090342503401c0440d5a0901c0c41040c8140d41c00c0384402c2d1400c1c00700c3c0d5440c02614020b190302c4029290904107011038105807150820b003250141c2c803c0080c0152911140221422500c20500481107a007203ea260600b07040c1d10751004d0001d041c0802448240d011441c00008268481e07040101c001280300c09244c2c0328031800781c0c016440284e00d00003030101180f0724020340d4042d00c01400d444144121641000c004461034000e8640c0810204042c0031031500001d00440b03092134160380d00c2c1225207542c0d581c03241c2c4141100c01c40802c0d9420303110038500341c1111241040414002d01007500c0384e495104003030004c0c81c102c03010345900d820b040307400e15051509d1040364016694071070890315558075041404001c1c3c01003092001da84c4403c01000704c0681081c4210b0f40035900c20345604285007009001c0002540307000e00204d4069180c0480d030000604001000d200e600d6007800c01e03c0d1144072150004000307010b08020502c4181e254070404c10301c03400d694840742c156807003101e540f85043c4006040c40350701700301115 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 402725341 1250 402724091 402724151
    0x30307021c080c070203030d0c03020a0f08040c1e090603030f082211010c061b0e030d021f020c100b030d14090d0503070c080607090b07030206070c1401110d 69
    0x40440d10f01548440241511400502100d180003c882c0c0c0140c211000f80c0308002c0040e6010484041c0540c1c043e440c1c061115191030b001080d800c00d0303100c10750070080c0c9209504c00c90300c4410301c06004104480c8030400604408a0802005551b4100a80204010707010640020801e20009240f48544440c400e00500040c841000751500c955941a51f01d12018000e4140800105000300264480c01050f800c00c010718091000c079a4039041c0076280c000e980502c148a6000010384d080030640c005400f61420340103040071201c240d11260341100903c81c01d001185607001d1003482c40b00a10160f006200c0c107420a82c2101c0b5950344c449000c85a85000440d05403607100c3c2007150880d18982900001d00c502d00503c1541d1030b0441d02d513103031190041a90300100c0b868001904019071b00c2d411003c800e0050400503030b0301d0314101c5550340c025141c0c000206620284080001d02d4000e002c4585603c0f065507003244000c04c00030400d59012515a0050744400341c2080c02c003000720040c01303400c94905c401201044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 402726591 1250 402725341 402725357
    0x2011d0d080106110307020d050c04151805010605030a02030a0b060c210f070f0203011121092407020c0a0f0f050307080703080307051303060902190e0c160c08030307021c 75
    0x47e0820060190000007658036109404c4170695a60742e5101d9003e00348945004056130354540900f2030b004034a20701b41260014900001007004030f8001040701e50040d0500c0005a50b60740c4c41c00440700074101946a00d80000d07011850740006180084c81e58210702c01c0042081d2032003c84c1d10042203521130030000c60313140401408440000f41c0081c07081c1022a1008002180d0358032840d04109450308440d205a05820400840180000716800ca254100701c1400241101d44c00040045142c0503420034448010020f510008204910910004004920081041c03452035903a240115843c03c0502400c1002a0543c2c400a124030f030010b920300c1201c2a1202038048903180d512604e0b01500300901c0c00c000e000b4100401c0704030900822030a00550b1040000080702001c90041c01201d511802c2050000c6500010a010001c0b000000c589e1190360707091400c2c0c0e5090894002004207920120040900307000c2c0c100400c5c0298040040e5101d00c9060b401c0381c0c3c2c1410a01d0f9081c055010702e0043c440420105 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 402727841 1250 402726591 402726593
    0x1c050f04030f0c060608060403020102090907090e010b0702040f14181507080c0d02070c0e01051c17250b160509010f1727010c08130302011d0d080106110307 69
    0x203c1442e14528050b490000b60555115042c4d030600d242240e0480c0140d50010b4013005070b142940503580c00c14114039026101c10f0030b00300401d8000c50180913862007030101040c8a011036981d0780224402d2009824244000314145080b4003085d2004e5442c10303030001e03411013154081d0b03c0020744000100c40f901e580041e140c49854007503500d0103020300410745540b020002040407603140d00040c80300034411400000c13814a084a07446103d20103820603071044602d030f16825050281001010314464100250001e40721103090014614461a00b0300d4403004c40309508001c15000180c00800094061820500d60b5621444c0385a50710608120704008030318144090301c1d255200c2c4020f00508421410580030328000c0074000c06600780c0c100c6034004401e00d11300b01042040c40441c10610ba69403028024440e007080c00c400a4605d4034000c150340200c10b2424200414540300350408682c4504614640d0321081d024030480e521104485142004154500d00000300315110fa51080348089501003e14100045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 402729091 1250 402727841 402727847
    0xb04020609010e030316030201140c0a03150f0b07140d1d03070504050c0307030f06060903152018030c0a03020d050a1205090406050d0b01030f06111c050f04030f 71
    0x480755046040000c00e100840658401700001c160020801c415044d00344032529009081d10345814030100022101d406120740c420340101914113807105800e001c18402d1040158034440b0707201e50320000301b0030400f8070300040b0701c04943e00030400e0354006d1207400411040300480540c0c401e2a000308000041d4107240b40751446038202d0452890010080a44140a55500014060b00d0080d28840c0e10140004148480030380c151203102c41101da541d80900c0a10703d403036800740c0311420703c4c880601410140d03c3c0000004041c0d40c490405880d10b0b007800000389a0a80d403401b0540c22402c0d004d000400010759170000b03440c0000e50307002845401048132240c81c0c216401c1c000402003d140440e124820301d05c8040010b40000144515003255a6490352102040c80c100000e4900d1035101381d00415030740c40707850081200c80a1407810340c0e4004070305050020311850a44010030300d05200d808040004101d10810301958003505c02240e41803c0288400c2d00d80109490104009550003001716500b250302c1307940540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 402730341 1250 402729091 402729097
    0x3040e060910091415090c03070311040b0a09060210020c030315040b030d08090705041a010302070212011104030606050f10142203143d14010e01120b040206 69
    0x5003001042d49580d4901e0000180c40040700c500c101d800e88001000000782d4551518155088200c0d00b428180c01d206007589054070005d001c003410075864103101c00c40e011134601120020320000c0303150313540c4842c54503006110940c00c1c059103005000e80c00c0d0160b2140c00718000e817446050403030042c40c510f8840c40e4506801204480480d0342180d00c03001d205207180d5080c803501d03145036942e480e2901c0916101d0700b0309080281c150030052041e450f1005007100000c02100e020140407003030800690b18000c0d400000c0a0051010003070300c1d29803c0480e10288000303c07101170000c80c2d1046070700303011036074031001081402044162025002401c074040e80b40c02510800c0044805002d0f80310032850301006100c1d400790344000140d44820305419200c1001004032440e014504403c608010f0001c110146840200b640c801c80314550302040c0c154800401c081030046001791a03845004104010308483e0250710008409200790700040110000000e04d002240310050341807907000f010440b01e55103c0e0300300308050b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 402731591 1250 402730341 402730351
    0x4180506041e06090e0a0b13032c100c0b0f06210f0c030601060918150e0406140c09060304060204350705060712110313031403040e0609 60
    0x941c5401c0c00c85664000b040160310038003035150002c60941d040022401c1601c010600f4085030307501011500307010461901e903060700290502c1ca10f040d40801420102e54640342a2500812624008046200030803414201c4052510558000405072103481d426503007080340000c05016102c22400284540708907803c05940312200400114150603100503d22284010a90003035030741c2d2200c00c0c41251194200b048104220048000380420760501100500350390b1644134220044186d10306da4075480c8096086550321010901e0150021552040b10b500e14080c26079041d03500d0307031070410342c40c429903001040144036444c4400b03030b1031400442030f0510009a000130020b17950f5035070901010038030100303c0448402d106502c108891000150001c182c8182c0706800c00c10031a0f070b00a02c0b00b0000354942400f80c0f0141900301000c190f0045080c50700740d48400341d01ea00c5040c24080002c000c010b5100c9001910309481c059804607032001c05034424680d6078899801006140604900042e1141c0307001450a9448 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 402732841 1250 402731591 402731599
    0x90d0906050d09170919031707030e18160903030e150c0105100303120203040c060e030c150d0e0c090a110c0109110909010b010e0103020c010e150a050c04180506 71
    0x300d030103455820f410008003582e000241c000245245d103e2515100c09514195403640c25040c8516661b200446101e1211102c8905400410004140750042e69517512116014241700008a8401034070450a4003c03034903140c50601c91781120088030f01c1003d10009481c0c1c142c40301115a0509010840300d090f141a030f0544a4004001c1c0160241c828020715015402c0780002400305030561030064402540d004002030f8a80c07040c01004082207042440318201c81e0181005500d4004000c0800d050107122400d10350094001b540d0b030500701c0c851000400c1c003118084800c20060f01800c01e000d80702e000030100c03180e10400c07100114818008035403100d004412a640d10924203030030503220a095402e040d00030743c0c005805601c213183c64201070340790517840080a4001c010b09416400041d0440c490100801d0415034080340c40d1080e440258428141031410708110340c128044078503145001c03242120003c001d40d081c10081001607040d5029141030f152104a40400c66605c04051b0b0004c0000030141644 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 402734091 1250 402732841 402732851
    0x5040f062f030114010507080316090503030703020c1201022b020c100c09050a0503031209030c0703050f100b0102060a27060c0809122a030a020604030305090d0906050d 74
    0x154618a102407040c1050402641c2d160743c54400400080d01c40d105810b030510900700301c040e0000e000ca004603a40094642c02140300340800c601c040359100c2c0560069900761000240b00d500780b5030005202c881c60002282e4840304000c844500d01d00f40e004c3c42d0002a51250350031884e000c80a448a0080c200000c10403006081c942000341d102d14104a80c600d43d04a19951903075007501d0381c0d02c0340c1007a024110580d60030303036030070b00d0304001c03c1d40c0380f1481d4401c8560241180c00300c1d6240d0b0051081b01e000210010884060a8a0f4107025450303982003415120684103200d200d81050f0a5805a182c0d0080160050b02d5a592103c44440140200801008110f10b01040006204800d404410001805a0300001e903031002c003a409052050b0181040d040c17644030340e604c103108180e05030403148032620218000860441081004c0103c0ca000c50804e4168080402c001218550020f003940c0300740e000c4c0ea014071090301d078900419203407030410b05240002408600c1c1402281d00030801000d0440300c480d40021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 402735341 1250 402734091 402734141
    0xb09010305151c1106031501110f010c090504050a0902010905090907050409031709060c09100c02030a0f0c15140a02150106050c1216060b03240105090a05040f06 71
    0x44008115101000d0f0442c1034071601003440094481d48a8020050b180f082c95824848910080400c1c0c12880904003c4408104203501400b80107800c440d004980091180c6890003c0203051106940619030255240900007200440c9074022041041c0d010b840d404075a48c1048203100003031030f00804d0028a4421004001102e4540384030750383c17640c0e00a5465800d04543e010703804a1b15240500749001c2544400e090005001c5d10808a841800741102d07a84401c5407101d07029900c42d01c04410203540340c05000404014004481a842d808a10a07540d0700300c019110380345c01e8001c1c2a80a4401c1c0050410354080204a035640c000740025001c07401264000e1074003910002038a0030136044540010b00100750144012800c003c03082e070b80c9050100035030404603481c1d104021220515805407083d03480340c3e1111040d0301e09010b078000040b500ca44e200d5868010a200510a2030207128503802406044009042803106c1e2107100d00540e0b01541c03a0301008059141c03800600481c43c410070642c241761683d50 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 402736591 1250 402735341 402735349
    0x20613080307062306091815040c0e010b090d0c03020d1505160e0d261207030212040b250e04050c07020901060f051c0203090709060b0901030515 64
    0x1401884090000c40c0d441009140c184183d449015501e040d11390a400c901c103c10011101107a800703e41a20482e4460392044c039a00c07055850004170030014052043c5020030910141070711303803040e40101e03000d51889555000390061503109102e42d070401d06042c8842507162900c442e94038a401c0c084e00e0030410480c2c9071f070000b44050000c040c04490b00300c0f40706008808500c45001301c90303009441c010310710545441d0f11005001081d600b41224801c81c240003d0004200c0300e001021044201c03107014202c26910701d000710703c1c960300054001c0f58151681c030014411521900840b24a4070458903034440f15107440c1d4400003044170181c8402d1403060301d00b1400d00f0718031040003a1020520f8995940410414800500003150f00203041e031403c0210410141015844416080f41140c20515084c041c510380bd03501121103010b040c1403080400e2400e010034122484903000b031405284100284c0300c5540c0d41d02046412194207125032100d254081c00700c1d850350b40c060f50005602c000034043c0001103081d81000a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 402737841 1250 402736591 402736627
    0x1a07030207050604140108010b0405031f0f05010b0409050a0228020c09190609111c1b1110202a0d02060c090a12020f03011104050f0d080904090206 65
    0x10170b88242240d00c0c4246030741c0e0040303a00c1d00518108000d50700d4541880e020903207a00322548140c941c148004151010511182d000748118544482e04002c82c5d40c5030083d042e0264802d1055042d03007802c0101040146480c0d1086400d803410303025040030040d001481d40d0381410702020100003540940780559505454001109100301c4c0c460000b1200300d40381c03007140d808072617440e0044106c081c0341c03480c41c03860380152130100c41c50034551054190b1320144030b040a5000c0e2224241d1002200c6c01414622001500403111150441c114400e483d0310019002e1007000721845250054050030a015201804182c0b04000301000380568500003c03108000da080c403001e00002030300071a56880382040c501e4140d4180308a07034011410000c1a480e1003004d10005240019078040c9030345d0134000140d0a01150385aa1032002c0c1007101070002c0c041c0c0300c4242c880912036042441054010015030200340c2580c6040310014660710790145070a0b04100c0d56000b4800280b000c40c1040340c000c281040016440113103a406 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 402739091 1250 402737841 402737849
    0x18010602070f08010504052d24060909060f0903161415070c12030f1b1409150a21020307140705100e030f040e0405070f1a07030207050604 61
    0x3080c2152400400030142e2000f5480328070720380d25180a11001400100d405040e46240600c4100c01c0f285a0691010b440403041000c021449052080401c040080c80b08243e0903001100800c20359982c0c0044c8410755504513011840c9400001c001400017011051070794000348010210303420f041a03110000d003000280e07441669005010079a506c006501040441c040217414203c03014541444003001e07140c000f02100003408044001c40c1074064a119502c102030b03440860409120006894051b10301405901c0c42050000b001103104988002d9408201c42280602134a019410307141050034134030ba0342011b1822000c2203140307280b42944804210500f4405401854010381d213080c0000007034404622a409002101800e201e800003003080403555a251101e0300c500840ca09041c6209141180700e204001540f502021901180f0080c00b60703296445584182d040b90305954903080700d003c00088a00c50490010b032140d41c2c08070b21444860145c1001407003401250300041e01e4000040d00c0360801d400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 402740341 1250 402739091 402739093
    0x14010908040e011a0d091110050702040e07050d03110c0d0317010e150613180f05061e100507020a06171b0a0315030606150210060e010e0618010602 65
    0x740034030041c040c110302c1a00400c0c0c52521090b00721441040740c070041c0a55001c0d139251590b2500490f0920001078840f820b206002440641d000c0022203003d441e0350002d1800b603022b01c0c42e11001c50244075000803050b0541e10020845d20742c5c1c0300c0541d070171114400070702e118841d9030040f14822500c3d5150f51540080e100c2c03283c0c0b5120494045d500300d01281d2801680200d504100c0c8406000449102904190301040b0940c0d20959803031031440c0541c071041e010740c41105030800c103d05c0d01c940c1541d25403103a0751000310034806105544402041007051059201824903a200001440b040c0340f405021002d040c0f1070360705040e070070060f450300011013640e015404000401c076030010f214681c072141c2008a40c096040c11000003c4440d195a415150090350341c140141030343c944000e00c030101c4501e4180700031544010144035440d01e0f45141c244118003000100c016101d030b01c9411800400600498050360300209d1a80617580c600000d459050002805054228100d00c1045404001100c25580a084260 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 402741591 1250 402740341 402740347
    0x9020a061713120f3b0312030a0e150901060314150103060506060915210c0702010806120f012c071202040b1e1503160c14010908 57
    0x30709158444000300b50711a01400c0c0303a92540060344440343d0b4100c80101d4034003054003094044050301c205c07500d000c2400104403115005518601c07000000c0012407035a5880141144c055010b0654a400c951000039500d030040c000240b1020303050b804080036080c0c51085558200c01e04000d490000d205a83d59a41a51203c4c01841403044112134885810f50880c010808000c0d02c0c01d0019080006000081206072202e012550599906064699046000b8000c51b040c000b40c07200f541840d808400405590301408110908a40e40140040d102d00d0441c2d540c680703441125401129411002084241d20a0700c540d01070300d4001c0100981e450340d02c4505c3c00001c02104014081401041201e00040b900840d1600c0104952001c114481150703001130049114411601c0020302400340100e10303d4200311001280540e03280c0988000c1c103034000a59005036040030020090803148401ca0b00780c03840c0302c60800081c944500c556042d9030b03014080d020004100ca0310454490035200f2500c420b6811342804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 402742841 1250 402741591 402741617
    0x21b041107141c0203030406050601020f24060a05030d050d02040f080105091c020304090b0f06070506013201210c0e040509070305120f0409060b04080d0c0312090609020a06 76
    0x81009400c5540c503a00f0a840000110100940da484010002001c8548076400320750b65900802c801c40340140c400e01030760f00c0f80840004a00074200d00b084841c80010303903c80400c1c01030401c40324200a039100070300a03046d507214601c0c0c2a01d081e8440058000101d60070000010850301d03041c030141c05004a8000890a414524038a510b8040364001c2111512500c1d03080c1080d0b01e4000084500f11410703194045038103410b020028410071651615107401490000d81d5008000000c82c0c900c1c1a20703e10301004040383c07031018034003124030f0765000307002162003e449482940798058014035003041642c031101c00040c4400182d98003926207601c5900702107031600b1110f6510b881e090241d103038405c03c00783c014003e191450b00d40994030b900c1c0001ea0710102c20700040ca81145008241110090704140380b0501080c1e9641e030842d960359209100b1010b140c0034031820810b030b1a200700200c45256415903984480162190f281f440200807020084441e155545030340c40050310350710016401850786443c2e02d0850200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 402744091 1250 402742841 402742843
    0x2a03020f01020606060306040b031f0c080709180f0b0a0603020901140306030a03030507170f012408060913141501050312030103030c02180405060a0e030a021b04110714 74
    0x4034480d4035055421800410540d61281010b40b584003a04039408543e107043c580219050001195151000101c01c040341c02c5a8205500a014500015500c40c4140e9841020842d00d48055006002007031208503030740e803d114115000000c45848200c0000f94014412000032020744080d030000003c01d80104003901a9a04001c00302003400d0001102403651034218001b0f5240d898466008003410742d075002103404107100e1103c10381c2d501801d482d40344480c100465001c0c907500092140d0400c241c05d861004640b503503c071080000e0340c515911403403042c0d201d9004003c2d11400c01000c0e44441c1c0050001d8038080340508031016500048440548199103000340e100180b890141c2046000754040145c490000d00310808690440e0342610708980c51241c0c85c40003840032050f4a1074800350000c24410b000600c0b60108615007d15095035040107410300c030019141d181c1c002c411121015030841c24105a5014907400b04046044000b080052028158150108250080c180545542000da8600740050700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 402745341 1250 402744091 402744109
    0x4050a20131e0213120c0f030506100902070302101e0f0506090a0c020607030f1e1a0328021f120c0801031e02041b0302072009132a0302 60
    0x100e20801903280107501d00c03010211400305d1103041c0c0708101c0a600d0b40d044c011020b440d040a0500c090f94034613841d42c0c81c00e11a1360b440d02035a09e82d01d01c281920300061508801d1003207030360030759045c0c025140451900340b501c00280050382c6102c080300c03c0107070641c90948243c403503140410840d1318000f82d113040500c10f00007002802000351844910f0700101c030740030a4000403495072014841c0b501003141c0d0115800136002c2d01c1d074086007003c1c0300333140340c100d4040c50310a41100401c03030381403010400040e201c0810907654040c01c03c0c0c6480d510f840c400001c183d0503901d940c11a0042c0c00600450100c040300d03484112960802074000d00011903201c0c0700e0403005468019014110a00c0c40c00340c4545d41103481d05881100360740c2e0050b80700c0e190043c1c07143c00c64842e83c011526004041c90102a0700d00070007000703000f03544217101c11181e0004007030030720000c0351841e41f45510440f0050181c0d505a81c4200d48920018204102510a104c040c2d6101c1284180c0ea809011010340f21145400c0561440c418444504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 402746591 1250 402745341 402745391
    0x23010e0307140304030b010317070c03060603060c142d0a0906081b030c03220b10050a03080306040b010c1403040e07030c020606061b03030a0b150304050a2013 70
    0x600208010004500003040311030641e50003c8841001180400c2c9c01c03000340c898440004c00c00710151100100340301c055480f00d82202d00804040c0300d0520803207030031142c1e0082c900d0b08260642003400f54116803a04454a00c1d03d005c40c08403400140d801890700a40315800c024045000034003040000c1c0200f41e84004c205800160003640804c801e451000d903c9000d000041c0b8071001e41c24040002080c06007038058a003000f11010980b614200c8141c00d102c0b6040e08100d071045d4084100000c000703000d08103072080d0070459811400c00c5080d5101d0b0300030400035189402d062410031520013030324400b0400310300070108070180080007150748601e03041450807010030041000e42070501e001c10740300d55280c006c0f80f01035000d10100c510316610703010b1084040d01c0144401e9240d2051102100f0008500c0e040d5103c0c0781a4001110354080c07074800d5018440e00e84c842185c0003485600701615034000580c02c990446040c4201103091185144140046001d0500d00241c003803402d80c90b000700c41013045200040742028 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 402747841 1250 402746591 402746593
    0x9012303010909230d03060605090d060c0c050709020d0b0a03050d08060102070b0408010e070e010f0621050f15040b0a1716080a050613030c23010e030714 68
    0x209650502944a00052280c4400d490b1075006803020050160541c2540c807459220a495a000214200d6034440348402c422020038500400440d0b258010400d85948a00040030304079000c46941d5160054208000e01d031041c030112074015400500184000000350144040c0141c4900075103400100340c4241e0300826010f00d101000a00210300003040300c010403e22400e0440c035544520700100e107007135000c1e03000f0482040b0100f004165004103410400c40c072600a022180d0f49500c460391030300b88180c00e104d1040049180f020800015010705d01000480e0003604002900004406855040d00d50856226503503400c14001c0061120340f4440c403018030760303080d034082105490341030210380d02c218940164802c500e181e460781030b65064100208108042d01c00318040c0c4940c1c1d90a155070303907403884c40011101c602480340001e010300f02d091083c080c0300b40c040d5503080c00111141c940354a0512089a011104d404030000c00d1401c80302401100c41000c40d84001319a02c0c416810700041081d08241d001400d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 402749091 1250 402747841 402747887
    0xf0703021005040809060915041205070e1608040c0506040e071d01080a09081b0d0f0503060f1002010f110c0c030307151d0d05180f030a1502090a0b0901 67
    0x4603503004c3c165800d00100307803042030f922030b88940000c44c1c034030510034000e0703040764000380202d10701180010045003141b2031802c81b0b00742c039101c101303545400e40d00f1039031803000705441039600803004c0c8100d20703c0d50820b0041211760515a243c401040b100d9000d80c100e1003030303078a100060107009a40211276103c0160b408030404850307506500024418100542648405030321880380800f4442035204840d15042084017083d2a0140c1c0403040703031260148030520300807450540058480a01070021203105c3c0c00010104aa0070a80204003e68821100c49135003c5650315616100300048a106085400107125001601c60003228009031500300300c000aa0301a810900042c40015035541e81c1880b1091540c2002c2400040001040007040740300304110200c1c46034140c00b48072550400014025545880c9210881c1c01e050818040c1c540406403405806600401003035010941e14010034144600341c41025241c600d802000441d00800c0e80c000300d29040d40000c20f0156580c2002000500d0703821a0f4418103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 402750341 1250 402749091 402749093
    0x81b04080d0f170a05190509070e0f100e0c0f0c0604120306060c08091f0806010806010801050f040c11010213050406050103090201051209070b03040501020c1e121804020f070302100504 81
    0x16480401400410040b0b45590115020049000c3c1030100044042007c0009143c12103949949d541d887c42021071401214021402001070002c02c184140b03114114866603901d001c401e111022070003000c082e81480180300c0b64901002c4000100843c540308001040b19013003030b05041089429203c10f000615203441e100b005070580100c004081c941d00880704503200c5000001143d007481c140c02c15840310200002c10402e146800080050140e1001e0342c607001560340c0c21006444219003800385540c030000d401d01c4401646442e1700030000c0b040545c542941a81240c1d40c40600f60781010b00724483c0094819414401d40c01e191103084020320003403070107000c03907103142d000600309100b181140340340701594100052103030031704200f000010104080b01e1075403450b0034106a4001e4104c0c00300090703540114207515920603e9111240b0a02541c00080c016420440a0072000d90384200100030030741c822030401c48519603407840580440400541d240b681c6001d0f6240c021f0400c8040040c0c030345021719007c2404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 402751591 1250 402750341 402750377
    0x31b1101091e0e090705030105391213020a080718022503051603050c0606010c050c010e01031107060501031703070e010c060f060305010c020c1c03081b04080d0f 71
    0x2c0c0481c0c0e08112100200e071503004541d428840550481a0190b0034401803081040d00c030b4009030008402e00300c1201d12003894200c0e075410341c0051a140000c140701030180541c1051020040d03600503a100c0c102da4140329655001c44d421000c69400341c0c5c5290041e10f000c220000ca021004009102000411032a00341010060400f0303101c030210b001148043e8858140400d4007410884441c14404150002541518070740200160301640c00001c55001e00d00c0440e03440e5015030541d400071075100f8003a0808a1809004480607517804240f1410142c44003030b101000003030400100541405500003003141d40c11420043c000c42c9102e081309a29000070401c0116881d0b00201e0300c80200c0003440d202d01021f265050200281104840d0780100fa8500700000040000552144441d0022502a910100341e0395040020107264031410700e4004003507a52010000740310f00c1c20740f43c1c044503d0032610381c880154071070001260099008072200781d1058400c460800c0e00f00045184240c41803801042c1d80306048020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 402752841 1250 402751591 402751649
    0x120c0d030e06181f0b0a090c081b04180509071d01050409111f0e0102070302150f040b0d06050a0510050703143007030b0319031b110109 60
    0x41e07410807403e001101c030b4a201401034071040f8208812115404400200001c01440611941441001600030006465802e80070391341c039403001034aa900300d95031a0441644652207518500401d0340d4200804204892880f14400d40241865000125881c040e46c1e80d500d8043c6030781000300304840079003001d1040c6035183c07112030640700240d901250030803a0f807510301c203184030707281c1c855a00105000001074901100e15140c40c0322000e5030340e41c01d02e40c0749003401a81c0300e40711400080d4000c08011840d0070515000b40041c40c004000c02d1905160a940d083c83e010140c104803044d81d002c4d0384401d01040a45043c600f148081e1004941d116240310848a002c4c040d0712440200030700b4803d02c583d598034824100419120300041c80203c40410290b12640001044400180d10b4040c00035032001c5101a0710034811a00070846c081c0090500c41c3c59181c0201100300040c01c210100440800790111b40000e0387c490540c03640c070030b06142a089901030000340c0091145c1e0008009a200344501380c50840c41030282c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 402754091 1250 402752841 402752851
    0xd0c050901050d1509062705210f090310092001050a0806090604090b0c0a080c0901170c130b030403110c01020d0e01050c0d020303090712020a0902030711120c0d030e06 74
    0x10004403400c046c1790803c042c08400520300f90b503804021000d810202c0806080220520400594042085140c0c0720103454004905254580c007040c4030320b80307a0607a400000c6c8001d00000b011503000c09140e2101400761002c2c02c000b212003500403032200c520425886143c901000090802d10305100c90584d005200a00083c00d55110300c00e101c000ca0540e4445034400a000794104055a000b4602030003241e61a6102c01c0342c24001a440ca400111120200820f84416940c141c2d40c468000c00c40e0081c544071990090b0140354880c0080020100610f44090f1301002401c07003220042d03e81c50207041c05403252807040c030070100380d4100001d1111203aa0100d43e64885800c2c0f410081f50076132510004807414019031483d150b2034819440042440f0340c0010145100d01000c408484070103444080d0008080c00d0a50020340042011005112911080d0099039000b1214a4848071506041100d01d140c5041d1146642030b5040c0040c941001c54400c1c416650005140e040900000c888440f4503641c503000188 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 402755341 1250 402754091 402754133
    0xc0a150501050d0330021804060b040302010f02100c1809050601090e18061911070c03060203280606090b090303090d02060c06070f17071e02010b0d0c050901050d 71
    0x50100c04e6044000100c007000c2c0c0f40b05ca1000d800d2100740520707009600074042c005000194424445a0340390074011441503503080700b881400c01d4a594015560202c11403105e0040d80070b41c0c940c9603044080391003485591003ca0303907144030301c110b0384110381c61340303012030300034000d42c0303090401700581070340c00c40104012220005110700c01c80d560301403101100392401d08400341e00c0c0070741410b100b58000400e007240f200d841d80100801280b0141e071415a0f175485028801040341126020400105410364055540100181010201c003d543c03504c1c522800031041c014602180e03180c1c01400341590141400300a002c03410f008030f00d0281c0d0500005c1d42d900441303252a1244d042468080c04640341c00c2c054035003190b041c108a400500344407902810b0003c04401000c00640a03000b030170003c0c912640c61600600381d0342c845811444058050000c8080a14000415592a001425103540f20545403030072241c000d85d9050000d509180030130500c0380040c0c0c401440340660b101400007007100d000340340741402a412 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 402756591 1250 402755341 402755357
    0xc0f150a0e0d18050a06080a050901060518070c0b040303140a0507050708030408041a07110402070b071b02060f0a09171504030903020303120402040b030703210c080c0a150501050d03 80
    0x10303020a21003a201e0300b2460300105d24240009a44d5007044449001d813400340c0040c0002e0350352040c22803c0750b015200b02584002c0c0100b8569041e20351001d05604140c40b4a020900e00805032640313214035409603400c4000a40d9050200c42c54580188240d400100e2a0428407140c1852080103005010301200981100300010200e010400c804c8100c0c0c0081c10502004d420041102d0001421500481c09c20360307095000210030700c0b0300c0c81d00c0e200301d80300e0607400018034020f502d03444421150301200381c82c0048828564094403025a48401c058210591410036083d590055240000c2c140380c0e0a42c0b040d0305c803441020792454040d00109644107006005001c1c041c8a590b142412102c0c501c00f903002035054000020729008100c15000320510a174001c2da02031022040100605580da009840041c100740707500c11140c92541c041c451070180d133340c00600d40202c1000c11a01c43c4a041d6014a280030010380c01050054100880480d00c0600522100c00411041d80740c4808105c0c02081c1c0c42009007000014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 402757841 1250 402756591 402756617
    0x302010e0f2a19060207140a090b0d050114011e0e0403270308030714120c0d020d0e07060f0f080c0307120c0309033c050c0f150a0e0d 59
    0xc00d078a207246090003003401090720412040f450100c103507401050014040d0002c040b4003101d070016804040341d000b41c840303d01189001c04140c0286258a40b1591100040c00c152001c00d00c00d00490b801320a40150701580e6524003c050fa4510403080001d150510300202c0400032a410031010640c0140c05081540802d00d43c3c245000902040f94910945071080e010040148030880024521480890b100c1d0f9034100d07022101d00c0010b004000184040c50400301c005034846c0c05800240403216514003001d410b00824103e1182915000011201036600418007044040d07408803980c0d00743c041070300b802901001070401c000c05c14040105160044a000804644001d1103031031280450a2801000c221070030000c40b004014184a902c190000303081c0d03100c0440060108218001d03868000014060b545000000540d2080190b10700c01007803140c144010b9500d85414058102101032980107403014541000b040c01407607001914288003945400030001100a00003400f00b20f40e03810b8141404141070f4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 402759091 1250 402757841 402757903
    0x1a01180603230106051909050c030c0d0e0106090e0a050c091003030804020f0d03051206010207080a1b050303040f03031710050609030a05030a030b04060504020c07050d0515130302010e0f 82
    0x10365441702d81c0003820318070010b0f15455044400c00980740810801e2046898600d8101981e0200351040c0b000c80108100420004c80c442c1d000c401d60309540d00001c112983d03100d409408a560041442215411060704d0790100b05062101580d511802c07151034005091444211b64050103a00001b018409400042401c3d543e40d201d005140c03050040240000141919000f00160402e00111525824581c0400c140e9800411100c0035610040001c003442021030b1944001084080200301c00d002d0b1074400815a40c07000c0c00100041c028000110401615501d4000c00f62880410351040c180000030034050400c0d01a5414401c80300102d61898482c01a44002401c0100d4400e0081440c0700000e0000741940e010b80042da0b900408450410246944905002c107038880c0e40905051604210b0301408103107050005418503902070720407105015102c4043c1c0800721415940008990587c07882d2070105a03090144204003a4130a010380700a0500030340b0a9a1000c80800c902405121410600c0751405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 402760341 1250 402759091 402759101
    0x1051510050409020d020403051b030d050d0b0607050c09011202060318010b030f0d0f0c080f0a050f0309010605120318130e0114100609061211071a011806032301 71
    0x600030700110b50305c06240c0d1250000b54000e04c4225090b0080054124404000a400005821014ac0904150391107840100c072203500651700391320101e585805102607610303104054100d07540300d40e00030841041580100020300f941640020040040e600f07851006132281da05480d0045000760101030402d90303240d000c3d40503083d01c04040c0d805102e804000f50320716200280704050b114654540000038440c00381c0850386072a41da030018100420420a99000f440240010002d681091501a040c56412030541206a0007550070b07498030307911010240002c1c0f0b491043c01c0e0004036188021864040c081d881d03010386520410780c080c403440303081c03d030000b00030300715040f01c9850010400200440000303207418403048141680d0030a085005200082880c43c0104080c0d42690445d480c1c04c060403840b000004040c2540005038604010b081c03000000140141c04030b608160b206515104596042603510801c00a05850102c14142030600030408905120107000d01d5840c071081c1e12200b8a18807808502400b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 402761591 1250 402760341 402760349
    0x80703080703050d0212040c080c010813021807050418021821030403050304080c0108042105070c0801020d0c031503020616020a0b070506060118091d0f0f0f010515100504 75
    0xd00000306c540c104021855201d108a200e030b42c914044036106d5441c542e40f6018011031034081200072020421101080c2c9094954030f1000308051030016200290002c142001d5492001081c00854203000074421803008502000506030114100070924111600300c22480d004180100040c02c8104812007440b51508030319600036046079603035607807860819640c0c1c1c8984140030180c000c04a9601d03ca6104d26a500c0c003c5401074900040480980d00900d010146601c05101703100f810841c00c4001203e0000c1000201080c1d000182c0303695079400d0303040607110781d14104002c161a2280f1840b40120008420f001e0340c0e0151000390b10303800954880803501c2d00500340a51b0150310150002070400c1e00307500502c0c0003480b40c000d8031926100c480040d02c1c8002160241072101e40383e5001804404420380c0200011829181c4100f5078a4130a0301540c104050a104c507511900300e081c864942c01c0b001c008100306164540d0003004603141370355071010044400400f01d0310030400300904125041c4a00c0070b64000d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 402762841 1250 402761591 402761617
    0x10905031f0b1903031b12030e15010323070509040605041704050307030201050703020a141011090a09020a14030f041205070f11011b080a0809030408070308070305 72
    0x456181c450041c0280d00c4051006100c030704002c01140103040401d408034030001c0300c8041c05103140c2180e07401e464a06020701c021508003c1c40c00c0e00d03008030b02d113180144c540c000320791070002c3e1700d08407080070340d0800740301c0926080340c1010700d00100005103241a41247c00700d410b090509600021007030540c00c00303461380c2c00140d01542000600c01030000300e600190142d40300740280116400a04180e034800c0c0260b00c1029490b80000000b08055401040185117107803003441035407070b0100076a403140e00c6441d00c4400c0d40000e52080c0f0344c86c041c99600c0d00c510f4588010b0112094201140440021903040042c0541c01800d41c0205401d100c0c0c41c000ea5048500c01103501c0358545130301d032203022b45000c02011a41036410412510403541a140603200301c6a03100c4d0801a6040d1064071504c6100703c4022402c1e0f414100041c1054008100c00715490200c07440e40b0070b504541d03654031034240050030048054442c030707042d4100300300802c000e0b0f1000a40038200c070b17404000f581d1200502d04084d50603000d201101d040c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 402764091 1250 402762841 402762853
    0x3110705030c070807170a030f051c06030b0c090901330302030a1406030d0c02150c03090414060315040c0e1510260406090f0b0a06050108160e01090503 67
    0x20b1802c045a0300042d40c038041d08503002d41d5a42e180c1c40180301d0a0b101d800005400640c4820302091043e18409007074011401e1803441d101043c44503d05041d10000d0442d255607407601c05004022aa0054540211000281508000c607100010b02201c0f018402e40080000324241c850a68100c807080007089496003081000030b000582002d0007075402119400c08462030b0210340300242c0403c1c000540280c50240003028001e0706408113407080ca4050b8802d036840021807050300d01e07403c04000248101d0f02c1050245840d1032840c403d11084d5001c1e142260103c4082c1410070186440c00211030ba90080703c414240c5568540d801c14000d860450f070000081301074840e0420100312030140403000510415100d03000e500740c03900d10880f414480d1103000c41154090a000c654130b040c51041180d005802050b0000c2c00341c0036561902ca0f03905ca25002102d6a4000d50b007040210b9115103e6000184028200044240391004150800c922086002c1051080000c01c5114591007128241d018101c090b045841d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 402765341 1250 402764091 402764107
    0x402030f0a030c1103120d0209040f1506170f16030b03190201170105060301050f031204170f0a03020d030507020f150a0b01090308040306020705120301031a060315070311070503 78
    0x700300510f5450983e4500348002c050049418000303860140c1d80d00c0002c040381040000301921020f5030000152650098540241d01c6141240344152581042c600c0140400c0d246000c9000e44201e00390306110401d102c131201005002c0300000c25413a0f1008090101079003050300c1010942c000c210709410503400d48120100302d07015140340d00800654074000d807a4864071544424002126080034021260017503004c1c00100000d082c246401c0d41e91840c020142d5004600580b860b005a401550040c541209204003d91240c40c091016004049402d805442c40b0340c1c0e00d49000e941d070a0b080001c2000c0541c6d800004200ad88203000551014070700c0000d5078a0319100c03c030340e003a10750400d866090740a80340400c0e0413155806200c82c0d40450b07912a203194281403441e11060000d4100702029203240c01282010300400c02c2080003940610300c20340c0500a209030801c02011112030040200d030180d8000e004900bc4803800f00c070107991003640c40c9070110f0391022071081c80b9654050401d0048c6540700c0030035946 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 402766591 1250 402765341 402765347
    0xc08010903050a0e0303030426270f0a060f1209060c0f0305010504060617180f07080706080f040b0c09030d09050909030406080403051806040e07020c04020906120402030f0a03 77
    0x31055444940d900b12000013604205501ca01c4195001004d00322055542c23004030030110008604051603507600780c280304503144e03240710082c5c01d41c6102d490341d031240700315140b24a0060150031180400340c4542a02d9410300102521400780d002c808820b0100a00b00602000001d1300300f100070960204c2c081c4030000c032000c4060b04989a0710340d010003083c10280040303210304080c855441201d0450740d400410039004508620406030141585400c078003040469003907038030700b000b8009007914a140100b0485140c05461824100190411400c01c41250b05004c0b444008060b4250031039000081403045495034004900300f0711841c0c00c210741501402c4038502e500c070380040c9104200d41c03058444021325601d00e000a03440784a1405040049500311b030214000c00d1203003002c0c00340c600d80c0301090780b80b8100c1c050004465805c180d004940240717185042000c00c9030f06000300702c1d44e188181c1d01581040d48400002d5810300480310100c2c0e060321003000141c159a0100810181950144140d54600c54141402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 402767841 1250 402766591 402766597
    0xc091305040212030f040b0f0c06040309030b01060e0918010605030d0903150507050a0f0207122103110a051e030405160e04032f0f0f0f03090f0d0c0801090305 70
    0x3a0310610101e03246418000004c4101c2d0394000e400343c00d25141c1420907103510340070381254007840341e040c100344001c01170f200b1704120071400760b4080d403984980103140d844c101564001c140c001104000340c0e900c2450050f11550b00301500124425403050488240d8860580100307002e500c03059061098800360b0b90101c2c1c0008e00d06080d40d010b80c0304941a4582c0700b0f000000da44040e02d146001810404c841043d0340d101d405410507005040c0b064807409552164103209075800a00c090300ea1424550389072242c2c01050240d0600036807503003018007162031950540c2c0541c3c0078a000b00c4060010000750240b030380191090071200c0404001540740c490426082003aa250401c54008030900340040010516100481042d449103605658840310800c00a2800300c1c107030107400c9a6240701e0017505035040001024050358038886402001400005038009511f440c00710840305032103613500200f05800040d180c0c03120785845104181c68a0a41000901c2d0000078007006a00c50f403515482c1004840801d6031020003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 402769091 1250 402767841 402767843
    0x60e03150a050a0c0c02030607030b130504120f02010b0307061214090307050105062202070807120206040201020601050f0d1b03050a0501140a0204080d0e130c0e09070918050c09130504 81
    0x800000c640824280d60048507140040d6056008c0300002d04854803e8106d141d60400117841e040c6d921100040d00002e0f60710076a030803583e2824403101c801c00c032a440381643c00012203900c0207000e0080c0c0038011a4650105020324030400a41c1c10704400d04a807960800108404c8400da07411951070300f41c441a0b242e8120841c1101c1070350034180401c0b140c0c5001c204290b403002d86a86580b1080000d150204002d62281c0030454900764113104000110700d50a0490a01e008180c02130b02003858144002424603105800180c410640d001e60140240c5406012405850f407005022841001d03000c481d50b40f81001e40e00081a900c101081502000b4064000d001c01c0042485101e001c3d0315074000d0907059024502482201b40d014400307010071148505240d12107201e0241ca50821007030740305005001d842c0c956044070003240703842011600504113071807130541c011040e00e00005102d003030203052101c03101200224103400f500e8401242030781d0740c0c0004580401a000348003a44d0301441005a0000d0082228 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 402770341 1250 402769091 402769111
    0x21090106060203040620013207050a020a020603060301090807081305010804021e010e280803030402093103031d0120130e010303020f060a060f060e03150a05 69
    0x400001d000d800001035909442c1c0b207032511500928101c5107244044d0701408050203940d2074030400b684401c00c20784a5185192540022002858070010840034000050310070700030045c08002a5820702d074081110030005504560055030390b101d501c0068050100d1060240c601d038400600d0800304602600107003003000803507a81d4108181c0c0c6a0064580200898020750400100700d00a25807480c40c3c2009002c1c41d0050400079007900341c02003c1100c59002e9030106007850152400c0c01000700440d0306160091080303030f0003103185142c1540850450a00541a0138005081240b18175000003004180304607202c0c11492002500c000d400d00030003600e80304040c2130282c040d00c1c2d078401c0d0114060203011801d1040303101050629400d0a801c680f10f520100f10440c0b84000900041170503a00c00d400f40d030081d806940245030745101d0581050401c1000382070502580d113802d10400402e41090092002c0703e07103505105007082100c00102e030920700b66440004802c040324040040c110903683c496406501914 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 402771591 1250 402770341 402770351
    0x30405090c120a14130516091505030a111207210201110d09030b0601020f161a070c0522020c010e0d0212090d02040e370f0609030302210901 62
    0xc091000b140c4d11005541508507004000034428644101100c4401c0d00c10402c0b90203084582c10080a0b00c80135401541c1c9140d11109044065445200180050b00084001d051904015990350401070b043c08140d81c0110090100703c103a007081800042c005240d12100d170900c10302d4000c0c5000c0d00d0b102000049002c02c41400300001000000a80c1136044021a1106039035941140c640304100c0d4002418513046120b1814a182030807000d00c0248944d04115070005d0a550a101c420100c0c10310011042c00051014020300e0003040860b0bc2c00d100702c0b10155543e144001c1900b0702280c008909241d81140a400002d203544035074815032100321040c0302d207803e403556281400d008903160000303280d2480c0081402d00140500b440c200800040c07151008000084170903107000d00721f0500c0302c0c0c03603c903001c01c09103840030f544602e403c810034000c1e83c1d11001c0fa0402100030366407114904c0004041c09003c0c01d0752100d600c0200b40c02903040303c440c400f6034201170700811a00740d03411240801c211100100c6500703003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 402772841 1250 402771591 402771601
    0x30e040f0501181a0a170105070201151703120c0d0501060810031b0801090503340809130f0606030b0a05010f08091006090209011826030405090c12 65
    0x1882072a05840c110074400c2801da011601403400b4044001e14181114000c444210440e541e1a4a0380e006144031802000c0c01807005282c9421210300610300300071369040c59030500c1d8000416a00c00c2c00d951044001003004500341216a20310f00881401d0f0070400c1e1810140948400460f000d00010003100700140100e03a20381c0021100381006990050707960b50180e0040c00066150b6411400360f5084c10004403100e030b542d00400e402c0d90846d0341c050b02d440d00002401d0402081e080040300f101c40d88002e20f900810300d80c0e031300810030b40c14000001d07040c0000810407074036a40e241c004500303a4140d00701050000d0320b0007240e44402400c41c0d226550100e803805001c074030b05091800500d42203520503120000d0b4446416410b0b41c0d1f18400420807280c0713000740000558000c88920400c4c01802c00360000507207400401c80003511403c205402007208401d0b0340020498444110210b02005426000344c81014040f000c80340c0c9580202c0d00b0265202c100c000030814502a180d000c2c20000000702c801120329151 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 402774091 1250 402772841 402772871
    0xf050610050f0f06072a0803030709090e1e030d0c1b0602070203030c07090b090c1306230d050a06120c050d03050c0a0b0103030306300602040308030103030e04 70
    0x340708041d08025100803186a610f88415001181d403805031102e03103800c010f42e48485443d050714901081e00100518041c0400d042d44c102c1d10080d12040c00190b103141801ca40c0a040c2d602184100b140d229150703504003104540c00e0000320f0140e245410300200d24503069030100d07140e4001c0d10840848a103049030380300c1100e11a450b40e00d0f803204038403400d800c0803420392103e070040d40c1300190603038240c8001c02050918000410100c17004100314040080e22a0341c0f0010001c031114046e00b01d40c0028000d10614642c032079034000c500300f00c5605040c0002c1d42e070b20854441c03030740820700c14006c0c5141c035003c42c080c045680190065841564560b20070400b50307072504443c0403100729401001c2c04181015a081c40300d0304205040d040118060300300f0504141115603175074541401054101d98004034000100101078240c001c2c83c01a0440340441c21304185031610f01c1c28081c9100760940c21400d004203000e000c0c851290704070307000341d500002040d039a580c680c00c000c1c0450a00c07201041c0120320f486924861024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 402775341 1250 402774091 402774121
    0x110d060806090111090922050307060f02030c03130215040e0f060d0804030b19020703030c0f030b030a030513031a01081603080301030b0604060b0301062d0c030c050c09040f0506 78
    0x500340c14030030030170144110004000d02114102040554001290810340d8008640e40d00c280000e5540d4030725450401c00350340480101c0654240180180100d0070b4115040d02c2d407003100e42c000e101d50360031107000090302c003101c1858a012a60b000103020408625010020348a500307c402305c0b117041d448a009100c285440800040c010000c20700c010700c000380000f45003580001408210f800d000d1820702c202c8049030302501e82140880e41d10042082d003550060200e040b030f41d240d0705041141c41c03040004039407a0355600000170200400081d18640700e1402d50200e00145400502c9419020340f442c030069119034081c042c220b1248102c05c1c9a5030191001c1c10000e050383e078811407680c1183d01e181d0700c55500c064003a2085d94803581f00c580c041000341c601c1020354000c0085903100b001d00e0849080c822041541c0c04890700c40000c416580100b0b154008840b0300c4007962615150050010b00e040160a00d1543d040d8158010b80030000d01c0103220190386040b802600442c01d54105444030211140400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 402776591 1250 402775341 402775361
    0x80703020321090406060509040b181603020f040609050108010b132102040908180a030f02090603030c010c050a030c1d0103020d0b0a0905090f06010b030f060103110d0608060901 78
    0x42c0c002400c0d000603010601c40e20020705201504281045102030010301a41c0854000e030000960100d5407034050700d4540140035412801f91b40c00442200f840c480324204e800300422100980600100c0120002d10a50403a050074200301c0c0702d0754845482d40c1000b04806498414a40040c2105001251801428046034458044901c4c583e50007461300e170b403000c3c41c00307011041607843c0722401e52460090b88a500600300350510071516242d81d0700001d02d0406051603079191031401041201014400036810718140403a07141c0403100341ca696550040041c2c994405e07602491900c1d401e005440c2e185c1c035013140140c0308081168500b1710100c000004212030300400c2d000303d4541000010701140041d4007907801415182c040150201c1c0d004031690105941c9443c1f0b502502c0200d945d542000703000001400480d030296000409014903502d44040c4017601d01025010500040c0c01102044c0e05a003c0c0d4410b10070030000640c00d41d02c481c0315030840801030203130b8801e813211400380c040003a04421043c03180350b94031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 402777841 1250 402776591 402776593
    0xb040b010504050c030f0619080a0b07021c020a1b15030507020c0607031b050304091a0a0e010302130e010f050a0203150108090a03050d0f3603210b120a0b010807030203 74
    0x180e55a40304208c0c10000d20508207412015078140412612028031001d00c41a00503407400c4058248482c0081c0b80c420310f0b9614140d14407900000c00304942e80410741c10030694100c4c05403031020351220300d0002420040c1d0310070108001c1c811a8004141e0301a0440c600c00d401c00d03000c1d500c0c80c90491082c40030510590400400003840b280801c802807200c2d29440c01d11501500450b070415885680280c201e03030403c40c055042e0a1001c00240c114034240841c035001d0162003d48181c1c5525541c0130a03034500c544888421801c1d2254640020190309500905112600a00900540c1000724180d402036109481415100807c0c0c41e0412240d40030f14100f90217903004200800312a101d40d1400c40e10f640000d10b0345c1c020035456aa01d904000c0407405000c40c1501000044280d041c01d031103013201507400680001c42815070680402c4042900110511442408420514036184001240a00411030125841d610081d0216041c202c58030004a18a90f5841249082816600c9400c200c3e69039415100003541 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 402779091 1250 402777841 402777871
    0xc1606080415112b0f0b09010801060602030f0a05120112061b080c09181806011d0c0d090f0c23060912070e0405030d0b19030201030c020304030b040b010504050c03 72
    0x301600342c44804000600104ea00381c0c0d61107035034050300751021601c0a004098440d00400c1c2c05181000c08a0f0040c446000204840703450714201a4890080200401c400240482c0803440240a0000c0321140c081c4100402580d603114200b020084121000a490240c17503e41e01003500484200302e641c005902c1d458080d501c0d0b0380c1e00e142d046550b00020b2100d400c001c01c01c0e07036441d683c2c4010410f00e00a51001780c14a06c03414030703d030302c0d03501e0900168444c0e80b009076981c2150040400f660f00712500300391410304c010f80d00c2c414100000040d2460103002088000c80c08881e00a003e504105035054070403641401c1c1140252600c4004031540c45c0d42d5aaa10030000c000c034181d5840c015443c04600484102540c080c02d54030461000c04101c12601602c0f0358000003592562030841780f0840b9107081085500340d008025003156490790100078040241030690302c524070340420b4000c0050b1401107134003120000b49480c1600c0c001d900203200f032140714000c038140004180c02e4200c190070f4900c5280140a4041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 402780341 1250 402779091 402779107
    0x20c0a0e0604020403060e0a0209090a1109062e021204080709051b0a02010b090f07080402010c1106040f0305010e1207110117070c020f03060112080c160608041511 72
    0x11444000d0103040d4420f0b402c02001001803081d0050041c0d4142517400b4162014050061042c10100100146a60741105103400c0c0003409000740024040b109440c2681543e490320041140084103c410310701003400007061016074000c00c031040c82c0c0d9072155401d035501704450380540d445034001ca00a10b1603607040b1403818011032126501c0b050740300065100301158131202c1500c511896103d0118000141d440c3c00b01c0360898188010001d8002c80384182c10a4186054030340189452800307000241003041940c00704003444003900309210f48032001840c203a034943c1d55299080c6a03003510310089030507508002480c86200800706520403041403011059203000c04507500d500e0398100c004461410300c40151100d1200183c0804554414078a035221800030017200d004102018800b009414425400900140704101c488030507000310a601030f03001d90703e031840c512144d4140701031200c25500340800382200042aa5011070340c0703400b503030107403114800010a915222080c0d80015001e08030040c02004140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 402781591 1250 402780341 402780359
    0x4080709050406180317010b0703270312020c040e0106050603010b07140615120f030a0c1109040c0609090203090c01110a0204050a0f0f0b030c0f031501060201020d0606020c0a 77
    0x250302c00d01c03e94001680b50310414480d222299111410780000d81502994030101c1030300000350b0301402c034500308581080e2159074000c010540c03014200b400c04401c44051858005400c070b00001442d0f0126841601c0882141d00965504005440300d200c0c42c10b11a010300c034040184a024255103010b013030315107035070300345060740f51664018a01203d0b8641100e1440410b0300301030100d0fa008040c0706100b000b640480d40d0410074203030052001b41c00c45812001940c40c10b000000216107101c50781e81803070849410301e41001108580c006601c00c0c0c04c0781440b0101300804c0b01241042055030340f1900c821000350f1311940c0300012408115070507501176010007644078440d80910b03108030046442d01c1c1103a080c04156400328090390821744400c1d1600d500e5900660b50302d1114000c07030594845e8503c3c1002004003540000c3d5649500c0504103004100482a48209172400d0103c505c0041c6a03140d0701801e540d403040024001e40c0070b0345520008901c0c002020800302e2010580410749540100b00c030f4401810304c911a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 402782841 1250 402781591 402781601
    0x91806040c0e0a03080a0c0507080106050f03240907081504120801120305030430020c030c01080118180c06020c0a15080702031603020a0b0711030d0c0e13150b04080709 74
    0x46c81417100c0c517400e140009508116041c0513000180c00481c02518100a00000c65120550244640c0000705200c103224084200032503c00c040d040e05100301c2c0c030303031058850901c049a00120b483d0702540c010204036900420399107004034852035100b000c4151034032085400400a0040c4070f00a04041810800b091044002e140c216001d0003621490070313403006070710540b128440003017481a22581c1910300324640501080700c214000f540600304000c21140000d1021405008070007161424441800141c0050f602c0020031031780300161281303544051706020030300014600c50900184905112500d16080401e250402c840d103031885980441e41160b030683e04090014040002c502c0103002d01c1150860b0032203122020b034080d40240120301c81600b00300b00901801003641c070a00010b0040215591130000c1150341050355100b000485c40c0020030115501c40709000b095a00806039500182c00c07411030344c400041e8118810592004039500d001202ca1801144902c5245d034100c264208420140c81e000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 402784091 1250 402782841 402782857
    0x9020301061d0609091807150f2003270102030f030703050411031606020610052d130501050103050f160c020109150915020703050d050a05091806040c0e0a0308 70
    0x2920703040180070030100b001d805c011a5100381c03490f10300e004840b03068820310070440035000c0a00742c84102100350101500200b05c80005100b00a4402c200503101241c003848006c1690300031065a51f141c80d86c82c610385200e150212079111402e1101c003100269030000080f1070b03100800020503400d5035602c600a40061100030400e0f00c031030b002c0c00f40d419240e030f406108000c03516803090a211182410841c0013850140000c118450741600d4000c02d200c180ea68111008540c6603002e0b070300095011915030640d0068090f80a00e4100d5940a01102c444405401c440d058500a0b41c0400060f55600e600d4040d401007500c210403103504103c0c8116880f446684070303d0720140181404510a669541c2801c4807501100c14800010345500e4103011459101d0350703007000c0c400300e440100307500c40c290388503103884505448103901441800102d40c00c2c264081c01c10707200200c40003890710200e14045922460101c03011105948901c0c40d2012604403140a80c01c0200c3c04003000e4101e030b91144c1103694020300c0b9880414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 402785341 1250 402784091 402784099
    0xb07020a150926070603050a0605041406060c030d090510050a050f010506030601030b0d080a02010509060403120f1806051b130e0a0b1c0c0e0103081e0f07050a0c09020301061d 77
    0x41d035810b61a104001d03c1d4010078041d40c00251501c1c200239a00101c030708540007e4422418581a4824440c00d003c0098001c001107038100c0c2d030f54000141407071a5108140f010480e00e800c00c035409040c4800800c6d456040401548188050b543d58510a001c841c81103810030300080e4440700503c032034248500656030100040c1000260090000009440840306510803900104000b810700403150342802425002b42000d80200300508155070081c145211031500c1c410f483d44d49192040040301190040810019202c003814940f070b11031f06000001d08800c03510303e80c16148180c203010200710700c002200c11401b0715004500c42c15081840c90000450003030050780031b842d20b81400f110740740d0302d02d50b688110940e003030309034654420240b800f141d80c01c00b60703845941c03041c03102001007020481510441d80c5003415088110815a103505840d0308a015640d110040510042004001c010001840440090060701403502c070750340d034480c0311f401e03440240200303000507285407440c03d9142c111903050403a5000080c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 402786591 1250 402785341 402785399
    0x60905030f120405010612050a03032a08041a01060906051e1b010f020a0504090c0c050624060901020c0d08190305060907031b050a1103040b07020a1509 67
    0x64500581c00281100024400b101e090204000707003403007100c00802041040241c0c040b0306440d01c1e5291010020042d06042e20350301013404041510b0840d030702072040e41c40d80745840c02d42c85100a00c4a0400c44081b0348005042400000d0b070005081c0441c1241c0d0360f036440802d083d060a404035015001504800041d455003001e412800e1980009004404144000078002000160003903007540c401d16407501e4101e104000c035550742c0b944502118290340200001042c5200e490408503012514504051f01e00d0203030360103016940140300a40e01645c801d07050034034112481502041502c2c465880b00e903026921950850041e030400d844022203081c0200b002c54140b559000240821000c11846100041d80d280200078851900d1900d464002c6500d1038200407403030402c15079442003000780b0308a2041c418003060807189284102c139242098400002605d8a1f150340f1081c00c1601e40008100f2031088800c11700224083c000c02c0c4445070744842e2a50707562006460305402c1000d10b443c402400250403030f20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 402787841 1250 402786591 402786607
    0x806070f12050103120816050f0f1c15050109050a0e3304060611210906070f050c06130b03040c030f0b15060c07031202070f0f06020d080c0706090503 66
    0xe2045900035030181078201145c0e94043c000078200c000050a84180001c403071192080350341d00c00281c0c1d485c10300700f034640c960310103003240400150301617006d0881e1850214005a81c04101d1a0801c10706c15182c80e83c50650f50ba04e0380015211007105005268001004040c03c0008011100807036400c02c070175038149036590403490b4400d820b200312450b40c03440c0d00c4400740700006581043d00c5000c00070b000501c0d0100043c07280d51000f07a259031f2225070b00d030900b90802844c28058401041124040c1d180108140d50b5440b143c6000d003a036408803001a20240569104c1d850380d07040c501e044917581c018580d40c0e0951503080008400036a0030140082c1e40503844100f0200010710318006c81044940111b80844907032403c900b01c0c902d010b404071382080c010780090000000e002c4000926070240ca520030300b038410710442e080c0101c3c68004071354051446401c0c00c200006009180002100a0300ca45a00f503401281079000c1c260355110b800c0c0c0345019400c20801240010070ba191f40603640b0b0900c0351040c2d904d03065a07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 402789091 1250 402787841 402787877
    0x11120411040e0d03050f0f060d0f150e2b0c062304050618010c050f07020d02150a030e0105010e040b18060c09030f0c03030a050d0f060b0a080906010806070f 69
    0x1503d400801007541e030000e0040ca6049090a00d51060760182e1004041c6400360110703106003046100140b60313841000311030080005c420304030002c0d43e21031241000320058811201d6690a5200e000c0c0d083d21f4100b90502c1b0300080c100c4c1c1007022480c2c00e615442540c0006070356440040c0743c0a15040d800100d080d04901081c802d40c40014081d9010300002d01180c00c002c0c4248000054100c805401031389880722241c4065085401d4541003010f44100c182c03030341c8150010580c66150010000d52052a0b081204043c02c0341d0341c09060100840d95042142002c48114982214828000c1020603810700c40080d002520750080d443c0e100070810500c00d001e10301715803000e2078801d0a442c008000c0308045608006c50070200403101e01c80d0b0354200200f40100120000c640c0343e103e8020240200070000076030704000c0c801a00701c40003c00003864104680c07940d807440d150b0a500130036a4403001840d008040380031420001899410381d400d4034040c1c04142c6411805070391036080e20080000740089500748102d5212 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 402790341 1250 402789091 402789103
    0x705011104061d010207090e011803020f06010b090306061003021314030f03040b030105040b010915050405012c19090603081b0708030a0c21090911120411040e 70
    0x114952025071658105400941030142408164440d00c0e0505940000c5a0b80016414101c5404407000070306030518000850240081245504510328000390803420141c0c0000d088401045c2c800a0b10000d03601e681c000382c154441d840a85501d81d0210020541d1460b2021107045d000c203403402c0c01850700741d0411100c84241441d40c030141d00000e00b01c0d010209410188120300c0444800400b551a11742031900c441620f01040c05510702a650707440b058403159000b10340309000380242001c0001e4400208100a00690150160301d000900700c0c4900d141424040b41304100303210700c02c00309115089102c0280300800c4c0c203141d450340d01d00804120010300e4a01e58400e05015500600d0795941d207402a03014140110014080e048555000c42d0003004003944c00300590310018a107241c00c2107060050704014500c901c0d000541d241c103000c4425900703412608180880d040300c280c080280541015080000301314010040c000300c0401311800082c0005d11001d004000e40d10700240001041200c402d0404d260070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 402791591 1250 402790341 402790361
    0x151a0310050d050606010e01032f070507081c09080a0f1104020f0301081203090d0f090e0c0d1413021c080a11060f061003020a110f070905010b160b04030203070501 72
    0x241000c01800400e59124040441f07e000c20f00301400b483d45012840d03949800d8840700f03a0303012442400d0024855210100b02c0b800141c100d000c60b2989525050f220317444000407144281003146100c0000350940c01801c800040302c88050141c65500c0c201c1d210b40c4019666240226007000d04ac001c6800c44c0e90300e600c042d0420600030f001e01906d07036040940082c03030a200c00c95031040b00c0d28184204502c5000010345540380e6089441e000d0001a00307038605940840107500920200c21440f020040d0151840000d0951940c03014414441c8441d00c1009039a892402d45201260640d0a40d010780582820001e507540f40d48945e2159000180b1134481e04401d80113415003c0000340f2002c5d00565942e010807205401c02d44241c00d1441a00700880000d8400c6103148903102419004140e4401032805030320224015241201a240f0010020500544498040c014a40120b14050012608054104c2510b0038407180a640b40d0105000d80c231180200d0074010401c07011440104218400a80300380a100e0b0030b6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 402792841 1250 402791591 402791593
    0x5060d120513170c0a0f05091626041112030405120a050f0102120a0203070504060c050c280602010e12090307080106090b0405010605030906061003090807080706151a0310050d05 78
    0xf4440c00381017008243c840e038003803621030101c050f09014550704c8070a0709030040d048140381d80100c402014199440c1104003100d0404d51280b1400401501e00038400313a201754440c0c4528080b003900c0c081000b80003500741c4038118803a070086c0424080c80c1041c0240c240746500c03460072200801440c3c0d44482c0b902442d0003108516940200302540e820414105840d0800074480d410350031403500368002020760290384074820412008850700720a2017000d01450340400710180c0a80c40c14841c5403110321140000c507089090031024a00f002a520b841032150985201c035410150454906801d9054547d401c00b10565505008584c00000e800509226003c020f1424500c0425031205180c10401100d005a100e003050000400400c81005004030300d03244e10140031500c2c0f0540c0000c10604400801c1401d00007004c03518006800e03000d0294110150020380d11441090001010001e01102c0801051144c0d83c0e500c2000c7c080008601246000b6590144608140782015aa0781c03000501e01d95050340c0039606 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 402794091 1250 402792841 402792853
    0x9080a1412071709011116081006060c080d0e150a0b0603040302060414030904090f14070b040905042f090606032a04051f0305060d12051317 62
    0x1009418072001c4800c4074000d04840c00d0215a44a15400e401084103034100c40d1000034603220180e0003450b4602201800d0000c40d45481403101d01440c407282c850007002070074800e4201700c0010300754500684003070b2a2140e6641102d08000c9d5201b00092700007040c5901c1403512201d090340000303002c2011400030070012004102504140e6150300c00c0395920104103025080410030000482d4000640c1a00950300001c1c1032101444412118110300500d0101940641000ca100040c80081c1591550341d07402200800d08200c0310003d1b442d5248000e1085400080342403004000c500300e640c0c4900c1d442801b07840d90040c2c19030300c000b68540c00d115003610440344140d1040c0e02d882c20704205c1c1210383d00076015244645541414004024131400030207101c170420300140000444400c800c0d0030381e0001d041c080d02610600f12000148041c40f5003803603000c40000c0c540000164146803181c114011985c11280c0100e442c034103040100c820380c7c8105120b07034a0222803640058030340000000d400d100b58000000e408 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 402795341 1250 402794091 402794123
    0x10f030206070819080403180e220c080a1a04050c060309190c0e07090f0902090f0910180603150b28081e0304090902130203100510030203160f09080a 66
    0x1014070100c500c03e506031211009d200e6003042d0544a0b13000036000b040300c800d0b00364002d030380204449551030050000415100001d00081c0c0060304071452840341c406181000514500441d106030b048078054140e038007041401c546402d0020045820100d010107840100e090310700c807c0c900309140301c400c0307070000c2d095001004003418069445400040303924081018900d0000e6603140c01140b80160800c042d4009510205541d40301d00b01c4c1031000000d40740b0b004d80c3c9092aa1034400c802942701e0018003480c000680790b0015190711407442682c0c0d201075004c0280c40a920340100604a01c00e1003a001420680703070250180501c0400041081ca011010084a04160704141440359a400300034000ba2586184403101c100031081e41c00340c40400c2d200285c90b4009000084c3c00944043d85003410510001c1800200b01c110003a0390196201520007220202081604500301d200441d21402680c2c203029500281900c10741c08101e1591030f44c5001003d00d80c40f40005400e02125003003c0750440d103070f451840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 402796591 1250 402795341 402795347
    0xc150c071406190b0f0f0a0306050c0d061d04290f06120c03030d1a220c0512130201050d330e01171e101103010f030206070819080403 59
    0xd40c004444200c1800488019001719810f0080340039980e20561103026007200ba43c03103c14584008540001c07003400103041c1104103a0541d07101c0a03160200f2801e10f10046200020030581c03a02c10746100c103481410360359548030b075004280020180004e45c002ca01d04180b10191455007d40240003005542c03699080000030070900c44070360300060141d074001e20301c58495560048141c0d184c03032003803070004502201c05900c0d542c214085c4801040d0702610502c3c4100807802c502c0d0104003014881039003044400c01038403007034bc4c5900130303131000b17800300d00c5d00c000020701a1700c103020115030309403040c1819405d0000385044002640c00c0031001340e010030305942c0340142d1070981c2031010010110701c0c501d4050300e07810480045c13445007050050184907032017007a40100d43c041c104001c0c00c01040c1006c41c03d810300414107640e41c980d03042c01d005040c103e01381b64102c1000391408040303034102c0b445440c1d0f03203580d903117142d09004064100380d409440c140000c2c000e5106049044002d103001c40060b954040907850189009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 402797841 1250 402796591 402796621
    0x703110408031c061d06030102090a060f0f020c130e01140c09090a271e0c06030b030d0e01030c05090a0b0c0601081609091b08210c150c071406 63
    0x80f8005042403010464910701002000c440081d20f00e40c014550740d044e000c6406803140341c2c5120741122501500142c03e55100103089483d00c0c4c59500d4510040000a00300e1b40c4c0c844811140758810884001e03101c0c00310b0680e1048041040210010415018000b64100d0807203044400c1d8585000014080c0064034008011aa201c000080d04100c42600844042c212682c3e102210f00591111002039083c0b015464403004080608030003448031710400c1c41c000944481301e22a00c0c012074200605190320f8034002c5a040000c94043d9164606a448031004601030800078a10b242808010046090251110701c03421000d003402e20205c4c1c0d13680d0340e9800780078035010050b808050181c200c0b00b0b480e036084440d5450003044401030072020070000d4041c103100e42c030168131028020b02100c003564002001d040c003044940c2c182c544245100001a4402c2c00d00300c140c07041e07812002054100382c1c4105040c006524400e904104c106103014140b0359556102d2050351540c007618441d540c001410004001800156 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 402799091 1250 402797841 402797887
    0x201020c070e100e0703020702041a0117070315080a2d11060c01050a05041e080d0e0a05030f0301140f090a0f18140c04050c0f03070311040803 63
    0x21450a03100c241295200d00341030140e0110180e071007000c60501001c603103280001e4012059490858280400d0241c020751041d04101e00560408066070010703410100140803221041c1c50301400c00055030201310410900401e00301c241a5600307a0641d14201c82d040b42c1014140000061040400c241880c0000010800f2200780e09030340803020950000340b50000f081803503480300640c0d10000003013000814a009200b41c402166103898100302420a942d0001d9004502448445c01c0a1901c0e04448081c2034800320042c0c101541002024280c1030380380e00501400040070250f45009445a50b00d506561180d950ba0410010100040c44075418100d9403442c0c050040769112050124600803948006000b007a100c030340d550f0780c210782199031640d400c100103e0300441d002c1c0d400c0d0222890403060039801c44518046e10300c6100710303103405400d0503c5154040c404c0903501c6403c0c0800442c00c540c550307100601002c201034032100d202c40d80040f600042c0c4040c0c00d03031801450301c500b0320000c071520310b080d0185 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 402800341 1250 402799091 402799093
    0x25080106060504120c090c080609060105040501050a05090d12020d0e0a050a030b0712050901020a08010e09070302090705070210091e0b1c0923151b030402011709030309010c02 77
    0x7000115000310071501210a00401c00000281606001c54074002aa2189920340c0c20100650200c42d80104914401c00003100e01c440700f41c076a04011030f41800349000305404110204100701d0b1240c0100046d000c09000109003641182a51ba15801550000050407004d40c0c002002034890f04c0c1c000c030403003207841001d8a5280701c06d854880018440070702480080c00314050b0740e012540c0f40388100703610101d08900714018441c0303081c0410f015000f03600c20816900058007550010801c000740321282130050107128002c01c0d40500f180c08000c0c041c100540030300c00b403007020804440117031101040520040c80e19201c80130401e00e4016055001e00d0203000e445052a100003007800500b8085040c0c525900303840c0d0a0070390005508580c5002840401d5020f42070250010540744004c0500144120000582c7c1c2610288210740c0e005004c502025111064408003000503070984102c0c00740510350107801450b1450400d071031540c2c56100c5080035640300070290800410824848401d000d01c3c6d83c0241c981c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 402801591 1250 402800341 402800351
    0x1103061206090c060c0f161a03191107120f03050903030603060106030213090204030b0402010f08090c040504150c090305060c0a080c0d0b060c010c140f0306040f020c250801 76
    0x8455680f100f202511507403103090089007401c0c10440402010aa94000c0022181440010f10b011403854116200b842d540000c40a03521800740144003d0383c0c0aa0955083e8544048604000801821403815541440c030010300101c0c0102d0030240c00301c00302c80d50a491b4a00f200c0104036004050b10340041915009074010010321196450018003981180d40500d0016210230b82d503940c0036294100f903801400d400b400420f02000b40724100d540140034034404d0300c0d800d2070000211420341d40c1c24011103002c0c8240d040401541403d042c2a00029481889144c0d10070ba041004490501102c1e46040402d0000340d00105c280100703c0c0c1000b01640110205a1290420080d13110041518100a0249082080c0880e0404204040d41c000464554000b88441e8070362810f00505070080405801c0700f0001080d241c019990704041e5000c5800a1141d140d42d140385540301c6c01408003800603c041e8031143c90707081143d4400f0610500011402003042c4240c9140a01c0c081d10458030354005402c00c00c11a4500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 402802841 1250 402801591 402801601
    0x3020c0a0318061b110102070503071d0f10030609020a030804030506040606080606060d1d0706020f01061a03070305060a03170d0f06050108011a0421050d08060918101103061206 78
    0x840e11803940b5a011000306038000000c170040703040c00c40640c0519098030640341d020540071030034405a0700c0402401d62504542d59420901d000080d07042da10760381c520508030001d0021a495402c45000c0301d00151003811440e980750b80f044060b80c400c0d81306580d2034108605205c10400d00c0d0061400420400000702624145a00015140c2c810001c10241c00c0b950340e840301c124540741c4003c1e6084c2c011084242c4040325684c05001c4d40b00d00b103090f0110702c42d51802d07001061848805204004165824501500390340c0c600c1c000b5402440003a0825501840ca40000000514803243d02100d1403a02135515403504403004400707051b1400280c1c81c8440c40e013021424010307668407038545070443c2c0d1040c4440c018881c1849001015100710b4000c0da045440714640b003a0750314076019403401124400c0084540c880ba1800f42280d81030310030789106900071440f0000c982d00c100440e1102e0b804215050a58001240f540b00e202c040328442445142071840100411180d4130301030042d40403c0002d2400b9040307520300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 402804091 1250 402802841 402802877
    0xc0703030e400608030705030403030228110607020a030302280b040605040f0b042301090c0501120f0501090b1206042604030b0f0a0f1404080a03020c0a031806 70
    0xb050202c80380e030b219010144804010560010001042d414040d00c0c0e55410700e0401c162241d0041c041540940304402000100d098080d07013242090750241280720b801074140c0d60304949120840703110741e0b1025080c040040560750b0400003c0095200b032f00100107000381620510204001c40b5100a84148024150000700f200c13114403981c404d500c45000981955185020034852a00b02006403a0200140c1000100203402c007060824400303200e22605181b10941002d803c1c1e45442c0c0000f070034201303010703070030880f65024014048008091003000300d4012451078a110854000b68030582001e5161442c1e0425400d005081103100000c903401f0300301500c1c2513101c0005040711032504d141c5400c10503582c0301c01c040c4010300341e030040c40d0300090f48041330401a00040c0c03d00d00544040012611b040b61541040980d40326116042d8030030075401c03085582e2a142c00501d0b405c407000740e04c1456000c0085810582c81808042e11851003500c40702c06010011360003540400168015038184215883c0c10150040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 402805341 1250 402804091 402804169
    0x807030507031221020a1709030901110708011e1d06041e0b0112020909011506080603030c010227010201110405040510152007030b0f0901020c0703030e 67
    0x24001525282c84644048101c071300c2c650280209440b10301c1c48041c407031040300c507400814851100c2d0fa10004044403880074200c00d9a41a00c164940c0d500c10403a1030901d5008840c0308801d00d1202050703030850340da240c230228291401c84549144405600c0700061401229124040c106400b0900c030504506640d820b2954588004c0c0014001450922101860300104d0104201c05613022016081c1c0c1e59507541144000c07d1440000c0344102c2d48100081c521100501c1807003401141a24540d00c514031b4841c05944440001e012960180810425900301e13882c240001d01c0d02034001c441514101c402d4140e4400b030890015901411641891007010754503010f41c09031000d6887c212070010f4280c0b5020020420310515138490b0001ca007030610420070a5400401e91000007580294402c0714880e8189a19140d5a041c003001f441d0346d1f440800300700101e0b20030075040d500884003400189410660342c02c1c0362400b601584200c0000d10902c070760b00c2c51170429852000001d07030031689020729500025007159803d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 402806591 1250 402805341 402805343
    0x1409030304030809010e030a110120030118182102011a131d01050a0b09011503020f040e0c04090c081b0a030b04020f1b030301030308060d110603160207080703050703 73
    0x80351500c082944c0d1002944040303154a03640c0b00b00ca80e200c0c03400a001d440c1c0740d03410000314003035460500300346410440c0b504617012201d00710f0011840c50382003036610322801c40c0a1050819044c0d07a2041d0640703005a00c1c1c2d00d910354901404000000c8800120052605801c0014090459040c24030740000c00196190160078100f04888411002104003210002401e000076032aa0403401007a041c00805819400f1b0340c00350500180a0150071141c00500074242d03420320505000101080312038019501c2503001c0c004906070790415514240d514104c0c0c400190090320907000f200e50004040000082a01c00c4d45215407039030820300040d00c5c040011056140c031144a400140b02c0000e40b1040c000e100307901c04009100010b10854a866401a07074084642141212400c000e00b55903021003001c800000340c90403268180c0c2d40c45c0c440c1e80c1e0041401070030541c000b03007101c3d5400800d010b1b02c0b0650310007024612615410515583d12444901d0003450880154450480b47d0814807050001c1800419000c05032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 402807841 1250 402806591 402806597
    0x15010918080316080a0c0503011208190504140109080a020f011119050c010306050d0609060b0402070302010504050c241e0708040f21060f1d010609140903030403 71
    0x81040102588080030a40d00c01001c180e0004200503001243c3d8500c89250441a0380300d000507900c100c503041c1207071403c0c1e8018010031800d00c010494814444a10844603224203481820b092111000a40140c202450707580800c0011400380a140e480e26192802d9240074039000500b5031030b10000548072000150042d004420b40d0500000c035900804101d2a0786007038000300c942d10300c00c0020841120000c11701c00c0b5a90b001e502080c10443d8820b0250038265040201100100700d415980e90009020b449401c40301d0b141c6480d0341d1070f00381d40d4502c007504c20203000303400109041c078040c0b0301107042c540341c0315509110b02c3d1456002500050000f05008070440c0300140c01c1d54400204414004482036606107030809500000c060f020000030380c01500031203401083c082051034541c00940c56025080840d020403004580400c03010074066006035103503003500f880000d0300f5030200c941160174405418540f82580e4444004001c2c0e10710621842454081204145d05182040c8002c0c40c0c49104c090400707410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 402809091 1250 402807841 402807851
    0xb0402010c050c0a06030c08010905090705190302040212040201081003080f0703020a0c17060702011b1409030d0e10030b0f0402030601090b03010e0709060305090c040e010605090108030408060702150109 89
    0x1005010480082e43c01ca0040c0321039015982c540c0001d002d44500c101020005003e0000001c13080e0b00d9005207805074030607001070301c01c0508041c180062114542d0224003664410000000580c49a10090514040c290a00d00c042c1c43d107800007610a40018003c0503580c05484000c01c04a504002a69280310782c120000703640c0ca0741405c0492402a03920701c0507010700c6000000060aa1203034001c60b04a082000c1507030340541d64008185d00f03e64001c4055449071840f2018484030320300c43c125050301e080103801080d08095205c6c0200c0c0c540380c445000704020880c0c80c400861140741207039a42c11884094501440a400d400c800726540c0c000103c00103018a40110110702c0580c00380130000d002e030019003140d98403903940b00d0030051503540a5944d8404203525070350118600340301e4010f040c80f0380c0012004082003840501030100405084446410b10f5580b0f01001c80d50340da03007003a218001c1040c000107540702c1c0e04011031a410320f8030160580d0195071204401000001c62114614111200341400080e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 402810341 1250 402809091 402809093
    0x3080c0d060b30010e0f0402010c060c020606030111090105090f0324040c0501030c1704110607210c0b0109050a0204050409030513050307061d06070512070b0c03040b0402010c 77
    0x1070195a00800350703129020078401020089240c244407500c80c0e100c4200380c8005a0020069154000c0c040c00c0000c00710a0300043c0c0100280016070b81251042c5004038020300192503031030407104030b000711340d00603000001485682e01c3c0034000c403001501c10300b0469191044804c0080c00c5441100d03459400303000010081040d9580c14089840c00220094002d40080100320134a0000036084400311007040c0501d41c08100b5505c2445004203181050301c8101401804806801401c81e006000300da40c145100e000803981d890742006072564600c00e00400b240c40c0c0c138601c01c079000090600501c03000c02c0810940140403174010103e041c1101d03c0380c40d0008441e2140400328019202d55008160003604140201c0d0030160702c20010540c603210070808800d0580c40300101a2503070003510811000034054090721641035a1a11407081c03815004054528011882e03039503030300389410b00c90388000c02c04e40410b07040240809a0000360780aa02013082d10b1441c0307415958610135400180004e410480b90700c40d40d0b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 402811591 1250 402810341 402810367
    0x5090304051e060c07030c0f03021c05010b190302040f1b050f0906040e010806060108073f0e1b01050703140d060f0503010e030f0702040c1211040608011203080c 71
    0x1410b1600030701090b03a200320840c1d42e80c0e07403200d00d0b1004540424141c00c0c001000380040200c03000303407a4001d00b041c018101803084030201ca10342d81016a0349541e60031642d011517443d1030107039803010000701d6108111031035401003000b02c9059980380e515050801d41803031181c2e2194407078144c411441c0d0074843d17102c014420b080c0304a0b002e0717a540950000d00020f00454142c1c0b0a01c08181200e01c040c0450310960303501001199803400c00d4170500c0100f2501c0a10408140b101054190600c03228504000c1100c03400300c1da05090040302100b818041e999803400800e4070814403660f400c042e25080b2070248030401d100001c000c4d118010001d400c1065988034222641d241000711000c1481011080c4412600d4100c1c003050302d00e0a00c14a44613611b13100381001e101c0c001205491400681c00811400c02e80940c09110281690005140400c82840340e0840748032a14840c000c0310050200349661510306000d0f0290485006030000880c0705141c07142040001d40c401501e5a112421070540c94454421100c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 402812841 1250 402811591 402811639
    0x5030c04080709060317070c05060c01090206030c07051c08130c1502010e010c0e0604051011190203160b07060f0e1f0605040e0d1407060f0504150509030405 69
    0x80e0796000702040029041d00c503803c003405880c0100e414a0198500c452400d003d44125032006103402800d8000304080c0c50a00c000c1c00708007203001c001044840140d0f0009580d1351086403c691200c41c0840c5150900804200d25000c120386400d4030041c04001e03240140c00c07101c0c010a0a003900410101840c200b120500018005025101c01403542c0141c003c00a8041c7c000c98411311215131a02c0100324070700b4880c80000b00f10301800b9180b58a014145824405040d421802500c2480700d0130400143c9000b00b0800000d940e00a90300301c9407006486c3c030406050143c08100b501e40d8100080051007400340c120112040c4540c4075800054003489800e0040241c0010301e40030819002d4190010301d440c030004001c00d020000e100d0100132150b1103200b004101d640018010001d41c0c05031a55410080c0651844200c040002c00c0e01400d11f03100f81d80e0a001d8940180702c62502030b03160303403d020411410307800f000d8003640308103018442407400c82030030f555038000c0d0300c1028415428803201b070810800c86c05170 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 402814091 1250 402812841 402812849
    0x30f1b01140c030603060718140a080703080309011109011b0c050303131d010617040302010b060403060c02010f0507080a0b0a0906060228121218051b0904050a020105030c04 76
    0x1805a4030300d4040007030b1030250002c0b502c4501a00400b000150030713622a21500d1511004408503000c218240000721300301c8000c030070718250003a00140d004101603808120076002944103d001c80d80e00c0c40d01e2000d080c00d4440c078102e090403000080c010a0002ea070800405c01218041d14040000c0070074501b02545903080585c007898040c007000404510b03d07641c0440c410240d9580740300c01d400c0e0080f01401c030341005109214803800034501d8003c82004968010860340c015001c0d200101c2d100a0000004100340e2096004403205650303190400b12240c0c0a028035002217038103100400c110714003030714003070000c0d44000c101100b241d030780b81c1d04058560760f240b0161000d06401d40041183d20b85903d4003958070b0003085601c1c85400640000f10768006030b4009942c2a140d807001c00420659540101941e001540200c5100c0d550340350504050744c41d030040d440542150085004042c0398240303000711200180d0805500d4003654400c0304001c0818000551034002c254286405940c0355a101441030305400b03541c01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 402815341 1250 402814091 402814121
    0x3050f0105013015061e050a17010801020a03050c070f0b06030a0501110711191a07060f0603030f03200306180406050708072606040209060406090f08030f1b01 70
    0x5120780c8401c0d003030780300d03140c14a419541e110350700d91196802d031249515241e00c003090034401390301b41c81c01170311801c0500303417956550034010162a0510300030358000344242c00c5000f5580d8046050070408d1b902d805003640000a0007a44c500e00a10398945030210400d0b0b02028100842d04004180355032410000301c1071240d0410b00802441c04005002c8100d0b502860f0203546c0d49082083c020b10924045041302412030000b4554035081d4a460035202c1da4000e803003101a00b200301031040501099160165006c9994240c10016080c2d0443c40c001d000800701864a00030989041455107010302004100d03841c00b10071a96041d00c960300d0038001040110402c070030301c10a0300954140401c00c0f030a50041ea008104949680015a54035002212860030712100040000030034039403911207003001110550070542c05480035180a06080200d68075a20030f42c0060002080140704010072401004554040c002503c0594988000d0651a180038046d06200d80c240380308968144100f25001d41c0012181421031f2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 402816591 1250 402815341 402815417
    0x6060b1c1a0312070203013204020d0f06050415020a09120c0302120d0206061507062a0f0206061206041e0209160f0807081f0e15030d03050f010501 65
    0x2c00300398004e402000d4105d019600f800341042c0f14030185c1210340b015070b58280300400007030000c9000c0300303000c070b000b800503a08801e03041404400b24120840764000c141c0110004100c3b42804d1905000481c030044004070001d105020b29244c1c01c0d400105401100c0d101444400116400e0030501c1200744103510080d0701c8410625030310744005012a1481c040c858035001d441e4156a0a0180b10410b20308003002c140c01d440410003070300020166880041c900b0443e5044092f510388030324210040a0121000c5070208404e40030201d20741d07074100401c0750f02c054180d9001040380e000000603560703000702800042038084051121400603501100c040c0c403c03500100344d02c640c1e0514030701c1c02141c184002c501c00d000905d5441c021640d0760082c202103001e00100c0e41e441169a407880c1c0803100481c1c1509140784038403402180043ea0003601c210441c003880c034880c100c6042e04005000c040c50584103c8000062504040420950041e12400b02341111001e00b02400300c80c05002000c0704000c0304038100e4111313860355 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 402817841 1250 402816591 402816613
    0xc040908040b1303021002070e0115020307120206011707050a151b0807110405100306020a0c050a06051e040c15030e0f16081504080d1508060406060b1c1a03 69
    0x4800e41d4040340d0098030b1b03c551101d0350203c00c0741c80701c040303000351148450f90740300421400ca0aa840c0c8400c540ca1b0780305032810491660349219051000001000042e8041030042c0a045101e4550204e10781000c80140355040c6042d001c5403440000e807084807500c05102d404050112f000d200c40100503400589031190680b551b05d851034080d0061042a079100000031120f4280f410184240350165134280c0140204500c0d41d0355040281d0701c1b43d29079104001c0306008030b80c0004c0d01004528022441500c01207414901048611900c0e0307a19004404240d0400c0d06000c04100c062050300140c41212520b0f82c1d9400c015642900549080c1c114007403e0700c56907910841c080c00c00304502c07007c0012190074405495503943d04681d00c02c9961598117107400888045000581c848004018000349110041000403003402120590402903001e01a240c1103102000100111303031041601070040800c081e0304000c0c2d2801c40c003c6c1040c10010b010345071680e41880c400c04401096030841890002011a01643e5030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 402819091 1250 402817841 402817867
    0xe0108060103060506010f0c0209060103021e0418052518060e03010b0105040609060c060b090408030906090318060703110106080309010e09070f3002091801080c040908040b 76
    0x2448180ea0440c07420021920540c0b24210a07c40c10106a648200f050300e16020041d8490b40980780741e0625a080004180c085102c4c9440e1001c45808090716031201d02c1c1600404e0301c030f4021992a901c140c80e0204012490f660724049506540c603161420841800600040e61103420032040c20618903031000c0000b4095610402941d14010140c1c0213010344c081d12401136880c0c0c0158010040441c1d1401342c14400c0b02c1c41080454146802000085103400600300030030020750b4103a5042d2003501002041046c010f408003d49600f141214009618080405c0c201d108a207440c10815440b03a80000b0b420810b05100e05600c03000084081e008200c0c0694448440340d0300d84c0100c4549011951542c440c000130324041620324440c04141e16894003600d402ea1040703403040c001816a91110f41e090382820000c0d0560039070449181018180180c1d030b0110803080100354480540b00030801b54000e0014402c1c500701144241c40050141d070041090a40d601c0c1240e40c90145810124501d2004076200d407031140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 402820341 1250 402819091 402819103
    0xc0f0818030a02010f120b060703110d090506030f190e1e0102040305030406140d0c02010f0615020d0f0504050d082d030606160b0a0605090135070e0108 67
    0x901010080d82a1890018140c840504140290100e40c801080980030742c000c500b43c07010944144000201c1c44020b4000400c0b40d0000c860035400505030740d2465140e00001c01c01a40c51021500745203104915050008003140301c01030141d0f40303581070b52020070707605050040000c0407a04d4000d41440414607020743c0a41d21855000400c802c0200c0442090b000f48040c4200e9064070b800c003014502d02420f003001034401c0c4001c5a503560000303400304941c0100d10700500c00d030b2041c2c449940c004195603d02101080c240c0b031680c0c000a40c919003003c0c940340e940c0d03000202d9204042c40c0307082050300d0074501c3c04280c400d4000d543c00706402c5a204100d0301d041021001c0104030340c0c501c0380c108080e81e5185ccc0403d01c10045030004070341c1c1005400c0012078003520b880d2001e04042c7c50403081c80c0009007103c0e642c09000b440c050300d80400385034880f030052200c0c0ca0a00e24042c050840106516402000d8400c1004c5e0010703400c0341d1945896582050f15103081003408203070081d2251111170701243d6990b0f50300c155925 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 402821591 1250 402820341 402820357
    0x140d1406090606040b2404030c0e06091503030327010c020619060602120d020d020c0303061018090f0f0504030210050a090201090303080a0f0f020a020c030304240c0f08 74
    0x40101e070700045a52030140311705604c000020700140340d84c0e000c50511504002c1c50052445000710117100c0040052209480000580b002c1c1748403040e83c4c01c01c8818020f8116020b00784400129103400880030315100082039030ba1280100d00520842c0e80503d16030f4542c4480e4408403100c03942031440c9031282c1500040c1890090000f8545c0b4100b811903101c4800466006008043c016086050f01a07411010301003d0710302e04003410001844d2400d80c0e0115000c036400445e110400d50070110401c52503150840d110542c104290818803502c8070508101d600101c4140549280079581e040e03801c0a03280c07030ba1b2041c04c0072006500104050f0500d4100655145d011800e1818540d0074600001c1d071080060140b5080a135045e1500168941156415207180390010980c1442075601e94240c800494103009410354104501801a030392103a1401c001e090800f01012103000741c5c0f0400040140c1c0403550320154078030300c559030700c001003003d0035078121190082c0920151840b189144400d0500c91100028145d00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 402822841 1250 402821591 402821593
    0x3080703051606060803041e1508090c0d0b0411041e090311030301090518030910080c1201060e150301080a0f0f15050a05060d0b06010807091d0f0c040f140d140609 72
    0x1d500c041c5900038065a840c00745081c27501e044112900305600031030085070000340180170340340070b008510007282c9104009a07081c0c8880802506200030301003e4101c001c00480140d07420300c5980f001c03210140160702e0300350414040c0c03683d4109070802c0c54843e039020003a54401d102600e550b5655100140064001a68000c1441e11581c040a4140300000304498200303070041c00860b180d0906510603107500a000380056080d2000f0403801d0203a400001d081806400c06440f0214040c04410600403441182c002d0044070880420062000106c000b460f40714441c3d200400301800b1810b460403522494801c10000c111052072440b0b00c0314130321940c004034400c840392503040110b580c40f8010001d02ca1200309000e440300c000c5202066440d445481ca10354080c0c0ca80c01e0810f502681d5014076002460540d8440d0382e40d804132400d101444a440c209130303802c603001c141d46504003400d01110444511b60741c40b8014290480c500c0802158941c4400b0050741c6400105000004248107919a15054119882c1240d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 402824091 1250 402822841 402822869
    0x10501030b07260f06040209030d020a03030c0504030507180212091f02090f13020f0c030d0e070e0703020d0b12160929041107050f160308070305160606080304 70
    0x1c500a41c051a03121043c0c10000488070307480e119400c4040080240046800c25000c1082c14442d481c104901054010a0f034010030a0413203d0034024104c0f00074041000c2040b604100800204d00b0014034001981c00700c074148140903c101c41c1c400c000348100d0200351108840041002443d00300460034145c0d1000d0107907605001c10716030301420200d20a0705007090f0b02010b911b01020b4a401c05065a081c0410306a40c01480d000c2c50003036070340030742c1c00501c03a0006a0740000703a4840487c03681d0042c9a4028400f200401456003401070360399403940c2c000e0040007010b50200e54000f1164940c4c2190300e1754a0064442828180c0d03d940c82511280881c1443d520b86c0100800000c10308030030310401441802d00110352600321510380d02180100c8480042507440303a110340c56070f40c1e8424840020000c46109500034001181020145818083c0602401d510100e000c07000304045036000c0d082b036000560628240d41d4030070404907100100f0f9640b92000c0c101c286844800708210300d0010091056946107003000c03c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 402825341 1250 402824091 402824117
    0x914060a090b07020d060513110303040609170c04111b160603200a0504030c0609030222090b0103050609160311040207030504091113120c1e030203010501030b07 71
    0x2514030880e0960030018603403150030804030040b03101501149100901d07900301c004440c1c4824007501c1043e01e038113140d1400c0c00d04074410043d40c00740e4081e4081c3d055024500302440c00320050b02d03501c2e5510905011854a04804104001c20301c0100c000c001c00820420100c1c1a150300101c82e0341003005408484104002c940d00c84100014860300c0c074104495585050300d04002e02280a03000202b480e174450300104800000301348411010f00614019035130b401d130b11140395042c25040c9900036400314050040d01e030028400740c0c030f40c9210341320b5019800c0b001c80002c5110944410080800d007002411510181d4000300402c0170101c0e0b12030180d0180e00840d40030304070405410000f00e10314400105101d041000700403050030941c003d04003c50003403d2041c00d056581081400b0b0340c0c8610360842e0080e0700003410803920301758400c1c103101030f001c0320100c019407000d01c0da2a10a0b046050281400042c15003103035484103141038400c0d8001d541c2c040d000b0b00140d6540d250841d00b01f04160391000c041364402003550 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 402826591 1250 402825341 402825349
    0x90e0303040521040e011503060506040b03010e04080705030703030e1c171b0f0d050a0207030c11040608030703020c030c0607020109030b0c0708040806060906090114041805010c0914 80
    0x2034011500702c0040d140d40222020a02494000d0141240810409000000d2585071010300d03d8020300c0c0d441c550301001100b0f40802400c584154001e90b1150006100a12103803c0c0102030b41e05503141202c1e00740c026241c5003815110742c055204014500d10000905e0300405515821011542d000e820890740c0d85d0240c592114240300d002040040085e0628594401d62000c0c2126240c02031071000310b481e0391f0300d2801c1c0e18100c0369024202c4071400e107000168800040707415200d010b41c000c203090b500f18103203155550000c003000800c2c1e41c0604001c40d181c4c590161552554405401800020304403545c5698500d0080c1d2691581d0044070311034080e580821070f850400000f00c1d030007180d0583d5005a080d0031552440b13a4294090900b040c0e01d001030003488001070407040108060004100200510310b0208200b28400310300609840c06030741c11400400104841101c4081d42d548100d60209140000d440ca4080031500103070090410340c00c000789220f00d9508101d0440c140c81c01c900d50300034680b111700148 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 402827841 1250 402826591 402826597
    0xf050601020c01080604090203060103081306020705090613060e0114120120221220010e041a0405040803070f0302070302030910020c10120b040b030c01032a0801090e03 74
    0xaa0142e0040114500719601c900046503100783e00401c0011135990380d80100c0c0c5402c009801c2190014800503001d0088200e41d40c120000b881c551009000c0c207414100421000b220180c1454041c1441d00c40602c0104181c4d0000c00181c880c0208600181da1b56110200001d21070b40c6456014140d03804d40100404418080c9100344080c156000c55000d2000071182c0c69980034107108404140030355581000b820307071031411000424110058203d0034000741008000e80201510524080361840d00e0345013280d800514180c12010210b900140c1c0c40505150005031043e81c0081c264818640400c0000b0030001e10041c6000d8010740d5201450b9000c03a01059080b8131480d4409400b6074030a010304482440e00c07502c010f240d09818410744e600c0650701400304581104140e50300e00858108071012000c841d00c0d201d2800180c0007103a0600009900c0400709481d485441c49ca00d0401d9164001d0440007098804410510032084a400702620b50300440201000070030301400180700d040c9807219074210400415 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 402829091 1250 402827841 402827851
    0xa051009090807110307181a0102151612050c07030f05030403080a02070f140f010b0a051e010c20030606090126010b0a0e09060f10060810050607030e040f05 69
    0x10346010403d03144e039201c1c40d5200c0c03000c0d83d1500c514003011a000303008403a001405040c82c1c02c04506140441280b0064103c0c94400d03e0465018190f0903048030000b0301c119400c0911194020220008148200c03501c6052125004040303041400b4405404a000010011503000fa950b4111000307010360708451500c8180d401500149640e07001c81c81c1503003e039004000052160071000142c0402d550380340e400c440704480c0c5110a400010700300c2c00d100028028806011401c031141204a401c0c900082c81c8607204911b00100805c1e0010301840d00e0340034143c44d9080d41e2304800d482820311500b5100b00c0d03a0484200b5010702078054900440c27141c0c2400300100d41a69400590f03d04604941c03904002d111803510040740c191b6403580740411042d21000301850284c1802410180f50307203055201c403880e00c1c0c4083c1403a100c40d88841e0400010b030b81035a400c1d006641035880e000358662100701928084403550703040194000c1e00041c42804042c3c001440002075074003900c013409503501100e0220202c03403013216 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 402830341 1250 402829091 402829103
    0x1501081e0a110d1505060316081207050c0306040c091104060903060c020a080417010b0603060102060105090403020a060c0906030f060f050105071410060e090304080d050f120a05100909 81
    0x1c100004079204203640c01400c01502840d4603404135110044900c42660741032000d643d40341309101c041d040078007905080c10260481482006c0c0741651151341c40026850b0410341b40c10204103042000703403e0010002900000b02156400d0a241c1001c40000000f031081c074001e07034900000700a00d481000c0a83e01200c94648419920902d162580c40c050207c07120858214055404800300040310003014101500c00410b440084100103003d041c00c4440140311203104a0f82071080200580e40016841c0c1910019644289542c4441ca01640f5120701040c0c014205403e0000b80d00340d0f1540140440d003210500d640074403100c100c051819080b40c00c1405a040c0c0c002030020705104550242c00149000c900c03030401413509028600300c036801d00b04080e80311035060391107030030400c200c210720401e0b150401d090382d01851801d0324281c2025558061441c603d414003801003010000100342005482a10381030501880c03207031a0860001005000c1100d40344802c42040c1c10200f6004220b01c40c05802c540d00c40c2c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 402831591 1250 402830341 402830353
    0x1030804050d03030e0a0303020406020f0a0c030210210203040b010e070210051b0c0706030606140405150c01052a0c100e03093a0302060a0b121501081e 67
    0xa00644a4030010b040d030500d03481c3d80e81d0f11703d40b010070017485200345d0203507400603102d0341091030017401d00d80800000040780c3e122000e0b81c408a414000c8c3c0c1022a603040322181810006d0140594644c0807000d03640114001031940780582c0903a540003580b28621841254056a8a9880d512000c00d002e42700c03400164403141101e40c99144940c002c50b040702c40c9485040c4500684031010a2943c00b4401b01c22081d04840010480d941e0503000d041c02800442c1000ca0546103c080741d6401405144949885110302e98540381011b00350b41e044031050b00706176000784000d03e020b1200b503007100c030124408049920141260f00c0c072441d60205683c070340c1140202524070300b4610b100180186c40610020fa203240410002c4640d555103245004000c0c22803410702084084401c03506001c10324880d41d080c0c3c001002078010400103540442c615900000364800081d81044003400700309480c0700301419801500c681e0861001ea000c1d11b0071818102d030303120412507030b1040e4142c205000703250a446683c01d80760310034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 402832841 1250 402831591 402831599
    0xc01030b040b030a03020106030b0112021f0507140303040b0c0f090f030c03011b11030f09040f140a27030e06030c0d2d0506010503130f060204031b0e01030804 70
    0x1a800c440100d8200034000300d5106044030009007810701203c01100541e54a00701041040002c3c0b4000c1c3c01001c42402410b803007603441e004a00c002d80e04010b0034000151104a014010340a0001d460045811801510361403507c180c0035a900d51003601e060710100f42901c00203181300e82002c2110311103090284864204001e00080c000d6255601805030740c9802036189070301e40798400b482000803224541c2d2180314903040c045000780c26080d400c01c0b5140681c00420081501078020000c583c1014029600013901660740440c0744001d180c60008560a615404148500d007010741c0c21821003a44440342e2001030612200d40d07801401c2080900501082c00903410103600e15107207014607800504528028a000c10230220f08044944902c04055442502d200300444000d151080204401d0094420803882c14084006401404000d054084107206a1000e004210f401100300c0b03800ca510030820b64a41e40c0300c0ca45043c20042030175460003044100b80000031407002c0c1580c018100e1760001201880c00d428 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 402834091 1250 402832841 402832847
    0xf010603111935030d0501030c060503010b070b06040207061401090605180115050f040303030614060310140d0c0f05011403040b0408180d1b1e0504020904060f06110601170c01 77
    0x54035403200f02ca03c918a0040002030390500081c144624146000120707503046250a8001d052190844d404001d000c0c00148003003079694044a249a40050311807640f951441c000802a03c59124020710b05410a03a0580148140b0340e01035040e61003119003030028903100c0040c80100b0b2509404400c1c81c507402001002607000c418042452403156152180c541510800180702503400b0398011400280d881d14200000014090154041801128990301c3e504111904000c2d007203643c040c20100401c42104404180d4650000722440d9620151a5048507560500050542114402c8a000c6204000741503103105410044134480c0d44e020140700c0031030311103440f0b003c00b580040c103002881500941c24621266a0001c100300c0003480341f0310031240c20300d11a513200944030180e032045284000d400070300000030940412007402d0796000d0320010307212000c01000502402e501d42c8200c0da00d0340080c0300031030015801160341c850440b00c4001c840c003599031003070a44208500c0c03a10908581d00580308403152584 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 402835341 1250 402834091 402834149
    0x60117031602010903140c0405130503090f0a0906080c0a09110313170409050402100503100308030a09120206041406010b030c031b0a020f010e0a030f0c050f0106031119 74
    0x100614110384d8007604e07a5144080c8140f424191541584403078640f03c010b19040c068503a0003a82404810404803032550b5081d0f503805012071181c420f80c208031070b0314860b8640e03020320001422400014008665079410b0540c680d14070b00c10319400380043c1c0c240498040150300903015800845a1540c0c81d6a0780c0000340e0200c4008104225801902c5607241903001c0c5560010700701a02d15801f0006050806204004404454818032130902c4024010400c1c0c0c032131751450400032207821031401a40c81e0f0300c01403c04010040d00300000c044480119050011650000306c0c14400e42c030070055103060403960800306035648401d10418001c40000c0002400401d903510141d41c100303031110300748202095070315000112504080340c85001039100800e10603502c8001d00500844070091409006001200d0310300a01c070208500492041c0920030900c0000c0040400244200005010080044589034602200600b22004006224910311107c0054210960303c0d0a01210f40d01c0d481e00313000c1e00481c044280141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 402836591 1250 402835341 402835343
    0xf030c0e0a06050d0c1e0f12050a12170c040e07050711030f160b0c032203050a0c05041409060121020402040315052401080a06030807030c050601170316 67
    0x6602e80b800060329884001601401911480346509841d0401c0c60b6900143c4e03a8080200601412036400c00ca545807903503400702501c0c44104010600e4050b82411498185803e2000f04400d10850100181ea607220941c582e030003580c811855026100c5c0d0011003064051400b403900d0303030000603000c6449240181e009100d00c0d0300c18441401c0210321035002030300700000580070700d0058128030320784c80984034034005807000f50182150141c00c0000c2c910f812680d078050214156050541c00f103078004042100700f1228001c6501c00115a03420b269447e02c1401c2ca12144980d5000324141110200c840c50603101c0e551080c1c0c1004c004226036840d00d4210170300910f110041000d002c642007100c0c0050b072143d00040014601480000000c603854003428411510020180660030552150b041c2c140c080b10400440015024030309000301d40c4980d440310b0300401c41940000c0200d1800201201095000040d00c644030780201d06441c0729a030303100345c3c1003003035090b40042d81ca9541040000c0c141d1900140b1001c1441 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 402837841 1250 402836591 402836611
    0xb250213021305010905030f0303370606030510061e2c0f0301020304080d15180b01080a1107060f020c07060c150c080f040212120a020105010f030c0e 66
    0x2211515040c0303080b81c2c450b0102c08000309500900340100e5801c000303c50010b05050700102414902c240042d616400301070400070301c0400f01c034074000c0e0b101240c40100b0380e446204103240c3c0c41e031002605030500070000392058002180c107101c0050500240510100201c4000d40c80b80301c0503801038805841041c407084682001d1224010a0240090808411f001010300070110500c1c08000203042101c001442085584642c0c010010440090500b00556000d5800d0041c04152044406086e104404090f04002842014143e0761001c030402d9410070361007041c00b03803a040c042e500c40c1d00c03011040c1c483c101082da043e21010451000003511a51280160b00413018005052219032600942408080d0b40158000b40c0d54565109c1401071000150034000d40750b4100b00000e185201d4013a0000c2c0c8014200d0401c1c42c102d0f8002000c1d5150b800c450340303940e0100816106800460900f40707003c1d03001601400d0042d0f00c3e201c0042054005000e00c82c007680e07004103c0ca11005d20b03201c2c1d48144d51600400861035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 402839091 1250 402837841 402837859
    0x6100f14012f010c020c0301062d0e040c09050609160e040213030b01240c03110a0b0a0203090c0105040e04111c080715051005012604050a0501060b2502 67
    0x6142d00d072100d20701000b0500781c00484c09004a02c00289000302c20b0140c148241d14200c01000104a138408240030b801c0700300c404900b0320168281230b9007a03411075070000c40780c003000c601000f04200c5500c80341002e4650300c0c1010000390712041c0c24003204182c11074a4590303200b44114400d070f609015440704440803100510141c82d1600b440445411b5048650044445141d040c0c0180101c1c040c050450b1403850860300f03440040e00c05040018a040c90004021701441900450902d003184181315421030380d5008030a204850400030b0f01e0303800a6104443c4042140101c006103529984500b0032039049030191004220143c13960344480380d44d40305501fa425801561030310b80d1100840240107d10369540070f25155502d42d489400c002c0d9450b070303615018510a91914007040407080420840009951080c41c00c40c1c0841244103007002c56403010035041075101010020441000000100008198800c40091016a40c0c0b00360340d04003405070001c070f901240c040104808070100101c3d0751000090006040d03a00d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 402840341 1250 402839091 402839147
    0x11b05090a080a140f0613020609041d06010f1508060906120d0507060605100f11030c121c020a080a020f1c0f0c02070807030818060a0206100f1401 65
    0x1c540001c035a412940d4044003d13980c10b42e80014070a5550801d00c91000c2c1c000c80c900032000054000c042d0b10000c1c81144040380b071240f90b44455100000c10300142101a0380c440414103401d980341c100f4402d0500701101e00c500800c0785110440d41d110051099118082e0303980f200340804c250010014841500708041c0024a0481001008150040d5126484240d6a2422424440705440083d04454014010003140c081e030b82d2f6002c50034941c03009a5103428868041001c0304241580305d20b02045a15124100a904046450704010403081c40c19400128407a150036000e102070b402280ba280d0003058280b80083d0380209581c0003170103400344107505d00c0d141c105503903941080711445012401030301c1d84d54541e5107541c80203441000b8a64890b4001010154500050941e44103d1400700601354070303004c110700b0071720922451608a0042c005000c1d0b915114a000002c0d560074040307a800884c50211040020741d100325440140580e041714201d078015140c03601c01520807510078282c280c0b0000e070340c140c450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 402841591 1250 402840341 402840343
    0x9030102070b070806060a12020c1006180f110313051203010e01090f0b0f01110f060721051009050c070609261204170c100518011b05090a08 62
    0x70340c144a4004482141451180241440b00c000c14181c0035080c00c11098042c0c50f003042c480ba041c154016001f45e078407000041000e0901c01d070494400038140c10b005010030454039210b42e07060340d03022601c0104000c0b070416031030740141c3e40601d00d40d9000d000104041034002d001c0840381d80d0941e01800441d940006541c20704c0c28035900913804614041c003401c0c01071110542c5070140c6180d0256042c1c00340440c522441c0094414509590801d040c450034056402113203c0c28049541d002220405880191601883c01380204c480440701307440604000a106106010b244070721170090046c008000e46107801d0154010017000050441e0998090600c074410024645010b61898288101c14860f6811a0282c80c2c00e400300044603001220358080c050102030042060815502030340064100d081000c18682000e0700c1e116001469559018142c444491106960044c50180c00b4840c002d62003a044c01074414200c41c01c0f0907420869000d40400c68610030f02c03a03409092000b00c003e18900145507500d00003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 402842841 1250 402841591 402841597
    0x20303040e10030204060503030c071806030c032307060c08070c05040509100501060c080909100509090609070f0e0f061c0308090c01050f07080307051209160f081005040809030102 79
    0x40c40205005a82c20700441c1000e0081c0e20040c4006c0c3c004500b4071300030840302602c480003402001100204100d03001c0032111660800c40042d034102c11049083d40d100c0c1410340c200d91059082d107524030303018080001e8200c0c000402000700c4400e5a101403040c3d206995011880e4072050b0140e03403180c52024003007900d64681c8109401502c4400041030040c4a520160b416141d05074099410302c44c003030707441c034010400302811a038601204865020749560380c40c40c400414112508201d4019035580f04100908100081940c0a402d09908651030513a4541e004194034500307010380c5466100050110700c400540056498008100030664010019280d12403403200c3d211701004d80001d403035807050288220041c4100f43d001003080c078141d481c00910340414080307407084603001020b00800100143c0c3e640e10480540b0340c146040000040141803411506a0701c280c804800030b07600703109600000d903031030780141801c0494104101821004a902441400810001b0015030700d0302d03810040c14046641c00e02c01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 402844091 1250 402842841 402842851
    0xf03020d060f080d110c060d0b04060306090305040905010f060507060b0f0907091a090a05120c061b10050f0601030e0a1a09161d040f060e0d0f0503130f020303040e 72
    0x18010390030200c00060070000b0b81d41710300102d5042110002e40750b8480d45d0840344200c48d0b03030703001140b0091100085001405642c0c40030b08800e103002464410181d000f801002241d00040041c000b0782d80314800100a000240300d20400f08804208020000782d1310303000394000c008000e010584a04050000c503170300303010889400c000180ca410701400301c8030700c180b143d89440d441c1490560601d020040880c02e1401d2500486d0f12404200010701c54071142001190411400540600d4075005c08100241c0710f025400c00c200c0d104e0060009403d18000c40307126181c4120114015059540c403070600540040c030303038482030700c1c960f005500940d070100f95a030100031030034401012860101e14002c1215401d000100b11210a06126075200708503080c0e075044010241150891310141c240c5441c54000110f0000c00c800a0200f03090a0100f110500082001598650030352122113104100311001c031114442154840e024000800c0300c10041101d204000030071070301c085d044038034280d1100b207011210352003110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 402845341 1250 402844091 402844093
    0xf02031c120902210f2401090b0d0809060c01050c030115050c030d021804140403020610080304150c08030f19060b0a03091506030614090c010f03020d060f08 69
    0x14a92990303544915000402110070004101000195001aa6924180d141030580302c29070341d03001342410300500c91004030070132030340c11070f180540c440748810800384108000e8040d611b6548000a4042d07006d0151031821b01c0c0040079084110069500c801e8503030807101c00707150048400e1180110020b024801d80d401401481c1d07407940c030b0750b24001c2d1441c0124000c8681d036080040c01d0051a0944000000f070f80c42c0b50300202c60141e110400054102400300700d01c3d0f03a566100e410028040491480e500740340340128043d5090b56000e13624035a0414103c580c82c0329840b40f80c1c1c0100002c101800c00701100e02c421546034980b160103404103403a81c42143c1c10581c1c0b4200c02858035418482150310411806100c95001c3c0014071007546040c0c80003650340071b0104d860040c035485152030303001c000e0307a0410180200000c01040204940b60304044000740903480c10041085001808a6000d500004400110320016914074062681c0c00314110040d400043c03140000d0303602c1d030f43d0200b03060b110079082c02e001e05140c01c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 402846591 1250 402845341 402845383
    0x271407052b0c1709010603170c010b0a09020c0c010914040e070b12070906021207020118090c02070503160305060c0708070f0b060907110c101101020d0b0109081f090f0203 75
    0x10580d038400000a07110402c2c0c2e03854a035040000030f25104200c02c4011010354040d48034071104909c0c40c05492100002c5a1111040e40d0120b1183c03525400792a207001800201c40c1203219003401519082c1c610300900204002c005210a1540f80031707000b04007001c6140044d84d00150741c5510240460300503044880e180075801c01080029540605840024030192000f001d19080489100d40603120349040031341000040255030744c0301b0a009550100810f02038908000c0248141c00c000d4407003880c9c3c01514828040c980c00070013402c2a280076041525002009024151107606600031281c0c0300031002c9648500a0110341c1c0403805d0544100c040e0381c00f50040c0c01c242c0c600402000006000140b81100340070340d82d966100180300010380b000300507401f602c1d40310040807092070940b0b2004511101010340c4d0b0002074001080b85841d04144c20260080c3c0718840c40356100ca40c030a86500c0950712140d11901c0c4c54405040e441003c1d04801503d6000301d0030308841c4032113038010906203200700000c1038041f0050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 402847841 1250 402846591 402846617
    0x3020901110c0603011505091f0e030c06030708071803062c0a030e04020903070f060f09080606010f12050708040311030f030c13271407052b0c 63
    0x110814002140308035001c0d0051648401c001205808107019107005042180655000c6c01d00440850f403044000418100300e02c8101040303d182417503441c2020700001e003502c20102e02d5080003d04800c0e00c2e01c00412407807c5942d140011101c800000341071340104069014561a001c02e0341c003211020307601604020445600302149036200c1201503109003050041c402e502d00003000041155588580c0c140b5062001c0821240000c0190044510003076143c00350b513000040e01c020140261302100c40d0ad40311069161105401900c01917200c0c41194002d0b00140c000400541c400d52204516140350b0800d840b1150003814000304548040b070790200490601c90130300c810b160300aa500351408103503100131860414016600e8415010103086e05210080125844107080305a0100001400c1441e6820410814900d40b01e01e0380c901e81032039a2812854a491400c94a0510302e01d00d100d914991100c502c0e148446102d25013400b10031012140c034980a000d6400f14400382d005c1c400c4c3c4250303a5666100f000e121 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 402849091 1250 402847841 402847847
    0x306080a0b070219030f09150c0f060f110405030f0109021305130605041401050903160305030402040b0402071505071806050a0306170a050c060315150c0109121107050a0b070602130603020901 84
    0x3041e0058231118160700d00700b480c00d0364011320b041c207419404561540b001303140f8507000014101d510801c0e0805410008054050701c0301c24007600488804404039000c0f400c0c005a03282c225904080040c6d044600c1c000d1800c1c5001b0540c001a4000c25000c0e0030540c038000300d486100446005680c00c071555400c80207800c42d03901090040031303044001103026500d8203100300b825003240e03002c003a0002c1c180032020000505541d0303aa40a28102c40703004c0c1040d55180340c14904403603100b008081004000349410003086842e0300c2900d4400e600e04918001c0e106240c02d040e4255119005921040201501c640c0c01003a15483c07202040030034003100c402450440d4242c500703d0f042c2016440e200e0f004440c01c0c001c0080b0300302c0306610880302107020f070303601000c0312000c2c12044500c0c8610b21540401e5800c00c110403080044031241e032421f8003a147d684498951402c0b40b0755480c0d00e0b180c03082d15400b80450310706102c0c2640e110000c0080b40d1080b00014030b0025600121100314003d41d1040300480d5001c1009603095070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 402850341 1250 402849091 402849107
    0xc030d051609081b01180305300703110a02040c020c011412010e0910020441090c07020a0e0a3e0405061206100306080a0b070219030f 59
    0x4650400d6809503052024990391240d180b8140300300c0d4445015101384070390095140d5910700224404440d00b01d80c9070b080482e078034281c10800142c001030300c0c20103010928070500000da070040c09165807441c1205c00e4404031042c8002d40c0500c1554040c01c0451801641d41d403049840c80c46c0107801030034007840c005002405a9000c4008016103200810100c900b5800d100c0209056030080b104c0f03802244c440e40d044500d00840000d00c80f02491001401140303004d04490f611480014400d4908a04412407442201d0a841d100d01c1c901d5212062001c40a039207440d8511640c401a0a810380341440707a240c0000e40c1c1028168020041520b507141840318580c40c7d401024401e4072040036100c101c00041001c038800b6250020b181000b0000251210301d60700240044a0041c08010205a114905902d245145c1d1000f550028410a8442c001040c0c1902034092031003103402c1c0d4000b804040c0256110548006002481841103028075642080c180d5902544158424081e03070300c10500c0041305401800d03440d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 402851591 1250 402850341 402850381
    0x39050706081e010905040c030503031503010506012606012609010b03010506030619091211070e16140f0c06040c050f10120b060d1e0c0c12050c030d05 66
    0x228055040d030645030b0b002c015541182d03805a8001020707a95810b1044581140c0e0704010440d00001081c4062000d016071040b18240c8201c1c020083ca40381d0f18010740d9403055040125001c0c40341d8148480662050818547d4800c006040441501d581c0400c142952500c0307500074405c8200b50414405440000d10600d9255030302900200020b08013200040d5884000400c2d0b4003158601c507070b030003201c881c86800001e285540040d44500f40414100e02508412244150008034802c90300f00081141c44007003014040c034013840030260741c0002048101d0310340103d110b40400c0c000c0e04110007450340c074071940280224810380300548403608003407800c20320044450340030138450003180c100500140c1d500041002e00b2031302410040280352a58a90700c01030107859000c942d1041000c2080d80425a071034224204100c8480d0f03840403051007030501081101e14801c0c002c40041d00030340e9504000f03001c40c0115583e40c02a400d0141c00d0505010207149168030032681c030b5400301d44a80c148001c16650020103204c0c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 402852841 1250 402851591 402851611
    0x8010501090209030c1311030f16020a1e08091e120f03030708040f0507030302061e160c02060f0d090209010603021c2409020a021c3905070608 63
    0x5120f00e80041d50310008918924440c61200c000e41101c01803550040d0b12120400349010f407681381000d4041d154502c1200c841e022034100d40022189a4400708010400356031100c00000411080e49403407030300040000d000c86442104000012441e1b44446060401c0399054030080101000c003424032000704224002c02d090f42e0b11003a0344030605031000c800d9a030710031110715001c10703d650f81c3d04140880000740907001c0c126000b00307100841455408101603204814009407070030000c030028420019a00e04a45803100104c180440e00c031521b114034016101c3c00c4c0024406410005c240d100030010341d10010400e0051640c42c800714086040840705103005003036a0800314104074504003040e0306280c102c41e00154190f0740b8503c3c1d4191200085403c0034500f820048101c280c0e03140c0c3d056030025840b83c005e1001510656a00060590003070007104007030b4010f0381d201841c1c0050601d0500000c251007111504000e90044113062019100310f20302e2000d40604000c1c4400e500d0088040c0c01c2c104050254070354 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 402854091 1250 402852841 402852847
    0x360c03060f1406160f050c0108070c0b04140a0c080a03140a05030a0509030f04140405010519090c030216030c0c0806012105070b03040804030c0b0423031015080105010902 75
    0x40c54010140941840d2410303a003d6507900001c0365503d44282054100030422480c44100d68288807002a81d12400c560a1700c0e0b9050b1a15800810b503811040b07200003c01c6240b041c1c0c0000d0008940d400c0200d0909441000c8035860031281d03480151b803c180d604000140c2d40887c1e40d28081c91f0340203800011010640b0303081c2e072600340c502c4001882c1e448020880b008441c1ca0740085102d4000030411210b425581c6424140c81d15100d000f07010b104059179000724807076030514001003548e1400303030581054083c031061150100da261074080000381003081d5061060603802c0c01400f841001c06201619101e1007944d4040306100309140010441206811460080e0b00c0300300103011090101d2001445400400d100c000750700d08901d825403404500750040000070b41f01209110801064402810549200d42c0a1b11105610b80151036824050380c842c0e07001c3c103034a4600c5200c05140080800346044805001c4e2130f54600740e0301e038140954829000c81d2031820302c0d62000300080d800038804c0c0c5003d48089541545 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 402855341 1250 402854091 402854099
    0x804050c090f0609061216140405130b07031b0c050d1818090c0923041208090a0506010312020f0601030c0605030601360608070207360c03060f 63
    0x956100003c210790300620b286008902640e1710991444040c41c1080119000c0034002852158525014812010820101100d403191880c0501520384544016250400204141e450743c44000c45d0107409101810f07600d507a00e05903030404c0c854100c103484158440b141c2061481c9001d0340307401481d20090081248101d502c4c80c003004e8040040003100c00d0031200504106580c0f541800403d900d030700c0141086c519240010b000c003055001008214820041000d000340182002c0e200b0f4032007260001e084481000d940181d0074018024140c1121951044a980f0307815980c0d1249486001e800036201c0020406403202150b0381004546486103103940036000399491956111b030126100d01424045c814003000049071a40310701c0030490041040050580f0041c5400c0200c4004000042000c40104c241071012400c7c0f0f024070b004500441d8280c0c02010010b02d41321110044106029041031214081100c00241140102c1d0f1007054607501e07a00040c00a48184003d0308031511743e88180003031164510104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 402856591 1250 402855341 402855361
    0x2040f0e0f061005030601050d020408070614040332060910050901060f050411090d06021908061c050106081e161212030b04110702090c0c03040605070f0804060804050c09 75
    0xb04042e051420300c681c981c6c0312040103a800d4014890481c4a0350310208000420160000d81c680465015450b00c0302102a000d4007500c2a00c558000909090704001041cac040c0280c080c3c01c0d248401c02800103114029142c03181d80e0405400341c0c0c01c2503ca074005211000c0c02d214511330304e60003800201c020807020303141810788802186c3c14815944901e0780c5075200910b00c802c44080340e403441802070011814030440d18010f8000c0d0401c091440e44030106003a4803400c1030064940c203002d101c0040508006078200e60303c490b60b40201746412104c1d9501c503103001403030340402c1140d411240324100e6201e0b0301c1000d41201038a04018141e1a05420f520f5640802c440040c4851600301e09030006808041c02011150681c040e0071400180ca812030316149071500350b855a039021740002882181c02c01c0041d26003031081c14150040b4400341900c1d8204100400545029400a01b0124460401c0c416621100e40303804806421551141d0080346400b0b040104002c820700c094400950708543d00155130809031030341 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 402857841 1250 402856591 402856609
    0x1206100207090209130903021524120a05010204142e051b07030c03060506031c030209030c0402120601120c020616050c1b0f04090b0f0c0d02040f0e0f06 67
    0x42d8120a9000035240742d952181d404600700002158028001c4030014903000395582d1142c0d82000540792410b001c00e2801036000a41c0100404199210030072900040c00c10018046400c0484210f200309514103000910a0029000600c0281c0c01028141440d005000144441410495640c04000c040c81401c4003148035004007862145080d0b0f489054038001138404003500741c0c102c5501d00c69964008100040922504240c80c41030030184004d48900c0181030340d514008402d2288020481510b0444a100380d010b007207100001030848107055008408181280e21803a40d140724a81007104000d1b107942c20203010521244100c00030440001d0b0000025290100a043c1c0b903c42c20a41140703802291144040d540048041800c6c0c5101d04040040f000c4d500840101d47e03800341c0c069066204282c9024840e04061030303004980f041455030f8040742c01c0b850342002800d0b0f0400f01803d01410164884920140003e40000d40715122102d080114003c1a5040108079040800002c01006030684441800c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 402859091 1250 402857841 402857849
    0x13111309270203030d1b0f11150c040504020d091a010b090f040603020301020a020703020909070e221202070f050904201c0c05131512060609020703051206100207 71
    0x300020505042c03000074118401c1e400c001c0c000c50704145c4203801421050305605414042c544a150411680c00016141c149881e038444681d60462915000d0030508480b40960291200100c145059201d10001d022078000a040c000d00d50380c1e07400144204401c02d81c007902418040c07a00408550f00d4000303481003610482c403000c0d0094042c0180391a0030780303c82c2c02c0704014641c024025500da021032000250340c1c110500c0140d1040c101000030603030303680703000c0b034101c0943c1c000b00000c581d640e80e0765981480159500d12a40e03000c20461a041000c68040c0f11401809003c660150002d40d240c00d6002c0480341d4607421441c0300e00004001c1c0300010381c1c0d804510580000c010002c4098564450000c1d141c0c410290300010407182200b8030310200b1041101400a480c0215070322010b40b6241500441240ca03017a04403008681c811800f486600c0da08010154980e11401d404508079864414003820b81c0c0040400303c01041000c070741307110883d511013010f940c040d405442120b600c5c001084000c0d030b58a41841 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 402860341 1250 402859091 402859151
    0x1201060e07030e0304090c080a11041401081e010e0702070b0f09240d0903020f010e0303131e082805041520060414010209091513111309 60
    0x83c0003040010034030030b580042c42c1c6e059040001c8015510098000101181c2d0139960500d04032402a0200c02a4151030640d941c2850400d039010312080191034a01002c0c0030240002c10f82551407030011a4521540d02808244041d40c8060602e000e02a2a1903010b40161401e4102070000b8519030300e0040917100c81c05003c0381c0713201c0701040034141c01d68030701c0504800e94552000010040c0c014045904110341b40c502c00d03403c4030582904141014200e5042c441a141c043e003081010a100d040214011000b180c0150f64205a0010200d94040c46490706601107940c0f44011a51450f1146019030700c040da401d8030040c0c2501410390348402460791045002c2c0c4495007001100d854181c0e1311459854890310342856140e441c03d4810b4200c10b0ba900c500f1142203912480c4804060301854041c0262081464058030388219600c1e110300c24070118852034011500300781d54018a035280301d094003c0142d21070912030b5260b0b0303541a82c0b910107180c03441a0020031107681408010208084c0c00840007a007480054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 402861591 1250 402860341 402860351
    0x31406011a07082b150503060f0a02030402030f01050a0b0a0b070323090d0807060b120304030305090f190513020a1223090c011d10030c0219111201060e0703 69
    0x8515261340d50b04071040e480e000c83d01303415000c8030359680009001019001500c45859884040590310034045076059560004400130030300b6010550080c5421910003029243c00101c03241e8181d08440c2c045810340200c0f9111043e501d42410404c407070a000d04040f1062a00d8008152005002d10888100312840f0300602d01003140403d0040003650481d89008100c4a40b48207141440565034018080c01c0da0707440d00e010114102450440c120020042c1010080c50915155840545007a0080515103030044510a003a1800f0703035031794405000003810b000c0e5540e2568244002e0190040100d215001224410003244450343d410405801c5c2c480d170344210200e07000b410009861b0b081e00d07003210103c13006400b1805014150f540030501c2d600840303082c0c2c2c41c0d0103203000082101c07040810300c50026130052400e45240400714403d812026107113034640119a81031203004490300d02d6101d06541603d0401107107684030031610b44204500d10300c1c2c0d0048001c0c010796050061f0201054806031a50b412705950b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 402862841 1250 402861591 402861607
    0x2102070b040201230f1b01020304120f120e0a030201110f04050405180a0507091118040527010c1409150304050708031602010e011404050114070507031406011a0708 72
    0xc28070400380384200e84c0b0b60358451350100c000404a4101e0800484030100724259402c1e0742405100307480c41190040100e0460300080d007400d03540c2d044416517200c10440400c40185030600c3c03d005205001074010300a02c0807050a04009007190345076101c803c0310303000c10800c00c0c09004500040d039080e0381040301c000507152945d200f074022a41110040c00c2043c02010004e4041c401c001c43c1103000c13106042c07400c0c0003510720034807448160702c01c1d16104665003070701004819a07810306501c240da005500d0f03202c04046640c403050000d008038040d45e00c80b1a0760b45481d152800d0070340c0b120180d01400c9205440380d0800518400243c2c518000c1d520312095001e01000041c03c1c084100a1400202100c1e01500c0d59500e450401607a002c40e4000183d020070420078111185501c034544003034921100140c030300c0c101400e0030011507078040340050600b4415014000c50010a1091200000442c802c081ca0b204008280c0f40d15400c00b141607006032000c4809140d808240d041d40700803242c00c5603001c0314241e039541403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 402864091 1250 402862841 402862877
    0x90f05040f0f050702060609070c020d03030e0f07080708190c0501030c050f180a170c060c010b130f050609010308070209070306080d020601231f1b032102070b040201 73
    0x403150a4031042e824203080c071040f070b50080345103030048a003542e41d10b07816651a403040d602800c400c20300a400104031040360000c01d209520103040307000480c041e90390303c1010701082841c00045800c44e103025009141c0802054904002c204000c00c80c1c2c00e0301074181c884a848420b07a43c1480d200e00c6060640740d13036034006178612030400c9504075404406e4041d119401030381031141c03400c0ca9001050180180c2c0001262002c5051000d500c1103c0041c000c040c3d42d03280f04103010890f0455108a0f800b5900c5403c6018a561401821600d00600d01c0380000e0360f8610300c9180f010340c0c6000c2c00341030155103401e0040c40410b02d0203007100c07406038043d91803000da515001030440c0100313030a6000751020300840038070400c0c4550208005048400d9a201a000c030040c4068010b1121003211000361321120000061580342100e00d204000611542012119001c007a11059210001100d007180000c3c4001c0d10040304c110703071540356600100303c06070441c14000b095036800145000500041d05106418507803501e070b106 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 402865341 1250 402864091 402864101
    0xf0f030e0a0b040f02060d0b010305060904020d0f150e010b0a0f06090b091503010b0d0e03090a12171216020106120b4f02030d05130e070e0907090f05040f 68
    0x17901601075075a5009258681d402040a1340b07140c0d00207803c10002c0f51403450800c09682c007503600141b000055040b266130342d030050b0420000842c1c0c0a8001840600510590b11a4012290b0f8000021840001d810f040081d056a0f54108100c032030140002072094503400304900050300d201d40c1c0c80360b54490303407040001c0100d040b403500540b02d01c10000021500d04c4000010b00301c8500d003c0c0e02881840d401d03040c0c058403801200c2d00785822440310b0b4000c0040d2101a41a0880a03025412402e003010700508c0040b0f03245e2040349080d0208524002b44200b1042c7d151034410502098070080043c1750030320300742c80450702091502828040071040401c3c0c5d0118102e03070041c14442c4110240940140300340e121001c018103141000c48404660154130710012030780784d2145956a000380034010408603008181c03082c0d004040c88014407407841c000441c0704002910114010809900c0354a2040d0b000320401c040702400611500401140600401c103401c490400031b0f0a99404176000308018a11680d0103008007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 402866591 1250 402865341 402865343
    0xa051902030706021801030f060b180103090605040f0318210203010b0a1509050307050307150c17030103060501171e010f180506090f100b0111030a0f0f030e0a0b040f 73
    0x603200044060f076001702441e101c0c5000000783c80600c0183c5910b00e0480490f806486401405941000221031100c80d4020300034010405040024075040b0644440c002c84004403405c40f9104061500c4000741a0801041e2004040d405a0201c0003800e10308002080c121451541e07210080a14082d0115642034124003041080038101045050b0795182007144c452010f6024008111913182c00b00b541e0a01280c0141610030240041c80428500300b030000040e80b001c15803100708511201c44e00009007180403459036070405500d03019100c3d415420088110356060740014044241101c04a9200401080c840001c10000841000000c0102c440e140540011010803c1c101e00d0710a10f035008048480e0080302050040003211a00d5940010781c075038032208013103103020b558040360040944a0043d0800500002e06260801000b902c034150301e859a00040c0c1c101011949031504050020f9002c0f0ba145640880d80c64280304041e00c00d01626200d00355100040c004848280016007400760705020480e4803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 402867841 1250 402866591 402866603
    0x90f1804030e04060501030903051801030905030a0201050402011b03020c010f021c0903063803031b031c1a0d1704080a060e06010f1401170a0614060a0519020307 71
    0x40c5468540100514072001c42940315901d0503101213110b500c280b0a50303090305c0d41502d0703251806002c0fa810b44201a16503591504040d20b42c54400009201800600b444560603000031800d81071a2001400c40e01e41c3d001c64000d06d800711500c0c400842e0b4001030f5441102404e08068456007e4030000701e0070f10a002e200b0b078048a080385149983e40350310400e00c0041764000c41003002541600d2174007000d410383c0345c0f90070004403c00e00045000d5040e811880380d5100b80042c212460200c040c48260003141042c1c6000e00507800100d01602222007a8014440303c03410030004011f42c043d5800d810311179440c10038401d4040c0c1c51009107907007081142d041d80368140700c02120058607640d07100e0b101036680800c020102c884038241030300c0e01d481c1c1c40001003082c103803020081d00618041c1400940740d400031314034020504110b5020491000703501c44c40000c5025403c503040118140d805c010320451484448082e040c024102040315145640c0e020003a00d0342141d41500b40e11504078800c03412491801b8861002e451 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 402869091 1250 402867841 402867889
    0xe13060218030712050f0d09230307060903140d0915090f0e01080708030c06010302010e01020309041505040b180a0b0a170105191e021c05100e060d0503090f 69
    0x1000a030303a84d0001d5400c0c81101200d0016001c406050f444640240281012806400c4240322016509507070840102207480001c55042e0043c00092510200383e0040011494840050040c0070906a2501351003039150000d00340700c0c940540041c0120507520482880302c40040d270000100740b0440c0e01d00d0003010941100c4074550344410344061402028458006140300e400030005a803400030095411010303456001d042103a103548c00542e81c0d0080d40340300d54118001000380e82455030b0b40f4440c0c465a400315240114449041c1001d2004960070030550900c608a40754004401c02e8002c4001d41d8040c041020114001030403501040401420381c100311030407800740d40024041201580250b128000300542c074002d0481504445044885070041100c0c207a58040c541600c480843d001030105607800252403014002c034607003650884030161030920981721300d802d0070008014291440c5411600448160060340d4055840d5642ea01c120140107028910108045043c2d03564034640c00c0f4101e6000260101c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 402870341 1250 402869091 402869099
    0xe0402070c0e130c0f1e08061b04090203180f030c03180a08060a090606060903120c17360603040b091905060a0e1c1808031908010e130602180307 64
    0x2525415000d54104421314014071400024580e943d1b00071a2141c2000d88041d484001101c826941d1180041c0c3c00d080d0100700015040a07203100541c4900c14003d868040315401a0b603060070014100c0e82005a81c0c400e00410003082800300807104c40c1c2d001c40f40000e01704800780c000b0400b00521540448000e0003003004103c02821280c101e00e41e100e01c00c8004110a507200d07401980c00a119000c00b41c1000c41049035040124020006507141078007a1451545a00317043c540d441d5203601c503503914607040444030705140030034020070300407141c85a070850000540014400421b0450000800c00b0384250301520104400e03281c2400503840903070b04602c10011801445c127285a880c202503c0d030b80c0341d480c0351507407201001c000800c100383c3d1801c0280136094007000100d0300315549070742d0321038500300d00c0701107030000541400400c020a0b4490101000c10800349422a001d070806e40c050f4003108a082801003000048070321203d40d0408250700c200016145e681d42d0b201c11080c0d0f00340507ca56054868800041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 402871591 1250 402870341 402870359
    0x605010e0a050906100308071b0605090a08010209060702100306030c09020c100605011e17040f1209030f030503040f06090804150c02030d110f0307120e0402070c0e130c 74
    0x41c8a4581e89200348055100c505007503035540012154042d007040d2600342400040c1c0204010000940541c3c0544d101d6011034060802c00c0c46170750302c1030012800000d01a001400c04510340c03001004007400842c1006402400300b0550300c1104402841032040e0000304032680e02039030040000d1900094203215607500c82c099030000398048080d01c1c0180c0b09902c00c1032004807003030041300c0680e0410794503142c4101a000761480321628807920304007403140030008035821444000000d8801d40c0104000601100b0500342003c00d481e09031002810045500350600110f00e40e0310001901591518045644c1d550700e060056054402a000500513418012000309100141000d4400d0301d20750401e81c4041c2034024410764603440007041c001d401d6040038048100c442c0c0540c50940e6442c0c2e800040c0c1e02c52100c258100c504642c03146104840c44c2038070b03e001e1008103501c4403c00da116202035500b14070b08081625441d145403094420310a821804400040c1119002000201d15a0b404028840c2050b1103c5000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 402872841 1250 402871591 402871619
    0x140f0304060e010909020a020706031505181608040b0103081309091101090f05010914061c0903180e0a0e0f07030c0e0a051308180d1202060105010f0516050a060501 72
    0xc81c002070344d006003c07400c00f1051080b1800000541c00a1040340c0c40c1400a4016100010b480c1d07100c407085640002e00381d03d482c0440c40e4503481e1050580e20500d01041c0a03441d000c00000c555040107924410000000c21030348040303040d81c4d0045811500d0329500308400b0005945508002502410000d480342000b94120140c03d4144098884103c02030700c50f01c0007220002c042c808c0500088060b00e041002c7c00074140c8840120038060607861174840340460300c000c000030702201c01d09687c1d5904290414035038007480b40d810003203059090800c114903000c07210101d1400030701701d0780400340da603042580f14000803c807031b01101d01c80005803034401da62420030300e544804e1403203440780c101d25031000100103140c40c0c4605071081c104120b03a810010302c242c0b030702c2885800440c280b80c1488003c0e800868255a1240d4200005214041413100d10800c441d00904200b030613405281448501c0a4500b00f4a03003000594a0304003a8808129911040d402c04030310b8030800c10000341c80b45242000202c0e560b0550015 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 402874091 1250 402872841 402872867
    0x51606110d0c050309030706090c09020a05130608071e020a0b16080903030606190e040f0b010e01020a0203070510020705100302041703040b070b13050f101512140f030406 75
    0x1040103056402d40b401c1d83c2600c000c984080007034100300a075100040c0b150740300d03291950007250555810354a0384d0810089a114105090206101240b6240b0300c81d05611071001800852030040300900740100050240842c2903842c030103040001900c490b50900c200244210700b034000c506000346042040c00f190100002c1e2070054002409100006c1915400004890041b14064a8646840f11034561020a094421064401c200100120032002c0c6d5543c090902a03502207400010100c44640014101142d410142c40c10754100c2240500946e0340481c100b0304036241a0343e104011130043c1422820101a500f1050380a403040c01c50340c414903413607405007080c5c6001400320351000740010f840746e50320b0069200d40e00768004100a2040010918032009030050040c18040d6203401d403560344c1c00c0c20305140115a0407181c0c00601034100c030640c0c600030500b003000c1c0e21605006403402d10b900884076010000019084581291074581e00722410400c4e40c1030840b0680999442d00d0b00c640c1c00601007018885 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 402875341 1250 402874091 402874117
    0xd0302090a0608040b06010503040c0e0705040501030b0d020906040b1c1209050d0804060f20010e100902151e0a0309110915010806120d120608060f010605160611 71
    0x11002c100c0c1c902861080d8050354000455400917650030b001120b80303600050040707440228401001920202d1101402c0c004c80d001d07120300e40c0751030a000004045415260780c0d02d205020031f42e4000f0140e1141d240b05504aa02640c0210702c5110301c03400b0440d00e40308000e03108113a801001094052100310308080181920302d82d10010b01c250b407502040040d03c0650000ba014180c00c110400140d0301550780c42c41c0d5150941841c4040521080c0074002e50174001e582c480560351543d01d1118114018000c031702c0e801c0144001003080255503000b0501031141314504407510100011500b96032216150500055190314240d180c0d1021030520007005072000d40811240007110920000d50b1f890046c421511802c9900d00c0c1400d01103041c40112000c500203482103800052141d005840c420040c0101941c6402a841360300380e59035a66600c04c00c4540703590101c01290403110030300c000c1031422107082d030444d14980340c400d4403043ca8030a40d072038408843e00d009106a16005804030441c600d01c2c0170303295001a070b035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 402876591 1250 402875341 402875359
    0x10050a0c02060417031509040f061d070b09030102091f020c010e091f05040f0b12030702030c130212040c091a0333101e0605070803180d030209 63
    0x58181ea0303814041d1001820800e0180d1350808022070f10f40615403111648074240d41a81c4c0000c0482d0000205035030980740100e81c401e291007404010f0050101d550400c203120211100282d490603115101d500540ba48900b000921003e03941d4250141c0d0386848000708160070791b1062040107980c142281b000b01b005030007a07094070041903009401c8807a800001a010819595070004006010701400c2010f070b08220b001c180100301034640b48660256200c2c0c410b400500c04a40d80304001b200c008949606c01c50340e008010034001030302c001c91b4180c0e26000555040e841b280304100e44030f002e07000f803c101c001903180746c600b040305000d80300303103040c01b16a41c060041000043e0500050810307600e400c1203d400d039012081307043d68010000b05817480103840100781a03021108031031040e08031505440140c0d641c00488820310907004000040c404501800c003200c90000d14110001c0c00c140100c3c04080c1c071500000c800510a03a01c001c10310b101d50b20398002600d07822040500060b000f50484000e140c0502000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 402877697 1106 402876591 402876611
    0xa020d050702360c0c16031709060f0a030209040c03140609071101060311190e0a050c0f0d091e0302030711030c0a060f0201140f0a0b0a0810050a 64
    0x4051059600c0c07034154002490800240321303001c0c6d5901e0251042000460a080d070004401443c0d070b07195101c801c0400080c1c01806816511189658001510030005500d94014120240211410010b9441b1080200c0881c3c85801a0b02062007800011950502e012800141e000700c1d1850b0920200720103c4030704d82507450a41c011560039101703550b025160b1400303581c10000701c0801c181d14030340640f800040700350800024003200910791341c81c07000c60305030f0300c1d42c0301210f007000141c170042e583d03d210040405008041c0e4aa003612500401c0c0e01c41c8070340c000811031820721150981d00450034030246880c1e100035614881c14650b45441100c129000365241c82503658001c041c00d031a44124100703442c40103425074403a95a0440c1115520080180303003054040210340110100c180012182016004100c607440725401081c01441400a031101001042d00304074810645010240005131007 = true := by decide +kernel

theorem cover : BRFrame.Cov 402697841 402877697 := by
  have h0 := BRFrame.cov_init 402697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 402697841 ≤ n) (h2 : n < 402877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
