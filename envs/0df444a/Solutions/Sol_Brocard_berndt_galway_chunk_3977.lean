-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3977
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:13:49.72207+00:00
-- url     : https://prove2.me/submissions/e6b8d234-dbe2-43ed-8d98-9cc7783c206a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 715107913 ≤ n < 715287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 715109163 1250 715107913 715107923
    0x9130206164101021b15010e072003160605090f03040b030a09020613120201030506010e030d11070f15030b09090303041b0e0a09150c020c15040b0307030f0c0c 70
    0x151803401020b900d041260400448650b41d82400075107019040b981410703102c3c0089001030031200381d02c550740780d4001c20f058000d202003203000d000744129207a104039000c03200c46181107140c003c004400300c2c20b030451054001c020018003911031140180406030380807900912440080399031038004c9981681e100e008a104441103040140001010321440360407107415140b008180c1440c2c600000c100e00d40d560140d4100c1112020601c900b83c0c01c5507054861607030400c800b42030040600001d00c0001e0381e030380740c840010740c10004c00707040d03520054034100800009070408414003500c0a854080303800c4481901621940042d0406911007038500f008a0000c0c000e21055005c0c40c42e40c1d072507803140302c0952503002000109031055540020310746884401e00d400751680c808003141c03101d400d08010b400c0170703925400c01424511700303000080c0041c5c00140e2090140829a9482c0c12080000400c0c030041c01954006030001000004004803240d1581c00360b00d940072000e10030001d408007110202e0789290182c0340100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 715110413 1250 715109163 715109243
    0x20601060f0909150842161806050910050309192117010603090803010b07020a0b070b0a060f05010504051e030106121506051c1103030a17180307020913020616 70
    0x200d0b26000d850031941200180c01c001c3c030500d259141c110702c0c4d00d48549c04000001c501060308121071819005030141c5484070f15103542941812140c20b40c507041c51180e00704038910fa10008004128a82c015004118484514120400c003491000b4104035460740c208512841481c00115009000340b0990001d0342d004032066085a080c1844081d142c1d002d54000d03030b400340c0c8405000840110b0b820060440c01d116008099032401e14004490641d5115000a40b0311001c0c2141844503036404020b680850f141200c802c0080d00020600c5040000f40c001303e2a099404d0600104400c80c000204035440c0d441074010480c0300e5880c00c04081146e80902420ba03003c0ea4041052120030f1a203440480c045003e00103000307045950400107460f50b0301200d040030101c6c1229074003616100200c119103a100020550f2110f4100040b10311580301d20860b240240300311541c00100f11a15806000700d00290340c05130120341c0d030308400300749205401000881101e030174200050012102404c40d00304804030040c200201c0e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 715111663 1250 715110413 715110421
    0xc1207032d060204090b0f09060d020d05010911031b0a031713140307090603080426240703090b010608190f0c020601060f0909150842 59
    0x71484140094103220801d8085080ca001142007030075400d552081c180140c0c2c50340740101030010340b950711480500c100c0403050101019217070100740c01c0e4400011034120b100312082d4030000d4a04a21311038090030075840d25445008000d4082100d564040e400c5045400c0c003c1242c0f1107030f01050240e000581c005200c08010400148801701c00505022251807040c1010814542252111641d500c40003030210b030790550750b040b070905000000c06070040c40001d004140c01c42e200c42c3c1d910720482c8951000340040805042c1803000c2d905800001c5802c803002c0d603028240b562041000c109d4a403e0002402c48440c0c0030a20039402882140c5209510169038442a0320340001980d20003001841e80c03000c203545014a5500c001544207481003104d40080000300100702840091414105800079420310024500440510350070001c0041122401f0101044007101107100c6807000646034058035941c4285048500c01c8180152681c0c86480603016151460407151404546101d2200c03c0740008001d10003c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 715112913 1250 715111663 715111673
    0x191a0313020d0f03080703090b160c1e0b060904020d20040e0303010801111e0c03040e07120b04060612020d1b090e1b090603062404080c120703 63
    0x15591059050444a025010369004188480c1e40c084003110842e030004540d9003007540010700d040e08005580750800c1300300350b99903400000800c0034042600c4c0925140c0030b01142131203058510b00030343d807240b106070300350220340d0b100343c2151151101281e002000d003001500314200008040d00c9640c000340300b0b02820001c0e1704c2e2041c1100c08044619092440b2507100311094803603000c0c0e4542e40c5104002940c4d03035031402d24110b086a4030b0780b1006494020400030720501081400c501303565961510709940d44c94401c100e0b4585144100d038060341d51040c040d41044032498000038100d526450101c02880410340c4901080100c40160191401180340d0968140b1140b040b13902510021081d4280002c4030b82a4a805d070aa04031501020000070f01452001e0000419030750080e508030001d00c1c8060018034004c1c022074040e00039810300902614010000460700d0380c40c1c480d640520f415000503d0524a040041a08240e1250182075407900c100800312007a0709018844000d242c40309405000c2c01401c550718 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 715114163 1250 715112913 715112917
    0x21b010e0112050106020a14071d09011401172e0b0a0e0c190c021c030e090414070b070206070b040c080303071218020306070807030905011a191a 64
    0x1103041040c2d8007030005082c902c0b40700f001d02811040d0010002c0311064644800015130030481d441c016080500100101061100c107400c000c604081101050380d641240b0500408e00ca00000ca039103040f0200024040c50400f45401b1b0740701190064592012400718680c51213084020050004070600c18824101c26141d4032125002900421b00c008072030351003414404407441030b211156692170015460520510b180030280380c800560401c0d0300340580341d8000543c4da15100c002103081c1401c1031058410184039100310307003c0500042681020f03080606002280910006a5000c2840354640200b80c04620400785c80e00286e00404040c039080c210343c1d5841c40010080c20885002c40418000301c1c896400b400034510030300441e603808104082c504080c0c01070750341840c3c0d400c054005030784061001d40c6010801a81c0000603041c0000340d5180c5d01422402030200c0000900a07500e49214400d802800e074196040c643c100b02c03040b10107591408040c0c0c10401d0a07105101c041040d01d241d03060301c03d050b000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 715115413 1250 715114163 715114187
    0x30106260906060f0f0402070614060a0b160303020d1406010f05131502210c10020a08060108040336050316030f1e0b0402031c09030f020a051519021b01 67
    0x200d4030100850905c0400d059130401242280c6468480d074402c61800956100d441e44500c04480600d20703141303000d400b10071074400d260340510011029204501898000d4044642203500f9480400c04040c200410001600061361580d0010700411042000079204100b561011100c1401c0c4012007450007542c403519070445c9103443e0070350182002620380f01040c02002050a0614144a55940080c4048606004100807003125071481444200d903403d51001000303522082c01e08118429464a0a05944440304111010150500d02252041610b010821030380540381443d071415049440f08100340d1149111040c41905000c1c145c001c1000c90b880d441c001244078060b505d6140e010508170081006405151400e4910007159014841103007001c2000d1720181b0028103249a10800c1c00710b0050016425110207094410990191410340d501c0c2607003000206401450f020040100d0712846c0c0300c036013080c101c8861102d600003a0081180c00828083d43c00f0042245488411031a000103540b9449403007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 715116663 1250 715115413 715115419
    0x10506032503050312010311011409041817120603010603050c150d022110050604051e041401170a05060a0c410c032a03030106260906060f 61
    0x1c0000071542c1071004140d81507501c02002425811420a58030408120828504114100042c1803072050344a0070349969850459003c1030002c0d00c03005050013407100300c0b40549646145c033b540b500c01d40706450003040f91142003e00311f60f0a0b40c45608060807550349110243c92500180c50212040c030706a00c42c5003c818001c0451400c11030382c800c0c008205c3e046401c0b07800c081d98000c007506881009140346154001d107440304410000341400c0100d051030080344180d500860500e90a1450340d641c4c820769000207200a801000340d030100e00c8666103140c01c00e118401c44000c1c1050f80d40d03900e00c40400c0d6020102e40050041a99885080c400001845a070640000b013254800a0100c00d583c10181c1014100c201140390011440603604540c044075002c0d5280c00e402c00070482800b9050003c000d0301c0c255040e0865402d103e031000c0301c008030492070710852018680000000130405c50741011008024408050f280d100d40c404089a01344049401c0c0c600b6081507100b8000101d15140c401001c00c1d943c0009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 715117913 1250 715116663 715116733
    0x304030b040b060103060803090a1502010e060a02090a0608070c0f022b0b13051504080724061202030316021903060b100309030c060504210c1401050603 67
    0x6034540c100c0e2208107403021201e40c03802c10103203c0c040d0f07494041c400240800301c3c091450401500000382100c3c44a00c107480c464203440040d26a82070003136210411511046003501c80340d1624052000080d4011210a4841e02e41ea190201d20144205000362090b2019120003612006a407548010102c1300c0e07101f00d03440110b400d011041e0090080c065186028100b01c44040c0704105c0c035100081090042c400c1001100e00c00458000c503c00044043c5005c0012504071040d4a07039050060700ca00c0390140180102200340d840340c0c02c01b01c80200d000171003c0400d0b400c01c60151124030b10007a822508001a515600074014008035007041e2140c0030032244020042d001c1c8101010f08581c1a076032550043c0c2d030760b5903190722280d458104644009050307810751030200403071690341d0350141900178490806412150b9842c00102040015400c031000d4800d48403180504c440780e4a001020f1280042d42187c00c00c0102070280c0f0ba070030f014090b060007090f008014102e4282c0c1d91001c21014441210981c00304484 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 715119163 1250 715117913 715117919
    0xc0d0905071508040302010c0305220c26011103070c12020c10090f2903090a060911030c090105090112030e041409070b0708090405190e070501030f020306061b0304 72
    0x42c1e10303122050100c068a03801d0092a05040c007900710f4100c00080d5003858141020000030095040300107030302320f000150a05403101d007800c0900114109400101c17109485554455508840c070b401c1c0b1a0658104000703100001440300c00d10000d000c262690400328503007241070000520440b200e170202240b140304a40340d0801200018030f018481074014800700c0c0354002f081c002c60300420b03085406006940c02040040404038800286100010002034003118040302003075100e2010311000c500f581d00a00e041c0199526414502003001c00c1c040060700c01e20454031140c11508044400b01c0c102c1d08010014502d0303a1800c16003c0d90081204411030410800f0030400c6401c0e030b0343d48100481d0031000d09042d0010f141c112031051520002c0d803c071000e1500f05201320340004d0f5100c0d00b210001041034a0200300c5d0b880c0c0d5107500003010551400a0403583c284441800500c0300000c11504488090307905000f01d001d001d040380e040748019540320307421800410112100039989048100c21180d00e50031686081d903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 715120413 1250 715119163 715119179
    0x209010c1209140d050d050a1e08010906050f0f0111010207060e0a030e010203030f04021504090c030e1c050904091703150414063001021804140c0d090507 68
    0x2003601c20200421840402405401d03441c072002206070781e00352803080405499440b03941c1e50354400302c19034007005030006121407858070406040c1e240c03204024016446030341010020b4040700003402420086840e01034005140d00c0c1210000007070210290644000300d100c6001100d518101c1110541c1e0f640d001c002880025151f846a4290303500301c4005009984901c2c540241540c0b03110004c281154414400e02082c0488850003541240e41102c115044200784101d14900d03005a500c17000105107043c2080c2d801c0f98140e00030005450100050b0707414801101501f1045400d80102e40c40002c1080c011891141001c0d4800755541e0f004001c0c42410b00c44100625140394000c80b0401c4030a10f407841c40f0003003800c19004003c0b040d40d49010302000340c641032000c90032207007209542d0380041c0140301900c0008411182c82c0800b04061500940d541d5149c1709001002640c4821341a0040d8a000300000c0700503c8000751500030750184003201c0c60107071800380700f20107040d00c11020384aa014034200040c4000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 715121663 1250 715120413 715120433
    0x914010309080912100510030317040c05130507020606010f0c03050c0304030503040b0c06070e0f0d03030b0901091a04050709050d1407060801050118080c0d0549120209010c 76
    0x1004d10760003800c104142c858a60240c600141c417440001e030f86800c0520009030000c070041c1c034014000c00500120b95460802c920b101c02a5030000c0d802010041d04038000952680045200d07040c03603002c48109481d8240115906100d4002c0000014101c2c2102c0000034481c03402400d140215004480c209a1a0b4603280c3c02c5910035405504d5a03680054445034102c0103200c0385a0103403860400c40713410160500428644280c200c07009108010350b031403040405009a0020101310405044d80c6140e40e10b80c01804000d00c4103800c0410388408540303485085140902429100348001e95803030680c0c5180006103c5030030101581100c5007000117130b4145e5050010440c02e001000b0540e101c09195240c030001405192130700002884040c0201c40a1082813400907400c202c2c07040680e0703107090320701c52810040d0800d0b51064040c8280407004c103a021321103604903100340e03c05014403244038031207420481e120907101000c40d1001c04141c286500341e58001c00c56015002c01241070400713110101d21a55204404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 715122913 1250 715121663 715121689
    0xf060d1d070f0603020306030d0f031e060513051014030f030a030c03110a020d0509040f050c030703110a0206010b07020111030d06170304030f11040605130903080709140103090809 79
    0xe036005032010407580c02c00341d6580b001061982030031440c508044010a403a141c2c030403d0041800100c9420010481c440e600200c4120400f0780b10b52803050700e404c05000074020521400d489900c40e81300e95480c03000c403440341901400034054451403042c9000c0b640b91801d981e500704a581401401700d20707045607d081c8010504410f2650300000e2001102c10082c08036046070320900d8003801c0601840a1040c0c0008558249540324203000c3c0d25030600700c00085c0a0300204503488003103170608040c4290840c5500140d40030321004d8409100064080318010f81070b018031100040180d110a004000d00c25407013001b040010300604d8000380c64000c00d106580b40d60300c0b0a000d035240c5603a401d810410428100f0b040e0004e003180d0009981b48c54995101c0810612000c200540240e07040e14502c83d0319903caa000b0401841c01030140d0807412000d55a510050000d501d090b00850340d8040041d203440d1203030444100b0fa41b000c00c82c4212200385400110028043d020341240d48a000300592222903848103048891 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 715124163 1250 715122913 715122971
    0x109081506100503090a170c0a03080a1d190f06050f070206010b0a050d0b060d0513060f0b150d0902211b0604050d03030212100e090a020f060d 63
    0x4582807000030300100c51038aa40708400c108091041c0005450081041030b00c85411034a4013501c0300e4a440880c046214500249101c0d1007080358640825401c1285030384104000242001203409005c00c034410391821610040c9140c000c482841c29400041e04042c41c2c3e54006c0403d00401c0d4800ea1364601115001e503494002030700319204010100d0380c1006024003410f0a210110b041c00c607540c8004d8258042c88602c0e00c0300179160760144065840c2e1406917040c3c200c6d441024880f07400c01e4100007141d14409031007030b10183c1c107100110701140c005005401000e4070151003ca58440340d1001800301e41c20a90424144a469a84903009a03940022207000c042c0784081000000350322146c80c5141c201c0e1103502560340004030119050303e540700e1082e0303021250140e40f10f0048695a03d812402032040c8908603c1140140302031044240099030141c06503084c045031043d03e92500613800c1d65038001900700a40c44006032803450340c0c506040f0090b001d0400120401719804880c04074180f800c0d43d803010000c41d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 715125413 1250 715124163 715124203
    0x12070306052d1e040b180a0b01020d030b0a090b042306040e0118080f1b010504110405040c05011b14030c0c010c050d0507170304030e1f0507020f010908 67
    0x500c4070480380c040240080312a940e0b016203007070000c9404100200f02a108031340c1c441c50100691107100700f020316079044003001030a51a00c062a0401494184c20890043c860b62240610150191041001002c030081040304010314091400c070140000d0241c19401988686010000e8004200c00040520050074500300c0d620b0b00000b07002c11a440c05a02000681c105840e014070b11101c651070007025a0003005403035444501c10395040c03091182044040689400d03011003074200c0419403140303000d14030a46c44880035120120401041c0d9030266800b40984141540411466004010101c081c4040420b4000e140126840d9001458030208034440c3c603030000200035606103014041d100e2411000d003040a40710665440380b0391f81300070041c2c4420a11400140a00c140300d082d8403040300c045424601113949207002d02d00100101e4884000340d0090040e10351240c40c20301d1083c64000000c459a54450a00d01d06800f0004295038100c0c04506004541d880818119030070310240d4005100c1a0b2000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 715126663 1250 715125413 715125469
    0x140103090807060e01050705121b070b1e01050a182a0c0c17070b070305091507020901081f0b180c0301080d052511030f010911151207030605 62
    0x1303401d55000505640030083c0c10080661407600c60781006411420f4442d4003204162078410314851485081400b0b00304551079410030884422800b12900c20b0428004890307944e9a0b1441440000100741c000d100561130f0b0000600c07030f4200558444040000311130317072141001118008080d6119003403052000015030301280710050010032820400105903e0400d0a8000e611510080d1600c02a00482500712400240707001418824001e0791040480180f18a001d0381010140c0219580181c500700c1c00780550400000e0410004221406901c1c1c400c8142d846084441e40380e08020201c502a843d0f01811400150040c9080024800d02c00d881181d0899600e5042c00c44171490314450800781000c00004010041d401043c2982184602403114441c4d41400345074a4080c403200100f07201141c051017481024804e03620150401d164546c000c60801c107000c0400c03c04d20001310380001107005000e40401850b040c4910b000102c9521950754680010ba441d103680000e1046c02d0240c4070002c0001135450380c3c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 715127913 1250 715126663 715126691
    0x504020c0106170c060702010c060b1c12020a03021b0109080303100501090801020405011718060916060c1a0702150c1801050304020906040209030c040212010609060801030c14010309080706 83
    0x40c004000000d00200a0701c0580e20003c1c0840c41806c2c0003e04118840a0341410810590000720350703040300502c19030b42121400c05a94241800103c1030303404a4007131002000690012072844001d0b40c0507405020703c0c004046003803008202c4182105c3c108001d20300c00048401080c0061805928120f0711500348030719000004020040540004105034410441003000e030f82c206062000c040d01d054032481ca140c1e00c0a402d03036940c503031100c40040d0902032601000720101c00481d105801518240b040450540c1b902c208503001003102000500c0c0c0c4500095040102c603265170b078286c0c000346038811920201180018484900015140c42e002848085104c041410400303030007009800c001c0c43c2090039850305400050300c010b0060b042900803035002070b440011391414030400080c0c2c1005081076590303628000d80c1d0008004244210400100c0d2400b010603128496074400b4101c175000040c0448481c04c009200700c44001014070203050554484140002501c46400f5041e00c602482c0c001444800192038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 715129163 1250 715127913 715127939
    0x110309090a090b091b0d02040b030102070b0627010e130c0b030406050a0b0f12210d05070306030209221e21021509160b03040510180201030509070504020c0106 70
    0x5071210f401521000f4600800c4145c0130f030340303a807084902500c01d080034000b00f0000c00704a80901d40550000850f1310078420000e415030f00454040d02c166500002001d128081c5440511418400d0f0081c7c4004100e44000a102d240d00003804410820307082004c1e035240c0c0c250f104180e00c8061407210100412040c0030b40d42c0328595028048110a0040055100c001840d40e280402c102d840703510844000f44d4181c0040000d0840c2500501c1c002050317002c401d14210054006614850402d400c2a00040a26109010b05821a5806403044041c3d4a6001aa040540d60060480400380651188030040350840d070f9051080d00e02c210420103100564200603640c1800c880c130344800d014000203521021940082c04038828800060382041d56207404130028100100c40310000340b00405100b000c5420fa02400065004520840c11600040040745150003616141c0d400403200d0303004084000c0155000c0e400284c1e0080040007603d01c7c194030340d130000b000c0b80c110b03084a10046c0e641d644240414920610 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 715130413 1250 715129163 715129171
    0x70804050c0d111311030c0408010e01090b2202220c02011e0c02120c0706020601061706090702100f05150a0f091d03040308120105090f010303110309090a090b 70
    0x2610b030354500310649808240308060040d060103800c0d02485404d2512450b4041100c05501e0000c240e6a8100503c299010360018001c1018951030700541400f441d10507c500e403201a031103a40482d4550720b601c00d8054a106041c44480510b814840d444011380d12140094000e40c2650141d82072640c0f00e40e034020484480e100c0c000156854160401440741c20000905500e25010201103152080503a080341030820500c0003181254000c030301e00c4402d5001042e00b005980583d4210340b01c90703903030350401c03203989a81c03074140044c01903400040340c910708010f18681c6c1d100c01240101c0b4035511005101c041100d00150311100284d0752141070144c414480700c41c40ba4901822200c40c10010706040044881505621812000c960382d40d101d18409a41c84809040f082844400d403919540d4031f04100c0b041da407141840c0c5070b1401c9078900101d91032624210090040201c4100d5100341c0e0300710342c4d041c0d80080c0101103c1115100c103202c50442903071084a21440344886120110304108145000e0380d51101c0a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 715131663 1250 715130413 715130419
    0x8190e030d0b190e150409121e0804031b081b070b0c060a0c0315031209050604032a0521010b010509090a11090402031509010b0c1b060c0303070804050c 67
    0x68409000016210f18015107403051002d21060b01d68090f8074011a100581860f005401c1541c03000074000b0021103254110b03510303160050394403a1410030f80d100410036500741000c030700701102103008a44210100601d00c01f50454800401101d03450301300f80e94101c1e69a071203010792040c1e10300400d01401e101d0280244405030441c0c1c1031940000b03646842e40d10041101c4101c3c2c0c1c0d24903a46460a01c00c0d0030000a84804060f6418621b8882c10142400b040070000d150106606131000609802c00104607000c41344c1184520280c420f0804840c40c20ac0102d0721182c6030800224004a42581d901b0316203000303e03101c402e000c00d8001c1148031250a40300421200f5041c82428059005070380c882100103507114024642c00030b60700042551055040c0a403c4c0b0054001d03102008010f01181a074000c1403684000b00c50640c80c507a6134058032041c61107149102206a00b1410441e4805040003c4560410340028031041c00c1c00760b2036420b9803860300204c03440000200024140001d000c41401b091109403010303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 715132913 1250 715131663 715131679
    0xf0108060319210809010b0307120b07030e10020909090a0320150703050f09160b0f250c1a070816051b0f0a0e0708190e030d0b 56
    0x1810000361229550202e11200c203000300451001c0041444815440c0304100d1a1450346420340240189210021941d00c12990f00e09851485185000a54a0300310f4440100c130004c00707082e550710106a82000303803485080c9529140c100c50940410b10008606141e80b03540140c4940011003040f0303e00b0307805028030803980c00268001d408a070780642c42e801422000842040c940000301c1000d45808014540d0125400d000d10500070b401d545600b0090290760100c0d14480162690044181c40769054250411440000704041103490003810180040400446220b41480100300f4018100f003148030207808000e09200c80101084000640000a02404400d000224541054100c10b41c070990901a2400d8004141c0705181c4c2c440d840340c145103031703071180a641c02d110751000e1559600d1400b0740000e22940c58110b141129080026400088880c2031100001c80c1d10703030308015104524050081e24903100e158010102c0b40500340a41ea0042030b04100841c0d60301c1405105000f00d0300c3c000441c2d4410001d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 715134163 1250 715132913 715132921
    0x1150906170402041122170f100b0109030b0a020d050108120909040f02041a03061506250803180714090a110d0612050606010509220f18020f0108 64
    0x8035112542e0080d0f0660340040d03c03c44a603103c2800f4000c0e00089021001e601c0083c80500110201035800c80b42070740c6194103e9003148030000e8072203a056014280315400010003410319261900100030a86041c1480d0524070389036250010190003c4586022a41e000551655640414440c083c010003012024081200161010101c5440740d860300520444002d8042018400441d103181d0705140e0080040044841100030703403a5014044230a03d119009100000e90004c501001c10118030b1001010285030017019034601240394965044070725250030701c04441c000030b21f0f443d0084d406507e002c681e040b00b40301071100040c5045141d812410742135182c0840241c00c0e454814070581c001010b410040340c01044480380c000580110414034020300d0404200054405100d03469400303c07401075081d42c0a599503000190754a100d141c41090f00180703a418150461114503419000090200d2008130315400d05070202000e5070392000742c2c01042203000d5400e000310301c0c100c2d215002102e020300307100c580340c43c3c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 715135413 1250 715134163 715134197
    0x10090c0806070507150b060d1523060319050405060a0615080f1f090c09050d021c030c060204030b1509010e130305040e010e0118020c030a050a110601150906 69
    0xe82c2401485e9150560180707161008680086031307403050150132151114925034218000d040c011001c00d006030340401000c5048840c00580c10f104041e100701c0b10000302c0881c02800300903400200744450304203004c400d40b04152564040c207402603025400400580c2091003000307040740c0c9030394001090b0701e07031980d03110219941000c00240d00c00d01c40c410500c41981d501024a9200421030b908510f9415290b0010070115041d511032420b4151a80d5000070f940e440b0000d008002c00c12140107940b19001d41c0070841c4102e0949030302c03c1c640e4480e10306140a00103075a508016a085500210350042c01030781007280c5035402c1801da50310540100d41d441d0340f0f940b4090701800e000c1800b4054000c2e100760350412034141070282040318001c0050500c0300d030342981d540002038840c00c001c1c051034140f1800900515440c92542c000c0d5804500100041e40c0f4181600500b603c0b65800004050b09200d1040f049050114050040c01d00a0070130b180072040703143c0034170801441b4030340c00d40141090210313800711218005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 715136663 1250 715135413 715135417
    0x60a051308030411030f030d0b0f1302090d0c0e01060e0301090f0221100506090c1e030709090507020706120606021b06040b04230a050d03081810090c08060705 70
    0x58000708255525181d50600c21000e24108941c0d542510543c00e145404000000041c250114400810015040e91100308600c0e030340a6000560310800202101070b0030340941c2d004103400c00c0010800101a005031303075580480691607000c80c00a0182c00300402405400010500c0711800840c003c10540e03400f0359503580042c41d4008040e00401a28501d859180d25041e401d1056100c40307030803940040c0000300c800002c0c200846100f802150808089440c9101c40c5003610302000c0180800700034114081e24542e220b40001b45460200412883d0005079540309206d600e000710050741c05080000d040c40ca0240540a025003003400291401d20100845035012401c1c2050505d140c40600246004c200012524007486c0c0141808240001d0002465010703072803110400b42924191401142a40c010810009610b126803504130b20040198070020740b14180055000b4144140e071071650100c041c2652070301420045d40e01801c2c3d5940001000d000034640540002c01008004107130614064078020700034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 715137913 1250 715136663 715136701
    0xb0304060504170c07030c05030d08070f0903020a08011a010e0d060e010b210c0409170702040e07060c0201090e070f1d100801031208060a06050703020115030602040305060a05 77
    0x14070703500e6010a040020714200030702e10a0f46040c0d9075456201d401c20240d11070300580b2003220513200402c80041c050402064500c079550b81038a80c0c40503986d5588041da9900313517500c10308080001d841400300c0148e42c0c0440d00700c0600151400044c500c40f500800c1c121100e06040c24070b05010003440c1d902c040d65200d9201304010750f40040041648100707408554094800b140c0c100d81d112511002000e0901e01c182c00707000f1a0000300e4200c612450212081c00f00712040044090007003e00500718446640d18040105006840a80700180070040050f490382080780c981c000381c00040a60b25103900f55070f44032249102a101400d00d074603650400e03150190184010000d580e0500c4040084540700c5e4100920341028094044c012190300040404020b0540c03000340411035550078504107040045100b03428452044801034501e0a1041c20b2041c1980c0c02e030131491003203085640310002041c1d580001d495407030045104442c00360701d49080d49882410a840204075900340b500e00800c00034803070b20700c1440c0c41003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 715139163 1250 715137913 715137923
    0x4120e240d02190f141206131103010f050a05130c090906140907020a0b0f0921071110021b12010207030f1d030c100302090a0807030312060b0304 64
    0x4449250a00c0014500414241c80801c62002c50724621050286607040b031620516a2081032000c04e00d1004d031202c0a41a82d00050b4501c14006405240300d01010140c00000090a0322040c6043d10100030599020003224004810f01000400c0460003e200b0325000c1d280c00c5500007201d0341080041101140348003220f1500540300c540301c20304903006808071405050045000e00c2016101c0400d641c14540703420000d409110584000b132030603880404d062401541c032090441490325442d8016105170700203060030050b07020f038051a2051400e00c0c08142c807454950320784503440d10f900b0300b0440340d0401c2c800840e50003040c208403030b800c01302d50100e20340c40b0303075070000c4218001c0c00c0d0000080b41c20315680c0d42d13100132158030004d0b0302428180c028542c40701280301c3c0d0b038408003505104400041030b010f0424142c0c0e010f1344040400ca95618107410003100440140c5001824052504001201031507180c0c40300c00c1e503401400040c414161b000404c005e103402d15a10501c00380c1d107000e16241c420720009102602d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 715140413 1250 715139163 715139209
    0x20709181703130c0b030f010b0f1207030f022a031905030703110a080f0a0b0d0201030b040f15030c0b03070c0f0309230414011202191d04120e 63
    0x45a2820984071120f4580080055480c0c43c1c644164104c103500548407607140003803142c00021a11b080304112504280b0308100a030070301c0c3c000703410240421409014982456251070000750480c1c204d01c080c021658801e011251105000c0d5840e0b01402e61046491015400420250284070504000c0701c2e245040380c98443d540b075681250482c001c104070421042000400203041a030b10340d00a0307650380200c00d054004407142c2c903150140f50440b080c6800325038002014118002c095030195102100481000d000440c1142c1490b01207821580b00000c40a031062591105009000000100704090a18850f506146042407000609400c2010300024003078410000000300305841807280c140106000207132299200400e40141c110b440815421501440c5010903c4a0102c40607511904888115030404010130041d0280100c406001d410820b2403ea2803000181400c896544140c2e60369136411101007a090034584000d0068851074940c00304030643c0b1145c0c41c41d64503803210300f01d800c0d010b1a4001c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 715141663 1250 715140413 715140421
    0x11032104050f070b0d2a0e0f0901121e05070506220f14060715200307020c09090109020f010f180801020702030106081f0b010e060307020709181703 65
    0x5460030700b09000c98a00da00403140d00280c3e03566807401034142c4141c031142c1801807103d0990080c5100d10303180041500d0020340e10402580a0140500784003559014180042600d166004501c03aa4405ea002d100f4050120b8010401e104a541c1090118543c0b01c5d00c915007030000751222a40c81026010b00c1d8481e600c00075401034161078002101c150035044e11161000d03140c0c1c4580c01e200400042c449d03c0c9103ca5090f81e0700c5034900d80b900c01c80d001d4590207000c24406201c0740e880b05c0000e00f08881061018850046680000740300d460140d4402c140d19030041441c0110001440343c01c01e0080d00000581e81400550001a80c1d001c1e10012300503c286850301105403580c030101c910929103440c1c501202c1c000c0b000481c0054040d0024540c0354009c1d0000d0000ca652500c0d40341e5940843c04c654008050000c02c4003603d0002e5400620569a051404111726040b600000d40c4075070003070300c440300942c0c00450204240d90143c080d12030205032010300c41950000b140c490300d030585000b10200628000000000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 715142913 1250 715141663 715141673
    0x10314090a0206250605070e0604290c1015090c0206070e0a050d050f15010e0103060e070504050f0603011103090309240c030a12050601050f0a090902030c0a11032104 73
    0x110700c1003441c684c00b0f0b641812590500c407001b0320081c0c0c0d401c000070f0400300303088805003440022102142d61000d5505190300161650420195840302e4004024a00300041e4000f01410030204c5080041030800240c248814102c1c1c2c1c683d0540c960081c0c600d50700f0410400d10a0f50042004c607440002c600b03003810b400c0070409c0010806619904a01d500100c03244c201d02c188900010106e107541411800c840c640c0c9071868010b5507a880c03d109011144101ca0014400078216401407070360346c100341c0200c40314262110001415a41c0c00c40781c914034102c52000700f103803074503003401080c507070741001500d070361550a01501c259100d03c42d51070818011046080c20f094075405072022080c900c98403600c52911403a560801541741d510034050302c0002200c070095005124128810030f40246016103d0030701c1c0c50b400c009805040c5d00319017540e8040c0160210001030700e801c0e6000030b6215448031406241c0d126044c04000e04041c103c6084006107034424400500382e20f0071009034050a4800b007600c095a0f80d641c0c508 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 715144163 1250 715142913 715142947
    0xc0c05030706030608010e010e0a02010f05040305010c0e1804051b0a0e09061e070210091e0804062705060702031f0f0c051314010909060311010314090a0206 69
    0x4020380501c2600700014045a00d90320103020384a074007009101001c40e40d0103841c2a03901c11030224429030050f6400b1001503018501c0714070180142c0c20304d50b08156480d140c02d800c468842c20400003046003643c8101e41844e101d111114402d5181e4030220103400c040d00c0302982c03000303102d5004051110540342041710784e072002d202d60001d00c190401c45400385400741c007164480030107580c02c504040d401c1c18100c0880c2c102c0b014041c4549040d030b00500440d0b1100c166079003d003401c10801d03a0100031080404540004980303107104c00600802c00c07540d581e4504180146406a1400024944074108060031341309950a00313410701302d0340115070b030039150041c60001030305000105146196082c2c078500200e102d0741294004480034417802c4420000c1c0c584802d029034461003100b50b028125031186c402072040030000d500c0d840e0002e00c189445070507151101002070880340c1540069400e9204500800c8256a2500138a814a8034087c03441101741080303010965030384800d05000744624070115450303038415030002d9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 715145413 1250 715144163 715144169
    0x703150e1b04030507031a011d190c020703050d17040f050c06031915030b270f01140603030f27150c0106050306090c09090307080c070f05010207150c0c 67
    0x1a416a5190340e85404c6585607540e100446035003407903010074502c140001d210207040344c0609206510305504031040c1c40811400408403074280c0004103480c0340309480362040d00c000200a40041101134210706003146000c00b9014000d082041c11441c16621002c001c40190300b0070780c04040442608064a00780b410400740403d541e0b00050040104000800740d6064502104085102001088a002c445c00c1d1320184c00d010103001c501201c0c010401402a000802c081c80c002c0c103001c81682e420340c244450500034040340b0405d190303440300c0e0258050f480c09481c00d50000300480040d0b1802c081c058a5071858090b062000207156001c003106c0c652000f0300f0024240050000300b020764800108181c403156a048000c803035010b0340c81c0c80800f0480b41030000e00940240640001004000842d40400504040082c08180e490005118000c00200d00c00090940c0daa0028050712002c0e0910380c000a810a440d40568115800311004002d02c4a5400c818045042e051401040441d00ca050621070123901d98 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 715146663 1250 715145413 715145461
    0x21602060924040311090403080c1e03010b120105190b130902030406020c0c010c031b060905150609070504050108010e06042003061005040506030c0304020315011d0703150e 76
    0x80070b40404100c030038024010340b48200c07000c0805600f00f0040c00300c0700c0350440b8024081424070000c00d940d0f4050002030b10640304a003107005407819600c1d406141d08d4100713a2008507810320104490305003006a03044c641c090001503038021880a664041842940d00c40d01c5010390306900054004195a141300180c0c0241070110815542c4e800c2c50b141c410001e52014040d04d03141d0181040450140d8880c81c0d40303059054241d515101640780c44844c080f06030816400468009035240c0d10580007a1003030226010701a041c20f8030000500d400818894000e8005003a001017101c01c00c400d00190380c100f403c01307040d6540800e5291040c1d0310100440c0090100b4001c40f69000060000c004003601c3c00340080d481004143c4850034a005d03225405d403001e009501420703a208a040c00090b2415040713001466200f800242140c1c01001610004140034400f81c210741022410491003420b903082c408883c42d0400c0d00c524040085458640310003911080038094124241d801102141d918490380c201c0000240c001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 715147913 1250 715146663 715146709
    0x121213080a05071d060a031202191a0f1b03070e03061603060f080a0b09011806020405010905010c02030d032a050909152404030c030302010c02010f0216020609 70
    0x180c1041036a8451501c200c4104c14600c0d0048840941d0804c5168040c0c04064401c0210b1429981c504601038001c3d440e034401c40c410b0000000a00e04007040040e10a1302420103840058103407882d5440f00c45000b030002400840f030405020b010144605c02000d111218810300380c8980b04d900003250940c010960359135040c42903005105401c0d001c800c0d080350034181910200310342130703032041e281c0d10485140c41042401c0d001200c420000c43c3c03402031000d6010303040100008291341d003000c110302c06000c2840b0079100307564081800d01c4076580022035100035107000d0805c0713800e9100c1d40d800641c0e100c2c1740e8601c1c002003503107990304d60000741c0416014448090740a45038400061101c50002c11a03082410040d100f00344070f1020510400860400ca1180e0002401034a02c207004004807080c0c2c2200003000300d040003070400c03000001c20080c4015501841c0300b58000300d5511141d03200242511441f100e4052030750320420042c1c420348172a549150f0b0007039041daa900d4035816460000340344002011742100035045c5d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 715149163 1250 715147913 715147933
    0xd1b02010b04060e1009050c0f0f0d0b0d02061b0a0209090307170424020321070e01110d1d0907090f1703091c05120d0b12121308 57
    0x103401c07950740e8800580b01080156915403108603411416a4858020300c0303a81e00500c02c4500701d401c102c0d48000d107580014a003650286080030281d1200c041580742410100e0700c080b00082c580503644038440d040f45c07503151038260b6400003500c40c81284404049007172402051049078201f84900b204140c2c00500d40381a40c54214500e0781c40707500410049416008000c0c0345503104451b4400e840a44040b000c40b414034190000300d049451040b00145000d501c414032540303e9140400524030420300c1000f5001c400ca0402caa4013030020360207200c1c0a8140542c200100c00c407408000f400c41c000400510705444210014040c20b1002508209aa5000b614400c1003140c0c994200c4030906c100c451140c85900090f81c4c81d000e142c04c0c0300c00319800342e0854104002c3c1c1061490000784c2d103485a00c140c81e0005140c00783d6030310b4610300302c08011034001401e030104128080c01e4961046c0e4480304001d458450402d210001096200d507130914514080d030001140840c910881071740700b036000d0b084110440c9d1078564 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 715150413 1250 715149163 715149167
    0x9030a120e0f0301020316180e04050a1e050c0f0406050918060c0703021506130203090c09060109030b0a022a030c0d050909070f02030d02040f050307080114010b0d1b 73
    0x80c0716540d090181c0d005001e90011400c05108030391082c0580b144190000c00705400c00c031940340c408800c884d021980031501088c072200c61030040307024a100e00001c4c5441c10b0b00e07103800300e4603584149500480d041e14810f5070001c180041401ca807040422a807903540040d1110009004100c07030341200fa0810003460400840582000f03010320302881c440116190b0759541c191815080c03007051001030050f0849844000034415000419400600041004103004c01c45425201241c0040b01d405010b80c0c031400790351820b820300b01600c0350404420f2074003210941c20342d25841101c14000c0d008903031703042d400a160501c0c41046100060380840188003030007003c44d00d0403015540d8003c00d4410400c0d000703088040c1d0a01c1d000d0790446044c190701610022442e038601800341c6543c07414154110650000704101d4040c4d9030035100800141110034500a0000d08110a05107041c4c1307540c210b07100716854000f900c86507214280380a8111034a811003076941d482d40081030301c06890700c05100e00100003a00c0c0f081d004a9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 715151663 1250 715150413 715150427
    0x1c030c15020f13080a020d0b070e060f19110a0308060a0308070309060905061204020f0d0501020a11072c041110031a0916030b0f0916020f0d08070509030a12 69
    0x108180f04001d020b02d03181c10f622602c88022030030007540450346903072000000d640d0060607070344403485041c05a034644424000c103205074401d10700401d00c0b410014503003090303080740b0b12618122915441c0a1a0030f4060a07409a07442c01c401d02c000e000e2282e4a000544103030744424100e006954001c000719120f803502d1401601070f9070760380036400120301c00280104507403d11500381c50400e50074000201107503c80b0f80a02c86044681010950072802c00f2203220041f820900040c00c150401d40d40f6201007144402c401030524940350402440c50164201e1070702041151040c0c1c55402c10000e200190340d4950341341c406c400f40c00120003d030b0041da20010615095030540c0c8500007a10800200905800c056003c00c2030741e12003250400309c00e000c0c04420441d0b103880b9500001c0900d10107006c40c80b6002c040320002d1014030084900400c8041c207030b00d80c0e042469043c008080c61192101c024405034060060280410600510000411401040c1c6880701d40d401c00c040a01c01d03801c104800a40034501000030b01c22 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 715152913 1250 715151663 715151677
    0x2f0d05070f06030203040f0201081e0c0309010b01050304021e06040305101e09030f21020313031803050a120c0b100f0f0b042102060a08070206061c030c15020f 70
    0x1c04081d000041c52601a0080345c0c4141c0d8407407136205150206a0055072503c2001c1c250703004c2403003000703030800140c003550f03a07000c0c011842e4101d85526858000c8500342994119080181040030602c244401030b00c1e001078071266240c40d440060341001054000c2240c83c09141e001606500c40d44000000c1d905c000d920541c2107014031005441c0107020820107205940c180a801400107600000c03142e0074071701c154640321300030014011120b03540f900c0c02441e00c2a41c10940d01d10a508052516040815030400b02e151a042c11f11091801c905280d03031145a26407440120140158410400c07680040388110440e412081d030003416142982803842000e590700c0303018080d016010710340712804140600a40102c1040b9521029a64138041c10a1050040c120091082c81f030f03880040c407110801651910050112040c60b076035184a50310700000700034034150000e400c603401902c2c0c60311882030340d22565108524464150503e055103005a2800c1d10b40840200c00d801c2507584003207190861400400010480c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 715154163 1250 715152913 715152929
    0x21190b010602010b181504110409240b040312180305010e0c0406230301090c06050d0510060e04050907030b0c07150c0801051302090312040315092f0d0507 68
    0x1504c001d103061200c100c2045120b0341d05d01c1c2444001585d001c0520804941503503010f0710204c0d20102500007000d00b50840c1d000761010540b54070030070b180301034580c0c00100c180d45490300d083c2001e032519000440303600c2503000213008485007075008166a8000c4060128010b103003071446181503640c0c01c09034000c0803a442040901c0c029183c0101007440c0c940164010b0311140c00d00e00500407400500200704805808000b074065403114a8600404d5001429000400e00b948a150342c4d8040310000c0c0b0110348000300350f0841501c088105010150b80700c4405170755144181e60000d4192170700101c10703103081078591004100121420411540710703043c4000d00f031901d10a122800c0740486070304806040c2c4201d440c89400003041540100f049185c120b41840c0398000e600d400500c2d0a010002203401c00a04005180009400003010410030603024440c5010000d24001080a44074550390355114012044141c8000d04808401c01c54950307801d44142440d075402010815140280c1c43d186456004074450113076 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 715155413 1250 715154163 715154171
    0x219031e1505090d0e180c030702211219091101020d02030301081b0d0c270c02060c0c15040f0b06010206011a070819030e01061421190b01060201 64
    0x62824140e016031805455a075024014a42c1074440c11142200170686040d030048002800c81800580520800e014032405080c913030781c915040303502902c0e006120310700094840540c5806600401c40105544034010b0500c4403243c1a250141c07048442105482990112403814a00c402080f8a100601e441034a0a800f42c038010711085905903140d000074440c00603a504050441e2043d06690480c4041000780200b8150714121952900420000142c10150303100300882c0540560b05030848044d501552007102c240028100c181c0001c0d1150001742100782c45500c04104422501030501030543d400810240300d481520300b5003032a041004c0040d00030744820b82100040703001c2d540701092050590340004030841c0c031024041004a079603400441c041d10075030003d0100e5103d10070845c0941c000b46190751703000728800b0260f25100e4215201c5520200d025401842e04608585502d4003028108a180c411541030140701c05249041028042000403400d400300c42d01d0003005003600086050740c0f0541c4c000c03c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 715156663 1250 715155413 715155443
    0x4080f0715050708030a020705030c03030a0606170103051b030c040c0509040609150e0a0204030c0b0705010e01020309120d06080a140606010206010311060c210d2004030219031e 78
    0x42d941c0d11640001403e180000c200003420718500350000c3c25250b02c203501700d0707141030488451181503400070340348402c2e41070700e81008005082e8071006508022502c2a654103055140d6030750140c0c4c0722040b060406000c200b04145030300325901840603921100700900203010400744040c00902980c40484030504c5203180002c00300c2c82001d43c0c8078034260300c10010750072006282414252032070040e00802c4c902c200b0341c0800c0084005108022070100030032101d008103880e103034189001d0b425510b13074916691080e0b1052013040640da0740003a01c4899280b04072011030751401c5400e0702c1005030045405c03040c401c0c4207100f8040b0802c20100700140d0003008404c00d50b00c007070f11703072800480c2c44000c01c2c032000d0b1403950241c4140c070f15031808500030020501804101c0310418042e40851443c20706802c0e0301210294089001504c5100328000e400b851200d00401c81045070340c2c00a44000c50043d4007010b0f000b0003803021210520551021407401030f58002d026001254041101100480100c8404031a1491b80000c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 715157913 1250 715156663 715156667
    0x100305060a0513021b070e19090501060308030f31060617030a090e010f05060c1c020606010f0c0f0b09100615271502030d0e0c0a0512101104080f0715 66
    0x1083c281e41c4070350f005103c03d40ba031401025940a04000305c8d280701d9a1a143d080c0020403d1283c0b000551003246c1050300e1346040700104000ca6001808415074104010403502150314540d0240c0c0d441c01414903210990b4030b036041c860018032054215480c1c000350a5410540d01d80c0000c0540010202c5a441c4206180c50740100c3c081102d01303104003c180b1072406018000c2e4a0311502078103e0040c03070021100100140c80001e2402c070ba1001200c0d000d6045901400b200d9607218904008071506400e12000000c09030340d584804002081025207080041408211254400d01209608e41400041801807a4464400365011014008850049031481007c400400d11047d001e10108902c4400408180d1901c02e500e4481c8500e40c400904500042243c0c9400a015114000c4100310000040c0218441d542c1800030102035900518411520040c1c201c103480303000600585158113404000c00c40c48446940310009025a42040c40540600d1a0f03d50303040d000000c010080711104105012600d0b100401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 715159163 1250 715157913 715157923
    0x90c0705061b0c0d2d0c060504020d050f0c04050a0612020d0302030c01020a1d01090b0d230106030507090b19030218090c0307030b0f100305060a0513021b 68
    0x100520a801c1600007400c600242d40d800101c0c808040340581c9001203181c5910704040030308070a0008a041001a43d500000c1c480c140c01c02034903400410807071030340800743c0501210039010000b0b02c1262510009811034030380c04920580c81d580300c0c0403a4402e1401c02803550f200c000703181440740201d20f03010000f041d4001502405007207074124080071120203956028808403100f0303030070140d095100801003007a80b0b290920003401004085c8d61246c840703c0043c5012449407a000f0340c494100440d0795010f0020640c0300302103688810041c4800102214004600d140c180700b0004008108a000780000684070b03099041903104035030781c2c1c0c0d0390311a0036140c901d20704441c0100441c8015100041203a1a0030600990041031030070760318a10f6080d82c2c010100050f104050485070680306402c00700900c03178065010700840d40300c82c00c1140c0295590b104013020428105815030322070300301a26403000c58001d4845d4102c00014110142ca200241980e034403148001c0c0d8031884082290740c640b2034500e484a034022803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 715160413 1250 715159163 715159177
    0x70b10080d0813260c0a0203070e0709061805060d050a050a0515061e04033005030a0c0e030604080a090501020c0a2702040e070e01050c0c13230402090c 67
    0x440c40f1407254503403500001c083c0703c22003410422070410031041040400906a60080c1600802d600d1040c0e10501d410a081548803002d000c550300b05102000d500000140b00b40c540e18946104030065084140401113420b60015401030000280c6500b025102d400c400e2040d401c0d07000034803ca1f2200201d501c03c0395012680e40201c426100c251000c4c0c1d00e0310340014006041c0200c00000e6040a940e0340d11410391169004580c1580c200100000301c0440c5005000103045c1210000401d07846800094160b10005201d644c40c0f40d0b0354024006d9407030107000c102034881e401234125055440c25140c080019401200c40c440030030414900000c0c158070010350407448003006400c86000c503280018180149120640e03100d4070480484200c910400244050002403500c4d072244000c5090107000a4020410360303100c241004010040c1c0c8110900018444040b150b003550860f2013405001c000b40c004040180c07002c1c1c1403180c003006c0c0030740c0b2040450005001d24001c4807580741c0740e00c61001025240c400d1728 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 715161663 1250 715160413 715160431
    0x301170d021e01020d06080d030c08070c080a050d0c03090c0906031505130210050a08010f2420061801020a09060305040c0f0602010f0b0411041a070b10080d08 70
    0x42c024104101c2d003103407a0a01d400280300141c203040e0716403003040940b509074101d1145030303001410b400c0b401c507070500070409000410706140e007041c240103c00904a90301e49201808480f80041c0342e004040c891011079004441d0000100041013039402d0040103005101004d43d40391280c400302040014091080c00c040b42d42c451040080d0000c0e2140c80005030000502006040303011020410158803040041488038489540d41341d5a0f0113010405401d514060b0840300800c540364000f80301d0101203140166041d440009004407200005800701d941104100c2078100000c52014000500ca60008066016003860000380808001d012007840c00c0380215580140041c1098804000c11030080e444131f9081809111800881c513280c1d0541c40101000d80c0c40000147e40d60009803400382d0141c41101e44043d0200c2e010301124000c5203520826002d1402000403d2160907580c2040c0c0c100c0f401280c600c194031030040072161600c107580b2148070500b4171401c003441c01582e5001040c5407040c200713984120986 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 715162913 1250 715161663 715161673
    0x1005040602030715060308040e0711060103020901050d061515090b070218040503070605040c030501050f010b0a030b060d09050109150b10080402040207050a050c0a0e0903040509100909080301170d02 87
    0x3502c442410f07984018150504d1582c4540200100345080000c00c050050400704401900781548028440070110004400341d4000c80d0050005a50301c000050455a003216400c035140b038079051600003000342d1500901c4070310313041c0c400240ca10306044c154407000720903403039101e400d42c0c0d214a400306612039500000d600561000001030076020030359015410500400490342000403c1d500c1340708a80040d1030a403451401c0c054200200b00090052540c04030690304128440d52601d803554610303000d001c14203002e01d612003046488a4488105844d400801110203104405c0b090a10900904060b08190303124031448038445401062401103640000d405040164032600c005811100410301038412a4040d4007081040041481040044480c50241d809480a803104000300801d80f9010b80c05060745103407503000c10001c000c012064604640342516010015a101054020b00c030407160000031750307a4648015030090251007006103069506480e44800c4008640300c4c5266582e822034400c000580c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 715164163 1250 715162913 715162927
    0xf02010e120a18092301050f130222121a07120221191a010504410f04020906030a09141009021008070906142502100504060203 56
    0x700c0c800001040c40d45940220000fa2039130020401c1d52140091540d203402d040f11907030b444070f0122400c980103000454050350904004004500030703403164940003072115400311705210f60447c1000715141c1035010b5162051006d890f10b820410007504810142d40c6203086180000d5041c00d0384c150300e8025481900c4910294084804040180d8000382103c1c81f00c07003450307494035070181c51110b0080c00b900000b00c0104a200c3e01200d0385048a80b078800b48172001c10b44400070b80b5180d070842c1c21901616102c150800072808026041c0004402e160158542001113211400e0391100041c50310b80044403c44140f440d0210b0031040000743d000e1400e04507070010b03041002c140c0502c0140d200c41c4c1000d00c10461490000c5100c0c06041c140000b018080100d15155172011046150080c1c4040030070320641051001410f084030000d0148801d030207904103000130003041e9800b642c0c0d41800d690002c5c00441d140c40740d900500701c2d22899007142d90700407402200703001c89140e4074a002c0c01c141c400b9612250300440c00c0200c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 715165413 1250 715164163 715164167
    0x70504091112010308180108131502190207060e0603040209071b05030a05070b10030c051c080a0906080609152e05040303120e06041403090a060f02010e120a 69
    0x285241c40341d4912070003000010040319120040500071405112040d45580710000c1034180c00c0320300c40040d4104440c0004000e030085042d00c0c2401c0854010904140740108526050000d1095603009207090300030b41a0741f1f82e92540001d10b08161070746a07450810511055090009a00040c3e4000f0740c00080306001414041c030419078919424000144960f010900d529820b0847d400820003200007800001c60f5803d005020210350341241024040c444000e180d5240c0451460b403a0080e18810002425010180a03c6510f01b103612038019100960351740310128040c0111401d4490b581c00b25800f46c0000c0d280d881c0c9040528400c0c0c1e400b880500200070b4100800c40d0f02482043c041341001c00070708112030542c8007070f602c60700b4140503600c03034a03070300c0d82903003009441c04a5440c0720030646400c103800301d111014082501d58000d035204c808060040500c9800c2c500798050989401d8100ca28804005002075010100d42c8c103071034a07a002009011000c1510a844900c01c3c1000d03110614108215081e8034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 715166663 1250 715165413 715165421
    0x180304031203021809010f170a050a080a0203070803090a0b0105030c0108040210090905011d13030509010c0201120c030903080a0e06060607080f1303110105040621061d160807050409 80
    0xf04000c0b0440507100c00442c0010500c8501f130b0442c00c0c3d114055102440003015900c01600342c905900c00404c000d1500b55a52566000174080082c510741000c682c0c4004140204140c030446030340089060303120300e055260b00fa540c0f0648881910f0840030795000180700d0a000c942e42a100c1d4069449540c16a41d940a01c5a003105109041e42004242c40b0001080c0400b441100e01070400b40c143c081c101041500c0c200140e0070b000d0000c09061040c1800180020303040b10131158500404c0c01c05a02c01812800141d0301075034041c24030710810703040030850054994198004241ca6110342c441c01001c5e00c1d041c0c184002c442902d03001c1c2d0340c160701207030128a0742c0c6041006850858447d141242c681150840980340700d802c45440d02c40041d440c1903081c000c0092000c1880440b090a18016040510740b020041060f0001074411030f0f1210120090031400e880d681004015050000f400035228407030303030500130000b40304550407108001c09070502209184540070440c0100340c140d60380d6040604000c1144014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 715167913 1250 715166663 715166677
    0xa0209010507060b0a050409050604062301090c020709140403080f010b120405011104080f0706080c0a03050703060b1318020301050102072106061701050a0b03030d09140102040e18030403120302 85
    0x2103002c5d400151962203014041100e482030000d030201d03003800d01d05401a51801200c0c1020a4141c0385451302440da620003443c1103d8110201007400c605000c001c0e0b04102a9810250728942421700c003511119881c3c0c1014000d500c2656505200e40d941e610800301c1e85820302507030000d103008000c208540c1140e5010584c000e40100c1c000201259020459031541c1d209038025046030300080d5240ca1a900b0501c001d000503c424105401146403402140486104203000030043c0340d0744501180006208ad0300c403401811600c461036654020411500704103103154400c5980e18000c0852001d9a140c050003544e040701e0068004103411070411010884130b50b500c2846142c0103403030041d5074000c100503010792002400e40c484041c903010324161000f405d4640040c99581e205041c5815030314252400400c8956000c40700e1400500c0d920240303040020804c0b900034a04ac5580045008034071242401c0e00305004544407100d1100881d00c422015469001e40c0c880505016825403005030303142e0003034005040f8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 715169163 1250 715167913 715167919
    0xf05090301060b0c01060302030d0201090f170c151b0c0c060714060a0902040c050304020a0515131509050306011206050606070f0605060103050604110f0c1e03120a0209010507060b 79
    0x45143c6400c400e040315084440340c2c1030aa91206020019824284061680b902442c4002d00c0162103503290814101c4040300300500c6e12400d08041104e45982e241580c81c00714003c42030b00c6000c4058401001e10600075541406100c0c8080e003101c0e1503890900c00c0780e86041c040c0c006010003112100401076540c00c020001e4915401c1c810312402d15210612a4030304c5a418100700040079500350050200b2140711000324024401c080050002695030002c2d01011074104855800036861040380c0310901f0302889400d5103980c50740540100b50004010304c1d1540c00c40c0d456031000c444556070001c0558400007842030b46130442500c1c1401d008101300e40c00c01548420080c003201e00d094620768940c2407a038814002910000c0c1d844003486850344e45030080a40089044500f4058084181c035000c000d84113400024810500006001c185c070201030240228a103c0c42d91380401404141181c07036142c0e440038812400c4554a41c0009001e02c201e842035815400c0180d42c0c503402c110140e6910300043c6804010300e58 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 715170413 1250 715169163 715169171
    0xf030c100b01260103150b092806081509121801090509040510051501090506090f0301050108030d0f110a1805040c171e0402091302030303070314060f010f05090301 72
    0x11600d800b103c001060100e01144841c0f1030341c510b041c00e40c0031140e001d0340440c404d07052000341d40855803143d078880d40110003408c80c218400d06824a040b50300111660f25407105003030940020f200300700070540d00011003002402c0d40c010382d0352000c01070f2518a16849107014000500c10a045a080c50008a000007018109222a5a04c030000105180305c200c40440301ea61140b03051280b507441c2130080c0c54010080311441c8040710301010010b000c440300c6015690207070001003881c034607694076200b4002e403c0101a00070032103561500080d41e105d0f845080f0403060390781003803041c0341050200e10482c5000721541e05000c1c20031f042d41c203080f19603e128400c44094100450f03404110355a952085601c460201c1d16201d88850004000041c03052000b0126a0814500030803404180303841c41b015980140c0c11034880800340c0d240700018500080340c0c100a0340500c0040100200103030154000c8084000008103480d195650808004541440703120403800648031514030782000d4051405000109170080c0041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 715171663 1250 715170413 715170437
    0xa12030e0303070327082a010e010801060c020a0e04060e0d180501260a0b0a06170103060203091c022b0e060318100219050414090a110304060e0f030c100b01 69
    0x68580000c51f00210030307803d14041c8003c00103106c000460031040083c01c2443c0c500755400000307818440e051040c20300740802c552408045540b080c43d914040e0408101c545000d0509003041d600508000542038150322541c0714281e4281d0250800c4044580a1281c90001c142444011121120740310000080080350b0385070800a8400842658070840e001c0c3c0000411542540c10410303101019800a010b00c002403a0102c00301c2c000105203070640340c00003000340c0c0d42d0b02c660958519040c1c0f035503140480a503e544000004660100d4202d91443d0f1182c2c1c80c510691115100c2400c0b000340031502c0c40070440ca165440017506044c0065a445074000380d00701d2101c0e170085141d9040c1958500101c01707040e40095441140814000f03034007041c0d2030910b0b000d42494201026a01c0604448142c94403034448180000e112941c3d50f0400a843d00078044290346a040515040e805002a00b000f50014010b0300c0d80301800c0c1e0000001d482e5000e40c031000030324114280c200103000400c80d241b901d030b0401c18109000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 715172913 1250 715171663 715171679
    0xc010c0f030e010c1509020108013309051806040b090606120a1b050d0c030509030f070602090402161703070c0f0614040804170a021e040b0a12030e0303070327 70
    0x69610150340d0340801d0851003880010308104050700841000f01b620b00e24200c00807800c40c2411003645c25a048801d40c00c2f4441c0f41a10220019484a07900221000c0c08121003c0c10801803402554142d074244015225075041001c002c01c1200c49940085040c881c60b0b552400c00340701640c00510400001540c0301821100c008003a00c24607028000c103900003070a421200c046d1140049036210703031408002d01d080860401e1703168030420310466040f42c8041141024001a036048480c0c3c03650041c0119a82c1702d050710707810245070000405803a130920b150b00c407903a03810031031085901c1203c00ba5602c550382c110315681d40c00c02981840382034520301e40d40c00c08182d817010300305c0d03110340154010080c15880e2464600c4400c04c41500542c9001d007a0040064480144c4807242d00e01c06030025941340005d9500b01c8408140140128480c9990100d50784cad4002a5688401241400c0c0a02942c0c0d6550308455804c1850780d02d20400400070001194055141c04110030000b001c07548036000b502c10803c85644200c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 715174163 1250 715172913 715172933
    0x9142701020c0c011202090102060c1b010212070318020120030c031612020d051207120f02090f0402030408160c170105010f0e071205060609150c0c010c0f030e010c 72
    0x1036222588400b0f43c1c3c080c2581c002508820444000701d0179440e002c400c8000079168440607000c4024030300f000c11917500c000c1041140301d461144c201e0085440305035902d4401446e00c41a9100d0740420300c1c1c0403119035510b04900601100c00d406031200d0800030300c00340b02c0d4a4058804101c2e103602e400188004214503a040c030052001d0300c4c82400301c1c250458641401c82100c513440c0b40202c00e56000c0c55080d1920b98010080d10281484110070200c1a504d2050640e4082e06e00e2951181242c54824a1019a440350b80a098202c500781c0d403400301001c41034140002c901c401e54000d00603420911910032011310700b09903016458860084000365654602d5036045d003401d2070707100750b001c1d944606c0144240b0300d12008010080c02008240601e43c20040d50140c001248005583c008075114000615a600d0710021074810034409071114894041c1a001c2240301e40200320070400301e0050a044651030361042c080e0030003c542200b9501c0fa60030301d41e603040d0340c0740c0440e80c14241445428400007000c80c03041c0c22 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 715175413 1250 715174163 715174177
    0x1605150105092509080304181b14210f0f070908070504090f08040b0c0d210f15030320070317031f09020c0606040e070306050c070c0f0603060914270102 67
    0x260071040e8030314030a0f2000a6400e03102d48209c42c550061200c1800c1a401986042d81e400c1681e55580e0381d0440f070740100d00c04c521a91544a804000b2418049041c06602d08548030f001e0350400312aa030703164803000302d6644030580701d05030860380315400c140b0051900b80d0080298520034a86050400003550724142160460b9000140c00c8001040303e40c1803172403c2c081f12511410038035014a4042d82e000500462515824024281e00d40d0341076103001c60a02540f185041c401c0c07201c0302c241081e070382e4034009010256812120f81c1454003101d8070a0000d00000d400015203074004542c2c5100810300c84810101d402c010400d400c1050b0b0020070b0201c8015900342e0602810400314096903504c44905d88500e0907501070300c4180510b10300b4102d88070100300418400140c035404000030a05884d0022166101c1c02280b00180403050301140000e140b08849105104030740311034505002140c1e440c01c0e50300032070f00c442070b2a03a00b4055100028041e60a11302645c584504a1b030701400c004041d04042c1822604501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 715176663 1250 715175413 715175429
    0x282a0b0c04150305040f03110114090307051527011803090e06010807200102040305100e060106090803040312020f0d0305070e09040507030201141605150105092509080304 75
    0x241c144030410500d20401c81d0861642020b000754149944d0300940f80624000140812150b44c140005c000c4003900302d030400310000f090891050804c442c1440d00d82d0710004c000c407858800c8080c1c840c46152004015803142e8015585540c24125581e5500384500400820704850f5680385104082601c02508000140d4060b684140c5407500704001210380c1d00c000350042d414001103004014416501903500290f200085040b051071444003103203917001e4017070358100504500492240880048440d07000075000c401711401c88016903030301d01e001e5842d40041e0080341590b1f00308000600106203900c3e1a6101c03915144100d50610014045003414110042e410300c001944079818401c0c000e0748000210010041120381000c903060a41e0b9481d03649555101c000c4c14020042c1c03200b82c40c0c0c0c0c0c2460a91b003828003450341d0b48414000e545442c0b600c400421440d041240188000486c560414800703091081802034508940314503440689444c00050048680c10030008900110703c00c90280050402000e01c9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 715177913 1250 715176663 715176667
    0x1060807172a1303020f030f0106030f060501050a03110613030b13030e0103270317010b1224010815040603260903100902010c06020c03282a0b0c 64
    0x842c403100484001004036030900c40e4280445184070840018a0003202d50464038030000c001a000401c1c102005014403081c2946800e0700001803000520900f00300034400d01d000c101903a264010400041c01d98000030307010b103000c5143c242c440d0400900402d110685801020321182d529980d040034440212407119600e1039610484040580010b180d4500c01b50900317081c00301c0b5182c011030b004a0b04ca0142c081c9600700300c22585000303060180c03620100d040c0820030260400d684a042c1c103001940300d26101d44003040c2441c0002d0081d44d20640c400c501003402e0890031508490000112102c14010380283c03603401c3d407010b05502c1540e5502c113103070040d03210390f10404241c10980c540d00c1601030040070162044000f001801d072140d50105400610250300400000e0240050004032444200030200a004900c00510600529070000c080c0c803142010320310360603841070100c2d586401407030580b00c1c140124040c400c1d28411071104298080d14480340b03581b4003003510001c2e25a5003080c5030075204c0c40e40340000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 715179163 1250 715177913 715177951
    0x10320060f12011401050d1e0608031210030809040207020a090c0f03051005011403101d0108060601030b060d02090102030c03030109090302250b0d020c0601090b0a05040b03060106080717 82
    0x40344034480c3c018003040c242c04189001c4000041d00c0b501c9503031824010b0f41e07690080003c5444060082c10400c0c89500002c004803230b2200402583c0e42e10408a040451880600040310080b140c2c080000762580151aa402d005410092001941000074101da004461070004921801c1520a00c0c4d40c000036595607030a0380034042d2000c0e00f141d401400d1482c0703510003001d007480a660008a02001042c05c6030700b5a98903036a0040d40c01d903c1d03240b82c000701c0302841554696258045920300c002e05880c49041602c01a8644070f005400711200891000d0b040007007400904200040c41d400b900c1e2015060064078038004004443c1425903000740c2041c1311490352440c1c9a424960b040000641300505114445d8000301c06100032a00300340e0b20b11450b00003103000245001e911070315406860180c01914200c03145541c441c1a00800340015a036001e0080c0c808000000d1149854001c0162484001c0c01030103069003000000c80314007400900550506c1304801c00465030072410811181300307880c2e8240342c03610004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 715180413 1250 715179163 715179187
    0x30902011e030f0b030c1e281829060d020c011a01020f0a0b1003020306041202060705070f0b060a0506030a0f0b011d0d21080109150608010320060f 65
    0x1200303413135580c00790b4400e9907070640c1c0d504c1d03840b824081d803c420940c01d002c3c0d030b4504000540e03e0500100c500e4481408100e40401304801101040a4400c0c0d002195140700c02d0b6000312007100d050700311181e44207410460a040810b104844689035142c080e140b10303e05040311403484183e9000c9008003400340e54600d4801c42c403110a140301002043c1c244090000080042034540e902c106910000c2c14900c00900800da0380e080345070ba038000459000e01a43e04510b06414201004036191100601601444002941c00c91040d0100d032100d07940140e045000122035150200301850040080b504440040c0f0080307002d40d611006180b0440d14120081880a10f452558042d10444014541400301ca440a40c409442c0920034504004040d03030003001040c024240345581c040580494618012560702c8002001e60000066041c1d902545050142c0c1c2222240c040f041c060034810100000c000ca00140001502003884609160054001d1401e8880d810001403007035011001900740e4a000149a07029a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 715181663 1250 715180413 715180421
    0x80105010b040f0b0306010c0f120f0206060d140a0204020f0715090c0918121112030736060507060e060415020d1401080601030201081b0703030902011e030f 69
    0x58003000150070b00e4034040c2c2015414155005040880c58044002030717481c1d1040c071199641c0c64010b284c0440081742802c01e20190326420301d030200003907207401c9501440c6000240c228003c0b036020b001000588100d848850540c1a1039084014a00980c4603034000b694030307070020384a0150b0841041d42c1e14041494514035520f074103180e144441d41441a080042040804110129031801d071010030304071494a60b0f5a4144402c800c0141088402d11181800303940c40581c403010442c0080c200e4000c0c002c6445510340c02e02084a07440001900b214103203134400a2071009022100d0761240f50515405821625070145580c0c1c0c00c9000043c4000c9010801d00580d40902001c460813400507008504003038032030410001d40a03d100c80d0b880d1300062010440b00c25503111201b44002d10940700030a584503400030f5100e040a00c81640050240d80203c0c60b103038082462030808020030301c911032424040d40e8090b005132060f128203905118444029048000c0000905442c10310140e800003441a00d56410f00215 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 715182913 1250 715181663 715181669
    0x106081e0d0e01120c05090409060b0112180609021302040b0d0f0c0801031709150331151d0a0201110d050405060310080a05060f1e0403030905030c07030c08010501 72
    0xc01d415400b8042079810001c03d41c01e4621103000440c00411042c025201846a05032403508140b404110701d00b44201c9504c4070f234110009a803400045e11040c0910303800e0324400c1500740da0240044035481c000904580c817111200b031020f03060803140001602c560040740c1040c2d000310390f000c500285045400c1480c0c840c0c55580340805408106c4120081e80c010603001d0140801401030340308140c2c4101074075105042c0d41c03541c600103040b84680481485905042e8000f030b905141c2003000b0202c85107107021b042140f010014075408641c0e1185e4a0760315010f044a5003103865030002030303449840c10300e41202030f450b8003d901e44002c02405881c0310380c0b000400e8407150400c070040d03d0308200c11484003c1da000c01220212a0200c1c3e899880b515007103608100d0304010352100e00c082c0b09891aa208110b004158a0f20443c0d445001c11065950b40c10b050b19101134600000e48041c443c04001000207010360b0000d40307018099000c032410054641c0c402d0749054059041a600c0305600c241c100f00940c0709000e05405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 715184163 1250 715182913 715182917
    0x30626120c030415093c0801060f17030a0e041b0c1203060f0506091206130b010509060d1217130213020c06010501112401050301050708071209050106081e0d 69
    0x1030703146410342d008240c581b0403000310900080605690f8160f0104c11003844010b842842d40303014256140241402480c1c3ea00c40c0780300044040c03000281004000c595201021101006917191a404010407180306100311206a8056902c0404000c58841c030503500d6140308154507601d000003070a04105000e0041c40c04520101400c00e40c00740003003103001e4688000c4030026110152259203010002e004481c8a54184409200d42404c0046203401c5520308849a4060000015166207840a1008940e82115026007090240403ca00024079a680715103401c0040d01e030945295a1102c09102090429644403540081504600c0b042d03140c81c24052103580341d1305c0b400311b1a04200350070254031040140300300c90502030074841282040070103021a28241c02c100000d810390070421420811616804c0c0113a81c069841c0c070340080d90550145403640d02800103501e078080082d0915840341c0c00b82c41d106100b10346954954000140c020010840120200381c0000c0340350440a90180c494506603480720b503101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 715185413 1250 715184163 715184177
    0xa030515091f020720280503060408190504030c12060f060b0a1404030507030f0f06020f03071e080406051b030c0307020f160b07141603030e01030626120c030415 71
    0xb0246d624001143d04032041128400b0300c200c5884040d900b5810b4a5111903014082c0fa010801082050801030040c4442e154854500b01e61480d001c6030305000e1400010304148400304203120480c01d041902045510071a4041075017140c0c144140706442e9a944403400310300012985071083c541040801440b11500180182480c2c510b445261741c4a00300d100c007500c400001003807003081c010b440c0c01a5107406d0300014155940e404211110002d503004070b504000240c00650110000500c0306691003d00050790758410998440d07071102d00c020030300034021380d101c103038910741c40c1d40d002c40220040d5120b134080451640c0c8a2920707290180c00c181e15401408420b801a6041040006081401d1001d444030105c1464030b41c8905d04d404250160940a50440c62007503290350b80da44d0246034803080a0340d21960710701251b08035000041d826149140200d803810250100d4210451a0242854090302100b8040f00c02c1d940c05580c080c0c4a40d4400c3c2d110a5060f000014144034101260b035283c40880303681c0c64248 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 715186663 1250 715185413 715185473
    0xf0902030703080a0512150a0b0418270606051e06031311120307020301060639060504150c020a03050a1b02090903040608060a030515091f0207 63
    0x1944480c02030100800d0f100001c038591106503c0b85095914907101070640c01e111303090542d030244015150304c00d46840f5a42d103030301c04100b00354a841990100d40c0a504d4403881c4d40c49080c060405010080900c80800c03c18020b003000302c003c40408008858000c40001031038500740340610011400c01e60700300c00e0000da008040f484a4440004603507000c0012004414031604914000301c0400107c090f9942c060400b4054096401c400710080a9040c800c60003088125070300c4c0e00c1a13035031400342e006454400c030f00003001e540705211108211740e4100b40c02c0c03410181070455984800843d401512b0075101035045003010300b404c0511788101c411b00251030004042888071950000e08502c11514040100b042090980c0200d201c042420b110035640107100301c1040c940702c1a40b07070b5290801e200b450005410200403481c40e0412007220b2050366007010180120206d07d002240e0401c2001c0c104e8540e40c812034045120081d842d034001e4000c41d818840140c1e64520a0500d4100380d4400042c504510810750f90003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 715187913 1250 715186663 715186669
    0x327150703080c0d02120a05070e011e110106060201020304140610050f0d1703060a2304020c12030c270a2c04050c0301060e04050a060218040f0b040f0902 68
    0x15400321541490060416a1012a00704450148081c1c016083c1e0020940300c0c01c02c3e4102c005140b060952180c10840b0356a00841150000b06681c4100c1c049500030100104010342d5a441162171101d6042003a01d0512950155084540310303800301005035408802c1c041041810301d0840608051000200b8450502181d00420201c4a03c141441162000c20b19815900c0b858110941c00760405517181410707950380941c0f41a43d000b140c085200382408180800d6169001c02440800c80c0890080f084003e030500074400203601c1a106d051861046022003010500714400071442010804100c6840d042e81c40035090544c00c6065500c0a9403d403580c0011882d02c070107020108440701005400030004040c00f22010042c2c0e0480b01038101d00643c0200414090b000030100700030348c0c0072340080101c40d5603080d41003c0c04c402940c0c005c2441e0826480c0d107021982e08d4014180e100000d03030360310005905038400101110651907250a08623103403a02581c4a00e403510600c280191409024803003c20781d5400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 715189163 1250 715187913 715187917
    0x905011d01080a110a020115050d2003010209030703050309040609063206071a070c0f0b070314010806090610120b04080d140a060801020f0921032715 66
    0x103240c100081c1600240d203040b0385030450f400c120615082c0a0795103003d090300a0283c40403a44038086401000400541c81c2401c0701c0d510780e4142c00156000c40394500c00894054402c0210032154150b4003484400c4160760103110200c000d5200b10000e40c4d45040c82c8051200390b0740f051740100340341850000d00304607603404200c03040b50140394070519003500400d08010900c0d02c1325203042c90341c008201040440802604200d200c4800d45a1030341c041c810307a5250002c90781910700c40002002a640c0c44001400500d40b04006608411142070101c0c103071003d0b040849000c40e00f42c0c446440b5920000a0041640c8203220864001000301c1000070054241800b0041c0c840781004001d01c000403120004040c440200300307071006540803d005010600c2d06114a218441c42580c40d010403034035190700000d420605108480300f411000150b03d01308000b62080122400e000e8060742c0f020071503143c0c01c0d0301055003840100300b64000c8050203c80c04013404c0c0700f5200740c0352502555015028a5440c0070903074540c001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 715190413 1250 715189163 715189217
    0x21c030b150a08090c0d1703100306181104050709261b011722080906161505070e040c02010b0d21051c020901050403060c03021e03040b01090506210706090501 70
    0x1034955901c0e1901c813403145009102b0b9102801c10752800384600d01c659010701918042c40d0046a00d0002c41303c0c00030400c41154025143e01c07000c510075600400030101085070f03440803201220740b4000b0724039403400f2071070a05005104681200d0b0030350000d6100d943e0094141d1140107103648907484249040340c030500000801104541010390400111010003180c0c0d81169500c0c100941810b80f41c079a44c900a0004600039001181e114540d500050f4100d103140c840c8502c20506aa202c85644800034240710007422004c000000b155219240c100036502c902c010443d4891141082c220704000403040d104141003801055020800300700450034880101d01240e010b0f10446a40c010f90320141c0c0c00040e01e607489658001080b85040901c0000d05036095400740210021503026120605104100c41c9014070040700c0043c80300c211040180702003035035603101640c0310314090049008a149503500381d51205001c52040030300c2d4403918003800040c0d0305c5040301c0d0041c00203080c0482e480c3c04003003035598110781c000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 715191663 1250 715190413 715190453
    0x70309021c020901263a0807120b0d11120c03061602010b090c040608100302010f230f0301050a1e1e03061b030b01021c030b150a08090c0d 61
    0x482d1601030441d41003941d11702c0d80e8945040302c0107054800c0f008103c2c118041d0034480e01c85007494890803800940e40e20440002855900c0c09260741e5110300540d000000004598540c5956010500c80c0342c4410f48600c03a0980103c540c2103641c0710707103c200801d40c100744254040c1c03074100e50303915002d54800080d801d81094980b1076120001b5900a003c81c010210702650a80c01803500c802d01c00d24548041c010320035a1080c2c1d41d8500d50740c5d18440d4902c030ba0b0116201c0240003d07561050807010f940328020800c07019004014014a02140c1880c02c0b0880e08501009007004000200401c45403601e905200010006066944d108220b07000000302802c40764403940c0c841c4026143c1c03003d140c0c0d603651040c10107188c0c131150410200304e480003d403d825006100c0d280100e4980020244c140d80000740b0700000c0c10340e0344200d08004410500032000f810882c074029400000449400c462046a18094201400d039503443d4041803400c280c200386403c0c5645a020b02595042c0380e030a010540e48081d01407443e060b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 715192913 1250 715191663 715191689
    0xc0c030c01091a0702090f1906121506080708150109060f0b0c0c13020306100e0922120806270105060a020f0706110c010914101205070309021c020901 66
    0x301c1a0f0300807032081d910006d520501c0303902040101459106a203004c0c3c8400c5c00503681d030351091101481155175500174003510340e01c40c1203084000780440c0b01da401110300100300422040d0303a4001142c0703040310f0b50304a6140d42c0c01040034415484c44404403a0b00500c40c500d0188541850320203007459a04407401403a00b2010000740c0241650410098190074000c0600400441e60000803118000e40055031000c1c40b4a410b414100c2445124061341014090010080350940c1c641c0400100c10282380001d10036648030608100c2c0110301040b410361911040c42d207400c0c1080c9481c01c00c01c400703181c15035a8103070414044505415020b0768421f006041d95800d803030295684070300c03a40a0b85000801c1d01c03012401e100745940030419950090301f070343d0410001c03030803036040700251401540d0505140c00743c080b070210114a4031310349250031f243c00b000303c074014200320344c1094102c4064401d5402c100c607030b5400300e80c07100301d40c40442c142074220440c00f0403058884070b850803559001961003203041c403803072004510b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 715194163 1250 715192913 715192949
    0x5060a050c032514010b090703020a0c05070308031e04051002030403210603020109120201170402180106031413080307141b071401020d1704051606050c0c030c0109 72
    0x1042114500008008101e00f0b10310a81040f110b0098034010403100001d010301c1003050000c050181491912004110046c82c1c1c0d26070070b08500070b40011000d074040055070406500403900c1480400081d5001d8640d4030755a203000b400c44c05403004202610a000417603982000003203000450900521420860050707074035152401c4c1115061200c00000020713a034940c00d0800d006c81d071035000d981100d2003a281c00d116140e0718941c80308541c0b42c0000281c08210481c1200c40d181303502140485d0f2243c0300603c240340300038000070325807a40e20003600170030040b0b41c2c0c50340c240041011800388103a00c810700c4903442071b1500c00d81c0d48a5016000141c0004144007443c1074030031f2180f1240c002d462080c50710103051000d8440d10343d001e55232560144500c200c01c01035450301000da9440412920707414400f40d103441718825130389000c0c5440303d40300410544560151002c14640c045804603100300a0680d9611300d5220740320301001c981401c900c0e505451099000c012a4a0140d0308100c04070100d9078640441e4000300d00e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 715195413 1250 715194163 715194187
    0x1030506010b1806180102010b0f0f1207080d0210050c07030c0602090102010f150f1a03060d080d02040e09060f01060f120209060f040e0901060b040e130c03082205060a05 75
    0x100c20380c4604d611003004120902c8855600d8010513a2040036802408050207403418411185003968416402601e4841940301904045004060001140d8102d03102d05607104e40c1e450070040d440380c40f800144c02c9645120700211150092640040e40f201300540350004c982e4000d0301198070032b000104a10b402080c061a2070703000794440700f8940e01da00c20a02c09070041e480241e0181940f8041c8102908501c4004100d40c811301c1d0752020341c0003180c18030134076641310401044102c00d4001c8048a003528204005d42d00755280380054401418550120144c0782094101c0e20305180f4014003e100d000120f8004000c540e034040e103e42c1001607141404900d2000d6080c3c3c16001e1b00c100301945c0d801100002e0300c9001c2ca000807000344201c91406080c002d0740d454aa00c42400e030b40c1e551240e100e80e1803080c0802e100d0704080414181d0000c2025801d03079900480381d910301c0c504426035802520116404100424402903944102d84803e0802e10a20812401c080006a043c06041c0f43d003010014080b82400d4801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 715196663 1250 715195413 715195447
    0xe04060c110d0306081902030d0809030d0e07030c06030b09040b0915040b0709051203040b2b3e09030f031c1409031b0c04090501150e01030506010b 65
    0x11036201c15100540320b1004081e014059074030882803d803080b04820080000b2242c580601c40350700030060310b41000795002c01c44008201424118072030004124081d140c0160b881412507010511018064440c0395080140030170706a43c0c0060141410003041040540c5e407045c00300d60250740901c4908260322034407902c07840c000d904241040d012080340184400c4c4602400c0c21072041403560748004485032690b00303218404503500c0c3d2005543c0e00c00d01c030900c25559210301601c01d0500c204008142d14581892001704550750b000540e2215070740c1c0b600500251200d4403600c16030042070b1196807400007943c04020f10301c0040030070f00910000104e840740c92542d09114610380300c490001101e03191000c0200c1c07401c060f0207441c032580d080343c03038610f03d44502401110000d2141d10f9100195003090030210001c7c08c20400302645440b01e000724580400140d803103129403000c0c0c5010304000503040d2605403c13052000350030b07000003103000b004400400006000092050644028800072604c0700c4903001407600ca4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 715197913 1250 715196663 715196687
    0x12040210050d0f020d1a060406030203150a1202012007060804080903011d061006090605130b0a020c27070518100c1a060f040c050706090b04020a060201060e04060c 72
    0x440e04114848a00c000f05401410010003041403c02480c0d151010b4091074442d007044842c1c00413010302c41003000c6406079014643c80000d01c0442c41d00302c030351200040c02420050b0802890503100032808400e55034000324403030b960040e900c0407100c51000f0200c41665003950f4403422040103c014000740070040a241903600d0420050001c1c403c40c0c0e94401c40c215070b0350403110b04c48010320550000861706003407040804215042500c903412402c0c200748044441c1e81c00f00440a22452025800081c00d54800c0d00926a10905a0203031a1000d21001080003212070141c0c0c114110386200b03a00f55200d600d40c84200d820a095042c1590b984510121484502001e910519880250340200054868004105103200348c401c1881c94010280314a01030050341c02a10b0303860b0800031380401306d4a9400c041c0c0c040d00c14410541810390500c05656a0341080d20018101110254816030612007142001d5400c2400740100c1c1c0002d000b02424200c400007040b400030005000c00c2d4a6012040b40c0314016405005a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 715199163 1250 715197913 715197937
    0x70605181c1428020f06070b0108060a060503030c0c210a03051209150f060d05100c0306050108010b030c13050301020a0c050f0d090312051603030c080a021204021005 73
    0x1003600e1a04180942c050144810740181c003800c410751a90298000503070007980c140c00e07505032104002c0d40038444001a00c0c1c0c0750075082401008180c0c003080302d08d9030190003482900000d0045150509548081d118164411070003030b0b00500a074480d150012510500b12881580c601311461003815140140c851107041ca034000780035185c108814907034407400404040c000030031414030360703200c8014903907940d600700340c001c5404140540401c0074610f500da545a0418001007101c0715030591511500d00305042100d040403a282d850700361120807070301402040020304003400c00003000e40c50b208000c0d40610000b03200d0700200c00e0004180b805d11000c102c1380d1003e044090000c5441300107041000e40890407504068529120307a001c642c200c0140040c55100c1400c00b60344142c5817520b9a40c1e151518030b041e000300401c0c4002402001942e040490036101c07210301035a0003054030408107001803c06c003000361008014900400150310700500391400190003583c180c0c2c04000c90844c18400300c80a0003003040c0298 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 715200413 1250 715199163 715199209
    0x21207170d0b120307061d0316021f0314060d080f0c0111070501090228210609210905010801060f030f02220b03070c030f020f062707060518 62
    0x10f03074070800002070410079100c0c1004110f0b152155820421040411400400c26441044142a1115100107034440c040c0b018003000c2040e140c8803e604c5c241900500f125000aa544600c0003140d200f0407111031304640192402c142e080001e44910381c551091030100c40642c01d0000b0610807291095100e01003203d41301e00d1040d1140315520300240071b0040858182d116070340c1817004075842070f011901040b0910600d00103915043c0f0b0724085103440c2c0c45803100d1010440c41c03220454081030281c080c81100610030202c00003d07601e9a45a40d4041843c968242c0070000543c80601691741c20001c4181502c21505000e9250f0b404c0310001c81c042c003007031030740c0303211b4140041902507046170301e1030380c0040c9040c3c05032105e906145c98944090baa03010485000c6d00090817040d485000c280910301203500f0903401d2040e40c4140f18140c001d24905a01603c0313969541c0d511382038501c0d84c600032082c1c0e0038040100c000900346045c41d04100929600503074124110782144060307007100036954011004602007642403022 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 715201663 1250 715200413 715200439
    0x10f1a1c11150408010e2e0b0a03121d09070c1b080708120c030f030c0d02031306060509090a141005010f03030f02030301180c0309050a05010903021207170d0b 70
    0x81e100b070308180b00d043d60304d60801c0a00049954045101007488102454106e80103100364400d10b542c180395414807007c950b03503840c0d140a54590301041005140241440f03e5103802c0c542008104a04034100741400300010840498103030794848016400050324540040b02241c2810f0540500c82000100020420b600600046440c0c01003140307000c851044069074441110940051602d1040e211301100c103410810603c580c000d2440e010356081140c2c40940d41c244080d1001d01d2003203a005955141c080d071140700c0ca0300100150380c019900a42402e44944490341000c014159407420b962000402d000c480b80c0996420001c00c006140c02c1c1000c40c40d051109581d111a0510102d4082c0801e40001c0ca111048140c1c1d10300003c01c483c12a10044407c082344030804908100030408180050101a00c508048000c55401c10829220b01c1c02080002209503252501900d40445d001e518071801d82c05018000105524500c0c04e0062000026400c0d915180d501402c002040e40b0005103901000c069154 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 715202913 1250 715201663 715201699
    0x1a19090917180907020706090b03090c031222050d020d02010e100509040606020c15070c05180a050f070e04020c12070c0905060922020d0c08010f1a1c11 67
    0x40c81040040d42c00390b02d84d844801d4220b84904c91802800085810350104000700d045480045a010905c00c050310341c0701385200006420b01c80c8260706191040b10114010b019500c100003190440400100c40301129442c101c081800d0781e42c1050003038442e0840301500c0341564050796400036540d000906000510190f0340b0043c0451300710310041c03400390f4070741031740800c98900004240607800c10041800c40c9903000f402c90f265180e070015500700e403100c01010001400e42c60f20740040c80790180c1c0480c030280501e442e0700050100c0304010040b148042445060112190700411159400c0c2c905903000b5075121000d016a07450700100790001c44540e140010100140714107581440d00f0f6601c8000c003072040751a42001c1000300c09048d11600721040400c003240c540d500306400d20819552000e0030340c01104480d40c4480c42c20030440d41c80114542d44507640380d4000045d0307200b003400514503a40d40c003100c50341a07004140c1c070310307240804d00300080b088480040c1400300c00309030605000401070201c02c03501c030540c9203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 715204163 1250 715202913 715202947
    0x7111f0f09060c120f09030c0b0901020f0a080402040b03073519030807080103170d1d01020d062102120f030c0a020a0602210315030109061a19090917 66
    0x1c0e502080b840c0c4805d01070061100d01529081507015951068840030b50303140e1518030100a400c6010940d800c00940c41e00b582070400cd085203940545905146151034014002540e0000d4051446904048000d114404070320302d100b031010060658107514240310406030700035551051042c2c00d10f4402c10442d4407102000c035800c003848601c80e82d41c0c00d540740c0b224001a6201e41081c0402440d0440160b2034098849075100908801c50703000340d000c107040005441c0d03010300c0313400c480c01003a0994001910100c0002140540001480305007240340d0300600910040104648400000703118540c82d1100c040380a40c00c00100d00d02107807010549980c0c42541c040142d40e510102c0f022800307003c071000c00041850010464000808007a0328007407981d00c51447c0c050055000030460003650881da401d01c03915440c00d111791035003140729460003c1d080501c01242c41c40c0681c01c0d480b8038030880d00287c5407013243d0308820700602210381c0860301040c0300c109440c00d060300c100c01d181c01e50041071000c110308080e00c1c20f000c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 715205413 1250 715204163 715204187
    0x6010806071e09050f060d0c020a030216050306340c05010f0203130f021f03090c0e04020102190c051302030709060813020d05070905070807111f0f09060c 68
    0x64105900d14a1203241c0b00c1d9200b9903071424003182c8004010801d078103181d081c1444040d0002c210500e404040b840b440c08494685401c600180e225140400400d07070100007010130440e4032703122214030302e20784400070b40c0d6024001c1907086d29142d0541c113482854822518038000401110b40c101d84d4408040700100360a0080005a40039030814408d040c0000841c0708803800303103e2234100020000c0c465215500c4409907600b00303e030000d4466041e011054000248404990b40a50300410b10303440c2c078282419860003d41110311445203036418000140c0c0c0015980b421020f00c20300d1810809201d003010424044994803098003c0c030a1000800821f0b090b6006520900c0c003502d502d400b107030722a5400ca500140440c0c1505403010551401005032500303c10b1503079080c2c0720304100c403002030702ca04108085c0c58060310058089078040d024058070703e4000403048480092031004120142602001010303035440d4054100301140e540722004d9400321076400c070103103854202038140584620340c0300082c1000c034424 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 715206663 1250 715205413 715205417
    0x9091b120a05151b03010510050315031c030f0b0d0308090f0a030e03010510030804050f04061706160e10030f0b041a0319110f010c0c0807050a0801020a080106030b040207050601080607 81
    0x250700d004c2c10540481524161100900f010312441003400d4165016400500b4403411180d1502e61001d07179039010801c01c20246601003220254076840381004e800d03510f804140710221410309010f82c036181c440000c42d18040340c140c50200160340312140d40ca400d21a40104c19000f0b809456000030525411440403100228203030001c1105a480960300d098907441404001c4c00e60004110403c140d103803d40040391180001080010340c1e99640083c03000008440c04000c0440e000034042000b1040c443c00d100c205141c19003040005038031540c00088444d43d00302984014103681c0e801e00f0102c1042540321001c1140c0c0a00100541e00864256580803051542003500c240302d1610340c4c0c001c00f0356031031814413140d80c003006040c07040000314104011801919820340c100300c0ca0000c10404030300141251402040008046c10103981040c05000b074015030342e04074400980c01008419021940002000c1c1122481e241c001610403012001401905c01c1c901c000d08207224007800803400f8039011070240c1c05180c490b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 715207913 1250 715206663 715206691
    0x161e0503070210020c0102100b120615040b0a06120513140601030b07050c15060f090408071104110a2a05100510030b0705130306050903030609091b120a0515 69
    0x3d00d004907900c1c005203c90a0040e013041c0010000b0505642020455103402030042074107540b010806ea00d000c0c003c17100c030030407014410307447c2d2981d00b42071041c3c1c0d842105c05c0d94410030750303070a10740040c2c0b01200c2c09200a070001d0781c5d000002c80c5440700058000a1070b03405000702450021a40c902c660302c0c4802c0c00280d0b00035690101241e40640240c1c00c940b078a050190290407100300c0b08036030b0b0020038002898030350002110254004c07150b840b45041449188100c01c110b441e1405800e1207103034550441c0500340201e103883d44040d01280868140c96598090f41343c6520500d0050301d080078090316601c1842ca0591181d48640d00b0040d000c609542501440e0804000740d5540200010b5211681d100103008405400003181c640c0f480742c802005603081b8010164003555499803010101c40301110301903503135003021090003c071b403a1602d1040e4008130203000508814064002200b031000b60744191a03c14002d843c08904d422909009550325603421801340c840c088004844600d62090880304525002c0c14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 715209163 1250 715207913 715207939
    0x18060f0a081602070b1e0a020f060108010b0a03060b1201020309010606030b24030c22080d0306050303031324060f09050f070e0619030209011211161e05030702 70
    0x142d95828141c0c455694020214546064110341c041c1d80500300b110714034400d4105840101d0b52a80c010000c3e0403042c0d0013003000d5007104109034244001a00b00b44030076414581d07030342c201d03584d00d400060640e83c000000260703400b800c0001441484000b5244006c95002004201c3c0d02c1d101076010074101c4a580e102030050103508000c02c068000000d40350020b4140403400b1150480b401c4001d03642c82014815101e1612041e0b506aaa14259548a070108503000c280140840300b82130042800d0120035040601c0f211741010006922808024900b048201c410030500003844001d5900300100340044011040034415280c401020300218040d00d10141d901550014200417584205407003041c2103034401c1140e440b210400c54921607009034040d0b010b4014040540b1000c80c2882e5542080640d840050b914022000003400402895005001c8249064015a108140b00003101c400300c04400381e064848080e0700d000e0211301002c00c554106003c0360a00c0900f0440000014110359008880d81c4202d540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 715210413 1250 715209163 715209181
    0x10140102060112060b010c05060f150907230d0509070f0b12060d1718040c02031204021c0c030605061903050c0904150c020c180f070518060f0a08 64
    0x180070f106040c0c1c098115404032000c15119072110605041c14904100710b0201500c40614114080d02c411661107001c800740411240b0303c0340409403614050790010a180fa0940011340151070014411a8000c1c0040c00303400034980d488100c410700c00111008210728100301030b00aa503220540039100c8558001c04000c100490140180c8801c038040c140c038840560303a100c062004c0741864480072500302c0a041c0c4100d03003007031144001e0f000140d5604030705070420070074400308400e54244001c03100a6400401903552a2818903c00e25440b580541da10703000c2e04d6032186000da4100b006a0702420007184004040108207494201074040d0400721046410700d5114245028589002d200c000c141da40296400e40d0b060030901c0c1c20030346c45030040d44c103d440c0b039400c1c0c05d0302d100741d9103003605000050700002c05a21342c51034800b0072580320440107a40d013002882e283c11003c0303000c200906400140000030076954580d6820a90f901c1101d04080c2141c0d41301c0c0b40400c0c1105098000952040c04202d00d0341c0007580d02d031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 715211663 1250 715210413 715210423
    0x4020301030c0b0922020d06290c0c04320c070605060111010c0f081303091a0c07061205090c0102030315060d230702031303060c0c050610140102 64
    0x282d040700c40c50742c2d218030b0800d450540350301410b207081d00021040d0805441c0c60b03078107040c1c03029105440030142c0c0e1241c000c2c464008171307940741d00600c201c02c2c004c00845041550b400900b868190340040c080d5138071521089d106242071700d1070000560250409440c0d0300d07180010301e440d10524450300c502500480c50a05542440e0500300d41c0700c807403c082800290081620f81c0c101030b4000e03206061112000782513207805c90a441401000d400851031450644140c607078415022070340702069200e00c91084000fa9001010320815109902d800d038405d82890b107880d4400011100c81c2004007040301c80040d81c0b210081c1c0440a04049038440510704000100003030070108001a114505901441c51956403269040100702e145207078542042d41403110540c407125a20950b03040c4820000c4035075114022020000840b04010100c004540050140d0307610200590000c0090300e6101501082c400b80c4103400302c602050000c1c0107072040c0700f90003d06c600e000c0b4510030076098461005196a0503400c41005981d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 715212913 1250 715211663 715211669
    0x2060a0b0609010311090d0b01061202070c0306090515190c02010b030d031109061605010b12060c0f19030605030d05130e100302060a1814101409060409090b0604020301 74
    0x4201e0801a100b0b0940c801e9210041880d0040340660405541d040881d11880a620301200c8600c524070040c0310701600a12128644116000309601e00703003140d9101d03840b0b1461031000911150f201d080200c10440c050200018014141c54503100e1454080185c0ca06407070000c1403038041a02d0200510f00c014418004e0f6000c051028004102c8032210b8038044008084d0480182c150311428000c0891690b120001400c00304c0c940c00d07414441e220303c2d00f05642124040da02d594803801881c0d0302c0c0c14054101046040e0b10070b40310013000380c45034255500203000784940310380d07801e03138400e5511000b0005426901040030381d00c0030780c12a200088815411350301445104140343d81e6000700d40e03003080159020510700741e208401e00b100740c25150b541d501180d02c81d08040700c0e1038040345000d0340c580190781c4511040e800924603030070f528454028660100d42e00c0066000b0020400810701726284242400500300c421400015240542e129680c001c1500101084d075804c48400ea58a004138019161500a90341a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 715214163 1250 715212913 715212919
    0x4050112050d200f030c0c010305042105190338040e030706050108031c15140406150c05150f0115090302131a0a0b0901050c0a02120d02060a0b 63
    0x303040300b5000d07503403601c100f40c69045510401c42031984400341030161050a0604100554481c85005541c0d403e043c982d089250426241500300404100703030f501903241100c91400c1050000301144021212881101c03140d0f101d00403510012a1202d03030690260b0541000c090800d600320342d00c1000440b01160b0301120100d1440c00d0601d000301490b10350301029a0b041c40c00b08803450140d5036a1254180d440076403007a001d98101240c00641548000d41580000c0b0003034100708001d1000309940701c903c41c042d0040d4603040038820317091141030b126503111001406203001511003909601400034081306103a02d003101d203402400b0150f900f0424485800b40104080105e0450030381c280401d64806a03da80302c40d41c100a59004000096241e504a0b4108606410400324030a41c41d1020000a0305010180c1409844250f100700009401c200540b00c0d0f12700d09103081c99039204000300040ca03000c0394940103035000c0d00100075200710403c0005c52200d001495000da4180d030b99101881c5045038200c0c00b60301c0e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 715215413 1250 715214163 715214173
    0x90219080c03060903031503030c1006050a06020102130e180a05070602250330080403110303100b1602121606080f04170c0a0c2318040804030807050109020405011205 73
    0x94081ca80340c400c10483d030003c8c04813070502a02076040d9107080551140540a16a40d083c28410b5007440d203400c0024180500080d031910007205102d82c201e202c1c91180c131980d60f040101081c210302c1800c00010f104c44045088407004445800c0068403036180707200c1c4402600c5488005000c0e00c00040e4850020070004e02c002c008180f660710740c0c0004d4441221240000108030b500035001c11240c1c0c54160810070a661280c10919207840d020b00f0000f59010728145a5209208008400c00d044a0100541e85e41e80b00e06130316055000c1301c42c0c203d426090380c025807003507c0c2c40c103445079800c0000300c80200d20f407014048030803599245800d5030313a40710aa80c2c08021010721000074000c00d030340400c860404100810031724030341021140c2c00b40c10100c890074215001c0650100401c140d0041005648850f003920405100990000c800901c1107901c04081c1d250314041400010140609901964000c58005107035070f5035a00140b621500138010540e00301d02c518a440b00104048142d0304200c2001c42e03112000700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 715216663 1250 715215413 715215421
    0x60c0f0e0a0f150201020c0316050709021815040b04081501090b03060705090a050909031309021614010207020423013501151502010506030c010f05070501090219080c0306090303 78
    0xc8610003c201c0c0000a5640070810140c3c4448104028140046032001120440c3c9643c07030040d00780105540a40031046c018031614074076280504200c11307618012590140c98030106100d070580380c025584941104640072400180c50540803c001240001c00720018601e682c8030b880c10740803106842646030f00b550007580012000c3e8000d1008002002c8001c1c1940280369440f000200402e0b0115100140340e0000300c0c007100400e60f02c0e003810029020034481503003000c0c1d008807080e500d016400400303821a0340e070b00c02ca04a9502e0079070440e0784654025000348402c03011003a80f01c40c1c06a480c6e00d03908003003181c1000080c03203100e05407200c2e00c0c100000c202194180d03000c000300c40710704007c59202c04d244c0d560b44039240c010028843e1014003c0c00d0111103401004000f040c080d00b103801c02010a4081d0300070000303c202c10381e07006568440b22585400c020b40c84000030305000e8018000742d04000c3d00144041c1034a000b08410040301401c40c0d640c0c0007101e0980c1d220f40d0506807603840a80d1111010350051002c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 715217913 1250 715216663 715216679
    0x50105030c0f03100302030609212b091b0308040e090c030a03110c010c08030103080703122a0c030c0b1503010504060b0405090a080d0b010c060c0f0e0a0f 68
    0x3180c01c980303188966828440c2c4024a8401c580c415030314444412000c0e0401c104506080c0031255024918030301030103c01c00c0d050b035000c0a440150001e1030440c0d2002034488888100100100001c54003201c1e0600c0110a0003188801030958041c00e0b110b80c0320085000038500402c000c1c00055942c0201400d05040c82d20100d14900000500340a40902071052a8011910700700803100700d0b240282d030340d80c520188124116041c0800c0c03e48150400529038004000b00d10040100d070304407039108560954464240c1002c4620003d403043d2140d130741d0300300301886d20b640c4017071881801010303182d0b00b004402c01600c1c070703055900d0032034600000d000c40c0c10502000045002121400d6120303441c22500851200f0f017000003400c491007100c0840f50f49559189a10103801c1a2184580c8001030000404489502d40c0b0381c411203010316080c0313031070301070b01c41c00c41000c681d00ca501803581880d40070100740980344865030301402d50301c849088100012421449680249801c0d09440c0c01c0f50044007600d403646081c4036076 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 715219163 1250 715217913 715217917
    0x1b0507140628030e030c010507120e07050d030908120c060c0301050d060c230c070b090d0f1a010b0a080901180305030405122a010203100618170d110313050105 70
    0x242028144d84007080b580c409403c1c0010400800400e000003407030f107843e1001900c1c0c00300b480b4807298010300e06007003801500d60024510090b540d04844051407040c0302d01e0125195078490708110414080d054804072405050006000000c1e80d400c02e48400f699406018025400309102e110780c040401203080340032400780d9005000d032444604c2e12251001c2c4403200341818442c240011034200c0300000f01005003180521211018028044801b4503024201c070018800700d10528000d051920782c0382c00a001c000c180b510800c2e4440582c12400403640e551001111160003940e8040082051180003507406001032040c4407800e0b03089842d030308445413151021291500024800c0b070320740c801d4000c828000c89000024000d08444040c01e441d80600d5551900c0c10442a5400800960b0041c018401c1d40e14800b1000341c242c90081c41d0000409410a074610000c070f8140d44109182004801d000405035004a07080c05140c50b551109100190010441a968854a40d01001126452030188010740c8130300c0c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 715220413 1250 715219163 715219237
    0x1090f0b0a09050708070504060503060402010509120a020d080d18170a0e0301052d15040c032a0e09041a06060c1005071b021f1b05071406 61
    0x20000b840720190baa0300d074a8040103402001d0560f100000c10086850325000e8800906000d40c060300ca01e061590000e80300d401800b038580c6c840d144a0618016103c0c0801042d03140e1034008000e02900c01c0740c6d0034a0401d651125101400540c2001030024021005000c1c4200c010b510141401c10640c0d010401d0b40e10785c210150802c10095081c2d088003244d5002d004a038000c00c02c0314600c18020030300348400440d400700502008489140202044030b201c8156807150b101d1003090703c012401c201049411801800101040c03245c000c1e00e03c9121142180020f03890b17131512026158000681342110030051f058100302d0300140304109a84d90707111040d82c0110400c1d00118050090b0b801c0600020406041c0103290740500d11165840c0104141d45a100b4000e80441c6000340c04003204489507008a01c886040d5040700950401210f0f0f0b080d801c0f4850400381d0f02c07081030003c080504900d54607001d0740710101c40c401c201300180d04907034114131442c1805c01c0395000100c00300da075012184d0294541d1400c40001d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 715221663 1250 715220413 715220431
    0x2070e0c070b090d230301050607020607061805010f0212150102070b071b0509090c0d080409020711030c06090102100b01050f07060f060609140603040f05030f0a08060301090f0b 78
    0x4801c800c00640020041800b4038083c0340907080c241c1040074014011408020340e04002507081030118552214034003105c0c199082650034a82d15001070003c00c40310f01c00d044000b03096034039014100b9004ca461000b01007070903101c2d0009002241704400c0d170390143e00075098980350501031007000c2054601c08001c0c8000001040c010b441026540c1c850400d01c640021800391a15041d04050120140d1602590009050100c5200d209802e1105100d696400c1401a850203170014510502c01e0200301000c0e42c00501d6006d00955880241b4a0f01c0b801341c3c2e0341901c0007400381c46840081c000d64074152098580038101a03001b000c2c40034503000000042c08040c5080c505001041120310f500b205408001c1a0142c090100401d00d038040f0710102c001c80700254801000c0101d0070354180800650034070f1058600c1c00450f001074483d212800c12550021a90f00d000700311344400501d410442c0591000352070281110340b01c9200c00d0752448103060903140c003000c0c01040700031603983c6100000e0755a9040307034000c1141c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 715222913 1250 715221663 715221667
    0x405010b1f080618010312020d021204120c0b0a020f070b07030e090c09060a0e120a020307150e040614210c01050a030f0c081911040905250e011b0302070e0c 69
    0x24042040d0b007100382c1051f24040210011722a4564040016030030f8510b4501c01812280e040c04401c505500030382c0140815181d40d684014144801d40803a04041c001e000460395480e900c0900280d66440c00044004040c0112000018084207081c15034814941580701c44021010f0b060800c01321a80040c00d02c3c0f0005030501200b012900c8408c0501031818840c1c480c0c503400340712074003008400c200c4000c24400d41c0d80701601c4100183c4000c07415400300c640002040845010b200003c0d91034050000034036400915002c1d0008000c290350840c0c000ca00000c2d0303610809411500c0c3c2d201d0710001600f21551440c2c0c011200103030729511800080c546900e01d0315002030b014955031080e005230b40c98103050500040d44001444202e025a01c82211040c41030801080030400b040140c01841c0602d11410030715950700c6000800c814141128402030300269108207c1d035611100e0041c00101c074581200b80060b52640a95400302042501020300756016001054032038a000071030105c280d8020a00d4040d1001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 715224163 1250 715222913 715222939
    0xc030a03050c070e01120c05030d141b0307080d060501050a05090603131a0a0506040207030206040f111306061b320f010504050d0801210215030f0405010b1f0806 71
    0x60b602c5003038044c2400d00d0a03440203820354180711400400d80c2e0232151180d00540c50180684d50050394803050581098845502d480382200100c0024050039505001408005642810045180020a01d00214030760821071680c0350001106d260040c17039149804181c00b04007251086c0703001000f40d03a21061219070b01d2041da105550751081c0e030106400c1000d0f900b0011050010310702039400b41d907500a03401e0f142141841c0031901c00940e10f0b90083c0014107009100500c3c501802050540c503160302201500d40e040c41105c0c3d10100c001006644180d2000400101140000442c8a80c0300300340320b9004002d405030382c03c02c61000c014521a20481c2c0304440400c0003280036615060040b4071600510100002d010309d020300300141041000c4201c1e0040200c0c440060082e0b01034200002a01c0704000c1c2c6c40400d20b011440482e620862900a41040d814003104104496403a1481c1906c218402d100070f00c8159540414040165082c1e412071000f0482044507508481c4205030f000e501a000030040c1c410a54 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 715225413 1250 715224163 715224179
    0xc1c09090e19060b0a060201020f07080f0c0d05030414031615200705060606040e0403270f03021011030405041a10090e130c060804020102010f1103070207080c030a03050c07 76
    0x42e90700c0d0485000e41c5a246005191804a08040080401d40025440c1400345149035460f80300d0701c80c00401900000c01c5500d070a4103082c041c1c0c1c40d00c80100b4101ea40c068074028010300765400444044804801c00182c5010382d0502205851045102e02040024031181e581c1ea1040c16524030700e11004c05549800751303c0344441030000140720850038802c0d1070b174503542d0b802c0080c10b2a400409a5000c1c4604000030429986c05044942c2d100d5050b00c0c0604040c4401c10802884840302c03210020241901e460106200c0198041c50003202d1080b07d050890012098046d129044078506807035080c1c10600003002503042c01d80281c404403041062907000810700500155030603980c1003150700020b07007040301402069035008500c2c5d00300c40000070908041c4800e595001c0c3d031003114003070001004800d90102c0c04690003500160741040c5907100c01d110440f210561b0001d00c0e0000c90321305006204200c00081c4940f004189a85240006000b41078070002503203059400b07500240c45040a48540100020176107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 715226663 1250 715225413 715225453
    0x210e28020d030909060b130b160f1101090e07080a1a0901090c08060d0b04080901030b06160302060a0e07050f0a080706050a140301080606010c061806020c1c09090e 72
    0xb84241c03500e0782d500e400e11000e90100d45c101c1e0070809489400308446c2c0603510b000180d10b801c075a1940d12181d0359607125942107000480c0101d00500114015004204003d03412030311400c03840b001e90300c5011180d940d00705800c070700c101940c84d5400320750030b070000ca8800c481e0740c0c00440c05141001c2c90b100240c051107012031242c800036881038802c5507583c04800d182030381c08a100784d0010400c0301d9580b1001d101c0e03281d01560440180004121410000b08500c040c0d004c0e0700700102240004002c51b89581c00c0c07202c0d8080c80c4032414811001402640c0c000b419510b03051080d00007083c5014000d0100074145000c0c0403800c00c1140c07940d54405205440012040420044d45018119603912541c0300d64000002404001d001410050300d071600f80010301000c41e001440640c0000b00f4030702502503142d64285480103141d40b540401e4603901c011815401d02a080d0001c0c0a1061140100c5600c1690003500c1007211040301c00410010305900010000c3c18800d40044413402800c00c1614820841c07181242c1d416 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 715227913 1250 715226663 715226689
    0x80319110a05090a120302070e06040f0603060e10050c070618050d1805011728020c0307260306010c0312141f06050a0c170406210e2802 60
    0x19100140c0d80c00a418280704c132500030103042d0680d4210300a2564060b45500490082d044803200c40c1001417826503484d04030b1829480d8546040103115100d0614601a240e0507014002c2489003051640000e045886034a106035005c00d0b6260a000d015609c07400030b0312a1008103851034040341c42c64030104a092128000d201c28544036000192101042c403200301215911250500170300303420346180010202ea05d217521401411480300203113110340141c14611280390b00d0a1166101040501400c01c000000b41103c500450407a06503d4108085203000c0c0581e8401c48561402440801c0707480d4000e000c0024813611a05000e50054140780400c01251030600c0c4100c4080d4080051040d03a203102c460305540c0208017004031030240c1c10800003030020300c154020082003040c07500320013040c041d1903c10380c401034820303044407540c55949080042010360440e00c042d6401d4182900140020f0b29413265040c0076514002503c560410785d0841c0103d10111908030b0355a04400075480016540c9400b850b0f80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 715229163 1250 715227913 715227917
    0xe04021c060320060304030e0d060e16170a0f0326041e0f141e010b010905030f071a0f031e071d04090c0e0a020405090a0504080319110a 60
    0x680c80c0d400e00710818030a2041c00702628245403c00101500da41c2c048035070140d01814008022054040030550344a101d110107001603141c41d4001d008003101203402240766089440c4200455202c3c450380566070821008569180d00095011000407060b11001c1942030103410319085211955000650504210f0851950303640350740c04010800c840050702000c2c90741d0102006854070340326918503a402d0b07001d82c0e01611148100c0c48100780000c0c1001688010008000307a96403050311803c50501901c010500f80740802d00c03e03400812641400220095004c501030700030b1980e6464400c9840304841e02594512240d4000c00c020001840090000d40c010202d00c07113180b4580f450300c0910403d4004c0540b61000b0014a100d003840045c403117000041604000b1140041d14489a280c01d84c61f54840754002002000840108900241194064401c80d10705550b0405540d031008840310803241c08980003003210500b4404100c4424240c1c401c1458a903a25400141091034034a284038150031003204040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 715230413 1250 715229163 715229171
    0x2030d030c02150f04030815030d0305090c0303030c0a05070c090e0c04050105062d0405120d020601090c0c030e01020a0c0b09040b03011a060d0b0d03050316020610060e04021c 77
    0x30039075504201c181180349080d42590391505100300071102d01003014001508100406021400d801c071446005403488400030b080f6400c142629001401410040351850380c94040c41d004070280d810f0100880c0c0c400c0c1040b043e0140341500c070354000c1c5e0ba281c100303d900391a800300006011500122038405e82101e00705a400070b01500003e61704000030b44005822082c003840301801030107030729084900022550b05010070540d100c100008180780c404d0040394042070380300702c082c0c0d043d111400010406212005c81642510303030301d81e00c030b072918070681c2d20309009400007484040e041004070340f050350482100c41052042d61000c1d8000e8503400008401e503080760703165401c00143c10b2950700e802c0c42034008010081d0300038010710702200007010004c00301c03802103402104009210900d81003241d03c45198640018405600c2054a00700205950401c4844403010322000e0000c2c40643d0000512602c40d00c4c00744100d480c0c0a08045046401d4041d0326020380d040780e005c1c440000e200f04100d0046c0c24003c2c200714001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 715231663 1250 715230413 715230431
    0x70308090d0905013c23070b0601050c100f0509070807050f0d020d080c010504030e09040b0703150902030c12010e0106172e060e06040f03060c030902030d03 69
    0x5003010340304a0050180b00d01d40d44100070617604030b00c0d8503e0300c130f943c80800c564030740f040c400000c1c01d41114101821401d0b4168110301c1c045401807071009500c0c00e169000340d0094002c8206450f10720030190701900c103011201c000380301588210000c0c4070b40c00d02c19054600380c04440d28544151180040e01e40c2d0308503280c2081102800c8200b15150082c04c0400c000c00340c071b03803504003c03400265000321041d01580d05104084159102d20140c008070301c1e0f0060300503503120801220035000f070005450840001344055000481d07441d000225030b0040fa040b400304129500e171004294020110700544081102901038005541010f80c80a1340c42210069022503854001c1043d144411074160854104d0300c1400d0010301400b0b6114000040500481030441c1c03481e00c5404420305481034182415504056222420440c140301041c03400c1111502c0d01c510692504a01c1005030078001c0d4010b40d10842148001000401d980380c0040091401c00c2c20002859000d0ba000703c0d09020b03c86002c0790210f03403185420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 715232913 1250 715231663 715231681
    0xa060e06070903030815060903030309032206051b071e090f0510150210060b0c0f060c0f21160e01020a1a070327021305330303070308 59
    0x10581c80340151814284240c15940c000d80400d5010f01503104200d122103c6460b03c0d11003000310f800b00d02c0e004081301d4032898019200380d500d52111001d1449000400c544280c9422032841c01820f48505072140c030300700b1031054021216400000403800c0c1340e22812800166401d2185038a4111100c0542044040c070f0503d01c0711015504996a0541d0040ca000c0412449101100504d4240d070703c3d442c607036011030600200887c03601e0480802101118505280001c120902500030015a04007030300340c3e00c6507944a00d10a0701c44804551f001940070003007102140b40b025030300c0107100802607003408446040601d402c9030740041007290b0304000c038841c4028000210307400c11984170070050244003c010b803c00aa44400148001551502d00d410110340495070f901d000f82c1216416240307008603d290391680001c20240758411140a03805400c0301c10714402d82540da03024040c8902c0c02919031402000c140c000c0080202150031004003441d01c0c100c0c40c528155802d100601955000303543e8901c0c0b60401141e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 715234163 1250 715232913 715232923
    0x406030b0d0b181002030a0e0c1009090902040f0203071116052d0d110a060203091f0c050d0c0209010e1014120a080406080609040f11040209030a060e 66
    0x581481041c0c41c001800020b030203101c2460703108040041d050810030f000c90b43ea6141c00c5056201c0300c071103800803080050070000c50f80540007001c0041c0c120380c0440c402005018040384c65280c8003000690030781060207115611341203000050b2020b000099802005503c04040381c1041c2c82c8003002410103001386455200c20402540241c10000c0503916403490000005e030194280d1500d0181001403042d210040f20038503100c5494903c02034001507034401c0d58a01628001c20703000e13403944103213900324000c0313043c61002080c0d506109000c0c1c0001d842d115004400107034030004a610004210403c1000b90010740140301c0034284031088d0b25840e640e101c5034810081e039520160004400c203c0c5000c00c00083c1410001c0c0001122605d103501c00700c104040000c40d10850752410205628465044510200181d00d4018422140703e992880c0140d00d0703550030015480700949000c0d080002c1006c0d10701c08204090360b0b482c1c5207500148018540b07084080486d05000c0c0742001510703c16581c00001038048001c8c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 715235413 1250 715234163 715234181
    0x20a0f050a2105071e06090309030501150b0d020c0705030d03050901050f070203090d020a1a0d060608010b07150b0d050d030f0c17040804050406030b0714070816030e0a0b040603 78
    0x1080d00b81c02001c10600030000d008071300014205204428a6078542c0f03503103100c0d00b40c3c8681c020780b080c4031031141404c010305140141d120403500c0e03602c0c04000c2c00703900c10360751240d000307507000e0a0b0440e140006c1e01c200c0074081d400140120625001d101000941503800704100712034101552400708051500c03112550846000509000240742e0300ba081200590b4084112142410125021001c420060011400140240d00400301c0e150313103035034146681c0c40260050110003102d18018060540ca680c41201d036201c003842a0f8402c04000c1c8005000a50103590700013403558150030001c1c031115400000f030b03c05500081d054801d5004406d0702507a00d6498090b280b2003610b42d20092050306010280100700c4100210711644031003030b01c0c010a042041c035008a40003000c0c01082401b41c43d480b0708101003685420342e00c98011815501520050190300307000c1d40c1c016908240014100070580012850714102984210304120288854220554400c105d18002c1d140d000007480e122420424080c2c00c81320301d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 715236663 1250 715235413 715235453
    0x5090901020f19032d050907050604090b03010b0d0231021c0b0a0e060f011e0504080d0c0b040b18150a0c05031501050f130909020f060705060115020a0f050a 69
    0x4000f8001c07810102c0d4019044000f105c8000544da503030110b00705d05100075900002da11510001d000240d5085036080744162681c220000c1041880500400c8041040d000380250490415901c48003103407003407400507001e030180110254814a01e609131310300b00d80c0180861240c584400c4203910007409948140000030300705403011072105040c0380c040015180d005150f140314a507401604c0c4d080740d10800d0b00128001d59420040e003510340f0480c000d8041d401078003918495104e5030180700c50840c85091018801ea03001032100f41503860366140c1100701d04006001c90311061a14101241c042c40800115440075010a51003019040c650420010b451fa000d1000007000070038000d004288100f41d00f0000b2101782400c22075907580c410000152103011351580c0407007640829600161002c0c83c0d4000b8a1034510803140c03101c81040900401017540624071000e08580d010400500010340074060040c403080e203900444030602c0b90b650303a101c086241602c089034907820a205203020080e07440d585803d26a500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 715237913 1250 715236663 715236701
    0x4030906050c1c0903020301020301030f12020318011b051507020d030608100f061211040b06030c120402010207080f01020c0706030b060a0507020402040b07060b030f030a0905090901020f1903 84
    0x82c2e0040341d40700d00c868124406820f81103ca0700991380980300120003154007038001e5403a9a52820a5018801026000e40d40040c00220b040000c52002c8111508084940f103402200b51494004440c1030455100c070645620a0000c3d03140800c00412440d00b0900d18200d40c014a40b80500d0000c0c18101038004800616040c610140076090011400c10380c8099070400002300119200080760180103168009803415200d080d00302d0500c4410742e0014080038080c1c60502882d81402c042c0700462004540540b0030782c0050104900043d059000c041d0803038014411a0740703070754907110f42a08007107140040b412242e40c0001d04440e661000d011801c0109558201041940400e0380031030014840c4001000030040006101c1c1308540d150360540b40605006a0280e8899080c0d190080c010301410000900c640329050b021418548000100c1c2c58040b12503840d4120249800d0a1100407080641605001d5400740200c25031303002800003400f082c01901d074110101030040c0001900300e03402ca00c5190101101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 715239163 1250 715237913 715237927
    0x20604320406050f1318030906020615010905041508030a020703170703090e09070317092d0607030e0d060b0a0b12150607021206010915140d080c12030403090605 71
    0x6000c004c600c60b0100756010003240c100c0c10320000003029044090004a00700509180c10300d6401345240003940c24a800b180c507171392907040024200c102c1030035860340050407101c01404a41440d0300b0444040c04101300110400c1e8a030f91000b03045812208403c001030b40f100c5400c0052024468422200f2000203846514080550b100103000c0c0e0346500071810b10100040208240c080100700d10401142c01011140441c50a16042d00351584073740c85503403107031902d400280b0507891503001d46114145e69603d0f05862112980c10310031243c00944040d0144112043ca8034010f0b00d80792903d1003620b2089400103401c07030761002000040c407500e0f08080503001051140a032805141903800b5080b2440f62400d031032624515000030f040d44119000250800519403028000c0200020765070f06803401c0290601c141e041c49000c001942e00c50384100a0300c1040a0310400c0305041490404c0341350342c043d40105140800003a0402d14220f007010100c0810031001040006041d03001404e2405046140b400e1454014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 715240413 1250 715239163 715239169
    0x906161413060323060303070204052e09051810050703200c0717150424060806011e0308030c220812210c1b01050a0c05090d0b0402060432040605 64
    0x2512304001c2c003ca50312404521801c03000d0006800004040402c0b0040704c0714030303d4042d15000c030352046001c25400d0201298000b02c039049400c2c43e0100070401044840c080d00c4c0520017800e030140900051560b2510042071108001d80725445414201c9001559101d1240210307207400d41c5a4051801c40058202c40b8411600100d0309900803001c11109203130700d49641c1000042c031401804035041c92030b91000b0712040c5050a40150088030901c0c025584160389e02c1030040d4070100c1c140100e6800854243c0140000b42d400d4010f0764000c800c951180341004c00075800d1101c21100901c9020315204090400c00184004220507200b2aa01c041c0721800d10621001c450307507400464444d01603100e00400040c2c4011076050607a0700045020f03d2245682041c0920107000b08002e85005020a0800c018503518034081c0084992400e800b4180020080035900c0d8a4070342c42002e002281e205008000c000b030100700e4004c6910072803100d240340c00d00400d850681c0304000307400d50750b10740c0c019801c054081190744e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 715241663 1250 715240413 715240417
    0xf030901091703160b041211030a050d020d062d0b0417100524040603110126040303020913091101030b120604030f080906161413060323060303 63
    0x10900440300d80e055040c107207524150b0041346034000a10740226840d80501c100e0102d514040c600580c1e007910244c403488001c0f1400c48248204a507103900801542c0e090600c680c3c0241200d038040b120050900720102c0d5440d0036224030380e010300f820700801461418582c8900c2c00c80c03280049080ca120180e146050102c0829004030b200d803425180000c4108032a40005105e801c0f4000c4006004015a01d070400da80c0e041e03103201d80c4d41400c143d914a02c4518003418644540c5c0e003680d80261901c0060342c4018011514204202440c14001c201d03a402001d04170100241180036034402e44026032a0120720302032204800c0702c1c00050407401d0030091520081900c11610600894084c030b0085500351010000c00c04074403115003030060912034042040213042c1d00c01403a4a103a0307519910691151aa1010581e032010251a1905420001000d4200d81c40c02840d102c41c103010b4509556080106001800309100c445611810200f600c50082a000280c101711f10b8200201190300720001d802c1050110340d6034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 715242913 1250 715241663 715241669
    0x5060d020402250b011811041a040914150f01080703050601030e06010e010905070906171003051605031009030507151b020a0b071b240c03020c0f03090109 68
    0x6a60020303803c88000d020f50b21001c801d800c42e40060319100c41d24948542c01e90320910580d4448000c4c1010300203140b200340180d404070704042581a00706418950340c81984003074145003c500a00070040064110385038055080b120f04120040301c00c502d0a40818480c025007502d100744507080c00d03160300e0031a81c1c100389460740005203454009115034074800160010044904a502c191064100000e204200c400e0304d503050301c480c59070520542d11054000d40c0c00745214001d0030086010441c0700101040b10a00c0c00c2e40c004a803502c82443c2c2070380ca482d02e03410a0064440c440c1150310305c14040c041c505003001411064442d034070f0108485ca01e035840052050042e0300f4020710a980758110110043d641303401480144007800304002180c8a0454003039603564914000704c81c50200100003c80d80c40c099605402a10b111282704030000c2d01c90341d64014040f038042ca00c01a00303000348800070300543c1c20b0f1295281440b80307500d006a03140d240e07003c92494502400616036940d841005280c80690740440c0307482c01c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 715244163 1250 715242913 715242919
    0x50f0102060a0e0304260c01110a03110114070305101e1a0909010f061704030f030c020a060606050c0f070b0714030409020a08061002060f070c02121009031205060d02 73
    0x511000d0140f094114481c941c4440f501d01c000b9480b10f055000b0b40f0080c2109085a20110b400620607000155041c00c2c1c10f0f042036103180c00200c0d841000c01d004440380d581c44170018000140a20303240101103204401904c03c100004e17514400c0203054440c2070b0005000e1700e81f002403000a0b40c01140c07509541403190041d000c000d24064a1100c14031003039400e42d402a07000a142d102190b840704110b960303a0119104405c0010905460030620b4032100b10407500843d01a035406403590785400003a00901501003d031001c40c030540c0a0400480c486100d00030141c006c5680302c2d941c0d1500110f00074030b04103a41201d009030381c0003030b40200300c180c0c054801c07075032500d9220700d8412540e400c21000341e00350b00903903101e40d202500001d071000300258003d034142d02c1031204917550103424030723203400881c1d03201d104548a41c002d0708681e000c01d201c2401901c403402c3c0a40300034031042550401e580d07120704103546441c0f040d150303a0321414884201904080e4616800807000000c0005103810f90020741000c50034140640 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 715245413 1250 715244163 715244171
    0xf0610110309040c0c02030d210207120518120705120705180c12010909120509010804030e030a150f0c020a0308060d03032901020f0a0b0114010507050610080601050f0102060a 77
    0x1289001d85c040c0440180c0043c02d94018110f0440c010309042e88141c00340010004201107195803080d607100b96100c231900300075512030a0741d1502003078a095001c40b001645584050140301c3d0b25035502c98400d00311140b07020152144130b29000034026a0031100c2494015a0030445041c031054032402080302d04640d44141c004141e440d02c034a540c4041c403800004184c10010754001185985590b0019a84103228046501e61070107008011101da01440290b103000514420100340400e202d041d416000d0341008040c0d0300140d42c1c81d51807a0710b0340f401000e142c6800380c0701e0f018803010744c01074840e01d41c1d0415540013610b241203486d85c3c010000d08000780000e1150700d038001100140761080d0300c5425401d186010b030644031a460a805595410400d0300d4030300605c1a44d10039000704c82c4c08035005003007950121040050307908003114480c0ca100d40240060400034184009404244100301241c0140035040c01488010b0a102d040d80c01c1003816040180260480701e0710a00c41e036400940d9941c401000c2070002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 715246663 1250 715245413 715245431
    0x120c090b0322200102152a090402130512011803050f0d060b340303020d0b0603190606051c0b01091a040f09050705160f0b0f061011030904 61
    0x42ca004045840501035154481c00700d01d040c0c0740c080000080c40d900344c08403100e40c2400c52042d50340040803034071010f41c0300c0040b000b10b00d400306001e82165100c0400d16036508002480d0041000c80e080041122400e02d440d01007003001d82060324185078080030b0a0024480c000002c460f1213070103000d4450007400c2040c00036030300007072940820a03900d008145010500c10b06940b07040e0b452031908802c0200e41200035220b000358410700251031401c42084d020511a0340440320b514290300940190844050305a10703540404030b41d41d584c40042d8400e0f03000f0404010111b0318940100200c6109410074011f0150401c2450140140d4030721000540c0d952400104c1c4d048070007401200c00d180c0951003182200c001d4000c404900100d603001c2c01c156102c541c4410140f6580d1446101074070001e803181408103400b00000c2c00321240307100c1440f107807038003400968114100076601c04040e20812102c50506141b100240503041c030307060300c8960401d19145407900100b651031880c035859200710900c45102d150749003001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 715247913 1250 715246663 715246711
    0xa0219050a170705060d0b030307110909062406071421030405120f09101214010510030903090b04060504060306050f0a0e06031002030c220617070908010903120c090b03 74
    0x13487c1c05420140681f40c65144131300e02001020400000a031081c0d6007040024006800010b01903c00d0b42440003444c47c13041442ca590b00384e071489810849c0c00150030408071001c55011040842c1c4100c4c01c01c02840e4a88a101c0c11000500407a81c40d103942903000c20500c00460000500341031440f0380004010364071281d10100d861944501a02203400c0140005141195a003005010b60402016103080c80740c504109001113103901c00340519076200580104046006110750720207241c8510a00b4032100315510750000e12115002580075000203180000d083c03091590500680c0c0c000c010580c1c44450078018034000910b410510b014100c0401640c9001a00960302080040041203c0f400119668101019900c00c150b102402056800350034401c0c80810003082c0030240c0440301c0c4da903260411011040160020f8141c042e25000801c2500400428107440030312a1b810b0381c034031a403034451041c10340c819058207407010502c940c0140b00c401c541c05c12040300c0740011070358011002521620114017001c0c007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 715249163 1250 715247913 715247921
    0x1a0a080a2d0213242306090d0c05041505090a0e03130605030f010e010608160201060f0e0708010501051312020a0306021605010b0306040809040b030a0219050a170705060d 75
    0x3010390b001c5458414080c01e0f011943c465800c10300d030840640c03c03003130b2503400000741441280320f2495489010844104c034030001d407070001840500104854504110076000503040031069001707407100d00081d08208050300c0c1c50b1080c50f529003103400c640c0d150503280200060307003504002c0c03120207050740391154109040802c0c01100c00d0003580c0c240060f08162107000080107904200c5007040115050700001c02c0341c0b0b00c4400d50714122981551303001111b550701c128407aa000b005100c1a801c1d9900c402c00402e01e0300605c00c41d00050440301c48200c0782803404060041c901d0506a2009052140420a80c5200c9102039240015100050030f000c2c1590414070119502c28450b500150070701d4408650601d407070407581c4621100c00d01503c0284600e03001d00080540f203001c180ca00501030700c4208446000c90510380c100d001e840c00000c082e0703003504402e50041101902c0040081120580709401170005140910b003207405880d00c01503d030362444031582c149954003424018548120300208110f1503078a01504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 715250413 1250 715249163 715249253
    0x4030f02070f1e0e040f170903010c110114010b040504090c0e0c1207051303061d0d0509101110050c13080304092406080601020c041a0a080a 62
    0x141078141c66941c01400884070702103d50542c075030055400000701344409101c4103004e83d40201514541403c5552113100404503180812030519040c8032184541c4d400b813041040203140d039120020407500105800d400c44083d05582c640b03c0c000e040040c022081d80030241e07802d9034403c1d20700180034103450a249103d400d0b0b41d401030790911400030400158a00040c041c040310410320001c00900d031174811041e030b00782c081c1200b104160003100e0310400200e0340c541c02c4142d05901d5400d20902c070260807a020360070b0560480c100d03404107100068103036150400006420040791281303080c080080d0840303040e64a030404110544002c035280c4003c2008034030348000711841c4801154443d5015580d410713400c0d8903038005100360750880e4903040700a84480c4031100d0340614500d4010356a91b40b1801d1110030380e800f10011b01180c5c1148264083d0400e035031514403030030701c65a84800480c074040c40342c10700304a40b10526410066881c0c00009408001800d00f903154101204a12244804500702181508102c84005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 715251663 1250 715250413 715250429
    0xc02040b0a1e0611120304020d06090203240c0412080a180e090d032705121206040c0309030912080d020301061106100503120d020c1501060e030109020904030f0207 72
    0x98403146042120b0721140084884680790701c1c040c4810903c0040d2150414890340c41e42d610204002001841c08128003ca00d43c0b00700740010304000c15401003840c100400c0c08516601020a00e00b50750100303c25107240d400b5400c0a80c2924060400030004c2e441001000024a420300100390b00e680c0c50300030b400480d800320000015000080e604c126007414494281c0d541c3d4810300550704801503651080c06010b0341241d280000c03044074411940ca2114122041c00256103602a02e00d0103204112480001c0090980414140081d402d00b0340070001150448070001c0c092500c0e0080d40c600007904201c052048404c3c0e0110110300614905040c3c00621070401a02c0c8000d10001c00271802d240c1141e609660440ea1400b140c01d15921440c991404090a00501340e160340107075403420100300540f00170320442040340805420700000110151a22542c031041c0c1c4907449001c8018411158004400c10140d04103c009010504058020501a074800351000e01000890000c850340715000304a150000d100070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 715252913 1250 715251663 715251689
    0x4120609050f100e07151d15071b240c0f03030501031b0806010b0a091d06240d020703030b0d0c1505030108030f0a0903080d050a0f0c0c02040b0a 64
    0x2c40ca10a03103800340110782e080081d150420380021400002100c005540b005454000311488500301034034800500540341481503c8102607005c945c860600c4240220005101280c441c0e01d00d02e481c41c2c020150301480700c100b1190f41000c10841e111010160004031030517606e440065110041201c400481038006002c171000d058042c07080551560015040700d01603003030710141e40c1c41d1001c40c900241c000d10440c91a0b074010340050201060f0300000b00b500300301074100490300b03d0f41d4100030385a0000c04061f0428103507002003004580c2c00c000c1d0802e00c0340700701700400840022079071030400054003c0c8401c03200003948c08034018080601a9000c43c02205000740107115070b480d1840d12a6041055019002c48034060030359445030f80c2d000b00c064a0603284684042c500f000e0154003010880e40015800008001d02d4640001c04100048020503190440c8040450135241842e41c3d44240c0f0300454103400c4040c6800e41c0035444a03817204021052550407240455231080220000f40d40c024950400c41d440020303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 715254163 1250 715252913 715252933
    0x20c120a052104020f011d13150b25020616060603060c0302090108011421061b0703050d0c26090f010501290f030702030921030412060905 61
    0x1001410710650004503250800b007402610042400d8103481c000d4210a00c01a130b00c1c082d42c00307006400d84490303064220b07880e69202600000c903038611404141010342c0c0d5514500d8071100030005020068460003012070310341448a560803007102c02d803e0715012010280000c2c03900b15550f04080301c540c3c1d034804c544c501c00160395003820401032010b44000ca0341a440c12803030502c1c4500900176501c0b5503d05071240c41940c0c0ca000340c100715410302d60b12100d41c4401103e40541e426941c1e0020718001c6a042d0008040d9407400303c000040c217851101c40170048010070f0046400003070f03102e412521041d0441001056914130603e0580d20a50041b008595040f10001c0e42603280d030543c4101031099103140101c6410001c0416914200c0304207008101d4a8029400c01200c20b08000c0c000f04100c4005010341c900d0a0141710750301e11583c005503101d00040e0000510a4103510b441401e030020400502c00d055406d13992010020350307030b1265128115000b407100070000240211588072000b40743d0020240c5070f540e02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 715255413 1250 715254163 715254167
    0x3091203190f09030f060914071a030f150f040c0e03060f01050319051c1e03050f06041e020a050909010b040f0927030809150f0a020c120a 61
    0x46058518030148201c0004400c29106088054030710a0945a803940c0c01e045403601d54417a0b80e01d0038145c1d00b458907518801c0000c0c3c80c0002c0c583c00c600e40c24014180c2c3c00c0c01d00382d2500680300300410381c0b035803ca4244144103404078283d03800b54001040c66000d08011400328041880e4071b00c44401c0720360003803400c81c02c1021a900001030985d08142102034880d40da44e1903248074401d41c802e0182c0b0350941c0c84404029003040040e80c083e84020700034002c80f41e9403511b6447d8072814414200243c80087d03001440c40519031151a44c948050103e070405005a01c1c00103050000414020141440380b40c039440101c10003c410b07482c8800c80d0801c2c0200359910440098003038550b0b8082c41c4128020491000001040c50028040e14295400002c481556a1501c01800042d002c2c1070080110760b0358031284240b5120760202200603440c40b984500b8514a41540d9076802c0c49205046106c400d00807900700015030007401d0070f140d4001c0c808800141c0300c811780e1a410707103083e9640044886102c000503840703000315 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 715256663 1250 715255413 715255417
    0x30501051e1005040908040b0c0319050c15130218060a06090e150f060706091407240c08030c09130c051e0906270d021f0203091203 58
    0x488030a0041c000c2581e251996050000700c41e8691080401c035014002c9140540007000b1840c0200320b9039081c2900d40c5c000c40d440358440c6121408175440040c4c051082c403907040310310598800c682001401d01440f245107030b449e12208807510301a0070342e0b000040c900c4842c0b004840c8860f50058000c2100751200303000200080400e403240e038800d0b01c0380746000441380e11642107903054485400500c0300c0350b12141800c0045072101c03000c450b0b1203848a16180001e0f124500a443c81030300078000862100410700b0445d0111064840d1104140c210132001e0003403101032200030b800d0b80071400c08500c2a0b101c1c100c0485603c904c42c10020304601c000002c0c480b1000b80d85001c1c21000c00c0c21038007581c0720104811400202d40855012402042c0300b40a000e4040c00f00207094a074502d002c00e000c92404100d08001281c0d50b0089180c1300d900320a05000042644125000000409059400340100c0400341c0000b440984107135402110406075079441c2c100584244140c8401d0303038000d0b04102514400d612a00c0d00c90f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 715257913 1250 715256663 715256671
    0x1e1b08090405060f0a09050621010b092208070510150e09010c1215030209070c0317010b03010e0921040e0a11030c130308280801030b061c0c03050105 66
    0x1482c140404a42d2518161181440c2903038002c3c81490003900d040d0002c030140c030008103610b500c40b06e01d0303482c4800402e80304142c0c482d20b00d04000000702c031000702c410800ca0103c0940701061034a9030b00b500e0300281c000c00f80b900f44942c0d0405415a1036a07020300e03009180c280c500d6007144081d4244402d21005071000d0b04150182c8015501d407031740716928004110300f22088901c40c20006541c18400b140e29a600e5884946030014641c1c0780e8031642e4480c0c01040600e0700c143d03210000a010345452505150b0b101e600d0074042c83e10b4140d10034040d458003c02c0c03140e50006001c1d0700002c02503903000ca19543c108100072402d0070583d40341c12454140707102c5c220040380c01501c502c00306c1c4207031000040c00300c1358144986412110046003241c1543c071104c2886805400000c150b82c200060741c90040b022805250140001c0050070f895a400000d40c042c8070900c0446151480c020701c003643c4014000200341031401a80020281d0310381c01c3d0000d2400010144981c0004040c00840d95034001100380013064201c1841 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 715259163 1250 715257913 715257919
    0x40e030301061101020307050a030b130e16140a05100c0b070210051305060408030903131509170a0b0a02270306090f0a080c030c030a0f0e09071e1b0809 67
    0x3d480460549500380c0c4422035101c40015020411151490f009600100e5401c20141001c8811030000c0c01d2070301181c02d0006a0350340740c2c1c0b02c1da84c003080e03041d0040b088078098100c004108aa4a10a0f030102c0c400349260f0141e1403082e030b1191042c040e1a80306042505801e03400c00218201820030404c040d44500d403c91000040508100c0000c49410110021000180e1b1100042c090741e40c49441d01d0500b82c0016010203018001000f40c000159098000360000d01614085000c140b030301d624006d0000000c543c00241c50001c0031036907507600440820045080c540221091410f40d58440d0802b0091040c2487c1000400b0b1401c6a980121500e138202c501c100c03000d40488607283c0711a10f00690700c481000301034400f5401951000c00048080016040998140307003241e080401c142182801e5800c1540c3c400000313a404503400c8e07812903200d180001701c5802542c04410340d04080d10001c000358500e4030800344001184030000040b500c10000c00e07103e00b002c1c0f2421024140380f07242040300782d40041d4400e48 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 715260413 1250 715259163 715259177
    0x10806010609080a020103051b0a0e1807200c06180114040f030f0f0b01030308042a03120c23010e0303280b061207030e060114010c060b040e03030106 66
    0x140710350040c1c28110039901901e005001c00da0b00ca900460280000604c0741400310060200d005d40b805c51040030b048101d0081d140c80c464071500d0410700100e02c240405c02d4410442e03c805014810342c00c4026031410040900003000c2d42d50084103001d01c0c0000d214810b41d004000003581d6070b501100340c036500d0941c600c00d990315501c2854100145415028074000c0c0c1d4050103101d0030800000e01c1281c140d22400c0c0c8201422080081181c8880104d0b0800f40c3c0b081d0701044240c070820042147e060844114005ca4039101d52080c000010314412404150100404500040421124090007001c0401c101036211012034240300311072140344c07001010341c40440403075030805112441505001c415240b05d1801c001d00c0c0d040c0c24058824905a40c030005150b041c00694640350070280341c40e51802130802c002000034401440c10003180c01021642c80c00c1c0d41c0d403845d400090060141c407014041c64018141c007460b05004040d0030f400c0c100000c00c07202c217003150f02929049079901e00f01c13030200c080d5048400c0307500d40039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 715261663 1250 715260413 715260419
    0x9040803070206091f0b04060e01080705030f0d0e12010906050c090a0801060e0c0f0d020d0c110a030f081918020405070203070803040f0f0f03020c21070e1f030b01080601 75
    0x1d6034845101da09a0013a603170000c480380703804403c0c5d13100b0702081500800c04a04265569000000ba42c420b0b0014071690708003041c14481d606041090b200d1122001004000507122544002c3c0900d4001111a11551034040c0d03e0003064403d4000301d82c2c1c2500148200321070b09040c070421402d64070866002c0e010301d41500000925140c103104600454051400208244e651510756040f07650000205c0819070b0710500c1000c00a203064800340c2600e0140d480d0000b500c00b90014064a1412100700711400c0b9803181c40c400c00042c1c0e01c030003050000b50385410010b43c0b0351a92410b120b0380d00c1c441c1e00b5400c02c09240c244074848450650803030502007402610b04014540795900203d031240305030180500300e070340c080000c07034009204d8070600700304d86000f10150b0600d603520303588039111403443d064160016030080c4145d20f00b501d4000224007483d01d140318084042c140c43e80e00341f51140c089100700c1c01180705240001d0100903e0101034660200140095142c45450b072501540f184028000c1c0100791240740004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 715262913 1250 715261663 715261681
    0x6040b01050a0803090906042a142b060510020303010e0109050f011203090509040f02040c1b0327030302030d110406210b0a140312090d02010f0e09040803070206 71
    0x20400703032500c10f0041d501c3c0c81c07109424010b4814000d40600e0708103650306200f100c9405004940780ca9a44190006920540300020040005a40c0c410304d10807034204000715050100154a1203c06040b118068031107000c20a040500518aa070b00182e003046040e0a886445540400150b040c4e4030013002140c0d007642c03101c0f8843d048036411035521240c41c81c2407005004a107010300c0014040da100c7d00e060100d061b200e00100b00490801e0301c0840d54500c0c9403c254086241900031014000c019140022520300c0c081c1013014161402e44001d410310103401d4910100f01c0e101503a030110909054111000180c1d240f400035642d41c403a0001c0c9e00300900e045000c1907407080000c1250700702c3c2c0b880c2d0f0766480700035020540d20086250a000750040c4030754401008926803a1102000e0003800300d200703d504002514800d050402e600e00040782140b440402000f030b40303561031080300c460490b028a0000d00744810500700b80c0e4420940444640d2000c4100201f20410041c1d0000314880c0d035860782991004c2d180c032408 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 715264163 1250 715262913 715262929
    0x30a0504170d141515030903041e0303020d030c081b0d02030405060f070e0310022107031b0216030803061203030406090606060c17090d021206011d0f13150c0206040b0105 75
    0x55000707031503445c040c0a445191020303580140012082c2d9181558800042c07501c10214000043e0100d6922010010b16405105440c00c0110a007028400540060002800e007500140f03400000c654034128510f508400a0a484071907080020031946d81c1480d090941d91410304489603c2101400e000003640c50b8410520251500b40180090003001c401c01103840c040d420643c14113040b8048000f43c22480302e941d4860b9401110f10340c130000399001c1d98030788100c03c4100065006040d5405a04441c00308540e001c1500100c076004250742d5140d4075690000303018000c0548040310148404418803003401090b074040e28259118520400010b643c0314001e4960ba4604c1c02e015003800c10200640030000920340041c1040311005250610032100d07640010701482c5c08404100d0035900540043c05081c51508003101c02440c0d03d5100401480c00044580444100821024080c50b00603410003c001003107102160000741c074803080c02084000c0c0310095440c1012101a510000490000505030400c980 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 715265413 1250 715264163 715264201
    0x7080601092d0908210a0e0106060507060b0621010e060a0305061515070507030b100f030627120906030507050405040e0f12030a050a060b030a0504170d14 68
    0x2e556503104105601c204003c2c400400c0a40744401c040080380380803901e4950110b01ca00c20050108a2400d10502e110f00f2124090301882841c0e00d402c00520165400c08160342d00b003940002c0c0454240001c10200d00c803801364498980c1c4444083c1e070982803540907980d880341a50b914500b000c1d007030782d240c1d42041190b200301d102c09400707900f000021820103864080c0d4003194210141210381c014000504910303040d4420a03003900e458000c52428020051102149500121648030860449040040c1c0e445203060520000b000c00740e450f180300c11144000380c080f0881001646020b5024241c5003032418101c00c00c40b40d848001230a0000c0402d416020b485028005d001d1070362075038285828203061000902c1001e10800b2948103c2e1182c0c0c001080400030242010650b8403155101c3c100b004505098400150564881508140c014403046800500f5294458180400403503039807034a05007003c0000c1804418540500300241040c0d01203d140c02440c041e11101020b98000c0e65003030351407000d0f404108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 715266663 1250 715265413 715265471
    0x3030126030a0e0d0c03081812010c210e0115051003060f210b070207030506010b0406050304030e0f030d020303100905060a0306020906120702010b090c030709060f03020702030708060109 82
    0xc0020043d810300c26508480a48550241140755880b030701c8415560300700403220100c03819002e480030a81e0511f40480415500100b0003449221030440300540590005991009484400724040240c00d80da504400d010125107002003105d004010f1a103c225285805138a014850030b000c0610700754468031800003160805010305d1002803c003000940320349240130901404540302c0e50b0003004a180c0301384270750042007c2e03002855042c0c514079220f8200350059000c0a4500740c140010815150040f08903580075505103812100008002d00003242901d000a0803074161145020808085400000440c02031014454040e00d0b569583c410400fa100126003036500407024000070000549503030007030000715800611903814620704d240c05030a011740c101c4112005039160810740c42c0500382214131035041400c00c080c8074910314040c800540154043d2003220200010001c00f54021031007681503440941d8010183d0380e80640d1070102c1e591350b00007801681c103087c0c5001c811046203400020700d84c81c130b0b6106d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 715267913 1250 715266663 715266677
    0x6040212060f0c09030a02040f0609050108030a0e041503080a0903030e041806020702150c010510150203121909030e0a0f0f0e1015020a06150501020a0b10030503030126030a 76
    0x40c3c026003100d9000700301c102d0340501c070788080000165203500030f40e01000e003460340c0010346528204600c0d042d10010703407001100b50802c01082d03501c1ca51001400340c44000a440c0410008a1400619011034496101401100c404508940c80355402180d64086034041d5854040800c1c005040004443c0e040b13102040b841258141c1d44001411030b000340400a0004002c03040742440409400d140f81d00440034000140d540c0d0b07013000800740c04544078102500015403200304810b10300f20040d5503440385c007460b889200b01d8840050922440c00b4040030032100206018044003030f05240240505907025000c3d48a65003408020461751a03002c1084100c41c030744008150340328a8006007640c03402026010003411070300e40c1404582c003102c141c0310429041556000308039500e050f040402c1113401030641d4440c01c280104c002c0249a1740003420f80f0142d0742148800c03980d0f488881c1180300003a041c0d8401000c0340008400010b4503103002102e10000c800380d806000f00d442c2c06034049900ca01c2520403200101b803c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 715269163 1250 715267913 715267921
    0x2040506040606051b01020f03090f07080a1709310b0d05030a0f050d020f0d0b01080f07030c02010e0601031b290304020d17030106110712030f050d0e06040212060f 72
    0x31111184a154120b200040c64482001c10032000d89e48201c3e99080e00b80c0c4440903007030004504101c000010016500031741000200381e0342d045013035070382d0001415009401040007110b07a0f480141240c0c0f03c000c22007940d00314007003030010062152941c0d091002c02e289000d019244c242054001526990743c060060746c030307040c8403203070903180404160100c8081102c144070394403002c2e049100929154095940f060b031030391800038842c41520040c40e0a14104091141444110e40c040342c03401d5003000035410080f44464000703504a00500202401140c2c62056a00010030b004041c40060060302000d01c01e9001140c4540c02111b412030b0420301300c4002c10b2032018100b405209500a160018070017841c03c505000c440d10384420400e24416000b58110000004008580d000b100304509542000d016048203840c02c261244850700300940075052141c1c042d42d1556051146044a080501c81c03030b4108040c030046400d0b659119401c82c0c04a020fa500c61000703640607900002c40a2041c20040e5041d507070360307035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 715270413 1250 715269163 715269187
    0x181b0504090b270a0f060f090309091e05100e1311041d010f0506100212030c0906040807060c06050c07020f010f0201061802071e0b0703051003020a080102070204050604060605 77
    0xb41c1c514052001d40390240c201d030946101848688a0765001c5e41034909120258145442242c0442c0002c8031054501394600002a0f0010201c40440c6d1186e240040c09044440c410309101030101c02100704c55180130704024a603030740210b80c4800da035200304440d410340d560706000b170100e0840307404080c0610382603442041c410b142c01c5c0c00a150442000042e15824503440c5011400d54648030000440291181c01b0048942415120615840750503c001c16060080303081c095803510010b0191a00c160001540580355212203084030010300080003200c00c02a0f4a82d002000d9905128003200c40ba402c0201041c60300c4181016600913980040c1901404030342c91006407880c5140040440035552608400940214640136445050403a100d01503990941c52810803c80c01201c1d0f03038003100d40c03001122003000c03642045109a112015060020f4103454810005104c41080e6000a501846440b00840c400c1d03010340107010800d1081d00c0610194490200308004e40c2c0c0c050240c0c6001400034030204542034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 715271663 1250 715270413 715270441
    0x12030c0b10030209043c14070302100f0e15040b0a02010f0509010b012006130f0b0a090b13080a03020703050c06041b08070609050d0501181b0504090b 66
    0x216045682030380c0380b66254085405144203d500341c5070030031030b6080050340b910307040c0e150450304010042c00104a600018844503c4036000c0d0f000d0b003100d091560b00c00f070a403c204500400b83d07400078069a40b01c00b442c4001401000a2100c1c400010400302d070181e001c0c20301c10302424601440151541c01d050404101e1881ca42021405004664030b440c1041c80b104481d2049a0140c00210000704002c0c48642c00548007100101e280300142c8901d1020840f50700020607965040070b415070442540d0201402c007031404010826018041c0400e401c2171241f40f03060755000c01115481000c616485554032404050201c3c6022000352548400704080580700c0e11030341c020200e90744241001030502d10280d1440386864800c460880e00c60500207010302605008030700c83e0f0014980a002171003402c0c207085005100d0501441402d01600c94014200b007042000e400c07080c640c503e40b580c80d0421100c5810948029003040c0507222140842d110045220b0406000e6514a59005035101d2419103405106000e48 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 715272913 1250 715271663 715271671
    0x305070b03041112011514030111091c1703010e010f0501170402011b080d0c0305061905010806011e1d0a050d020609041b02010b01030f180b0c040f120c12030c0b 71
    0x6559681800c400f04540c10103600242903104482d0300e2801c0140242340c00c40e01e0055000050b400c003848140c0c1d560307640c080000703220006882e030034050300710624016110104c240409401d0b000040000f03c8c1d50f414000d00d0f076040303c80b55054107441560740e60040d114051042504c0ea104240540000e015500410504000b55000f008101550107151200340c625000792620705d2146440c1c20b16010348a9146c040c80e0380141c0d00720782003030140b40031541d00b080c000710078800c0905020000e4001043e44e8040c40c0621800258420f09805005800c0782c02805c00305203c00c40d2a4540c1c2140341d14803141001d1000708183c030b5003d40f580981d4800c0d030f020409503070000d442e12640329072604d1540400380003000c5842c000901c40e4001081024030b55002500380c600002c007901e019890080c50f8210800300382003d0402a4200400d030300c5648800003424240d101c0c6420a08112419060000d0001d641c406602241401b500348810f41b1501d814a000c02c1004401d4094002a25603081e00c000c182065072403500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 715274163 1250 715272913 715272949
    0x80708160f0e03240f060d110f04140603120a02030a14090301020c0601030c0b0f071103010f050c37050a1e110c040504121107031b0305070b030411 65
    0x982030038440044c0c5030001e241020410300d07203141004c0c004551030360710040c0c000c0007007841e004c540e01d406008248070381d04166000d40b8085070b00d09040040d8542050320004504080d0042c480c0c03d03003007030700d00c0110181601d01ca4080d108010402d081000740ca02551089201c0f54080c52034210f200d541280c0e4030100400b104000ca03400c1102c1219a5024801083e0030800c03240600b44130341c514108074034114030a41c44a0110841000366141084542088440e80b0754412054450009a80302103030040c02d000000c5c241c106d2038502407140d0f060000c40508000c0182c030b2090919590038800d114088151030f200c00541c00c0d1a00c5038414000c5c0140c024008040c03591030180c031001c00c035002d10341d81c40d030b0001c0030394020840c0c540300c040500c0320a0140100c1d151040d2800e020320308040c0e446403e0b81420103c500100042000f4a440000050000c0e0f00295009917a440b06020340b124101e009900d940700071901445407010004915280703005481c8030703039040362061100180c05024803030398011103545084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 715275413 1250 715274163 715274177
    0x50906090607050301171c08072304030b180106060207090c0905100507051002131401031401031b03080705060f010f12060207080906180a1e030807020d0210050a080708160f 76
    0x3004c7c89040055001c92000b0383d50360901d414012301c00f621080700000c2001464807402603144401c0d802000322802c40b94015443c2e034040d0380741070350300110f1001784405040070b500f0300b06d00145003035002440f04103031380c03521100b0003610307080d00810f4884075450300c152a00b0089407000c00b4140c6001e0400341c143c0c40d010b42c040d90314010395208944200e030300030108594141c07207050b410300a1410700980041c2d00b800130b00b02004005410841c00700505c0c014800200700014246148036a0002d818070140215800502d090301d80c400d51a009403262401c0354000388648410000144d0380240d40e00d80003c840070340d081d03800c04020b10723201d85010750b101c840d0507030300c0b00c0d000c007c0c220382a19036070020070170616030420a01860440078100312010b001035000d41100015040c1d01c2d05c120985903a40001c4030740c4030031260741c0c03120300744042112030241c2e05010750301031400c5511400803904100200303001d09481e524150b150781c03107078007c3d42c41d10010740d8101c0400c00690000c1ca04540a2000901c0e6100e5608142e2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 715276663 1250 715275413 715275433
    0x2010f05151f0e0d05060403080c180904060209030d0c020405221b030b0114090108010b150c070905010308070b010902031b030720030705010b0306070c120311040905090609060705030117 82
    0xe003602c00408402c071042c1d80641b04000a1590065035550800d01e18040207140150b0440e5203082c1d45c01c2c80c0141c030300c40c042180200302088110f9040795082da20203000c0d5070000c0b24081001e8500940d101c0241e00603400c0c500000c068101c2c1252024407001c410a00c201046e002d52113120f1700320309401d091005044840f81c0031010a16188005000302105c1400302103540d285400c0c402d01443c181c0c0045582c1c2e042c8107034141c250303652840404080311184403660b2503648140202d031030080a6405003030020b240400203c140540e42c1c0060070b074540070321071000c103130f0741d860008408071f120448203180c0004d080d4848140d0fa6010200543e04105140340140e00c1c0055514880140001801c01c5000d561000650100704502070245a900120441c09460f46d4500380c1805080d80e58030b648018921082c03024421140c500a510034040c400840405c203450f5520756101900503d03042d070f0700e8502e5100e4140001c407407620010b001c900c143c040e0766a040c00c42c0d00c1c04140c0074810042540d414583d01800c0c2e401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 715277913 1250 715276663 715276669
    0x7050715091d0a1802030d1b060614030706050c0a060f0b03060c09010e010215010608220f0b0f2701060b070b07110304080706050d020d0c02010f05151f0e 68
    0x6402d46103100750585205040c10740980b070458103100d0f0004110490300308510090307a0302041e007450700603d60420144080c60241c82c3d07828002101d100401d1946840c0010944040c0800601c84580003681151407860310f4210541c1d240c040c114200d0310542c0b240c84183c000510982203040d5611104602149030309011001a08002c01201c0d1011401808201030146603408200340e41c2402c030a0010703010709041c0c1818881e00410501070307030090143d07a0380841c500c900c0c00b991350014604045030501c3c498208e45409659050012010b9074a203070480085503000b80d40504945c0940380e0b414862a480c080580d44000c0c607801100180c0c41c9540c0c407180002c1c0803000d0001061090701c034841d50f00c00340ca0104005031a5800c0c0703406000030369205000034071501f44000f5418083d500e89040c07560700c0702084011200a4482c0038407000129007402d4103020b40680540201680010040741405650340780041e0803514102c1c10f01442e072120300d18940b0001c1144409644404100070326112102d0300000c808 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 715279163 1250 715277913 715277939
    0x30b030312060406051801090504050c0d0c0302010305071b030c02062104120f0804060e0109080f0319020c0705040f140c130e1303180302090711010605060705071509 73
    0x49184400310000810615283c68414240030307050031201c24079070303218807500140c8808050080070703007941d80c0d04049010b102c41084101e411140007801003142007050310b41500b900d052888224003080c10840820512802007134202443ca8000101804244960b01c04844180031f007841a40c004a00f0032041d460f40210100003030b25680e03030000a1003141001d2410345081c0421240d150201b25640d040c000c61181e1001c0b038103070019041740303010842d0150090700b2801848000c1c4028002c0c0750001c1d0014480d003a001c0a1440703071021440705018920446881c030140c6c825032009a07115000000148114681540315108440c001100010f64403071840e4101c404007016505204c0081d00801c445601c00c0e410f603c2440600410b0041c42240d0a20f280a030a1310140e48a004080c0710f8800c80c60b40e1403000000c4080b00a40d001820500c89090410f00030386031035440c0d192942903500300740740498a418860111249250f02200900406d803070310400d10b6034040790444002c204120002d0010b0080c000601c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 715280413 1250 715279163 715279177
    0x4020a0e061b0d020703031206030f031206210203010b09060f0d1506080102040f0602030406090e04030507051e0f0a170903070f15082508180a0c03050d0206011a0901030b0303 77
    0xf071030000d05608000c2c01c5230307042d280101106401c0140034400a0040a680c161581d41802c01c0d03509082c8104209001c3c0c02c0c80d400191000710410b48418090110804281707105000340d000700030102000d420b001240710201d50050b0048481b0115240b1070030b010402c0c0074a03d002d100b00030707100009020101c050300c40c5c507408110242e40118051240f140302c1000d0f04010005400114600f42c9049406889612144103500d903880045001a040c18013800488440316407002c19034594040300340ba0310521041d4480c004500388101040c0c1128200300250316255a5000130500c80c2c8890209184103241d400540096014040c071440020074040d900020405041c8401c40302040080940005202d001d00030300504c4800e1030f841503102d61a1041203610180019441e160301195141c4501003080c1c5044070225002c0d00c90902c1440c144190f40c50580c0c2a43d101d0015500c036080102000c0741e5510b001c4c000c41c00d040800c442504c1c2009507480041450031410704000c20385c0458140040d00f5500102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 715281663 1250 715280413 715280417
    0x40c0b1b01050421080f0703110913050a06060e180411030a05010c080c0708090d081b011b0302030c03011e0b040305100b100f0e040e120a0e04020a0e061b0d 69
    0x200303102001303c4540d5000c3c401500c94589210f491410910301e0803906c0029024805040d565040814170403c03004c1100c05505014001540c1d10029910284c0205001c5078030841c0e09103404000701740548918600d200c64000103107648001c441c00e403a4041c1c2104054421164030384a0881184607403130500544410f68068000040c006014030400381040301e00500a10351024200070b24000103210500f56411a0802d440e50070004400e403400038214829071448000aa2920381080c174010015003000c00300010380d161a46903181c02c400280d0690006540011060b4004e1005000e026440000388903074079041110200701d59030742e03020901c840d070140e00305032850b41021000d00c03980000c90089210003001614a55100b40c1500d0004200005100c451810003059007020400d694403600210600040710007600c0c0c107011b200d0b20b9044141d010f01e005001185c881c0c1200d02a5142c03030702c26039440d01000e4407412100d010390001c0241c9548103502c40040366241da0041d41e80c500042203c1d0782441015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 715282913 1250 715281663 715281683
    0x2061305031903021b01080a020a030f0e03070510060308040e0403230306120d080c09030304081606180503030d020f0d0e1e160902090310090606030b0f040c0b1b010504 74
    0xb0f050084c00c114043c240d03541c0d4603600c0140c1c0060b603640001d1040e4040c00900300181c68019640c01100a0201c80364200001c90030400201441038002c8000c1800c180f01d1800c0311aa002c010030390400350f0341c0600c0081e100340420710081200607903840607164020f10034606a100e01c2181d400310103012214120341d50450798040104007650800300804240c000b81c40000341404030031803200030a8800002c00c11007143d0404560f0350055101082a80c000d400300c00180e035150600f031001b0192070b40700e500c148070005400e082d80d10742d106c0d14a0304a4080d294080c0107140b034400040e4414001c3c2d0300407880190807010400c18108a81e140d4450882142a0880600004031b4a031741035880e0041c540307014005503080903100c01401016048030404417074000c3d81c050b0f102c80d008800070342003c401c5000c09200b0f07401d0001032400c0081c40da100e5015284501080d80b005e80301c0480700601d02070b04607402000c80d0104502801002032540107407540345098144c803000070381e5143c140c0342518030545c0c0c11030b105045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 715284163 1250 715282913 715282963
    0x9030507171b0f0a020103020d1104090203093304021507050610050f130e0c061305040f020903061b16151b090b09010201060308030115090906050d0206130503 70
    0x559210b00c40c902d032001000f40810040603144540300c5401000003414181d0000e40701641c2d4a064009640807003540c1c05164a8955850f0090b01035402100d00244500505021500c244440d1241d00c503c00c02c0360304045401c91001c00d0343c40d001d12020b0416079000030b20701014030b00d0383e005400030302c2114840c40180c0607604142515031152580360b04401e01c540604000000d0689400c0301480c0650010440410740700600c40101e42048101d8075980e070805c60000d10554120200d0300342c0b80403a03005490401222900c0e0480504031f0007051412989030308002e02042c1a000c0c607244542c5c009064148880ca4607102815103e15000f56038000c48540b13084070a41c1ca4516010b105021650441620780800310808030801050340007140102d041918001c80d030100d00340d10035070110000e1944850324513903a507112600f0a500600c51645000003510b54540442c1c00c401d40c3c003881c401c8801c06002c1c46580c1000d03908102c0c198101d01c5054206540c00c0b20002103c0d40c080040c14444071401c4035003514512 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 715285413 1250 715284163 715284187
    0x714041a0901080106031e0902041b08160e010f08092506093f081602190608060d02010507020301020a0923030601180b0a15030c030e060a0903050717 66
    0x81648445c0900d40b0b0000fa840c150035600e21f40c0760000b00e10000010b140005440060300a080c010248141c0040180404012541146030540a00301900e458000c0088044086a070302d0f0020403024005543d0b891100c02840c00346003403542040c00c0348292200100c0c241420032595941d88032481c580038480f0410404a81c00c4000e480240c8070792000903c03a2101001d9170381c03081c1240c840c41988010180105a09441020a5852220b5000304042e0340c03541c03154402ca50851202c03200340d120b805800300b901f40001a0042e00421903900e611404541d6460004100d00340302d40d0b410903410b100b410041c0704c0040e5400c4c0f00071310005085456402a0324101920100c0000b15103401c3e454040d800c0090076500d0fa400070301213044070b01010404407551020110306000d440d485e252180c1100c2200000704201c0c0b45c0b1001c0c0f1610242d41c2d9010003505a00107401c0701030b210040c1e0003401e02e03001036011400000d01170b000004d03518000d00b0003500e4032810b56101c0140388208101d903c1030718404120302819907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 715286663 1250 715285413 715285427
    0x30a091b06090605030606090919020403060501060306080307020a06110309060318010e031e03040804090e0606030c0a0f15051b0102042309240d11120a08030714041a0901 75
    0x483c3e0310b0320504500d004808101540300740c04404d403007501c0e00310015100251405566410f182a0302c03007551910342c0c0c0d02d080c2e40906030a01032000401d040c01004900c5140001c1914069a0010070305c02c042464150113071040030698a86040f203020401001e9402d42b220300066002d039440203000d800d00b118a0084608403104070701c7c4500590001c20640c151199885002510f4071940344040c0e80da82c58501e00000140304650000c0090b41c20140100c41e48040492600d101d041c00307400340d411682140341001044800f83c0a8100300c516490404e0115400e40000c02c9000d04003400e21074540a2500350001e0001c00800360050280c3d00000c0c2886101c402070454180035203204010481d64900c03e0004401c02030041809040c50789111254500c1c0107222480c421144015090000201250030055540d8400c2c2c030036140039a101d16880244a0070003c3c080b202d0f1074000c0082030658030780007800c6424070b070b0480d200e0946400071300c07000c944030702310b031030403003034030309507039110650b98020600058000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 715287769 1106 715286663 715286669
    0x6042405041d040b011a040b0c0307081204031106010311010315031b0e060f03030405060d0204030611040314060622060e070306081c021002030a091b0609 68
    0x2c900ea86046a02030b034000ca8100c4203680e242c0c1140080d04400142c5401080b800304010440903c2c07003009030091a1500c0141c0b4500b2403140c941d0030381508170000d1030030f0003c1c03030205101c01c1582060404400c06003100107070420b50701d582c8400842c035044010960615807a240249086003050500034040e5600003251032085420707031600c0381c510200b8090069001381c190085981c2c0d242207081080c078807800400451a00307003000144100368100c24105804603400344004030010396103009200b081030780d000d00e464032589142003100491003a2071259020b6000b01040c03040984500340782c0f9403008109648071201e20105a020401041141d10403028908400248640070741c0c990010000c0316026401c549801800c095980004c140c0341c003184e00960300001c0204444803440d000f440d40301c079104c0c9000a40c0c101c01d823074121003002911100040e480d8042d20074042980c00000c03000c05 = true := by decide +kernel

theorem cover : BRFrame.Cov 715107913 715287769 := by
  have h0 := BRFrame.cov_init 715107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 715107913 ≤ n) (h2 : n < 715287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
