-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1307
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:17:19.010931+00:00
-- url     : https://prove2.me/submissions/04bbdde9-3ac2-4515-b03a-3383293fa942

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 234892086 ≤ n < 235071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 234893336 1250 234892086 234892103
    0x2120a1709040f1b02010608190609080c0106170d02070f030b1503060c04060207140109150c060c03141803030a020a02030c0d0918020c0c010e0d02120105150409 71
    0xc030300020104081c00300310200900108a4a00c040030400480702100311003403c420905004015140e02881028050302400c0050034001e644102040060051120002c0c116a6100040070034041000c0a0710404444c9074000e0258070340e035818240c1181c0c0e0050f000e00081c02024100058035000251140440300d10100d90605030349192207a048120b001080c4542e160020320312003070300366000d01c0b000d40702d0142ca424007515642480c0c0021714000315034020805414901494841c0c684e00201c1c800111042d105403103106203e05402152139a034269001020f090809070038100490b0160408007041043c40c85026641d030b81c91081c20400d0030605200b010075081040490422a81c40e0000c000c81e03c000d0040f20f19020b8207021881c43e0100703100e044c01c00201c21620070300041100814159110700b60940a5052144a410840d00d8220100e52541400a20401062151210400f041d18150018400c0303410700c441d0a41e9a010f40021034005140204d94068074959140c203224014409820007201c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 234894586 1250 234893336 234893363
    0x70818060108100c02011b090f060201062117030f0103022b08130e01080a0605010b03010b0a2f07151b0210090b0c010c140a05070b1b0c010902120a 65
    0x10001c1411304003840c11035480d03201180001850124008240101d0303a03441d104645854801100d06040c0d400c10380c1164104031003003000e0030003652140105040c940003150b81c1c000e0b80c50901c102c407040b00036490f00b248000c020400c100031741004e80ca04880c0252140300320802d1071030078002040c02228541c0c3d043c05176070940102007207280c00500001d68044180103040d640355a14080c0c400b100b6072080c45107501c6a4161000c001c080d0180c03500500c1259485401d55042180c9040301d806450b84c650100204d2910440c09800da03406c1d20100c20b900410501401840c45629030340710240e501423208489034038542c80ca0858420021040d00001e2039541c1c4500d407070a5420040c135012440c5101c0c2c1008018500440d001c95114000d0042c0e02880d80000381c0303c400d030600502101d90721240001050020302440944542110864080343e0740400019040d0382d0b000d0ba0070a822071150380004c001a408901045010015844450102e0084030014140c8030116060342e917507418403100a1854400040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 234895836 1250 234894586 234894613
    0x30504081b120f07150c0c0311030d0608240105010c0b060406080f060103110604030b0411010c060e010c120e120a0309020904030804020f12030f0d06030803070818060108 75
    0xd09800c28800002e0340d800c410000802d040540000740340780c058050001c1c14108010902c0d0394420680e08114050101025044014060f60b81d40d100150a10800326000315401d00240211030782c0c2c00c0700d03e104020141c0c8a10314a40e0380c100252111900741c487e8001031412030040c4440c01d0407544160f607200455a05c541c0c03100310143c40a4330b0607070016200c503130208004200740103141d05055100c005265944c50340c00e20300d110860308100380c2e024520401c41400854001c3c0c015641c85a0400780d03003a019010340780100c0f01108201c10191a2034900b03054481c80c11030642241c8a0007800313039200e4022180c0801d624040759420100c0c2c44581c0e000c01e8000010340144009000e0000481c240000c51f4161078003c6244507808032400c03400603071040c08020031803a040c0c00c01e0252850a880e82002d41212032190760b52031241e0391040303000c0400841d02840554040e000790b40950742c080d40064484c10144030107890041c040d6100404e9900f6540c01301e0141000007422812290782c0710080102c64203180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 234897086 1250 234895836 234895867
    0x201060e0703020f210603060c0703120207050a050a03030608010c0206061003052a0d0c05070c170a0203071401262a180f0103141503210306040c03050408 68
    0x204458610248140c42032148503005002818111710030340c810520b4114101410180000c0907401955018445003000c42d50100160555603108140140d8070807003804e0051030807154030380041481c41010010801c0503403580185049a1040c4002d11110009090580c5c076800201c032a941c2081c44144071505051080c0c216035001a22200080445141b400e00701c180400c10940303210350380e540081c000c02c00032a20320605035a00300b1443c1582c100181503840a000c58213601c039521200103007a1001c200e1540511002091b25402812a0052503960704200c25104c80d202419000c5001c003000d0100700d4044d0b46200c0740c00403001d0f00d120450341d203200300706000d80030b101084240c8800140000b40c40d40086402864004071039801e62040402010030000c0401d04074000c41d04141c200301c44440e15208004500340c0003160705080c444032a501d0400705c1d00d06000410700340301c20002c8002c00e00d4561201c2c0c00947c003030b48041d50181324103182c41e1030690540d242610002e04056081110112030103050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 234898336 1250 234897086 234897097
    0x30308060607060612060b0310060e0f0405030408010207150509061b0d110d020315330702040204060c03081b0a0309020d051c03051305030f0304030903050703080a02010c0201060e070302 82
    0x214030000760744d600c07441c8100500021110032114075940701c1d00e01301140340421400d1104160250103000c040e0030582c4500c6811000351195900b100c20f200032808100091003a100944041c60085488807090300309171007608220707180d070b1350000e00c2c0002140380c05201003269440b4460b01c49104525803825072843c9a40e5009074180d45629030f40c2c4c0020954441c520b0020030703074a608030101685a003807980c00c0e01200e401c0c10301054070840001110014807131034540c405e45080c42c1c003041070f0040071492034007480e035100307001e0025400380c80003601140c0c003500103000313a4a142c00b980d22254143d852800e14030b0f1011141c4150100c1d01000d01014090030321940001d03408520142c10203504100640d520761901c0c11440da80980c40440207041c4c003555074580305150b4000072220346910042c0541e2a510340301c2c4203520400e14100800030014091500826508001f164000101c449a9035030b030800701000c0d00b02045404c01035003040607681c542481400b81c0c5c3e043d10151007815071592603800040d8000c1d07112 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 234899586 1250 234898336 234898343
    0x9091507210f0b1e06070203011e061505071a0c120403031d0c06041418040305030a0b0d12050d0f052a071a0a0e030a0215090106030308060607 63
    0x44070a607410a80d48080203100e901012101040ca1409a1401c1003500c44144209000d0344a091031841e0084903103e00c0840b5000c00e4070708a944094a00229015007080c02c07518612020118158140d088036030f02c504101c0b400744400d1021902e080c403003159284a18000904109540304141c40046841c40741e81360003c001e00c442a00c1c000c075041e00b017140c5e00001c54094001c00d54500c5203050b19402c00481031840751001c40502040300f400c0000901500035401000081c0b1101300322445a601c480c1c086645417168244841c000b482e291800521071352080f07440ba0012030600040d101e16050a1107a6150264040c11a4401402d2503000702d501d9000210049001a210517040d10101d90710f2207500c0c06544c0100c400050b00764902203805030030380b0b851078840707407c0410040100441c1c1d20b14125100a440703d0324946007078450030003201c06444020304900d0075010024492420540000e42005200044200c88000342c1e0307a280401c0c01c8170b00b03e12002d0301043d610030000c1d40a240c075400411150380b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 234900836 1250 234899586 234899597
    0xd0b0609090403020703020405010f120b13020a0e04030f050304020906240d06030b0106080c0d0504020301021905070c05090601020a0602090613030308041703070509100e030115030c0509091507 85
    0x10900060301c03a210664055001d80c0107510f0500c15030416000d0345003d410402107001d4602d03e0030089084e01c1803480c00190107802d014001c02c40000600c80328841c034030380007088000140d0b01c1c0c01010380d0740001035400f100481c03503800008025901410940c0d101c2c9400401c00d4205694600502c503200b24200d5000f0820241c401c260031000507020043e040c101d030802c900040c0e1508500d04858021301c1a001141844013540400c441d10f00300c5400c07075007622050b01000c02e1907140c0388042070181c05881c100c0641d500080c200d00030034586c0400500780d080c3c0940780503240c20355184103120000806861701d5005812122803c8003041c0990003c100724200504201d1401401080581c1c0302050b5030030441c0000c09034418401441004094200c224088081c0e4a185041034800900725205400c032003801400c0d071003c20142c40f070152113003d4186070007074000c2c40360144031a1010603102150000312a003081c000ea0105003420f00f11849882100008000c104e1410400c034044180000140200308021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 234902086 1250 234900836 234900847
    0x50a030308100807030f030827030d1a0319080408010603030809010f0e030306060f0f0a020303060108090f0c130905070b0301150e0306070c080d0f2a0c03030e01140c0403050606150d0b06 82
    0x2c00782720300d4200411024025507180d000a070000000d40b0b559034002075034542241c038140910741e0007050705004103085126000340c1c059a0315292034580100d034000301c465441c1442c000103141d00030780014422040c00000300300a210400581c42166000e14450b0b070154400d0000070001e0070042d00030180c00f0b402c13840d42410030902000310381450b03101c3c0e01c030140103130404818480c3c2c0e5600040c00e03036008407400000e060594000d6800c00d60780c003a030140d164420585250294002480c66111514064014054880c6151510003031001c0e58001e2260024801c84582d107030709010712550030550b4103a001000361505880701c0a0460740c000c44150281c694190030881040e031441c851041e0072400c0300188000c914084217000c2900d116404204910400341511003001c0b801b0340c86047c4c0400c07154941800212012500501c600611441d0701080440014400780302c890040d1070083d100301c9100b003040311066a200303002d118000f004041588540203040c0704001566040e5001050700f41d601130714144c1000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 234903336 1250 234902086 234902131
    0xe0106030c12050c0109030503030a05060d1203241d25090501090b04061710120515070306050109030f0f080711040f180201050d06050a030308100807030f0308 70
    0xd5810398803460000c1c60341880b18040040900003422410004d09100540e45e2450700ca90362240310042c441401c00e940d840006a41d66036102c0840042504009040d1881c140d04c2c0010300184034192101c003403800b01c0150070501034924a040c005a0f800e6601c8104100240c45078400340c14400b9004842c8000c444024940c009035a803c43d11a1440e10380d44c140515213003200140047c40241c024018001c0100020300002c5d400400d042202301e444840d000a80d0b030b400003520001001c1e90001c01059040502c0803007800000509507030b0300d4005444125054859107020360071a0041d10034503004c501d4104041003c1000d400c0400c1140d0f01a086003029841035544010440e484030500f183c407100040b105e081c49060901ca0031800fa43e081204010f40d103800a00020590041b0100070b0402a0002c0c560312072140c10707000080100000382180c00d507541c50385401380ca0064111202c07a00700fa0780c0c0350b0004121a0004814007200d40100746040d4001031a10300703c4a4640081511200030318107240c10001c0e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 234904586 1250 234903336 234903353
    0x8090f0316081e04090501090207080301030213090b16020f0c100f09180c030e0c01050913060909080304260a05030411030a06022101050a0e06030a080703080402090603030a080a0e010603 82
    0xc204080c1040742d13495003032120b002c0c1100c00c180c111140c400d1041c008240010311200840c0c0c1504d80403910010800f101034441c60280c02e034150b004021407038040034803544e0540180e0001030307210b444d001e80b10a86042c4143c9503813043d900300d050345c0c401d03000c00303074481258019400d1072444481c0c0d00d440340b400c603101c0d00c1c043c178145c0403032030044020f941d03035540c00b45860350500c45d2040c0028100301a00c1124280c000003030241c0501d4000c2d078450300105003446c0c80380c0034a50000c002080c0c03003042800010054100422142c0044030151100c50922040500c0d030002046044d60311144d005401d82000b1303080008035402e070801001183c994058420040c0c1654040121600c0c40e88200230243e82e82d011254092078060321106501c2c02c3c0d81c0d01d0307030062010390340700f51440040d5900c40c234041205540d035070f0009142c00e014001c00303054204001400b80074143d014041611442c000c3d184c0b6549602c849007130540e40e1040100100000e01d101001c01d800440d16001070301100d10120012900685a482d940c69 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 234905836 1250 234904586 234904627
    0x80309070e06100507140706080601170f06190503010501031505100602100c2a120215010515120106170106080103030e040506040b0a0b030f090609070306230a0c08090f031608 77
    0x100d9141d004024196078000b44480d64204a20880d41003420101c0f4480b14520000e0800c0d44900b0fc440030007032030044070020b001c00803d001002440309503944d06101c8015410700d40d051441604040003e0402e400109040301111034039030003040707103000e0b03403081900400c9046030400420000305130f1800c1c4a2140700c008440c0c02c09025905c3c9140307200d8a40181780007805101c5106540144610b0400c2c03102c591981c0c0e0440d001501d00106464409080c41050f10541c003150032842259400821220341c010510034810b0b5401801141c5039803548015280ca030001d200060004001071071041c51403c0603000580c0240c806403000c205d8032296000200c0403030050300812040e10001c0208240f00000203052a00090a00e018000a0070484100c585412031800050106a10740b403000000300162005034640084800503003405007030402c003034809080c82c9115a00051008000300300364401c0400c200702c0c1000580c2c0114900705615011044110107494244c038841c0d4148046d01140000d0340040b003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 234907086 1250 234905836 234905849
    0xf0302030a030b0405070f0c0f1e060b090f010501030b030f060c09030606090403050301032a0b0c010e01060e060f060d0c0c05061b25020d080309070e061005071407 72
    0x1511003035501c1005040302d000008a520aa042a0030f120b40c40c0d401c0101c0c4031540300c0c18544180000c43e54140051048080840100015405511071071b14a5060b051070034540d11034201803000308841d42c100326809100b650784d429200d061900401c050342c0a40e000d180004006400e41e0070100031490b03c03a09219040b55074902d00c00002880c810baa150074020365030310140071614526a03050585004006010500004111030203189810418030390008800c1c161210007924548590345443e400e02280d0080514041c00d5820b0400050045c0410701892082c1d642d0010030003c10b40d514020010b44200c64010160040c03401c11103140000d50500898800120303d86441540000b24a0880c1c03501c10001c14080d411100090004201c02d8014119201c04551688001846030101c641e00f000310b01a480081d80502d03583e0748202004034000c0558030940140342a03139400b03030303541c80c62413000c09085038415400100d402000340135038015005025601e0003480c1c812001c01c17000c030300f01e45004850341105 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 234908336 1250 234907086 234907093
    0xc1421090601090e0304030b010522051609140f13112106030303070c030e01031d100f1e05072f060606070515180a0819090815130f0302 60
    0x180b01c0d0549a01850007a41504c000031071419240d900c2d0f040c2c1c690018000c1600ca030681170240b06100b99a204400d420107009101040b05042802c7d001080c4040041c51001050503074400084040449040d13a00c4843c01a280440180c059010041909502d0100214440da103608d110320704a0314002070f00c44c801286c2c0d920002009843c103290110740000300345a202c2d40c02041000f0300c035644084503805655150820421100035000141c016180054204910010141441050310340005940d084840f51000401142d41e601d01480c080e5404800400001c801c600c00e6038268250395404942d014440749041c8480308a00007035011400c0a60528044044e10228030340d02490342441000c0c2c0081c821160700b481d100399641d4858841d140346140e0020514202c002841d29012482c21002d96035907502074400c50141c0f490800e500740c016210240011052503003443c0310724090217014040c4c81c88000101840d401c445640d80035881d000303052810585174a20b0440c00200c003506140f85491007500036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 234909586 1250 234908336 234908339
    0xf111908040b0a03290604090b0a030209090618070b0406110c0919051f1e08010e1e0705090c031f03030c030e010e0f010e011103070b06130c1421090601 67
    0x41c0c117150382d02840c01c80403000c0200002606559441c003141d0484280352401314042240100046128001e5800a5044800b0104101800202083c800c0c230660040e602c0400d52260310034029030328440c0f8042d4502e210810002480380a0040b500c1401006282d4110303508110040c010521001d41581c00f00101400b015854079000081d0094591050802503000001d66910010b4600b01550744203801c4502c0028001c800100240100b01c005031243d58024403d0750440f903406a42c8800f100a000c4002090307541140e10310201098580450758028401001e036124560781400c1c9a1019100a1401003084010440e507130385900008011030082c0c0380c401903003056040245c820649142080d04201111310180c807155a402e40c42030b03c01c00d00b0303e810241c06012030f00585031610600300111079848082007000800034071404c140c1c841c4000f5280b4883c010b0300e84548005950f01011a14041801c1e0642c064080504801070b20680700d0b00219091203070034a120b04107586106540c0e610761604007100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 234910836 1250 234909586 234909611
    0x40506250c230a21050106030803150402090904060b010c1406011401081915030f200117040b0c0702060a030506090c040509040204110c0d020106060f111908040b0a03 73
    0x8a107120301c100821030981582142c8000345111070240160440001100000450448060004008642e100d0003c10005031281484038543d00229038881e800303480c40302c09102034107050081e03807006040603015101c141c1b12070740c4003000340543c0d40d801c83c10407420481510104e00880a440b0815100304003404c56035044c08400012140a40c40b81070600402d94180000c0014504140d025141c03444000074000c1051b03290700c0100700c059400904000034a4404800303100d403d10001e02c16045000c520b010707801c8803c0042d5032100451900642080c01c0c6800940800d520143c000c0d070220041400c20f00c1c0221550003d040c6030800d0b503840c40000c0c2c1e602c04101a50601100c400c0e005101c420005042c07034036000004400b100010720080c0555103501d0a801202c50050607208030005d4202a03a014070202840240284800c0c41000002403040f0080302905018944e80d40e00042d008000e00fa42052520321007504040004046841000400c000500042044041d000049281d503021610b244d0044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 234912086 1250 234910836 234910859
    0x60d21030c080f13030e060d020d06060c1e060b0d0303051605130308160204020a02100506040204150507050c360f1602071d010302190605040506250c 66
    0x241c001080c080c2035003c0c0040454040055940490100001a4180c12516048a034814401059034000801054400811034541c01900100c89001030030040256503140850300c01440302005400e41031001c3d081d200b450040c80005101c45c0c0a030001051441d10440410320b0078115403000d40000b640c8606100c808005000c0c5001607401a14000341400860803901685804c50703c8000d019000005150902504190164a2640c1c00070411902d4912140c0045c0d00c5802c4040b407030904619220024440d8a424030964040d42c038095946c0b101c004030001d040d10140c0c001581034615100741e50601149036142c880c40c2c10004030b11107030320101c4481c030010011001603c91410b08201e14010030032200080c040000d0760302c900c00c21810b440113105044140c1c18071840f90425140c603982003012b600c80015403040c0a0480c4e00c00c0e204a40d0a0304440140442d21407540076400009504100c2000300c1e02d800d0001d03000529000c0e0340c03002e83c0018040d0442c01000715032802c45150421042c01c001c50403161 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 234913336 1250 234912086 234912101
    0x30103060e0d11100e0f070801021c0207081c1805070f09110306011803050105091614180a020f0c0606040c05071e142b020a02090a05060d2103 63
    0x1030500440040f40f89101c140c59a14041c8a040920b51340c0540540c0d00702d0400c080000d001200c41aa0707003041e00c92030014080c1d40503d0580e82403501c0d00424412200084c800c0f40ca10640160013070f0708100501170b1701480c880302e0150b500c101c0c680340c4000514501c6502015034200c0c1c4250005d0200e6482c008110080034585d81c065101c5034600f00724408285260801ca950003402480d00701e100c0c680d062018030714001c8a03000608158a004104144030b03200107201d40c0469100d01041041c56500c0155441c6801e2030700c001500201980030795284200d0007412660046007000e00076081c4010005c100c0c0c90f5400c01d42e10060603620000a000c0c041c00d203403141081b00d039580c0c0f8016140a00d43e0f200c00386040042102e480c0200c214129a49c240a84d15241100341102101640c001e1120605401031340d0300c052180059070844618040c881c0303400010500b00890b4094a00945590782c82800c0c402070500411064105900300c0320725002a18212209054891410b0b00c1420041c0e0f940d0000d040320080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 234914586 1250 234913336 234913363
    0x7020703080f07061e050f161d040b060a120f060f0e040203032107090e1b070203100501030c06080c03040c0e040f0b010f0302040f02040b042603030103060e 69
    0x11580a202140c031420480b0700d45400da006656441030289054001401805440c540310b44022221681d0015150459400386240090400580d210071880700c0b100b001014842010034400c81c031460300c116020ba18072164050091000070303c8500c0d28080ba003243d01001c004400146000061407840c189440707250f50001410404000c500c0c1815000d01c860740403402a01c8100c001d1400040c21590b00b001100d000654a0a082e1094181d0019804880c0400d444900c082203000f10085441402c124000d4403a0034414280c02c203400d04a222034000b0780c01588240d805000300070310054504820f01909000b10b01c10071118124a107040002003100314042c01030f10380d5004c02c0041c04089401c2d10300c0401500d25100a104541e203c030310704201080d402000080c0420414800000c1c90740c0800035400840340280c03014040d514411402401301d111301c3c09040000c10b4144420b1004452390b107403030050bd42c02911100400c0030558101407940e0426402210a031380c842d040d0840740c4c10b040c030409010180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 234915836 1250 234914586 234914593
    0xe0f1e0907030b100312050d2d0b22150b040620070302090106030b0d021503160203070b040b070512010b1c020909070813021f27030209071710050102060702 69
    0x2903940320b906d0264a00102d008000c4086501c6000035610b500c25038421840b1481450681d034402c40034441d4044200c4100c1003649840b901d05640e0a01490301e100f04603008161100c074100900250008001010048110034900000882c5d0b120600004101506040c0c40b119150b4600f40c85e041c1600c0b015540038440d5800c180030400043e01c075242c095054803400d09020940c202c8a03c0482d00d0349540846c0030b07610500a150300001100701c10004c602400c203070364410b920b8411441d07059a4030701c40c00d58000c05001c0c582c070000e80800c0305882c00d25084912480c00501c0c12208102e84004040281c020240c0040e00042d400c0004041c1c0081c4a1010799681080d41840314080001c2c03100e80c001041141402986400111791002c034050440d0003a500804d200000142946209107550031104108041500d80e00c01480003c000b250f00588503074040d10715031109046900f030005180d030241491080c0300100000c10bc48090901c030711480b40b41064900c01d8010b1400c00024508040503007040250340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 234917086 1250 234915836 234915839
    0x902030706020a030f0e011202070303060513060f3501060f0f0e0a09060e250e0108030f070606031a0f01061b17040302040203012309010e0f1e0907030b10 68
    0x70b400c8007000900400c40e0600c06d611100c02c000584130948a000d00c004410700c0042d8010806030140c5c842001e540c0d0585101120441100c29141100c2e420b00032030100d034002890811000041420314510f10764500366802080c1e00b404808072040c0c928000a9540c0e07510703084240003400805440000420020103119482481c00900c00310340c2801030321480000e91206c1500301442925002000c1c640341d105c081341c502880b00032490036144107000190a4002180e032001400c0881e24010906032200031000d9032518451a68603009607210a404841c01b0341c07143c40010205850903450450220f03a61007110107840c044d401c251014038140c00c490b040c001200c1c0d86070006015511100c080035402012803444250710301d0000b070503000b203500c020351081c000000070628800e21002207182c481c030030b03001700d0f034008400f001c1040c04c03a000d009081130360301100005103503210340402294208503500000c8000785e42000040c90402e07000c644010361584440d000b00200941c0c4c451300b55002d92043c13104510603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 234918336 1250 234917086 234917093
    0x61605211c050403020a120e03010b060408250b070f1407060e01051c05070e120316061814010b0a0905040503030f0903130801090b0c070b06090a020d09060902030706020a 75
    0x209408001007a03003640d20000941098020007040080d02e821200b20180a22180001050688250020390081d401c051070300089051003c10313101901d00c010b010707110070203e80014140240d043c030501c4000d20b500c40800103d99603508002c1460754010504402d410341c680c1000780740070034090074848181d8000d80741000b002e54002d040f40f6580c0000d00e0003a5661085400c00e04803a9003000c2e03054102803030300052040b0035401c081105020343e030640e00c84a40b6588000d0450300c3c0e00500c86000c0d007036400200b146000030155484890000700d403915000400ca660380b0360604d02031580e03040003002d0f03664202e0134400380361a200c01e4005007400c02041c8060310301691019200e000240020307409042c00d0001c03403d540d00900036104100c4920f003542c0801e66032104900d0182c600c0714000e0b40c0110f000e07400700b070404014800702c0314443d400c01e00440091300c59070280428103100500e5200044c0d4280714100b07141d07445003d40c1100b41d008101c08646040e13140101405c092065200c1c10545d4010400c08001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 234919586 1250 234918336 234918367
    0x120103020f120c01140c0f0609120301140f0111060405151006051803010204030203060f04121b030c02011407030305040506070306030f1b0b0f0a0201050a05100e0606160521 76
    0xb0002e082c070b417480503588407000350307211406401c08081c800e0046000f403060202c000a0710754403a01ca40340803103080d10f00340481d080303042c4020700542c0340c03408861500502c0e509100310780d0f6041e44010700d07158080703924900c04281490000e907000c035540c0d0040c11182140200811045070001c2c949899840c50b00d246c41006461440f03041d8901c1007858809101784925917081d03050390300840d00581561898a440c5400c006a00c0003110202c031000072000d4003203100d900c0b45a000316815500d43d05121400042d880a85090241807000c0741045070082a90360303910607250240001030700c00d4601090300d040901d8810705105009000004042c5004020404204040b115822080d0072a41d0011104018800518404566000a41e400324002864000e01e006e40004204402540d40208010345801c41040142c680c1524042d071241c803c0c400c10711644074101209500620001c007498680210603010f80502002201c0a84540c0c1120400c0c000c0c041c0c211020340031404400404d0762520031003a200c2000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 234920836 1250 234919586 234919603
    0x30606020a110d060203090703150c0c021201110f13050414060105030c37031104051002070e090d08070c020105031315110d060503030309061605070602120103020f12 73
    0x200b289501440921519501400310b41c441e0001010340d6203160513218a99643d045100440d20705a801c40d180c00c0408241c8521100402d140c4e42c0c1c035501880540811003140c0070307d0700c01c6060307560b2481700385504140580100384030182406466102c00c0c9502e080c50000140351301c003902847c20000d4030b503107440c49000c82940c4a2003d087ca65200c3e240c0440152050290b404a1042201c144180c529203400c40300061586103100000e2005400b20740400701e040d5515145000156401404240518540521081e4205034640b040760140c6942d01d41d000c020b00b5007541c410380b00da048070072600c03c21680300084a50100b080d08104035490010f0740000c010f0300c002004241f01141d4808141c0070008105100c2199a090480c184151802500e0780c0304181e1111480071442464903000003418203010080c2c03441003034098041c20b510760710007842203e00c40000ca000000c0100400054000805a20140500d141c03180c40c02c40030341d8110b1052210411312256854030440c940c5004980748070b000580d141c0f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 234922086 1250 234920836 234920843
    0x503120f0307180f08070e01091b050d0e0106170f031c0209060408010203040320151303020f120301060e0a29041d04051203100303110c1206090d030606020a 69
    0xa021001c0041d5141003c0e503000710f1103441d40c0b81000103074a840051144299505854030b50b8071640d03940d20507412918032200061000c0d02204800750b0700f50040c4050302034440044030106030541c0d1844030380c0c210b8075143c214801d030908205035811030341c404001c00345e2803180c2a0b00940c0340c07d040e940300045404030040c07000102500003a040100c0e468030300988000f000b01400942d160708203403401038000164082580c0f001c1c13400000e506d40c40200041c030075026059000400c4059103820081c1d08460724101000d07030030761051002c0450602400c01070040d4400c410940c141d22541040c600034901346601d41c1482c032030014400309100600007160000020614544840c55a0300200c028040d90b02403a8401710003072a00d0011040317241c91020300c2c2031049220340e083d690040400b0043c44254002a00c20100c00040014107000080c0640312406038041c81e0700c21907152131004000510800c42004201b0b025410500c01d10001880030040d00d00c400c1c00909050041714180708000755500d04442026 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 234923336 1250 234922086 234922097
    0x30702090c030a090c0b031506090a0e0408070c0303050309010e120a0809011d01060f050607030918060819050f0606031f020d0c0206060312030103020904030f0314010306060503120f0307 82
    0x4600450f15842645072070f0307002c40c0c400c00c0d20780e81c0c2c0c29000d01c5410882d6910851000e4000500b59498181c0448034954002840c3c82c40399401d2200178820034000400c204c0b0004030801c1800040340f0f9942506d401544203a0700d055891502d00241429107403502c18501c1300c0c1d031190941040700c110910580d0078442007403401e18025500d100131680500a1400202e43d0310205090804035000113400050944e6202ca80c80114a0350700c04c244490f0b80f09081c0c016002464081040c0042481c1c201c13070305a0800c40c40b0b4081801034440d140d036401c05881760a5184580c02c000a078904008090000c484407140c1364006d0140e0303181c0080440e841d41c1111010207540c004522030340d0f0200f44158180c03400c03110750071000c110034603062001a6498070241c1c1c440388288036000300300c2c0d844002c0d80e046034141c03a4080c0c0301d2a03071038480350f070280d90200725418a4801c0c1500c900140e1000899401c00600031030054502050980c50402490306000501e415408250b00420203041d03440c22580440e274100ca0b20b0320b000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 234924586 1250 234923336 234923341
    0x180e0307031d0d0b0601110303151212040b040f090e0d0305070212040b0309070e04120c060b060313060605040c0801030f0c0f08060109060b07031706010e0a060c06050603030702090c03 81
    0x100c00001005042c0240d2141002408209000c0b600c0c28941c440c0c9000c3e203a51044040c0ca000f02c543e0307130008803401c59030415070105103141c506090780700a024502040441c1e00f001c060351107003c259002a0015100c4240209081061030f40d0b044c40c4000900034034004000850000100903241c5080f080c946041c1500c40b808103040520030860034003080101140103490701d84880b5407092a52082e030307005602d44641040400c80c51104805070740110b40c4484400066190001d041e66040010b0000f968141c0e522000344015031500c20046208050f4100c901000100500e8100121a55500901e0203030303140c0b503030354404e40d5004951a8103503900130002d20605405403510b510404616006441800c0c14044002508900041d00a060304c55180c000d11400e40c45000114072030042e054003400090105001c42d0102543c1c00c41c0070740241d4189810052581031401240700c441d413075031020000607503031442c98091011074455035800c10401c03400341d860060242c000940e400806044000720020001c00f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 234925836 1250 234924586 234924617
    0x9100b0306060d0c0b210a0506060301060f030b060301080109030306080d0509040e0a051504030f0f17060f030f0a051203041a0901150608010509100303080106031e0e07180e030703 79
    0x86400080c18070100544c0d0300d80601074000100304801900f0000c0d03038906800728004202e035004449c400c120160409086a180200071900c2c0c540c404104001d040d034800164282d81c49100046010746003400012800000d01e01d4010304139a10f0354042070702030304000100c5018036408421036034121002c07140842c01d07440744038580f4100101600024101d20400c0b46042440c1600c4500c1e910550207500c3d407a83c0032011b20703025580c0c041444071143c009a80c114040c11400b0407070311103a402101c0946656400b11815002ca0710307041501c2d61001050340001c4c0224108881007100c0800c6270281e22265040d41050754480145941c0b01300c204000a0801000441490003544400b0350740d100c4140005810743d1b0703140003038a480028001e05000d03001c86400075210a6103002e04800301c9916036070b11f0080c1d030b18014044008000c2980010b002c16030071400000040703074a0040058860b00200906015403a04802030a40010b03800120202d604040c1d24040705040407082c0c6000d107401d81484010300c480c050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 234927086 1250 234925836 234925853
    0x81e0105011d0406290307050702060304061b05192609160b090f0603090a02120304080a05010c110a0309120606050301050a091205071e020d080309010509100b0306060d 74
    0x1100315030010f281c04800100341c9119841c03c2c5c0c3e200521031107140301e0010040c400407030f880708841160210b80108409401800d000e001558468040c1100041c0b50b00054034420810703816124000c001400464401038081820132082d4220b54607003461038048424503a8100e051100d401c401d155a04044002098a501400304401c8010030403100108180c6070f0400e00150b412501c2a540507003801e0b039040d4000d0402c207045a000354080e800030944441180e08001d0410110310304801c1500050200144014040013896000d40c03203000081100341000600800c16400c0c010341100a5002d5010040402d801001690550780310040110b55406e450a2510140140c1e5100070781541c80e10040200814040d030010342c8041c41a03043c850b03003100c0c00c101143c1501030704002030300c0300a5031011040b1000c07182580800d2a07101a1602e040b8001c252600407182d0002c584038a1242d444504102d0074500500c4411400c5138a5a01000080e001c000401c1e0b603141c0c000d00850240844841c120107009038030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 234928336 1250 234927086 234927137
    0xb0c130513021305010c0b040204151802030a0506010e010c0303020d11070303091104110414150309150702120906130801021303060f0603081c061e06081e010501 71
    0x9040380d210100e0310710000000794014441034881006002002c240740d0f2261000a00150700f140407840b26403200d0b0200030007002001103e1140d10300d14640043c0c00c0806062804051124410043e12498103040720340640780d00600b07007410440e0400154642da80c01102c0260700c25014940141c0f103550280f02c050040c901c54400c01102540424180c5c209a4560043c0701183d00c18010381c1b84040b0f48105200c145d07912071440140e01c48041c070090180d0364007441c0424490400410b407000d03944c5006070070200b40c1e02c2a69085242d4008000012510384401980c0750030030100d1000b8140c44559616400d40740c05042c500e54410b82c00044e00180c800404031800e40901000f600840d40d44009101c1103c41e41420301c0100e840c0c500b00b035155841040306102e0a01240d42141441385848414140e5000c0040500e000c00c61240d594403010654003d60740c7d2983d5450000c140c01107049080c413801520b400801003000508172030406210712401c03013003040eaa0444d50282401c2080c038803c6522900c014a10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 234929586 1250 234928336 234928339
    0x51507030c030311070609200f010c020102010204030b01080312010602161208120a1508120304030804150501090c080a0b0a140301140c0a0906090e04020906060903060a1d07030b0c1305 81
    0x101d200303028080c00794440c07c02c6c02d00c1201000500b4000b2044c0703e0480c0b100c0304030329074000c0050f145202c0d43d50081490300301c001e00c140300040c0b80985a0340c4450940a0a0708010300c40d40c404588a08405040c69005016200da0300041c640e000b02e286001032510310718000da0f140380c1001c008060400031790b0002c0d203881080c06411104070b8a4030041c0c0c28020003a695040d102e0b40f880350780009401601240c00c8810b92040309000c4e1660741c0c0c1d41c9041c0e50020000d0403c858804407424080c800e42e0300d43c1b2030f10340607103000007000c6503c05180900420542d0080e02d10750303086103802c404030303010340c1c5810108088407081021602010001d1000030b004000e03203041e5032003c90040080020442d0004000c209024a544071442600c0d19040100d0f400a09405007441014010300403c01610b485101d217940000002c0541c0e1911180c0800b207410724000340d03910b4000035200c07080c5040030421810103240f00940e810080442518581301c02000f0f00000d0300c0701c00504000120f10440c0c1003078001580c080c110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 234930836 1250 234929586 234929621
    0x1f080102030f1f05090f091e0327030309040c0e10080603190506130507091103040b01051c080c0c04050103081c0c050f0a091e03050106051507030c0303 67
    0x412205003040004112094100c500358400036003040c6045400075030039984041e0903e40a42e4421b104142c0c084c6018200c40400e00ca0300311a10b500c40074a811a19550000001950302c40c1c0355500d0200e020744283e0f002c03450740f402500d083c040e51386002041e5521004111804140040c506000755000c910b90118141c010b640700d151504ca013900540202c2c040c20040d012a5030410907817a5807024201d010000501c503070810008901d104801c50342849506004600350380038669035800788800c6030782000c0900a10704000c003c1000780001c0701011070040805407001e0321801010040c02e0308000c50800d005180324800b14001c00152404c021302c54201002810410095031a4100705045400c404041250303241400e400e00e040e401d0070300851034074051a403105d0b414003442d0014800d280c2c21260300c134410000c07000d500242c800c040c45581400da50f070745200000018210304005094070390507003040d4020218078048900003042c0300100c0e62003541611f01001e07a01c0c01480c08401901149410307050b03484 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 234932086 1250 234930836 234930841
    0x1022a01121104050a05040504020d030f020c0a03030e03010f0e061b07060e0601030b0c040f0e06060d140a0c030b03030711120706020d08090604020906041e0603080c15010b031f08010203 82
    0x500b0060050390301c100c0d0110b031043c0c0d0310030400c410741e84102d90081d00011194032810011b40615400c4000c2c20081c0141c80e100c8908001041e410001a4001e400040d04038040d20002d050a00c6074450100301c40301d0912000744240262642c40304090105603000d0501d14400c5800300521040c2c8500503032050080c07102c482400050f80e41c1b81000e000544000910300041120031150a0444040381d03412012501014030f4000c1956803490000d00c6c0941040341000191040c0406106644840b640040300321890f081c003110340b00c111000142c107401450b14202102c54103503000429500b00b01da1181105894121141c04648034420081015842c0c0c070511784003048142d00071543c3c8016400c0d0b81d44807079066076402949a82d4903010388001c0e402c0810940491180e0a042c0c110b20160018102070300151403007520700303c04461546c1c0c4251141040071a400e03040c40303420300202c5602649514030f03042c9541014840b010303500c806400f0b80103044e0390405074591224030300040d40041030f43e00021916071 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 234933336 1250 234932086 234932111
    0x30c0601350304030303110c0c0d03110d023405090901020f0c071d0606070609061b021e010b09150301092f010807171506130905010501022a0112 64
    0xb40c0150004401181c101f0441664000c40030064503540158800205140c65000c0180070f030001c560312065007008146005040030071002c025180351904554002c0c107104151018813002030242245170243e03e02c426500b0480034041c5c41c110401c1d43e0044440b1801c584865141c0e038028407a058441d041d00f8408602e00c604442d021411004982c51020f4920301060701d491b012044a1044442a40c40341c810b00c86c0c0d60201d502a1701c084819881f0342c4000404d0f20110684240c0484a8619240140d00580e054142c40da2a0140036108610301d8009000b108119400650241c40c0208915400c034216040740d28282d4094202c0034185400c0000c4000080760f02e18811f0407910816046481c1068a83c2c12150b254130950f8190f104e1145551540500d0003040d031440c50310000907040018000d00c089203400c682d40c0c0c3c47c0003400b1200340212195500d9280c10618400e40310168412030564101c2d00101006c07180e02038030316070b142c2c1460052100450312400140c42d60084403a00800301841d000405230325 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 234934586 1250 234933336 234933343
    0x1611150f010f060302160b040c03150b120c0307060804150c050711150d0216050601092903070b1b010c0e031b0d061104080109080306010809030c060135 67
    0x582c1c400c214401c00c41503c0b01c2d810b43c02e0b4031a03410407400000341c035404003004c984441100d54100344280740002d604c0e6540e8031090804078051403104600d540c0c0b084510442d01d80219080500d02c910400f40500c01507520000f6143c01d014854102071020301d1000074104400040040019040e000c0d080181003000040100f5a80111104890088040301000000d152051f480b0303031203440c1c00c02041d10b40044c8942910194111506544040b5002410746001500c140041800ba014912000522041c00800602d030244140c050040c800700200019819403000f20f502c4081d202644125603407401040350b45a400032404060b0320303255103080310000e2902e40c03000e5032040784038003101280c82c00300c029405420000c460890343c030f03442030b01d40c1d0401000506075080149000032030008203080036a0703154003d003075481c201c40031110300d1000010020a5a04500c02c1600448584000c600f04952049003a6888806000703001a0380900030b44240061500b0303115201c44d121084101000111803801c0c590f6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 234935836 1250 234934586 234934589
    0xc0114092e0f0501050907080405060114030c090112060b0a031205090105040312020c03010c171605041806031a07050703031a0d0309170c0102030421060218030c091611150f01 77
    0x6c00c0c56404082540350303128a540703038003d07600140a040f0300e134a071a4040310000d40d000c103440d0b01405580301d201499500d0043c007500810f010105401550898900003003150a1007804500c1000500300c18404285002c9d0040c007401203a080441d907604507040140d5460080e0ba000421130794814080360143c0b81d01141820321001305800034040010702150580306203c80008159110080e000080c806491001c0c0070000130400c1c0c204585015140e201059100018550080c181d50721000d080007002034500c0c01c0302d11045c0b1124440b24505203500000c0462145400141c10903440c3c1440e04c0d200d203642061f0800c0004002d00d07500001d1081e207070141c02c4120500c6000234401c1c0009a4060545020a0030306584205a010b1447c09050010340e4202c90310070198001c0c44500c2821074800178080d4402000c55001004c1da50b40540d804204040c03400020340512030107800140300740443c8840c1c048800c11b20f00402d00701719002840b00200301d031400c0d6441c000070344044c403000c05200d41d1003207a0400c2030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 234937086 1250 234935836 234935839
    0x7052109130b010815011b02040e060906090d020106050a0e090705061b01060f080c130e070609090f2705010b031006060206010b030f04030e01031b050c0114092e0f050105 75
    0x2c4c240da50714244555140350041669020a46400112510105a40300043c2d40e620090000a40c0030604001500c1d0080850321000e081e480241032042d100c90802400600c4000c0d44001d004042c10b00000c00c00000d168424610340d0a00103020442510003031190308041c08028206070344480106503480110a28072042261350751070328070045503907454100b2800540700c0400052141640b650180506c10499050180c005a0b80d0152150f09d07203010b200d020002c051559400b2031440c01c1c204c034101118200c1000340c801c140b410030300f00741d0703080311003040500c0c5244026841c0c5186023504140e800342000c4c05400b9407500445508003001c2101d64481e8058401950803685c190f038881c400c03001684000c0d55540d0725400d1080000780003034800d10200303414107018540819400202ca041c00c403113011900004011031030100f80101c4030300e02440780d604504283e1420500300e08094035090307140e08040c009405100110f01e429821050038100c8007283d245055800c01102d00c107059804000c5c0401c0c000c03503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 234938336 1250 234937086 234937097
    0x402030627070912051b0102031204081314031c120203040b010e130321060506070f05010b031603020907200a1e020303090d11030f070807060507052109130b01 70
    0x420a15602004605481d9100c0010603c2e40c0040301440e1b840e4030b0031411541144420044503131240d082c1071040b4021841031042c191203006000c40c0003ca44041c1c0c2041400d840b2000003c450b0b568001040c26400d001c20520090007401c08008456078210498410403460000050104100401082d141210b00604141010341c443e000400b0607464902000b07000910302d080e900d940f01c0d0101c00e41d012145148100043d8682e66800441d5268100e448140c881c0c0d2848240d040c00e0000038024058040c50032000b9084036400760300700220400507400064016a03007100002c031018001d4016081c981c0b000442d0074100d40a08508039601c4042010468920000501905505075141e191030740460b03009000e9030406c2801414000145031070617056820084203071b4032125684081c0718007060800d540c2d000d000380c2824480203500d0900c140d0320403410000c0411080011403004224542c0d019040702e40d564968811003003011840c015188800c1d03110600201d8800e19100d0345d400b40e00007a03401e80b210b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 234939586 1250 234938336 234938339
    0xd050c010e030304020607060b0301140717060907120f020c0105090714060405010c02040b0307170c040e060108060f070905030d08150910060e150304050a050f0706050904020306270709 81
    0x1550302da001c1642d00030f41009003402080b00040040c1c0201001c0b040203070000a04200a444501c031003401a601b40c0c0100303282d25000750340540107001580d40808251500b100501b0070540040500c01a1030b40f10004550318a5a20003507032294049450000300f01c0020300071420540c4c0c42c0d5844000c5841108041c0c16071000351a00f0703050520948007181c205031140f402441c020380a22014140381290b05525014003030021961403011012000c200d00e0340c0c4024800d00b000542030008407004015000030548c42200108081e100010301564071040304408100781d0f80701c282c0180c94088071508080c0d4940071303851400c0c01855001050302d1180b40c801e440d41c0d02c03108070710003400216607060302c1081540b0b110010900400740103080c2c240c030040025000c22030643c0034000901c01038006035001c5440780c0050403a03006004041100d80c1038500243e000e004000c0c50203034068003610400784168012030300400001c02a50743c0d000c40c1008550034140ea0428164003541424103588215042008202886070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 234940836 1250 234939586 234939611
    0xa020708010c051803011529070b0402240a021f09051c0203040b0c07030c060816030b060c030316300506060702190315020c0a120207080d050c01 64
    0x2d410710a02480c2c481070301c0d001480380340c02582e03400814141d415648415a8081d02081071001c2401080c2c014010300c0801700b80400307103045844610070143e01c01004d1140f0f90200e00d00707603001c030f40080c0d04640841c101c24810342c6400190482c042c030682024404244565820380100b02807005120607d00082e0303001c2e4017100b100458058031b00141255006004408900c1081440d006007416980101e0b81000e5a8545070319150780902041229904080c0c002c00c2007100740b04004004c3c00090410803918685108031000174100c00409008244d25918041541c0c1c0300c0d801107601e11801034058036940c1c80e00305103440c00000d41c803061038000b80c040200d1410303c915101c80460740b0340101c58000d01072001e440411014201c0604156888401044080011f0740d40380c234402451084071801780103483c6141048083c002e64a000108210300400410001d0301000c0f808240e07499008a10700b50f20000f219080745041c034180c0000c03901d03200d03102000080b507800401500113a05c80384020702800c500300c0c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 234942086 1250 234940836 234940841
    0x100309030807080c0f1b0c04143103050c0705010f05040e0c0c07080d0210060f060507170c010b21030f0f0c060f0612070b090411090409080a02070801 66
    0x11000340015606a0110300d005101d600115080028262194106140c85164072610341c81076604139060f049100414100480911940404240c21141004552002051682541001460305051501014882e500d0a80c2c2001202840a00300c02002c10074030703a4940070f8640da0241d110342c811841440b0000419610480205a03015402d603103403820300d4a0855400c9150b94060200340c2018014407540030702580c00c001e1a03009000000040010140050010382001a049a0320081034100304050000345991310800d41198454035140b41d03a040c490800074900c2020181100c2c014070001460307200164150810b125011040b220091184400c1d5880400b52300d0310320043c0390a400902020501940c0c000150096000030384001d440d11001194840c1008021a4091098640e920a012145c100410184250a4200010503429003820300044e180e00807110144d2195031500041044000c115003a1002c40102410601403001e0b24030b010b005a80008064000510490070000f91703906050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 234943336 1250 234942086 234942101
    0x30b09090a0302190c1a222702090a0e060102011d060105040c0215090325020f0f0112020403080405030c01020712020603181b1002070e0c030402040b060a0e1003 71
    0x540003403a040009250b0310a619101450a0b17032020020303000002c1c4102217240f003486024540c0c0080c3d030780d80c8040d8400840d2015003846401c40c141c500c442072145510b442d171002c100703c640003621841803210410500181c40f904105d582c02c8200a0000207950075011000d50146000b41c0007808582040c0d1481c0f001c500d8034000000541c0c0c40480100201e04081c0e0000b04506003910584100040b2905003420340c04041e100b11507180c1c0001003901c8040c482c44a90001a055044520a007041c51f0300091100c1c0956800f13035100e0711903900d20005581c06000014001151410b0954130303950b8170b0500a8003508188180e900034024040b031345119600c0400c03250161350282071000c030503184540900070715400c001c0500400048501c44400d10040c10031904000050b0401007071640114001404100c0800baa1043e082d0342c0044001d101d04207290808071f81c0728540d80c20342a1207560702c2c0005800361a00500d1150040400640001460340c8100130006002064a10f6803a07110300100407000c49854 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 234944586 1250 234943336 234943343
    0x41e1805010c020c09010e0c0903150402010e0603070804060c0e030a060501050a090b03060a020903102910020309010c020a03060903090e060d0f020105130504062603090102030a050c03120403030b09090a 89
    0x105e8010301c212004102019084040760480324205420500801d151610500b81805000e4020703080004540c1d00c4201c1c90104442501e0700c5065050402d80a000404050401012662541c44500005108901060f21844004d080f94405001410300c0360081c40c080c040c041c080c205a40340860303078160b1801380505001d0083c000788440c2e542c000c01c0388025003103542c92a03418002c150120f00e01c2c2c41030703005441140d035520400420b101850766081d04020184240d00d40a503516200407030065802000365982c400c002e0038460800010303480015404541500b00901042c0742288040501d07900c00c83c09400e032280e4a02c004910344036882081000b106142e03005140e2820024200010b52103800034112180300d00603903400d001d40300c1e0001004c0e200030340c02c1101e4101d42108100010308407a030442001c00c0440014514040d003d0f40004d4903071146151100900c540056540c8103900c00301b08a4804082c0020b034450307541490b00d00180540741002c0e40ba0702c189243c5c400f144403000c0102b00308003015803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 234945836 1250 234944586 234944599
    0x30f090f0807050705040f020a030507020d050301140d05060a0204230f0402070204090b010b0c0c06090a0e0402060c1518010c0c140a080412140d020309041e1805010c020c 75
    0x2a607920101254820304007103c03c0e0044103800961038507580607140101c2c0c0d404102680711f04810714002d04407000184031a0440d80204004901c681e040401c42e410341d00071802440b00c4001400c0450031703038103001d0300040c018400d100802410036101d0b030240c81950300509103290803281042e480b400000302c3e50075440d408600c0e580c1c01c000b01e28203a401091103a05c060004210032072151138100f1150402d9000380d403a40000281d8107181e8009100b6151820750880d091401c0122650100b03010001d540a060034042c65180441d040d95941c1040d00c102c122078030304441414400c42c0301400c428609a0b45804a201c160009000001041c000d40d03005169a648091080c070440e191045965501048030600c2d014030035208002c1354103940100040e040c080d200340c0b40c40d1703214035008203141e01c0710700d61175020f030400100410100d40c00b104586036040c0440300813880911241d9000e1101441200c5e049a1600d000c0c610307440303840403400740c038021401070000704500090713140309030b0f10307880040d09283e4401c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 234947086 1250 234945836 234945863
    0x9040606061e120c0c12030c02010605060c030306060a0314070e0306060105040303020c0f010915051201120c0b07051e060a27030c1b0e04050622030c05160f0303030f09 74
    0x243d07258001c0381c65412a140c00c0c0d0380000b0f1500c4003500c0748090002c540001e41c446408030b0301a502400303901c0007042c081d00c415280c03602c0219403644030301001d400184036100010b0082030f541d00c240c011358a2400c098112044c1c0e4248018041c008480d08a940b900a00400c80040d81c02d6000e0410b4030126601900034060b1841c0c4034007009004041d10320710328144100b990303000c1042c03ca40c403c0600110183d0b180e45943e5a52030800c02940c00059000c07000540401c11b103100041c5415803924110b5001007451070300c4041c0c0d40703045800c001100c9018500e28041c0990300c08c0721709000400d28082c92007210f00b0411002d50001825540202030300902441800c1c161040000f80700303035400345280d40a00d004d0262442d44c1840e0040600c1154400d40c800400981444188101488a01d800c400340c100baa1785030200b49450a4140002e012000d020b11400c440e82034140031042c0048104800c400c003260080075220701071100420210300065000903d84011100303030345001d1007038282d01904510303a0403491 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 234948336 1250 234947086 234947117
    0x3030705030f040f120302040503070f15051c1802040b1e0f030a08040803190915050c010f0e011508010501080c0907050408060a0b01120203130602030c040509040606061e 75
    0x400b0081d000b11500d0524003503150210301562a010034111a03540c026940e949018101031400d50540c00400442544010030086c1900d4148083c03200d1110f0b0800540b00d11800c03580d452015400881c0c0b104480c20440c1440340c19150040364240b0910807182040400144010300a05c0c1c1c0078192188000302e00702c1d0096606141882c800e03602130304003d044130006c02c05503845003110740003a030000801d9800400c1112a40c1000041d0945080340741c0303062b5a803a46031072219400410f40c4004101030003400218111703254401c0d0000022000501c00a00440f182074000c28000c2606042c4200d030b85465810106440c0010702503e4100c07034481b0300800400f400c0e04200021208081c05c6402808001c0100055000341801501d1045004032000191040e8500014020240800720b85e00024410001c00a0780340248200c020183d821090040e00c965940b0038000b45480f568200c03581c4104c2241c1003008000e526040355040d14160341c0d410700b421440407600070544d11188031aa010402440c66491b04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 234949586 1250 234948336 234948361
    0x90a090b0a11070501060e0117060f130828120b090a0c110a1101021606050315030102040503190c05150d05060a05120f1b06040e04170f0316020303070503 68
    0x1a00c0c00151543e2a021083d50b94600710390316035102c000001d4001c401042480c03088000d038103410744c612015000600d072205100d40081c5000300300b0390346102080300c4281170081c43c0094482c0300d190f4060380e507804001c016a90451910242280c0001074852039400c0265100c1d0042122101c0042c0508a154445948640151941158140c10030007003e4440411003410066648a039020302604617442181b8000242050441a0440303c20246c1078000c00c10b0a81c002c0031280d000b81c000c1c404140300c0200d28000390180c821944182c0e45803107401d595004e05c1c031034581d6085074070784621007041c1019902d1007840340c00e001c4000b1350362221400f40440c00003030401e80c1249074400f90041800d6403a68440001035035060701107c11030380550100c4c4644100700c0c000c01c4440b5110f10030001412020800c04005949446180110a1100303228800f203810441040440d820311800101020344a0070b1100c00098290011034040446038152560500311034001b10441b40105407540c1c44525559540c00d14855 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 234950836 1250 234949586 234949601
    0xb0a08160303031e1e0516090b0307090f0f0819051f0b0d11013011090603010311010906080106081b09120601080c06030609040318090e070302090a090b0a 68
    0x21080c2442c11150603168248984440365403040103140281c0611716400d011100010895051880701c54076a44e04650414406070803034941c09081540c0b030f0741ea01c80490b01ea11441c4e110100080010a0100d00c0349041c141c0c14090b14101011111014203621402d2803026441d00050b00356001064480c11584548421594060b003140c4003048041d0407001050545035455810341d15201c01c21202c62042d079108000e4082d0215242c0101c1d1104040340305030420368a12986030603003650b02e0484036100c9900000356018035600030207454482d0380d02d080030b102080300c2060690003c1c8880001040c900c1c05a00c07030300c1c180c0311540c1c0c44881c0c664070182c44c0c00340218a856007242803041844541040d5987c814005100c4603480c02508007075142c107001510341044501040c0c85104144100305180d00e402c0059a403080e05807424110440c200c0303240600210140c1c0004040c613051a48944004900040d00e10480344240c909422645d5110b6502d4200c44440800400700908403010403031050050300402c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 234952086 1250 234950836 234950861
    0x8030f090f060a02090a05040c02100213120b07020f030a2127020f0402092d06030108060403170c0d0c0e06040905011d070909050c040510030b0a0816030303 69
    0x24030450004400c00d1030040c0880b01c4038003c41c1c0000d007285113428145000c0c4000d00302914203010130740c1001c001a446540e40e08a6030703049980822504100400411400020206400c00703448407203075030500c1952030808480c40700240c440e1030492900480300004603841e00b5810350300c04000c484084400c0a0103010b010840c4045515018003d650b180500039130b0540c60b1210f40b40c2c0103007140c3c604c1440345c801c9411a40da4811032050215400d140c844407020360210a400c5a800170a01102481d60007048055071410340200d0040000315400d100014054000c5000340c03519540f401c3d4495a80c80031030011501d070001d0b40c4c4180081d10094a030358200d400703d6025400c0144009081c24045009a041503008a1391151110010001d048100c642694101c071038428810452801d00b4002c0c10403074151113600140d47d038810000e994400d03160107440c050140203010401c10408658014007030400f0024491090710a9400001c1d10807000507400081604407500180d11803841d2001d900401c1e041c88500c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 234953336 1250 234952086 234952093
    0x40305070201230c010606020102180d0212060414190c091e020d1a06070201080105190b130303081003120f050702040603030504030b0109050609010e0411090405210708030f09 77
    0xf850440c4441180f040e542d00000e81154569440414050a48207140e2100e015a4030400180c1c0d208509181204c110b044141e41410b5028030314404502c011780c1c80190907091b401034030f003800108020202c0c070403045004101101c9000a4100001c00300c03002c00d00c402007040c0b010f82c60800c5801000e404c0b0b00020111900510442c0b07194260328400d99001e00c40280c0e5071036172503501d9800f880c440c0e0311241a10205417005400e1100c41c0e4000386c01d554045c02801d01c280d906034080c4191541000d40c0d00041c01c00500025180d400d424102c2c4403c12160004802145508000407104400300c00b030001102d4000600407610243d00006440403400c00c0102410007604020540c0075884071300404000398030aa940c01e9031207207035003014840e40c035060308040142c0d400c040c14400c0b50b5441180c0181961942c03c410720740368541c1d2a08181c1c4419900409402c410f01508100c00c0c0480400c081000c0c601d800c0c5102d04d803c00ca001031683e10311410304000c0400c1418804180c00044031810706601179001d2044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 234954586 1250 234953336 234953357
    0x4030b070c1703060102011409120906070503040b1306050c101a0303030f01030506090f07091e0504060606080108010e0a060e07050a030b150607030c030e01030b041a0301050c12040305070201 84
    0x70344400851015007210103007400014000c03a17580c2403265581d0704114228104450824039450380e15100342d13178400d042d5801d000c64405920740d1090221003801d0f074040100d990710b1383c0c1d4400701f00d0590000d54004000201500001030f50f00d01800480d60320309602806403913542012101c1c0c0700141031164440ba818071000b068500c2c50f48041004500640c49825400c0646d807461070500d15168006000c00d4241d0407420b2911403821000030284140c8602540110b07000c1800c2d2500c05001c0e8126101203007190920040c0414841d441d40010191403240d83c81c0c0c02c041e84c80d0b08201d800e0310255002d4905030f90040003180c02280b00760380003642d070303132100380c103445142d0340d140001b40703218501c3d8005440c8a001802401882200341c00c40c4030303000e1003e0b12214100b1415803030142c2403c0040c8400340610460725521340742c0d0380c03296001200c0e10070000d10400013400c42c49003071a0040c1400032035074060742c46e0801040742e0104603401d59403d01d11480282c002952039617412505a04116001c80c144400c0081e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 234955836 1250 234954586 234954593
    0x60e01080606220e100606020a050604030c1707080d14010f03020906060702030f1b010216090f06030215070303050f090a03050706020903150610080115030b0a09020a0203120109060b04030b070c 85
    0x34180c0c109100038010160171745c1d0421040121740f500c1c0e000380c0665000035010340014401003000d95205805003402d221921050908102e009401c3e03022651000380015880100032180700600680e160010003000f403010f40040711030746854280100c400103a4846002c10052800c5030544d540504d0140c062400c0c4611680840c2c900326241300461490f401000d110840d1066400c03041001c80d90901c02411404d1040641c8103031a080703401014001074455000307498045ca9500188011680503014a0440e10b41d003444045a4121180441c00642048003181d801c07040030301400d01405016002d0041e100d00e039038060301c3c00c1c0c1c0300000403281203400f400001a150f605100c8200916061240341400345050000c02065010440e490801d03ca01640103200783c8043d061a14118520350400041a269a40c00620008455071103075041a00010702410040d5000c03015102023000c5080800207031741c8034080b0800b41d61080c043e0484a18003803000300040703074002e40380daa0802e4280c14100c0041d42c1545 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 234957086 1250 234955836 234955841
    0xf0c030705061605191407060e01030b030c0a09021309021903180b0c0409050603150a11091e10020f0604060c111b1c051504031e020f01060e0108060622 67
    0x1245170410a206003184001c1c400510004004007040340e0180200c2414820043c2c20448094000c030704141d82e0380700116094804003c4100d83d1440140352126181c0d0340c8007484003961000c01c10328120064080c0c0021300c0180e500982d14015444040c000d4041d1503070320118010024944002c80c1032800140341000300760300c0481c160003890440c41c09540c3e1400c3c01c6034002540d0000d4125800ba6120211040d1520b0101d15907540144045001003858030900814840398040c0c0e00750790b640718155249118a001d075148880410003001e036143d240d40113920600b80d0b180c80e6000884546a0402d9001030001202c0e94481543c00c0d001e8108011010100b41c00207184c2000305411004224480243c1640c5281809411070340202884d407d80072101c003595030079194020500321016141e03072040498201030181000562240c40071241c1004003102102c02940e80c0d030b4800440c0310030351070048040354a44840a109050325141c07001401584c40d15410710181e50710034090011550b400c00d04d0081c500c070003070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 234958336 1250 234957086 234957103
    0x4110d11150910050a02060105010c0308040b06031f060806070503010302060711060d020a030c080c090a03151404051f0c05030c0703030f0c0507030813110909030d051003050f0c030705061605 84
    0x75940c2c15241c1302217840113450208103030002c2e414000d040742440c0c006503002c64450b5000340c0c041d40d83c841c56112103010034500300200c039071614000c0d20700030b0344000640300344c1c08001252a00d00484125845103201601d15100078000a500200108034007800b01b117407800040640c0c1c40c0074001501d000030810b000c000701c1c1c000c928488000303900d40a02c14080f60340305403000c2d00210f124030442d2074860020300041d640c01c2d007448018054030071306240581121103a0302c403c8030301c10580d00404407032034a0715005460710143c09019580603480400d11a0350402886803007041310306034485034a1750703c0d5402c03100520b07000380200300c0c201500e6013400500c805d00c0317004100c00480152203060b110020741c50081d1002c2d4000341000a410744130182e00c400700d40c2500c0300501040003031307494080a490340d5100e079040d031049608002845042900344825010303140b0416080300c0c0108242d0314148925101c0702c2d212512000d29540c1a80007013803e03c102d144c041c0080003040a049140030900002d50b42c0c0500380b2200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 234959586 1250 234958336 234958369
    0x1e030302030103150c02030a11030d02040e0105100804050601050f0f180a0c051804090f140c010f020114160306031e02011b050d03110705010e0604110d111509 70
    0x201c010030070403000da582008203009411043c00515100c0000a41e24000c100004040108e5400000c00303440082c400c641000201242c00d550b550380340c4140d801125800c1c8103070742c010212012804031452041e99400d00440e4804082c1c0f00d40c1c0d02e04800c20200030f2208281c15800a45640607099682c2c3d01c050700b40003242d003500c1030045880c1c070344029421520300341403410901900700440440311082c04040c1840369011540003980041c81c1c2000c401301040008014548000f640b00c1c032540030000503985000030005d80e01c40c52130180400089007039914000b00203482d10560070208841c9642180402e000100502e03001440030781d2500ca080171034148070800b01c80b03182d194901c40c06659200007040f20b02e6038002405480c0a07595652907960b40b1a0107105020155210766a1481044010480340c4441d0440000c0c0101d039908050603482d072600761801c591300b0303400700d0220b00207090501c94440c071a83c10107a4071a400318454140f00c60300400c419040c1e100841004503640c00d0f42d039000c41c8000000f4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 234960836 1250 234959586 234959591
    0x405030a050106050307140d14010e0304031505010b040b0909071803030306050a0b04180e03120a0c080603010b031b040b100c200d06020c0a29060d030e0603041e0303 73
    0x340c442450704091b4250080c940d40d1124002c445055220071071090310043e4000300003181e841101d525203004000c1a0800b103214040000c000050050180d00c01c0740d5141e000c1020010350742c1e1020021014410b030300c24038400d158280207024240ca49019003980c42040c03402e007103a1401e01d01c4942410b10031150403c50101e582c811041c01313541081400f034030140003598262880d181c00c050f040c0c00101c010824030103005071544100030746540306005a0750403c03440310303a0300b980d800c1800b0410082c0200c09043c800161481000407410310301402140880c4074040d01400890041032214440d02030000740c81e580003510f030340da101c6250b2900d00341c4680c0b501c040e940c0c1c20305c0040c0780d00d0841040e002ca1540601010384190f8000420382e2080007956403641c2c4180010383d12040038451034141309500f00d01800300f100143e101042e00400c907145c800a046003201b40b02090717a42d00d04024500940030342c050001035400000700380b40e09000c002150440d01503400d42d102c41c43c4010766407050b00141e610840002e40c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 234962086 1250 234960836 234960839
    0xc060f022205090601050742050907030b07030902120316120c050d0c02130606020309010221040605090d0c091d15163c02060c0d09020103020405030a050106 69
    0x1040c034241c20094a012190300c0840d00340300c80000c00c0380c0140440078041c9044e48007005800700110113425010b18103a03401060b410f800b4207035201d840c03015441c1c41c0fa0030f0b0300b0000000c00300d510100b070b1003050729800b0000109988403c0c80442c01070092000480c0c018400c0c00d0b0b124070444042020382034801e904600d11311144507600e00714000491440c0c145d0203100c003400d50305001920210315124003051501d8030558809580c00020402016155024030152601a0105500d40d0100c020102c0280c2a0200c410f54036441a40481a00c40144402c0d21a40e05110900c50144100001e0001c018001c1841405d102180ca80c901561616800a141d0696484600351190100c195030800c1c948094060310310146420390b5096101e1005081c00300d841201b164520300366014814020780c0107021221010085000b11103842e921126071001c032083e44502e117010343d5840c40000c0ca80d00c80e1520b0140c0c542000c48400c600c3c0007070800d18100700e040c560203004c00702d1030345ca042084107006030048001040f000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 234963336 1250 234962086 234962137
    0x2070506070e0117040803071403040c0e2d0603030906030901020d060e070813032307050715051c020d02030f063303040516030503040e0c0702100c060f02 68
    0x503000c40ba40358140500d4241800b40884114080c0d41d00c19002800103699a6540e8011920301102c0342800034414000300030303c0240803807001804155001c00190810b5078668240c1c2c0c001d8905580d2016540b82030072003544c0b61180c00701448580019000d0200d07402c0100410018103030f50000c444c0019903030b5000c02c02056146190150070b00524904844613068102040010034081d07008121446508684040904040c40f50044001061001031050b0701c141c020090444c1e10340c0002c00c1600c55100c0d44c4000300d40308580d5010004400010341340c0700c2c6404c4200076200045102501d020f100c9030350070700c41000b800d02c080c0001c5206000d203001b01900d510300b440c10403148283e80900c52548642440740c030f500688480c1e061000c0d40035184036444d107907941e9291817490301d585540008000c0005130300010402074000068010385410100b011100d5413a18065500c0380525080650300c000940c01d948403442c0113000e00c5500c2801544003280302e078405400182644d00c640d042956041c6a400a00c460 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 234964586 1250 234963336 234963347
    0x9041d010b010c0f020108040314031e180a0201110312070801031e0206030c0f0903032101060201090302100e1614010f0206010b0708161a01030210021c030203090703060207050607 79
    0x240000d00f894040340d103107900c1e80b18028043d0b2034024103009030900450f0a05010740304c019400d10f9422042c0c0d50364940320310042c803021a038600151824400b8004960b0440c50304ca840c581c501c0e85075000301491020f603001184e0350200f406141046020820103100c03200350010403d40304202c0c0b911881500e514518055840b400310f240503002d428854424000140d40c1c18085a41113a01108041d48950301903a2500c200e10070980002d900d0700c00011114504003084411041c40c4020382403a42107070380d81d044207a098544204004006030001500341c403031140d15038424050701c0241d408481a000f1410f01c2480c2c45082504070310840044806a031080d90703030008000c803040640e80302600e529490f009018400c0e00401c0002090410702050800c54507141e200c8101201d6042514010382c031104020f900500842804240d0040d800384400d40000f034000600c80400b0340398401194000e00072010210000c0d00050400c1e003440c06031070320020120700140060941d040c0242c0281c00c0d14208020080d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 234965836 1250 234964586 234964601
    0x91d2502070f12031d011709070f08030a08130c051011060a0b0f0f0d0213090203010b0a0e060d0606080a05010f0507020105160503070302090603040f0302060105042f09041d01 77
    0xc0c01e9090f090508002540036807190000031030401519260020000184c500a40c000d8694022174444000c01c20101800521001150300c02030402c035001c1e4992521a450b441010200c1001c981c5000c0400c60a075030380d1220094040c010341280388401c0c0c4400c002012911402c40001c0040c2c0c14200700c81301100140a01d075041401001c1c20003844442c140410042c100000605100b800800c1d80d0b8285a1984a81400f4141e80100608546405040c0307940c000c1c2842007059029600e4007040440d1403c0c40145501601c01d4446581c0a41da1a401086400101100c00b1140540c44104c0042c109600300110041144904004a80c0c4c46040139130908580d0b0081070507003161304020501009004140021a00440c2458550741e00c0d0340c0e410301607010303100d40000c00342c12180c0041000140141d0a003204035051013642a02d0f0142d81e030303004120a84400c013422555444d0620000c100c0844401100601d028165442c00c0c00d20504c800000c080300d200700c20a081ca1091160744140010081c440c0a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 234967086 1250 234965836 234965849
    0x30a14060a050f12031908010f090501120b040f15090b060a120305030a060b0304140d080c19020a080c030909010e010602070e2e0503010606091d2502070f 68
    0x180014501400a07140500d10b20016010328441301c0d00450041c802d00440321000c0080d002c95144050544004040382e409201e10a02e64803c5100072504018600071039048a0454401d050608040d0f141ca10302c40300e0191044400c0c00030808901c001030701410a00307040301c14180c0006100850760411890340000200b42c0341c0700d100b601e4414401e070400701c3c13000c42c101d540518155803660b50780180d15005000d55080a8a8408040108001c0081c162220b07601d4030701c1501610a250341646041d20142410b5500700c401c010184801020800944181828143d041c0b0488040f100603884207072140c0d001c4040804582c000107800c03600c508055803001c1c014032049089810b01e6141000085d10754015024890145a03c4000314006482642c98090310342c1f10039403100c056407101001c07100841c0d0503110305800795080c4440002c0301c9005100709801c8030500c8802c00c00300100c0f00001e0380b132990001c004000d0140d1000c2041c1c3c40588107840350101000c0c54004100e482e0810800c0f11b4100180d91054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 234968336 1250 234967086 234967099
    0x714040b090406020708120c03040c090203062110020d02070605100e1504110a0c050705040c1709161205280611160c090c0c03080f0a11030a1406 64
    0x600a0780c952070401507000d030b0400d40050700e900035071a00700218490801044402d9190a080c082d811000c00700031405039109414880c030103580c0300720040c107a00046a07155440840c0d80c0c4044600f454514040140c03025840c15039842d850444040b200703e0b00315000d003407034080d408602d070300802042d071044540110080c107d00012134941404a010008020710108011090b0043c3c4212910355401522240412403000750310b490b14560028030000f02048240c2da50b100d100301c0020281454444c00c2d10380a550b5980040750324048200d05050030006d480844c041c070907118040314000801007110090700e14180c60030004e01c800c0c24018507040e4074602d035210300d0713041d05100b040c1da8000300e810554035030344014045407240030304064018274020f051501c069a0000702c107040400c041c042a1034183c0710644000c0044213601c1808855003400e03a032000b0302041d80700c804141c0c80306d07241012640c480308064000c21500754103121580a40c02c02d071180300f016130301ca40b000c40d00c1c8400c4440761039100400f51520b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 234969586 1250 234968336 234968351
    0x213061d0a1113090906020f040303080405060f090c06071406040503040f050402040509130614070c05072c0c07061b02060a0504170d15140a060816030c0c0f05071404 73
    0x34041c050f0a10501d070035260780b401c0d01c2e020040a40c058030f07050b41c0241401c03074031140c0e01d080240502c041203400725598060013000a114003100c5507654000e803024002400c21552200504c0745903800310030141c511424640b07a00417121803c1181c50b00c928492000381d5110351405150604c17982268100600c614018041881162201c50185a06c61007060289801c850075081c24801402000720211181d88000c0802c42003682007114101e1040c81101207500040e503e040d43c81208407040042d801c1042000801030001070143c3d00305401c000c2040160303140c98507a6031083c040b10155000c11410703140480c5200c4d541e0b134040c0103030390780001c910074140402e150543c0d546441b940000514014540085880c2c040e4400c140d00c090845411610200c19050316018104891244140081e209200682000c10300d1071080c400240206694009a5515442a001603010f4007402e1003400410140305191000300d00d5008c0d40641080c010005040103e0800c00031a0355001d81150260285060804 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 234970836 1250 234969586 234969607
    0x1507091e14040f14040c15110604060c1e0c0309050103090507031b091401090c050c06150d021801060809010903051204030c0503031519060c0213061d0a11 68
    0xc452907203075080b200081c0d42190440b04100824210940640c0303042d000c0104820400114403401c152100c0d440e9981c0280c0600208a850745807002400c2025080080440c00140c02ea4002c2c1005811f5402d000250004280711340308507540301c0f42c00c580050b100700ca5180c00d2540040340a8043c100a180c144036400094480c10b5640c81d00e0700c40144100c041e0004040c51900080800c00504003e20302030000070070318001c132055008203014212040e4980020311446038003e60803078082d03168040c017421495881c1d07804000114030403101c1075000388100c40f411005980d141d00030f000e20440c240e210b5400d035042120080c0b445d00300a00c0c400c80c0c0d070300d003107a0300011a03002001d841ea40301c07144c1ea9021141d942c6260483d12441403003001419840f002c004e000c83d59007015142c1e00200c105581c51210040d40c40310340c150902140c403a80c80466012040c0c1f5025041242c44080b81400c09207001c01d98650340d61100f141003c18134501d10741e8443c1101445620b17000e5001e40e440852100c49800d041206440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 234972086 1250 234970836 234970859
    0x30b030a030c0c051002010605040b090714130302040203040602030a0e03040f030b0c04090e0304151d04020a030b091006022526100c0e03060c04060f021507091e 71
    0x4001e42030000c055050010051103010744006448050400c0d45402c0400602a0107420701d03004651140b030034070031f0b003015504290690f54030070801903443d035501950102030200e460303011202c640d480e070031070510120240e16640000c0d0b008601c21400180e880ca0001c00b500304503050880a10700035082040208100d11100e03e148090340d801114480058480d80c4284c000c602c15a440621503030304181c901904288048050011901265500800d504440f901181d14403004030708010001a08503020b50f003410540e02800c446101d03401c000403107454800c00584206c404481406145c2d5210006204940d410302c40407600c6903061081c45025200f001c000e004002c510300604880150400c0e0704007000c2080742044d1502e6000300b060300c1c030520701034841201404080702c0ca02d01103902da420200982c103000600910410304500c0c854105420080220b565440e00310319001103124080c45159440f170300b04100380c054065902c1e0074200b1450400c102100c2c140d1000e0064840517031301c038104030030213215 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 234973336 1250 234972086 234972103
    0x6010303120c0e0d0b180d1713140609010b0f0607140a0807050115120201080105060f04050301052a03090a150e010507030b012a15020f07030302120601030b03 70
    0x4110100d280c0b100c4000496600ea4601440c0342e01003042d03503848040c490303000203a5001e4036034002d00f40e0203007600c940d4440e130721000180040c00040c10f034442115030104843e01b05400c8400c0d040402030a5005456400303503008070111a001907003142c2c0c14130005040c02d2240300001d90301030750004030700303008007000078039501036112301a0455501d01c1d03107400484824010f0a07000d0b0380c05040740d5154080c509080e8020b140641c0d08640d5034254040114041c10381c0c1514990041c0d05130340e2115181e00b05400d00ca10781d0440381030410802424000030940380da003070182034070589400018110385800145004072400d11825104007191040062102c01c51002c03031503001c0c0741d804c100000149007050700d07040010401070301c810070103505c1c1c03105000400f03900d03800c4147e109000341c4e0703003852100b5003243e000f41040301401c0980c006020108030740c0000341100170b00e104500c501300005013094403160a501041d4840f10003100001d60020b014240043c05144a6802150038602040341c80c4212010a80da01d000303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 234974586 1250 234973336 234973367
    0x6040903081b04031707120e03060411031903180605070b01090b01020a0602070609030206060102061e0c0405060703121503020904021201060807080c09091902060a030608010203180f06010303 84
    0x181061645020a034000321001140c0c07001048603c196004c2e4150171303681001104550500d41c06400c0c5010381e124a40e5207003c90070040181402d40c6469880140c1c000f2140c1600350140282c2011a07812401021040502d5010752141461406131480702d00c10050590416405e02805002500120341d132013130700700e040d0b41e640c450010b260f0031b000b00140c4c90008044002401640001003500c00c1201c00d8221102c0d251294007103030f082d5101d05006988500045881032040708071485c141c4034018602d4081c3d42c020128501c11403a2680f1400826142da10001c000c1c0c010440ca201c940c81540311030310806000700c0c81100041030050039603000a81c0c145014102a200310302c04000010f0411082d1b01000041c01840c0072540702039507810f10151550301c6401414425070701c400000d07500f0344010520310205040d2020701511011a54204659904190030b0f01c41010780d03401c0046a4104244002c0d0b00403076000300d8041d8400007a8082c03900e0400101e04292040d0801801040000d400068401c0501ca1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 234975836 1250 234974586 234974611
    0x31b090403020a060f0e010b1f0c0f02060301030b060306071806030209040b0901030b01090c05091032040311220f0e10090203010605090f0c0a030b040903030b0103050604090308 78
    0x4803810220f280520034400130304041d14240080310f900095502c0101c00b5550740c0024008440f95004000c000074105004450a9040c10f4107130110900c101c6a40166910a14490940f0185034000c5083c5800907041110304200c0c80c02806114581001420703403120303180c80d0500404480040c40c141c4401d8510070750701071507004100b43c3c08990b50b40d00201040782003d00811105c0d170f582d0800045420081c440c140d101c616041d058104680b08804440c0c500e01d000c1d0002000099202c0211807109031402141c402d030034070080544001860480c1d2000203800e0300001c903140c1d42103080c201a1840341103010381c464503000e00c2c40f80c005401500300c0c0186070f06401c40002d90b8040c40103d1400b45c0315001d024145401810035036010b4188940c01011214000e070000c04c150390700c031014002c600d2801d07242c02041c8420500003911010120001342a8030f0345d1803901140046070003010600b44c80030070b0001c90109441d0340b51001d2559244c031421f0741c81481107405010800744c1344c030003400c00e00020308841c07107042c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 234977086 1250 234975836 234975841
    0x6030f032722090606060315051005120f070905060406080a090c09060b1c020705060a0504060207060e0c0117060f120a02150705010f021c0e0717010207050c031b09 72
    0x584a104200c10110b204001c42010144a01c0c400000e00346441c0440d012440e1910101e41548a88109410441c1d00011034084604140c1000489611891400104075003000a038400e00c1c42c201d0202c1c010b0b01c0f10340c45c04100d420711182c09031a850b05a00712a000d41c2e0240010401d8950155841d9000310309800c001075040094104001e00e0800c6402c8100c8003030400e03600140d02d4146100038240341a00c0010404408244507640080c2c1c0b04aa40140255128201151520f0b405501c01c61700544204001441c080d0541d941d0700c00d035407500c40d1004864019082600445d604141142101c10380c0094454040c9030090005608500a00c10746007c1d0070800d141c1144007808005007810150005c10341460648440c01900455001000840704c03075080000c01189a42d86000340c0d981044001d2103030203000350600004000b80b02401c00e540c214403c0a1000960341d6404140c17000c8030402c000056035600d00ea06000f0320304100e5429150003607000e0720318410b15280440e4240b03032040040350100c6894 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 234978336 1250 234977086 234977089
    0x5031311060406050c1006080c15070510060806070c1e0c03081305030f03070807060b130c0e0a050d0c06030c11030c010b1003051005190803030f06030f0327 69
    0x41459008007a00a80002404540d081c0c000019180034102c500465098014803070285060300e45500c160400c9070300c518034540c014500200050250a0842080e6040594585800c0e14004011035000d511503514042803282000074080582c2c011400c1c1001789054215541d07400040140000b01043d4490071090308080000d034101031002503803c14000b030b4076080100155444800c1d2032160921904c1145290f012041020065500e9580c001c00c01c103041110580354000030702594854240e00840d02e1000944c2442d1501c01d030f0201040c0381c0d40303462140710b00304c080c80301a117102d401c180d01c03e801c0b0810041c0003c240e01040d40a0b103100e07280200741c12030301c40c1003510700705400c072060111400041000380e17140e80150b01c1880c81c5d010072200035512200c1e01e0802d0301110380a94078042e0314040081e05111600304080b403014000081c0d000d00d10003a136039113001d070308540060352540803140c03040741888050b15080040c0310200303503030380061440d240150720002000d06e005010088809030196911545 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 234979586 1250 234978336 234978353
    0x109050105040506090f0a05030d0c090b03160806121f0219170106050a05030402190504140a200a0c111005070b0708010807030305033c010503010903050313 69
    0x15588100280241d0506260950b00d81c0812605c0d0585486010380e1100c0c044c1001440c002180d8001000c0c51526a100c40041c4c00342c50039000300e40520550510005003906d54000840c40384046146407148030a041038020010203010700f14902c1280410b5000640f000301241c41c0400d1102c0d0340c2c01c8481c520f288942c07400a1b006100d5030140800e034006c0c42c0c042017904211010666010b104031166036a80380c0b0000c3e40d05000d258070071800100c0c1480018018201b00b9008122034000a42134801a50307203100003005d40b183c4110120106100c0424484113202d103014085010f4040d000c0080c011032407016050f45401000c441d08100005009140f0901412051004c040311028080f20030a110481c0003608590100004451004103000004e00e8180326005247c16200000c01a080103072864a0413640781c3c0004d08190440300c58000d498002c840503180d40f10300c0c015808241d030703001c0c44c00000e21105520305a0001e4044d90500a031800003e600204a03030303105035142090b410f20019420003408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 234980836 1250 234979586 234979601
    0xd02090a091104080f01140402010c14010203010b0a03062c0a0e01061211040c050d0f1113030218060d15020909090102250b04060b01020313060305070f08131401 71
    0x280380703030860712541c040c503030b50041064426a4040366012110108402c0c00c9920702403a0748240403401d00030400540c441d030110f289103400703841d0040b80c1840c900e01280c00c9071f2081c0e10009070014002880000150103002d4503004211000a203806104821f00204004002141e681a00502c18000401804040c0d00038030516140c400208110351715200444000f21704950141d80c81d821320415104079142034003504001c08001c2d0380305070a020303869948401030107464043c840a182ca0300c4a08424080c00405460000d4401a207003008614500501400c0203074410000980c0103c0020444641c640002402090364424220601e4001010302c2000a00800c1291030b4003a21510602a84000c150094100c0307502c04941010b42e0494040c0c030b04c10140c0c445c06d00a0944141000040200b829039000e00d8018106006891911242d010b219061100740d40100d80403d50b130300d044c013a665038402210499540c19003810921418680072643c2c800120034002410710b000345001d105007440a400140c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 234982086 1250 234980836 234980849
    0xc07050d03050f0a03050f060303090114092403010303110708071a090d03121802010c0803040204060515120a0605030c130617010e0f0a021e01020307140c040507050f0d02090a 77
    0x1900d90080c540001c024106c1030f5168070501c41d4010206256280c044200d5127940c82c161140034801d4902a42000e80d41c000b1521280c2c054030250601900d1085000d802d214103580c048003e5896046140c0074100b40c140020784001030f8040c4505100340000001d40710300b0f5818040c9505180d9a41094101451003140c0319543c02030f103280803031010075410520311922818038280030320809011442071502030340710000181c006040004454003148070140195040f5001900225070741d0744880105050015220340345969450018081281e41d445030036842c0c00c079411a4040c07041605e4400026a151040034601d403182004500c862030b0420103511041c02804008051380e5650101c0300460b000b032886031002e444030f009940c108040440042690303411294010516820b05050002071802c51000780c203030300c1c15480b0820041d0041303911000054104580078000f0850394903000b00340401d41d00301a01800a01100b440a0281c058200080e075080c8814a40016107620540c00010141401f0390300c0f42 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 234983336 1250 234982086 234982117
    0x60e0a170604030e060a0c03080405030d0c0f03050702070e01092309010209120d09030b04031115070f0e01080c0c1615080c0301050f09250e010e01050c07050d0305 72
    0x11808140401d00c40e209038000d85807950482c00000900500d84914a561030001d50b02c042844000390052001d035420038001d100f12800c048440f6491003ca611208596020600c0400c0582c00c0c20341c5170080ca54002c1891018261a610303023040700c0308042041c09040510740d110b81e00100c180000000340813451b001745907004031031306000100d00e00079800000b8140c010075222206480c00c05000400044550141e40c0b03c0c00c2e42c42c03a540301d0411300c540140c002c400700710749102a20090b941c10450f13a1000810740389500c1250804181c0a402800d180c0300380c209201c442c0300d440d01242c0c0c2000b03106034848401c00542c0d0703403101990b00c05414880d02045002164540c42c90214041d49140700d2451100400c0e2211000b5445001241d5070078007003403051507804410000c401025007800d0041c01d03009060190011f08003032400c1e0700300f610704840101d00f500042d6040c0ea000302641c1c2c8900b24080d03581c000e0824601d8078000c0c0c0c0347d0503100c1035030b4094a4052400404d03840304141c4200c1c1141d020081d40d614a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 234984586 1250 234983336 234983369
    0x210b0402010813120e2409150c011e050a0b01170a0902030703150b01020f0c04090204090803090109051c05220f03030e01020106150203090906130908030a0e0313060e0a 74
    0x10340110f9502d0b01d940e000301a00d548950354002ca065401903250700700029641002100000c00241414088000681100c1485152278040c001d008030402d0b009082c2d000c174861038250071a03030102c2d900204505010707410091070090a91300040e0b0b00348a043c81d0420105541d4502c43c5100140003080c5009400d4802d401c400405c0c0312116001c6084075030f941c02c080c4110301e05080126610201060340d01c0580c3c2100c9405d0700140b809900c01011300388050b00201d2190135640301e80792181c0044034041c0f0140d440d85909010448148045803070403600d41d920718090405da181c010000e00910080c004d5025024540b003111501c840001401800c2401c403403000552a850300500c0c030885d058086000d5070900750007150686103041c1e000c1080019a00541c104103443d010403c01400242082d0782058540c203800030030704018040c1588050040a00981c0d904082c407210b0110742e200c800340b0b04290800d0010f1540340001d1107550084501030b04c0d16150280e1441d000512103401540161080c04203030a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 234985836 1250 234984586 234984623
    0x10308070f020a210218041e0302100204140114132303010c020a0c0b0307050a05090d02030f010212060d0206030c0d1401120b090a080901050c010e06090601210b0402010813 76
    0x5881c04024804c2d0303503000d43d040c25000c41d040700380700c2550010f0205800c1000841004032061040707501501034070488a0305941c075090bc00480c0c4c4250031142c4a52a0a840040f065801200880202500b0204c00b8940300c49240010f4040400d40100080121115a5030640c003181d8000a0840d900040080001d9108480080d5aa404044048521092075070000a00c40003c00c285c85c4203a04580352985400c00841045a00c0c3d0b02104006900544501800e40503840820065211180c2e2100040c0ea418070004c0b105060340000381814852100503c1c681c0040e02e400d016a07402000b070b141c005803223039940041140504031a14040c501e10709c48100006091500d41c0030f2a0381d031070003440c0c0c5101c56254104102d48424190801501d0358030100501101c55200d04000c00d0303e85007036070001406040f00000302d41000d4043d1004c40407035103d840180800c00800300d14080007140e40900980704001695007161010700100060b042c014a0400a5100402040300c4134005501c041000c680da8103004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 234987086 1250 234985836 234985889
    0xa0206030f0115020d050703051b070602010509070b1804050603071215060b090916021002030412030e0304061409060403021008150d051209010c0b07121103010308070f020a 76
    0x8a01d0750791a900c40f15a00d106400483d601350300c60b00301e50300d2514110705a1402ea81070f60010358a1803281030800000071135950240805809415280d00100355801c0440c0780c28506446074001d00040d0004020307014034441d402d910b040080341c0c26100411f06656083c0007030300300001c40e403206010b51482901001013000f4428154103103404074404024130b944542880810303002e91140160480002401f00d02d070100e903007404180e481c0151040394640904408030320b05a0b0802d403070465002070120f030051201d1740c040c0140020120600c0c000c5042510704103000b0b1030700c406290184042075002403204d8080c1c1350841210003454020b09000710000c18240001c140080440350881141d4040f200d102d200e1a0040505180503000401440b00503075004091880d503011494450504c034801550500194018900c0c0c1e1003203465440350040245000441b2080e10902c10780031a00c510700304011f000060040c000c0d41d1301c80b9081001809881c43c24804220311400c5030700501c0800c1c0f040192a40d041d0742c6079 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 234988336 1250 234987086 234987089
    0x10e1e0406060e0a090206070b0a0e030d05010503060f0603030a030c05040306110a030507090503030f0c102409090b0f060406081b0a080d170c12010f0815070f030903020a0206030f01 80
    0x910010860340d130b40b0701000c1c1101c0c3c40c460002e6200c142080458045421a01d41982121014100050b13410510221510303541c010217800001944a030010045882c0900401e0340c041082e41e6440c07014945000041c0d140e104124010f01450354400c955203070030303224401b61805154050403c1080b141c204d80320901c10741022005000203401d00740040c00d400c0c1304010640884002a00844c1800311400c4941ea0341d0300000c000c80c41030700c00c20015800305c61403404ad00442e0040386044071a54124033810302c0080f540d070b4216540707036400c00903c0703800a40b061091681c42106403003115480e40318240001c1c06804240e010500a1007004584603d56110b40300801c400b94084074862581076581c00e800f901c0d460700d881c6041c0440c00a20100c4003042d004000c1c2076000710b465a81a250882c0a21142c910742400c4c0c002840341e07070660000340048042007180e280440740ea0101c080261402130300091000e200b060b180c0c410580c45118031000c140c000c010446c1420741c010711968481c9084d8095008030701d401d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 234989586 1250 234988336 234988349
    0x4270c1a03180d1209030e090a0e0d0e0307030201260a05071805100804031808010b010e06160201050f040315020711120c040b06041203030c030e010b0603010e1e040606 74
    0x192914203002d0200081c1d00a0740d141540740c00807882807541d88034009009026040c0d060140d041d001c11040d541c2c014441d031280b424000b0028081004001c01481c02902100b00d409004100500c02c542d95000141c030b104903682443d0440b914410f5036000b116a240e81c81c02d410001c1000d00a019030401d0301d0308514820034055686c598001c4200c200801c404500388181e6802480344602e1220b040d02c00d41c2e20380d501c640a4100700d080c0700381c4c9802d405440e0000794004040f070b0359121501d28940d0f0b4031447c41c10034001e048800314100b441c41458417040c49120040281840030000313a4108010744107003520015a08a840002c4102000000b04040e51100c0d404130f9010025028805151a10840da400c3d07124040004209010124040c80014103182c11141c0d4000f10034400022150307084048803025500c01d5030b01140b100c1c141c840c05420307104844d8a841299040010710480e544500c829241100c9408203184059140c00030240741c200400c41c0118420442c4400300824030000c2d40048045807031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 234990836 1250 234989586 234989611
    0x30509030a0b041407060c0615051206010e01091a0d02040e010608070e0603030a09090c09090e0322120b04020406080706050403030801290c150a0e0c04270c1a03 71
    0x144e00340381600c850080c094280810000c0400c600400c950b640030150903c203c0b040c07481003079100c00c00180b40944600040000781c1c0030303d00611202d00340c2010740340140f55803003050041c410040ea00d041e200d00071048081c0503192400b1040d0655403240c0020000301812002048080d440341842a1920000d0055040d6003460300c002c6420341c100001261030b01203080d52000c034405e06194140e000741c001c1c90003040c108076801d00b000c1195000391080a503224190001035a6070194105506d0090340c403c07100c5d135041d0034580e2003005002040040043c40310340c005065600d6607601d200280042c120b036000059248540703400821100e400800900503a0f00944482001c0e0f80d0352021042c41d07904c20408007860400c0c3c08001e8540c21190740c050a10662180280c81c80c03046648040300e40d034442103448019107901c0354443c15243c001809414030389403040c0c50610050007422101e511003401c116586000030544000340050004120104020b085d1f2039039070354803500000560030216041614125480c0c20b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 234992086 1250 234990836 234990863
    0xe1e0112050c01080907090f02041e050f010c06061208041a03010305070608090f060a0609110712050309100905010902040e06060109030b1009090f051603110904030509030a0b04 78
    0x841000900c4826a409401810b04000306001119450b60241071010306109100c00401d0007a06c5014198024684500041c6c4492501d404040200f003050803103851182c2c5000180181e4561886031001220b00f802e101d448005d4619160000b0a403039840b400d0344100c1c4410050030092072200070300840751004202550080781c0350301204c280c030081c4801001940101c0d01000b009010300e03036407039214201d4026102c409400402c000e041c00821180c2a0045941d4841800801070b1031041e450440c0300c501109040100c283d0380d14204829844e00c200c280030002c400224030000802428079400b03001c0909008800442c600540640f5101c0b004034880d508200d003680d84880c00203003441c41841e0580d240341d0801d1950315802d074080c078041c01d248002c0d0f1002c4408580b20b4098040d40540038840d00110b05e0060242c1885410b1125507600304080b5601d02a0400108101c2e07140080d076288201c41c039651a40703a0345010f5a481c0700b003442075501406401106018810041d4281d4440d0703015400002075807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 234993336 1250 234992086 234992099
    0x18041b0518010302270a050a020702090a1b051c11041d060405010b1c051f030c0305060c0f1b16091406060406020d110c0d050318030a020f12070e1e01 66
    0x5c0400450200f90414503038000b65040046821158108803e11001480c1c0304c150380100e621080115101d000054580341c1421004a2a0000e803159030aa0718245040c258414144002010f18182c51807545489070103080d051400b41c401c0350b0041450240d0055000c0300c1c55a00f1940300c0040b94070610640c40c01c8000101c04107100215240c4040300c10102ca902c140311420f4200500018040343d6114241100002100f21080749200184d401088140050307031642c5842480e1503c0140101ca40c904148006c004c804901701c1070b5080504c80b001522100310303010020394580100d40c48280c6101800d0000080c02c01007a6010324004490003084100c60764656041c00501c2c800c52183c4001a0721050341801e4587c81400c1000d181d034448020342c1c4403414024009102d44080041c240c1c0c00e6000000c00c0003500c140140268075100058002d40640c600d5500040e07204102151003c3c010304410310b40d0926070105001c0c801c06400b10070040be125050400344041d03001d50482da204188030f000000424074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 234994586 1250 234993336 234993379
    0x9060f05070c0b130e0c04031506050f06030a09150515010801050109050609040e01060b190906020a030f050903060a0e0c040504020a05040923030a0e18041b0518010302 74
    0x21500002c2240c0e94602d0b102c4038003401ea124000740425084006000300d000e0714288001400340c01c054008940321411401d112480d20840e0110240d4107140000400040c0c590003885640030030103d40498a9a03503090316000078180d001c0d001401d0b8111203803205c0c2d081c401c0380d000074012014085c0c0211903144410040d03620800038024107003c40c100010411030791400400520340d0090180011441d0303201c0c60100c03401d40c0c400f0f0308016200c04000c202102400100c0032880c01c45140c0785014040139150241c00303522840316500c06420440c004295100c110b0140c002c5507a90b800103422501d05281c071045d504000d08100c20890058014084100c00902d058010240144d13002006010380313500d401d041100410b007906d0101c0da103201114144110000724941c007000c02c4601c2020b159101c001c0c01004204c0302207a4902445050a10f1709207030342e0150003c1032540b00b0f6110131098026900c00c032503210198030300d6100641c00a1168400442070310424840c5040324802d440c0c000042082c074681918 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 234995836 1250 234994586 234994597
    0x80c04051620070f0e160806120705040f020417070605120a021209060103020a06090501021c030b0a0f08010c050705190311100f0501060203030105060a0c03090e09060403021b0f041d06040309060f05 87
    0x141c1c2880129855282c010840d6a00444103c1107400ad1581ca901050075191504c408040c0c007903020038100324045d04909000c00003140840644030850404a019003d4055003c840000315100320006003612800c3d8101c410b14064400600e0741454004d0310203544440034041240510101d960000b04207002c0c0c0040c1d415100160045d1104840d02c2c840700e0080c4415281d60010191030344000d00542e140c407080750010b0720f41e241807011918100300e4000d0950b05c00d05061010414100001c201242002c10205110340450551614030b00032403e0840e502900e90700001c0c600d00454030501071700501c0c1e030300603100d0101c0c00e4018001c681c0e0703500050fa03c030b0009104403a0050420031004180b10300c00c0c0400c01c58140b10b8103100c41e0041d00c541e082d00901500301c40d100821380c8180d0a01c010305404004204440d032136401d10102141c140000f040495410b1401c00e03010707a40f980201e20403c1510850303081080c0081045401e14038050600520034111441000301144100540d081e14621071802c441d0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 234997086 1250 234995836 234995881
    0xc0e0109060809011b0206100602060417090a030b070e0a08010902031203091c050421031b03110f16081507081f0f080c04051620070f0e 60
    0x180040c50312000b51000364004100e45544d5603079010b6200b4200d500c40721076220007056802010743d85008203504442038580d4000e001076502100802c40081c031500c40084000301007100f03081d03d03641200042003184242d41c00091074144183c042001c003a52028031b146011408444050b0b490f50759242d41c9003210000c000c080d41580103a503d10394141d0100e40250b42118008040301c41600c0203a21508034080d188000500040c0006401c1103c07120801e8449000100c0f001c200c5450f0700696030150007200c4d240e02040d0701a440c40707541802c0c180641452202c401404d010303640e044104060761501d581002100c04401d074001000800e2a480000c2c20318420070417040c5401301c644601e502510001001030030406425038103e205c0204900d0000c20400802005400205d40703030904421038280100e1404550290f03240c401005a080c40d412000002c942c070b142002d0040584010030b0072162800c05071440fa0794070541d03000240c8128600c0c1c84070200c407107a91105145450b0000710b80c070841108000c41 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 234998336 1250 234997086 234997097
    0x13090905060c09120715030606020d0e1003140103140613080703030218031501180c020c060f0f0f03160c0209041212091b060c0503040e10170c01030c0e01 68
    0x6a0040c0b0140081c81940d1000b001400e4980118030032031714100d00c5420034043ca071100c0004a00c40391301409900040c0405002074010716411210050000848003802c522642801400c3d0004070b009034403d91000c2078030b0891070601e60316424004801c4561031000350071489940000740204081e282c0c1d8030070b407951100c911843c0c8020781d02c0880c00f0350461510094040c002d00380700c020640d0100072001e10100e01410f42c015540c904441070309100d1014400700030280c02e2038200b19110b5800318038007043d00d10071564551158002e0120030814000d51200b00051000001c00e000102100000b9610802c182c540c0e8801121410504840171810040000d4202d03014070003181c0010750300c043d044038504844c90000d418100021004050759041c10060b6203001c5041c150a0400d060385c40c254000d80154201140681c03100da403141c1c0e43c2e00c00c0c0d11441c081d01000d040882d080b031114403050401084482d2004d8401c851f4000078a480300a00505240480e01c1d20703068100542c040c001c00c0e44c5c00c40050319003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 234999586 1250 234998336 234998341
    0x30807140c07031101081303111c08040b0a110d0525020a0b06030a080306220203130b011e03120903240b09010e070518060310060206010902070b010b09041d031309090506 75
    0x42c0c0e105c0c2e241030409e040034010301c0180000f100d00400c02d12003c3c0d20540c0c0c1c8250710309003030030010445003000e440004500c0c04e0907102001d442c4c0200440e20301c00c04c04040050155101c3e840255000141043d0a00c01000c1c00390b40741055900198580e4018000c0410300740c02d031516010169100701004008007803c07428000180c2038503121641c071a02d00c0708002075400000b4110307110000c03a4001c803605001d1200140400d014041d1206445000d4000c60502402e5442a02d0005460520502c80204241d6000c81401c5016220f50170382002194400d1149200f8800303501e51024010303030303105011045454132086228a01d840c410a41c1201e9020111b0041611110002c4445900000004402101d41c0d140950715490b00c0005501ca08004400065820b041c00002402c151040c1d0003200d4035401803080780c005c1503024508504440000d00c001d0341e42c3c0303080d0000c5400790591045119001d21070300d40c40c01c03070084003000500c03001c50304581c4048144c1e00d800542048603a01e0750081d10071340c8500d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 235000836 1250 234999586 234999593
    0x2030c0f1612062c15010503191403040f0905150a140303070b010306050a0c14120709080f0705030f19060c0e03060106091d040b04030807140c070311010813 69
    0x40d1880d0745004440110740da484d080b628040b075848914104820b0103401c40c140039012024003480c042480741400d288519450400006e03a5480c2d00220784191540d070b501c18504000504401c614901000c006694036141d503010501c800490340c2c8a260300942c1400d0015404241a90f200034942c000144008126800c2c00454091003048410301d903007611003082400c1c0400e210400e060300942c03240002045074601141030ad8162810342035007900b030201089010102c001e030003040d201c1000000081104640d64034604645006682d807100c400c81c01070050074904800c02195a506850040e03045421400300a10205d41d101d90344190074541c0080c407030042d000658107402801c0010494540b0b81007070150240000d003026820f038032020126000345c4080082c001000418100d51144400f281c0c0c082c641600c52200340307400200300030704120401c000250414010a80d4800900f90b58030b0190701c6200102d21260364201c04d00013a18095402e01490006611482409200e00403000d05141074000b10768 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 235002086 1250 235000836 235000859
    0xb010c030f1107170c0102190803060109030605130318050307090e030c01021204030e0f0f0d02280614040f0b180616060506121f090209040302030c0f16 67
    0x1100404002e210410031650500410407207001d09030b4840741d18240c140140100c0e207409a04d119050641d0850030003428000c002c0e0b0041102550071440d500e940c0d80d5000c0c01280c040b0056040103080c0d07450b10040c00030840f5041d1808184038425100d2001040904400c01c40402581c07103044d600d83e21602c02070221000c00d0b044280c0002e50007040700c2c100264100b1090998002c8000103a411a8800401c010706611400300340e181581a40c03080707813600001011500380c403003200056000f003443c03903066001c54580ca020011a6004001c8080d00564240507000c08201d00307200b0302c00000d840803030081030350392043c084908a0760b5109401004520300004101560440030807120304d111500c0d0f8103100d546580c07004002c0c01200f0b00c868400e0510711f241882c1141d601414207801800700100c100c05c100d6000842d600d04020300c101010b0702c0301d40c211105001d4580c0100081d000281c00e400c0c03104043d0000003810900c0a104280d841d0f00004880c090742e10b9118050404814003289030410541c0c1650 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 235003336 1250 235002086 235002107
    0x30c030c0f130b060412260904021809010b0d0e240c040b1306032301030b180115081504030804030806011e1d06040f0b13050a09021c0b010c03 63
    0x51400f00b0600001030009100e82c2003944070154902496804c4410080600c11308038020700b07450214504542e01e030039a07500c2805500340560049500048507403810f148001c0c114070110006102d2605507841d251521300b41d0f0007880c0180462810b22035807296921000c5224551000c100e100440240c0d41445148440100581030b00c80d810700c20400412625001001442d43d00c59401242c5582c924080004086521403482008603072041c0303c0802c1c02000c1074000604494029204041c2c540f40c44142114211114132070a806601e050314400c00818102c1c1264112280c07a815103007244540041d80200e0301c000c40d0000d000a00700d0000400080c040c0620981056040c5807641000d0030100c0415403200300751103000042410381e03084110307203c00f6090320941e0400589845040c40e203070410040244005006040841102040240d5480b0344c4410040040078000c0c180001140d03580c900c1c400a502030082081c1e000311040205040b1400c42c0114101d080c410381d1f803206804043e8130112070701e038001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 235004586 1250 235003336 235003369
    0x50304200306040303020a090b0313110105091309151103010e070c0c03050609060109020f090103090f050111041d06010e100306261c020703021212040303030b030c030c0f 75
    0x421000303805031000c0080070300c100c0c842d440c0169a256524400380860800307030b21400c95040100b0411250352106d80c817154205078082010103940c910880140d56601a030750005822418001041c0d40c2090303281c1054400724000e400d0140d0781141008140c043e41c0205c003030341081180810040060303488807881039912102c2d0f45040f00c5420420754520903194440c0c1c0c0207a44550044051220310302c0240102c60040108000031450422500c4176580319009580b01c0354107266890f00b000741400341c2140c4804003154094000c00c8855150007075100d554009025040c3c04005c650b003d01da00d102e0b00c0031514043c1105848030810b07120014100528002c402040e1404c05480b6100020940d1000441128804103145071b80c528446421003285003485442c64440000015407502c07621540114400040e42c0e010389120989210545010b850041201703548694010009000014150705601c903c2c0465070850580c0c00b00d5105900301651a1a0122101d5020801400c0c6096914104240382c240101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 235005836 1250 235004586 235004633
    0x50d0c080906130509150306070c0507150302030711030a1202071a04060606110c091f08030c0a060c110d1206030b010803030601030605010c0f020d03120f0c0e030a03050304 76
    0x1419008204039401c0b0500f0a0807070450a08144118600149a980d1180585880c21004075490000035601da802803d94003d10410703246c000c080c0304060280038041c1046461040d0356039078030040240250300032680c800000e03207000d1103007189880110889071040b01903641c100384603d0440740100207501c07884040762043c450040c0d40e080f11888071600b5208030300030540059003514000c00504401c0c002ca0014800360041061020242d8450805d1038000c035150321040b15003028800c220080360030a820100d03040c840854014121800080d0181c4820310909041c044108005020740d01c00411545080ca1600009800303d081031040f1100d980d114859817004c2110f03596900c0752140c0310000e07000b07074a05c0e8000008010665801d40a008010202842d040306500142d49500b058601510b400070700c03400c844043d1005051043c0700711414260411070401c81c0107144c90310307100240b240d030400030013203403210962584514000c0b64211600b038164860350b19645e52540d0f4552182c4910201040c0c0d020b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 235007086 1250 235005836 235005847
    0xc1903030e040207290c120c031b19020c0105180d0c05040f0506040b0d080d0b030304150804050d03020406140c030705070b1209210904090b0a0f0f0504050d0c08 71
    0x11084e110744459130240303100c2150a40f40c100490640820002c6c040e0443c1a0100011500341c0c80b0f030303002c19900000000300b040c3c60f42ca0720b40d100440c000d2482400000e01da4080360a00940c1000d5600d0f0701b072200d00d50201c605107030107540152010300401c45940750107018218905214204042510f030494070650b600e010081c0c80344006802c0320321118059460503580c0d4100030290034140714031491801c0403641d03405080c4032580d0b00d025503c244130200c0051501c80c0c41148080c1c5080041c0d1b006400140c5001c40c004015000c0181090000c9a00351800d02c40d1184000350f0318003070300c06c0b101940c810780d40351402c814003410348a9950340030690100c80d501c0b0400400c03020071010711481d0080c6ca10a8001c030381ea00d81e03004011310380003409010510f00f034100c0e6005001d000a07500350304111541d201110364440441000240050200c42d0303000d40380a120104015070700c1c3e460340c0204064000c0c40000c1204544101d00041258401c84000b41954400b80342090250702840340c19407a144180303801483d10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 235008336 1250 235007086 235007093
    0x1006120b0a090311160e06180103030f0309051509010b040e06070507020111030a020a0318080a0f06181407060c1a090304090c0c1401051302060f04090504050607020c1903030e040207 80
    0x5442240301800c4010000d03824001d00003e0881d03587c02000450b119092040d10702150f001200040c413005040c800050345008542e80280c1020080070703003110680b614040380140d003602c082001c03102c074000e55203001c4041e03c2030324141c46540d841c0356403c0c0003890180d4440701c050700c050344295002d90502500d4074030913034503100400080000c0c8440790f010f0000428a0b18020b4038002c8800c00800c2d854551010070300408800150104010fa002000b050340400b10b070504200030700f40d5405201b12074401085480521584120300128030541c80100c0d0316043d51a43e0813600c3d2410316100520030040540d0f4081900c0c0001c0c0e125030003000c44403d492030255910302d103000701c9008207070300c00118050f2042c2109204d1407060b03022850350300700028061403410040c17a400c0ca02003190001c0c804c000104d03400703261408800030b490150129403c108050b0400d1b0420707035580c9074116170440045c80303810710480c1c49003090100803400c2115600c042c04881d003540d40946440318451a6a50010390034080071012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 235009586 1250 235008336 235008343
    0x90604031a06010c0302060f040c030b04050c0108100305150406060f0e190606021011041a09040f06180f0b0a03080c0d050c030901110c121006120b0a090311 69
    0x40d403080080480c2009071002081d101d4500038015030600c421100440007007500801c0140d07000b0f40005900c801a5900e140c1694064081d400c0174100e091110100010441c0020388060046400d880b400c8240d59000034074807414011f400000c040760070000303913952000e0056481c03540003407003080046101da0304c940031059240f00039400807501d40121010f000c0d5003008402842d211100c4881c0c144401070030400d02941d110300e00c10803004090b5070b50a810b4104400c00c1c080d28040d05a0050111181c04200e28241e1603402009429106030b00d001c40d4240f08052500c140c408070b80d640312403264042c401310803440007048000b944804040e203860f160b10250b41ea038040000a0b5208124458072034202072000307450444004914018040d0070007441d9031000002050f500b51680034a402000028045036050820101d520010b810100b010366000c2c00c64130200344455003034510700c0c0800645030b03200990340c1c10400400d0050900d82f004400f0558442d025044000c1c424024206422860ba401200d10b1a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 235010836 1250 235009586 235009589
    0x1e090409030f030b031506060c1e011e060e04021903060903050d0c0807080a110c0d02070e0906100911071a0117030712081803070515010905091b06090604 68
    0x24070000900d802d02034240c032882604d141c003a0000c00c00030001840201c1120b0300500820701c501c0010588400c07404081003003e25503248035a00e090900c0d5070406481c040c00d8500c1c000e180500000710441c800d00c445215078021603034003ca40c201207859540a1200088410b10043c014080509012020504900442036880d1295854170703030390f24400304044100c4a481e0700c07000401060009006000380d104034410740100c1540c00000b0008040b00c0082d800c1d00c01c181d0076901c02d000740d0f60b07800000d9401181090454030440302c00035059607001c0d00c05d43c03110001c0358207030107540e0201ca044c800c0c01100c2d88049141074141e4166407a20340c1e01d8a640b100701e41e04a580c0a58510ad42006021071604040d020001c405500000d50400e00660340e03030b0740503c0e031a040c07902c200400301001480400b072210344d1903801031140e002d0f079580c4d2040b03041c215120300c580c0180001960000c4000a00155213115240c459460030019281c1000c1d901040c3c03458440308641283d000506101009a650750b0302c00920 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 235012086 1250 235010836 235010843
    0x2130b030c090405090f07030201030209040905150106080108120a0c061806150614030609060f1201090606050f01051801091d19140a05040201140406050d050105151e090409 76
    0xa40b2510450104402e40b8001452407410783c0081200100700e110000d4040c040e02da09007030150300c440340c15000c03c0027814400d40251071440b0302e0342280d4a89101c44040c5051381d9665492150a0782c80d001496500c2c50200d0891406000812452444034412035103122490300c503040100c0c1600340d400410401440703c1000b590420783c0c07440003951400003000c0200c0280b0103824240c40100e0120151580ca000003804903001d0100d0384001030b02944e441c5d8030084407850052000300138442d5030200c103000308000c03401192134070714112003c20145403906103078121681c142e65141c0b502100407070070407940e200d513a02c2c9418060b4018010400600c555500800c8000000c807011007898111100c3c2c02022407800c8070744000346003840a500510700800d10550102c0718410101d0300c1d44552004840c03140301c002e100f000195003c00c0c003180c1540c0c0708004000b148007403002440303180d03242d20030440c40b01d40075802444508020800d0039000594002d0840002105141650802c5407101c003203420f9035a1410100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 235013336 1250 235012086 235012111
    0x90b04090213090b0d060207020303090303030f04060c1701050409030315080d09140d080304170a050306030c0907020601180e030c010204050a0b0f04060c1e030f12020c0c0402130b03 80
    0xb6101c080c1030510351070080c0341c842c40c24028004000c011030044007140380d000e040382e40c0000c0c841040d03443c100708170f5028030340103000c50380da074030f0281c0500c071500d001070b00c040303403100c0c1010001429644940c03804091400c12071500012039190500300801455055030480030700d6110300c02051001d1031408280c00500c0d8031409032018036094000242444819041100d40c008800c4100711252142007505007020350040c18290740b910b40d400c02c11803010000f01001559800020503041c400d0b0b00001460141c0750035411030781404400b60030040d07401c000711444001030707021b8401000440c00100e1051002c00c60b5510024004403480d040600750b074170512008078260f40029003007007542840c8001100402c240b28006060520aa20103022846540f0540c0300304484c0040000c24071007034454400d03e4000014181e000c00310145406410a00e8150341c0700d0110b02c6080c1d140c18051114000c584101104102801c08008001d08000081d040900031881c800c143c4c40010a0381401c800086005421071001c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 235014586 1250 235013336 235013347
    0x1b0603070201091b06030609061a090a0902160b130209040809120307060e0c03070609050103020d021c06090b06210c0c070314011803020c0f061c0203010311120a080307090b040902 79
    0xe410795050350303c100ca1942c50100c04000a0501032200302b10018000000c2d6a200d884d50300003051142d00350000c0305018400110f0144144d02e00d011034000901ca55507201c03696507800c4506c04d03e880248000794026282c0707000100010701520040101d1400100b000f000401c240481c5441c5801c941811100655144881085040c007000031481d1804105c0090403050305181008000070303283d11815042c581c0116440844c9200342d01921302d643da02058408034101c000f41c02c200a0714091140ca076846103407030141092410705108a03060301082e1510b854640d0800c40300165640c50042c400c9041603820310a0846101007440420011409407014045041c0d03069051800c465110070568400345c08241004002034011a21495039002101c03d4400407109101040e898400c103e440404404c0b4444103148076101503001d14181d034003551000d1940c1c500301c0e080c80b0700e14003010180303042a03102805034800940d541d070003103500400b2b6203800b0f412079603074084e02081034200c0d03080000210307004540c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 235015836 1250 235014586 235014599
    0xd05040c080d1d0d0302120304080412060902010f0207211109100e06030604240605060c071a030f0402060c0c0901091a0306101401030905030301060f111b0603070201091b 75
    0x5150024103c21604544500d40c1036402940e034074502592103200c03140200c005014040d200003a240100703041016006011041e10700fa00c010003c0300b004030b021507900d00602e00320030702c00140c61080c1c1d51010b614850501200b003032000e00d2588214112100ca034000c940119903190100b00b940034001e103090000010341070490b01b58140c000104054002e501003801c01012602d201c1016210103504e200b00003272016180c4803000a06010f8000070780207100021000901c2800288090481c0d9944141345100e020301d130358259051105030390000003515482e000c00c0241c0340400040580e1a1880d040300c580c00840400300740720f00704c00d03400440c01c203070741d5011200c4085050f00c65052028044010317004a250941e01c080460019002d082500c0c242d2105610710341e4041d40c4014401c1d82c220701166183c4d0b03517034900104034401032914440001c4114181c4959110001101d85060661014980f01548888140049074000600b4881159228507044010445c4401e11329000c0d000e035448882c0081c00c0c101d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 235017086 1250 235015836 235015877
    0xd11090319080a0f0c0506010b1c0b06040614040f0b040e01090c230904061403070b040e160e0409030305061009060c0b0709031a040c090204030203030d05040c080d 72
    0x7115030741c8507004070803400000340c4084110b410003903040c2003098160900003001c40c0d01d8001c0300c800900900c62400045040c00380740700a00032001c288007823594a12207020510341900d08034008544c00110138003040c46404d000700c400088809421740b5060600356114004d101c00101a840300c0b00d03102000805004d02d403508171580f800740c000302da0184840040303d50b004004054800040d581c451030000040d5800100c1011110808401001400f10b00d8581c1d9104106c50102408241310f0f2103448000500c01002005503401c880c4000c0380c00c5450381c0c9030140410340340140004030007000842010041c2c40e90f00c1d4803c20103c030f40260b400186500d0031600384000400304a80380020301400e003004100d420f0340401d1800300c444d444000007209440c0c00c4c3c01510300700103070340000700074241401e840480c0d65511000c141c4650702984040741400c0c1d40350340071b0049200ea4040070350160010441c80303201d850290400d80c1c0040c07260540751412981d8201150070076901c00300340000581e400060101c00b00c506d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 235018336 1250 235017086 235017103
    0x30412111b0103053108090d03090503010506030a03020d050c011e020904060e012610020403030206041e0305090f130606020d0809030a0e19030b01030b0a05100e0c0d020d110903 78
    0x40d071038840100c003000e8a07010141c0c0380c0e4802c69134100c805c030015042050400c1501c1c5d14a6000d401800b9040d450315001c1c11a00700350080a0180d071814002404074a13001036801005601500600404040d640c800c44041c0c2c0b02259424032507480d544600c0e00b448510000f074401640101c4010784400024041000b41c0b0699400610f9000b0260014003142ca4040040c08580802307603040219400041e00745401d01c0b01c40611580c0040c400f05000003130640100c0c410348210f01c81c40365101032903042c000d509500b030085100540050002d200f404680d04114650880307410b4024468180b0491094444050360f089422403030041c0c00002d0004041500070840e1608111000c003c0c40c01c00060480080100c801742d03505603c07803400d401d079010622224129140242d900303d8032052680d80c40c0c4c241980041015641c1d00c05540c42c0c400000c0c0d200c94540c5049042d00d049028941245d00d40020b030400035080f640f2400182a4200400000b0312302c82c1c881c8145036180159800c0d00e0300e180ca400c150800020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 235019586 1250 235018336 235018351
    0x7180303051b06041e0303090c1e06050c0a02220501151112030a020a3b06121602070e100f060504120807230a05010b0114030412111b010305 62
    0x10306000003d81d09940007502c0314a0170302d04d601c1c840302c903040071070103007207109030240c00100001000f040d0480c121122903035081c1400c010504141d910101140c8074422040501c003250403074460200145030440703001c03d01080704000c1c10102440f081d4203400700d070801e80c044d00f044940d9515a00b0300769008001c0c04400e008040181003050420a8440800e01c0004c02d1089541d600144100f100c2c2e00412514400c0c9099614510400c0e6508108411421856245040601c4100340405c3e1500c1c01c00704035aa480400105442c094803500340e0400fa100a1070030690a41c000c800c00401c44445491002d84200003618080740110319180e00c1110311016a0061010850100000d103d00302e61b90503002c542e1a8000c50380c6a4800c4c10741007100c16414100c101e24101503c104182840546c0024000641805000208084140d6000664070341c01d10340c58001540e072091000801003400d16404111002813400c0c413122200e000607526041c10071400300c044044284041003002944e0610510790f0250780c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 235020836 1250 235019586 235019593
    0x50702040e30031503070317070b060a0506070b0a021b0705121219120203010b03060f04020a0e01030f0207020910060f2c0f040204140906030a0f0b07180303051b 71
    0x9035035007200070611004161480130305070324001d000540c42c20400701340107640110803c1907443c00d0418015040d402440c00340d4042e080c0c0008910180b608a034200700f107c0000b0012850418507555440328040c0c01400204400d80c20b200c40348050b108040b600b241c201c0110044c02c809824601001944601800001c50940c401d919070040d1130000011190401128802c040c11a20003800807a5034103e070030010716841e800032000017000220b44001d140a001e0032150007081002240c2404201d000c0d0320708030780003c1e02c1424803e1107940a40d20104140c800002c000d8504012600401c0707942c582070f00c0d00304140041c0d110030060b4580c4145c04010300b150310710380401074030020a00c224110709141306001c41403110070440c41e044d03624894940c0003540094015511642c3e55003088507030302c1600c80e9513030041560400045a902d408500400f40c50307440117100310202641d841c2c2442c1c941d40140003c060040c030301d07049141011201500c0307004501c00c4d0358040e6500c3c080030010b60504140b0010310380590 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 235022086 1250 235020836 235020913
    0x21030c15061802030609041403160b090d02010b0102030d18050a0c170601030f02010e01170108100c0203070213050414010504050a1e0b0f090106050a08031b0a03080c0307050702040e 80
    0x103491b07810007500290041203071011240703a60066404c1d4491060340c58200104a0000c1c010070100305141413140882000395405149503034401d9003a510b2042e041401078004220441001400340e00401e08002880310003404501c05a81c0c2c0c525102594400303494200c143c180400aa010303d00040000c074516402818255165680d01c0d445103910000081c1032090010705511964418120b1003050075800c40001c1441d40d540008944800c070800b1005251030801401003001da000204036054154050103490380e440b5a03240d05401400e000c2c0046807141001c40c15200d005c41c09000320f034040c0d4041c1c0c001c1d00d0440b40702d242c404d4110004d00d034000c1ca8054804402008601c4a0030f805a0107800f1903a00000d0360303150003295004100301c1d0011640050b40c1d4034080350641002000c0c000090b5102c044e07030f1311000d840d24005d6440444d80300050002c0c01c10000111006100b0000d180c201142d41013060412420b940054152903240c0322003520341c0d000c40382006c4804144100390442c0c00c446840200c295 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 235023336 1250 235022086 235022089
    0x301050c1303060b15070309050f04020c030405150708070c0603180f1103100608031b030309030d09020f3f03121e0f0403020709020421030c150618020306 68
    0x1d008a10020301810350301c08412201c3d803225071180a113900391040c2d40b40c1d03910440c500a003070005079014813401034410203100b28080c2068421110580241d00003181031900d40010048001c40178004030040410074000500090340110203042500d00c035040100005060070002400c403840d440e401d0322300c0584100c3d90b102180390710034010b4040ea005985000c0c208080404289803240080781d030317540a481d290000a0210f00031000e0030b82500d56021155402018440242e500d00003518115515081000b40c401590001e500103807a052000c0c04c0c0c804803945890008015000d0703840a1034000f0a0034501009414600810070821281c1c40a104180c4000015241d0b0f03c0c000c81c032007400717103103002008100f031640d002c1c1d0703d03027507007214000382092614120360b10100e1090150307030850244c410a140070070780043c0350082c0c4052303402d030604a00c0119120292a0f02200c0050310030380030b01c00c0020101d408240001d03110000c400c84240081102450400d09000c10150300041c0031090b8030500c140140d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 235024586 1250 235023336 235023367
    0x80601020d0503041e1b0603050a0510060819051303030b120c04020c0f0a080702090a09020609150c01050703020c16031a0717040c0e090d022a1e0301050c 68
    0x42c3c1c10003882c0c0c40c05c096050780c480c8100d00580340a0141440c000720150050400103042003995200c1ea0184125220343c40c101c815900c0548000701500c006040501806208101595000c2c00340d603c10721050050f001000d0032500c1c262034814021010001c14070500d90507000e901f17010a01900c40005a841442c05075464804044e59144100e400040c08400030800b04003020081c468a004c0c5c0b49100c616140c01512948080c1d412402480038000103610100c540c411a81c4454000d001c9501c1c00111100308207690300340810700c400070304061282c503070070075400d00c5a240304034410388005994455805403280f40440c050200d01100300d1180b008c0c400158051900199104d0b28411810b00c1d17180c40e40b042d1200d05200300030013041c0c0d054100b0042407220342c1d007010341160017031040742c2c00ba42c84000d44d40c1e440300200d41105000d40d002160b00c6400007840b5114405807039400d917a2008000380750700000c00c3d20112642c40f0504003420525681e1500e002c1c42074a03040600040710600e800d03035107089040c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 235025836 1250 235024586 235024591
    0x1206041205090d0206030903070201230301060c08120702070905150a05040f091203480207050a0803040f0803090102120a020a06180b06040507051813020c030307080601020d0503 78
    0x200a004210607150f521082607202c2615402801c4a440380f810031525035580d00507031801e85c0001d0300d25800140f04036500c0b04481c104980c4846052440e030a224040e1540010f860049410748001c2060462050580040601030702c01c81d80540206843e190008081c0c8001814650810038440b40030f90280d550f20a040c4110740d0281c40101d1007001c000e195100030200220050b003901e492280350802c0d558075501c0030301d4441e02407840c07044d0405052040b200009042c40952000c0906419050010314480b485c03201d0b0421910440710300c03e445001160015819910028143e4400f05040c8955032441c604640a07103c000c0c021400c0c5801c1c140002e64980707404250786c11808000581029940c42032090540701c580001c42072110700421078982c640c00080360401d86d071418881c4045019403425008860242c2501d9030344038280b2000024164401315002521503000d204110020841c03103a90001d8424108030740b0245450745824000607145882c02172025045400410480254503005030a03030340c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 235027086 1250 235025836 235025873
    0x114010804061d0d0311090618041b03020a020708010b030c24031006080a0b06030c09010309050a290106091a09040e010e1b1305090a08120105120604 66
    0x2030854075281840e000400701c249401900909140002e92240c6002440020004941d070f010070a04040c0f81c4540c039140262604c9542c440c5041100080300a010001864a180010300005d600c003414407014103600f2161000c0c2c80407a401040b41c0c00c0c91501030103090000d00c50407009210041d60303580080d80351038542c0c020390320070061820012003007480400c080080100309540541c1d00d0074100780c0041242a68410000080d412800213a84030340b190284c5404d040d0040c1402d41035440d000b521840d01e4110454150416a542c002580820030801400d4141400380c01041019051443c036113000c1140c504802011805490040206550098151040701c0000300c6d404108100c0480341d91452041c06a01c079840340c2464055180d8010640c4003200f9020b4140841e640441400000e03d43d0700030303030b990640d8054403407610916045010381001e03501481341b4054030304d0040b403030707583e90541e411a68980d090403598100501c617604000399618005902d0f1001403c10f40741503a600c21501a9949619 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 235028336 1250 235027086 235027097
    0xb04060e030c1501180c02070501052101030b01140d1502130312020601150320030618040c0503060f15010e03070506070303020c060a06181a0a0e1806011401 69
    0x200c40d1906006a03461801414181c800c8004000c4822000400a0140ca000715501d092201610001d520a8982c0844036801410b1120b02e003c00550301600b00181d0102ca4200c41001d814030b4034030380711b031440c0a0f622641d105003140d410105041600c0c99500c402c1401030108404160200d1040c55005a10312203409000d07903602c00b8600a1410160b8682c03005061f40c11a04810462036000b08116059501181d80c2d0540001c03201c03402c03401e4501c45809a04070101840d0b0104a50107500000c1da88007130007401c001900b41610222440001c8119426207002d103201703505001514050022507042401442d0010050034803c038440780d802404c2600d10705001030f01d940c0c0780c2a51414002400182001000140c96604600340a0083d500080149240d0f00800000030541c079994800d4000361002020700b002c82041c0ca903001c20080c0f0a814008201d41803800501c005a0794100c0401c000d00502c0c201501c0341c2c18481103040880503e40ca1051680d0003010051064102c0310303003030108008003441c16 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 235029586 1250 235028336 235028351
    0x51903050d0e01020d0504030f1101053306040f150e01091511030c070e060d0305120c040503190218060f040f02090402190816080a1a0a0305010b1504030b0406 70
    0xb01d4024030078040074441e964203103030405c4240340c0c1003c414100150719440300d101c08240407080074222001196150030b56001c2d181a14400c2d903280044075449a4002c2090303030104046400520b0642050784001c200380c4003408180040c5038841c801100d0502d541c240f0256140420001900c400b01c64041c00c200f02807848100684203126055855131000c1c00750980380da0b4240c0a00b035540380c011a00400d401201e0550100b01c2c02d0402e03290100c50960141c0e05c0d41c2c140400400b0400c17003240013510b001031b11a01480042001e035130900581c2450901d6a00d124841e41c1d0600c180046605038120680c9a240c1c0d070b504000142c4c0380e03041014003c502c100d50000301c004007402804002e01554207900d40003880071071800203410741c00d4801c040350b00b03080c0c80b0f418240d41c591402c1000c00122000704000a20000c0104150f942e242e00b08000c10f1243c0404c48032111074140201e04856055482a90982c1d1503034000400d03030400801341042c1802644a0311700c0c0c0303400c45d10746080400c005031000308415540c03c40c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 235030836 1250 235029586 235029611
    0x5040b0c1903091a03060306060f030f0613030f050304020307051003090c0e0105010314070512040c0308130e0106030204080c060702040b0306040807021905011e090803040909051903050d 82
    0x40d1140030400c1051844540d14280140070411501a86101e8104078181000c00c084c02d2080e40c2c0300d0795004004081e513607620018450f09aa80c045a941c051258444021812600340300c014443d055074908600c04482609001745201d268520103c01d00c60104244030160f140881c61105484c070036103402c1504001c0d0384089004100c104809001c0074003100020812000c20440141210000d03681808106200d941c008620581a61440041441002191f41509001a8484e80f05001d23800401c00617550391600001030740400807181c210701c20503005001d400d540201c407501410b402d103000c42c2071a060020b403035610041106203078400c28010460038119583c907041a081c00b0005425254030781050701c1e01d85200e812442c402c900c10940038003811000710702440d03480304540e01652518912010307503c054102c120115001001c00c50311a20108015404100600c000c1115131320009000740356040003824461010040d20b80d10200d02ca042001ca0790000641e401808003020004090590b40b6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 235032086 1250 235030836 235030843
    0x190f0f08070e030f0c04060e0112110301020d1a0a0e01080a0602032a030f0601031a0d110907022503081b030c060103060605010e030a05030430210f05040b0c 69
    0x4034401e80c14820003113140c00100012482c1644648150b0301032040307540f41c002c07032407103d402400707000b1461008081d0740c0042000d1441c2440c0d00c020141c0010718004c401c0c08207500755690f01200070001034510a81c03001900b44090500000d101c41745d40d10025504001090b42c0322031540802400240d00440410124080c1081d01030101030400c4d0710302c0c03401030070b001d0b10103140d002120017582003c0702c080003820550090090fa03081c0410038500b0400c450103401008502c054000c4252604440c02da0307010039540f034100e00315004800c03e40041a450f030706030076481d099141a40740034003120259001000050411001e0700c40007034415010314580b081c4141101e00c0c6014061000003240714220000040c404164420070a1380e00a90707501ca0365402103818140d481442c000000c150b075100300801c000d0b0f200c14415503000400142c60392801a00c51800200144030342006c26241c0c40703818880d0064400310944a1805c0c2c591600b00080a5160300202601601440c42182d100000004210b60a08410f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 235033336 1250 235032086 235032107
    0x12a0c05060d05041401021305040c0c06111c020f0406030e0f0a031d01020c0a030605060609060705010507080f041e02060409020d0b030709020405031b0301140903190f0f0807 77
    0x50442a112460381c800c0c18090070060304d0903240220030780740d200f60110040c021a41110154540520418504403e0100408408500d1400c00a00c80003030303800070382c00340200705550006018860322107900c0300c0000303d4410110300d1100d50a1041140b400b003c0100e805413800c50341281800244d1501046080e41017803040c801d55081402814004070416400c508c0c00c2071454101c20000c40000d00d9140166a031303501b56040280c0c4030308818010070002d182a08400d90008003d030000c1d0800024001048440e000000b04640300d135190b904100190790f101e011940e11003410402006c481c20251141d0024517070f403510008480701c550740b22000b03544958007124005d041c00d00d01199590300d00d900000003810707140d161620902540d000020940d0b61703070081d58207890006001d012940e8180d0648601500700700001b9405541b24280761080440b60080648200301c1c00380a1030352642c401128120300b455801003e02404070354014020360540c000203108400c00306081041d03c0d500c078104103035403c030042c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 235034586 1250 235033336 235033339
    0xc02070e04060204030512070f1106161104050c0f122203020606120127020a030602070c06030e01060e0703021606050709031a0108060402060a1101060f030b06012a0c05 74
    0x100c0d000d0004100701070307000344100ca015005540c0386000038403141c44240f0820301c0c06032803281164448c0d40404d4607200e086466480c02032a262802a140341c0f001c0c260710100e00c00345d42982800c402cde101c0d00d080178046d469010b6480b40515180c0050a00c4c0c0e180b0030f0140c00790007410401d030500040c8801c0c0707040d41a03a908140c000254080c200f01c500d0000d545442c1159843c0c0240f078443e46204d18074905006000c811102282d1590400030010090800c511440c242603a20a551850000c0810128401824040c2c025144080b2190805901409444201c0e610100f00e81c941041004000103580803540c000c0e0700b5150150341c803240d0060407094002c00801c00b030045890402400304490b0000c0030b040882e40710794400c2d0030440006030715403403083e805d03c1051140d81088000030014680340004200f214200e0901503110310f4601c1c1e9060869506402c100f10b80110880c0a1042c007911500059019009280c03035148a65921141880182c00c1a24442894090480ca6040011907150500034010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 235035836 1250 235034586 235034609
    0x20c0405010b0301061b03020c0409080d02040f0f0b040f0303080601052208100e0a0803060d14100f05040507060806060d09150501060f080601080a0e01020310061812060c0207 77
    0x712509501d030b26a1003885504040303a1817541d4461007202c91240441d50940540103491503001d01c43c02d200240404040413158803500b00040007555400b4070103003029113110343c03100d24040c0c181203120000020b40c1d00541420a000e0104009030008541c1e62070540f030345448c0200304c82c0c840c040180c94901a21f400740548500014a4002d60200b10310f014084034422000c840c0022107111000007211800c0c114030400d504001d48480c0030401e90b400440d005440900075006d41c514903200c0302c00d040241c42c0700803010b42110003d000100740b02e00802c1c9035141070042c104101d0801d41c0d201e0b070f9151040e1041c41c0600008100260041d59403600b40e80d6815104c0409004400c40c0e45001c030301c0c2040709501800e00501d8180003064541c441e9403101d28040064544131115203a03c8019203120600400c4d181074a603d60b1400c80c980c2074280051401190302c4203540180350b0414001a0031141c0b100741c1c8426a0290300002c01140c040045518045900480000f4100118503403c0742003148a80180100c0c48 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 235037086 1250 235035836 235035839
    0x10440c2104080d0b010c05030711091f170f150f01061e140f0708070215160305030a06120302031215030318030c06040f14030303060607031d1003060303020610030203070b0307020c040501 82
    0x310ac00040f510040888100300302d651102800c03080000c403140307001f1403101202014400e84c044140c2a540c5190303180c088820f20b0350002c0516260480b82e89c104844c01c00060280310300d4503a0b903840c850141500f410080c0c0c032500500480c4283c40110f03c205030401c03103050350408000762548111001c0c00c0300b07890029552038003814030300d0440d80103c80417805500412800300c0c0b4442c508056603c503028040700c0c120400e20310b41b0115007942014100710881c0b030340c85400003400c4110180341090b45200303401554840200038038418216000900c91074000030300c440c242e261594007100711504001c82440c240300172421080403074030381002c0c080c8180e0450000600030076443c8086410004035443d10480038100309452080c551640070586006d60401003c0c8001000680581594203140c0d20080303015411004041c009161ba200f0240c143c80403a55580080c400e240e03050050030350003044040090741706440d60b804241c2d203c4007480340c81900d44e4040041204584248929281000001c2c018800765 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 235038336 1250 235037086 235037093
    0x1030c1205161d010203040510110109030305061305010522020403080a0329030303040b090c030d081e010f0302060f0d0504060b10440c2104080d0b010c050307 70
    0x1000d2014200b001c01e004903c0240e00340030385202c4001d41401a405142020b03e05001d200c101c4c0044070710741041c85075201510710840c0c0309108040e003450007036a0110310b03800c02909100107516504d80c05000d09040400500040c1c0705c0d20040c1203004505959004960302c8544490700900880c0c00c020414800015000d104036490f402c68020103100240c03501c94241980650a180380fa071800d40d903010b400c2400020040f9258000180c0e10040490503031b510b09000d01d0010741050700c00c8140501284d2a901842360501140b00410000a003d510f1103e81d5414282c3c0a20358840a1100070312070100004e81010300c20007501a1642032561410a00944c2810301d0020003403c004400e01d409034a08400301030300c040c4104804450705400c1901200540d0042d15021804018150103440d0041c0d020f11000e8000c003020540ca10031b00c81e007842c89859034114024424881c4551039003008100310f860601c400b04046070100c4901d01d0b511840003078101e10450069640c018a17900c050100d01002c940314051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 235039586 1250 235038336 235038361
    0xe06090723160c0503032b0212070210110403020f04020c0a0c0f0303170106050306102102070c0b0309100203040c050a0603200a0f05090d02040908041415030601030c1205 75
    0x103091203210f0f014440c946400c20305a50303024103010701d42511038262a843c441a426403200c80c01c509001005894804910f41c84820600203452a1005901032035440d100c101c05d5100c0c00c0a0800348002952509155400182d0b1603840841e4041c4140d0340082c03000c034103a40811222030b100f42e00c49000c07102155142041102d29102c0d00c8180c0100700000d1180c802415240c1800741607641580b135150940e110350080c4003030603540740007507002d2100400351802c800c82e0300e0010040040c03d00e140941d44e0b41491801e41040c03c055804040186018024094111004120400071903c0e8060050303c9a035982000181d5805c02c1e88401c0d08010002004100c03140c2c55002441c1c0707071500e11030014401510f424410240c0c8203c000354000190940c2180c01114804d900401004200501102404455800090403140300740c004075101d050005d800c024044211140a6001008640120710f11400303001d1804030348401042c2a04150796484a1406075010f20f00c500d018020701c5408010368540048071030700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 235040836 1250 235039586 235039627
    0x414090a09050a03020f06060102190b07020a0b01080c0f040605060f0d0f0f0207030314010503030306010309080909070e091302090604050406091403090a0f050303070305090a03080d050406060e06090723 89
    0x1580210f1f03000030704a500000d00300415041c0031039003118030f1402c2d80b00c0201009018125000714014006060013080741146620b01074900d000c0507061044601c0201f20b04003000d003002602450800300104015520f09007a41d018000c00303800e980d5144d140e40e0250005111440d08040c1302d07881c01040058a00b480d50103020818483c2e1000c010744290b5989403400040300b40309680d4180d10420004020354425000648418811505d090a082408000401c6c911086400341c0c000f170105d415a0146161045149801007a04c10304440034004a070042510000f005141600403038a8802050401c4042e50020000f603822042c44403248030507558241c3c680d40702e8521a84501c28501000c10014030016a201c1101c0004005600e003580f56035090b903c98100d083c43c1d6601065150700007002c10188001000c010041200c00101450603107821801c84403d60810500d840c4440200803032511402c0280d42c0201007801c0420b212800c2103030405111040d01010f42c65860701084211085010855120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 235042086 1250 235040836 235040863
    0xf0304271401090b030f0c0103151212171012141902031204121209050307030b09010c080402180a060512030318060405030d11040b030c0a090b0414090a09050a0302 72
    0x4203000444041655a0300400c00f0350740c15800007000799012350b0080e440b10304c40c02c04a12025406541d110780d860b10002680c03100380d51034454002c89500d200e50101c0d1940000051140c0381c94107040158801d42c5401c818024800713100711080c956400d011500304542c82400112003110001542641e600300c8060107041f0880c040e00c1041050300c401d081550a5030240c6c0e407102c03c1011106015154140c100140c0e083c12401e00054000201c0c01e41c4041c0a460003031406521001a03500701089040d00f10b502d0403494034100b018207010310006a03a8020594a043d080010350b44072034070750840b10401480c00b41d008552040c420740c05400c003c070001c0301851103020070f54404034480700c64030031007038072010102c40042c49a0010441002c0024181c0d1080d100310b5502c1003054280307a2980091146a4415a9074200c11840407036901d280c1a480215200a41281c40b0a9030070285000307040c10b0030809044207588240340100015206016540c4414441504003084034a200081e040c00780d1690501882c41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 235043336 1250 235042086 235042091
    0x1416080c030d03020313031413120510050c04030b0414070602070608010506041d090a020315010302190b04090b13020a080105131806020309030c060708070f020f030427140109 77
    0x100c100314003a2081d2072044c041d407500300100d0b03119560101e850440205441c0c08c901c809000360000b0211401140d801390510541900e840d4919050a0b0702d80390003007151580503070802c0100009486c2d01c01c15030701103036031048001d509600c5601c0d042d6030500c01920314448030720882c4c400040b150381c00101e03682150703070700d0302e54900503603c0e00107000d103622580c05012081d0721b514100e14448840785200039802151101070b0360a003181c950000f410b1611522500008402c07010044c030552500c004982441824810000f44071441e0034042d0302c2e81e02651182c0502d060b82c8611070401030300c4002940d00115111141103590b01356015016103c1c440a00a5a00403c616102d9100b800300d9807194202c1c40c1c2072021201280c030200d40d82c10010754402006081540401d02115089800c2002201e028a0311078403051950300d0294001130400c007100c150101198000d83c24450041000b00440701070700c070f0000c0084450b6003041b0120b030540701003c1000c0300b1540b41204280610301c10701c41c498103941d00c10105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 235044586 1250 235043336 235043353
    0x1b031e0806010f0201060807060507171c0b0303070b0402130e150a06150c080d090b0f0708060402090904020d0c030b07110709140601030b010e0d0302031b030a09031416080c03 77
    0x803400c0b66520b000350b070700f6a8001235061017468000e8001e084040d01c21042c0c0900312004000c40d0000b5005040640541455202c010030302d40014010ba49070002d06400071401c0c0045612100300f00741001e0700c06402103040c2900c00e6009481c5801c040910301190701100c803100c401005240c9641030855454000e10b182c0500400c55603584000c0020b1600f05586d080c0c101880c903101c0003c83d60103021018071081d542c4010307000103101e01550b180f14008581101c10070f0300c1c0c01800034003d00001401c0d94811407040210780c0d00b5039a40f603190303900300340c054858002d0400f03289800b50f980c0700160409401d00000c40c04000b9080d50100200100d80d18140560314095560034440d0f0507546540841e02e620904072001071030552003a800880017045c14034007050f040140d1000302d82c00c48071030030b810740042c0c000045440750700d034041448280380d40c03240000f0b600c0c1c1051240b00a198420340c0c0030050042e510004035011070101003014200803041070307403080100d6607a8a941c41c2c2c0c1da400700d52164060b0003405030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 235045836 1250 235044586 235044617
    0xd0b0402030d0e06030a1505090103110f1914180c03010617071d1504080c0a0f05031203040602071a0106120c020c0f210102070b090c011b031e080601 66
    0x408942d100044c1400b81141c032500c403290058403031a820700307090900c000b00000341c503980c2c40080b500030341c080e00c2c50000038092581806808005d030f4003c00e0080d660241c0c510000182c51040100310b803003550401e99aa81200005034240d152403e15400c9042c04071b05100c01b84458500031412182c0fa038560000c041ca4410000c4010807045034036001080e002000c0030080380c281d020604140c08002d2000c0007a80c2c00c100c440c21103410603000042e0a5004c07420138200d60a09103c510050581d9031001745031603141100090343d41440c006151456079002c40030404210071501500c80050340091303050100300341c8010548851001340306d104009888003241203001680c52041e501a130b402503015100e101c43c100c0500099400780750301960014a42032604480c00740c0d502d09111505980c00004d40d8a41580c02e01003085200601428a6600400c024006580e040110355181490380d60807000b1743e02d00c5040a90f00308122844011480c1040c101200321550f006003a140714510036251190400c9070060f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 235047086 1250 235045836 235045847
    0x111030d0c09051f172815050607110409080d090f020a060e010914030c150307200601060f110105070c0318030b19150f08120a020a0b060307050d0b0402030d 69
    0x140000101300800b03040720400714071045c5d955200a10707408600002c4411440200314000000103038107074607a66121006114600003283c1c0080008036500e50a089440d203c868240041c0000d2900c90b0b980e410b204d404210b40c090130348161000c0f2060400c4620200c0c1000040303c040c0f00000c078030459107404081507a5016081440400c071040c1d40d4440b8403030801c4054072260702e8404242e0b80c50302c07860006e180d160380c500c090740403081c1d1a102c40c02d0300c0381000c00e409403a640414982510011700700744030454444001500c1e504507000307850301c000d540303a8603801503c64040c00c001d0001d0070350034001088a0f40350000c1c40c1c0d502d010310a59455542c8001c48a4101140d1024007004041036024004140703105501a10003541c810207000014000c6140d0680027005031540e400160010001102001030790b8040c001d6440f0b182084441502d88070552100a45580811000810840d175480228655441c01c1042502038280a054564400c083c3d0404d00b80304141146c0891083c45124202400c147c13250 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 235048336 1250 235047086 235047139
    0x510020a0618031b021203070501020d0b09060306550203090c01051c0203100315050411010c030e0603010b0d060f0602190303090b0c03090f0f03090111030d0c0905 72
    0x10b565500c0e81424154442c4d01c0070718030040c2079a004d400b8800d42c0301d6000040c402041c2070f512800005a49021690300d540c180e51240b200c07284141071100070051241c03804180b85a01807603c083c4500e00702202d40c101d03c03081c1000300148912420070281555404c1c1892500e07041e101118605904000440800f18103a2004840d200c01c2504101102601135000f60054910f1440341c0b250201040100c1600008a800c22111107400818030b020400038403403c0803200707140003c402c0042c006403503d51a070040001c02c4000c83c0f81046202c09030703207052510132203180c1350700030303004110f25582d581d1072110751480d4000041d40c1c0b844516107140081c5e8090072042c41000c0f10680e030003601700c840110303140f125507030b20080c8190141520b807242d0400044032040c03041e1140800003440fa490b0300300500070b1031900340c2205850409a003c0b40c0c11000c005400010360300075440034078112510b0700b000145941103000d0503060020142c20000704600203a048801d403001e0300d0b4159178840710095204d1001a100040c0f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 235049586 1250 235048336 235048343
    0x19060f0b0d08041509120b0f0903030702150c0d05010f090e0a020310050c070501050103050616030b010206011509031e02101d04180f03020c120c010e090405070510020a0618 76
    0x401c010440301400c1d0480c0e04d910f4105092000b01e25964841ea00c0440b41003003000c458102032001084803c3d000c801c03c1c0c41e000108540158114070781101c000e0740c0e5180758825101901150000644081c940f0000c0380c00c8040c0c1038000380301d01c0d6510310302c40523181300074096140d00300d080408400c20444001450347c95160014018081c0944480d403030001044041c10400d02c14070100328080108000f40650f5000f540300d100148030798541510510700050700407141c001058148210610540e0b40080d442c1d0648618072850f020280d141002503510001a40c0002c114840300140d00c00e40302e0a4685c2c409030b0900032f4518032625652082d0071108080c00d8003044c4e0030710501021000480c00c0a50004040c0c80c0d0054810804040c262607200c400700d480082100181d01604203c200c0b030030624a210701001c220001013034074010490004e03205030b00030301040e4040c500ba84005410f0040030000301d402000b011300100c000402c07584000b0b44400d8003040507900390703007401400f807841d002180301500740540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 235050836 1250 235049586 235049603
    0xb0607080409020a0302091012060506040b0703030b1215040525060507050102160b0406060e060109050d06150305030a091d0402010302070f020a0914010812030403050c19060f0b0d 79
    0x200300d6402c00a4011071111000c0680c28007500301c0c02c0c0c403500404907040c1c0341a1100200c03000c0003040c1d281034841581202e40100b500b40800c222922001069844e8103030305007030118000c420310004c1004004040400f1015214075034031001211141034a240c003c60180c8140d17aa145c00700600c40d81c50428101c0d0010140401c4107041050f1882072000d810b042d8030840000d4a060b4006000c1108000401f5081d20003030340c000d080c40100a110b10070f08005244207c042d511610300070002030b26903240303885014095521542190208800c6038407900d01c45214201c03004d52107449080c616507941002800350301180721000c010440421164442d40807608051103c2040da5032071b80110b000e034010400440381e080c3c4242107100181d4480e00400041c2c03800c07078000101e010b0f60980d8024843c00680c071510550300089041e1400300c0f010350440e03501076014108595a03401403030601d440d11340d00c409800f010050804043c42040a182c200c0801b80e408000c050180310100f00070411490001e1000405454 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 235052086 1250 235050836 235050839
    0x103050f090309090405120706020a2012070305040b040b0705101a060708072103060b070b130512030c180306060a0501120b0406080d020609060c04031b03120809010b06070804 77
    0xd0a6155681d0092082e415101c4218410b91f1181d00e80e00b04900840d0000e80100720304240070ba00442005091441740001c01d920741c54903001c43d0315082940b00c06a88034500046c80300c01c0c076001d84110781c020000240e1555446644901c00d0000d9003207450103c5141c01001d420240002c0c2d58056864189510041e84500e000588100922a0b01a1400301c418000c02c0c401e103030104200c1c1c60250050048118204444441404020200d4403680c1100e40d0b0031009000b1140840c050801c6207a0007811240804542511030078180c1c0342c5960b4113a42004007400004003c3d00d4110030000e00615846d400250708030000786070806460f07803411101e564004030344000800003980b195031700c80d16400302081c000803145400b4000c1000e94415410601d9070b54444402c0c0c14415070304215a55000d04040040c0107642441e0300540030910481c400580081110032800b40681c3c04d21113544011540200085400c0c0511400607020f800202c03200c440da9481c0146058a0342055000c607185158400c01d07075440d05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 235053336 1250 235052086 235052089
    0x306140c03100605090111030a0804050712051009050705091311060c151f080f1006180b0a09050a05040c060e030a030309050c0a0f09110a0914011404090b0103050f090309 75
    0x150003017000c00741080200b2400d01040c00c414002040102d035503544101080ca400e060083c6082c59691101c00e407074121f04140400316a002c190790500d030444000119a030401401d1562504d05160082a4890301101c18410181c5481100d10811032040b80300320000f0170301038200001c0b4010504200740c43d81184a0039654004025001c0d0b504c4034000d90b881c586445069100d868480702c0f030304124200d502c054040700c04038004001e240c424010b41c1d07000b4040903042071801984500d891500c5801c081e00c4181440059881400490290185890802c50f40c0b61081842000c1c01c81610186c5000c5900e601c0803650a00c10740e1b0512820301c0190003044140c0b010380d8100e00170007164400303407803d000348a081c2c1e50903a2030303841810041441d81821046d042c1085140c10840d02e8415454243c0300080005900d147e0b004a200000c40b000620100b202985220040e64070100c80c481d40620316178001000f090030301d00356000c92183d51003a6400c114a91324001841c030000700c1982c80069036441072221100b0b5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 235054586 1250 235053336 235053347
    0x30c09060909090f0503130501030b1c0b04050f0102031510030e06010b070203030408030403050d020f15061e04110d0b04090f060203040201050c010513030e0f130b040e070306140c031006 82
    0x149449401079542c2c82c0d1031030f2905030030f5410442e50140f0030000b02c00300300409d6a0500442030744030b20490300b4070b852070125103000b0980403113007000900c0002d10a0000d002d00901303100040d00655914000e543e02c0c540f00c85803044013070141c01c80a111301025084e40441510a00c14280010b001c1802450540d09001203e40300d9002800e08a034107100420011400b0320007880508000c42c450740c01440100703502d150107824400e80c0f4918030300300d034030001e64440725126940b41203070001015030303a00d03400092411442420130041104542c01a04140b2a503a450451800802c6400314007042003001700340100401c0140e0715000c202603c0c006055104801003020350780115006441414035500d044040710383c05095510440d041d4201e903504660390030174544c200c004a001d48008403001140c18400c0c0d00002c25203d94a0303c490340e0300d5030741c5128039000d80b525030000100f8070762141150303441580c91400d48080c01030400c9111007402c04034089040c00c8100750940380a0b289000e0341001c1c0c2401c22404a60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 235055836 1250 235054586 235054601
    0xe090307050f01020306040e0d020307020d02010e0405090c041d0c15070519060c0e0315092e0b0307061409030102070c090c0f05160f020f1906030c09060909 69
    0x1060104011100005a0401c0540c2250420704005a124030380541000201e4005480c40416030f00b2102c403c9068650120850f01c1140e4101c1d001c0c10401c030300b0300040303558040078564641c10502c0c28080c05a03502001843c0e40b12810100c50a11020002e0141120300081045180c149684002d03958400c9107001e01c035009441e074030500b4050a21410b82c40d420f2a00c1403400ba04030f980800c1c011548103111b02405004244501424814451304004000c26911180c0c0c2a080d44460748500100301040d505003c0078049000820210501c944013212451b02e401042c10600c10181c40c08481c1901402c010650008844998490b1050442015102c144545c007850489a16550801c0381100140328900d0300c50142038007040001d01103094035000303014003d0084245090150600070b0600091041c0415210f00b580f14086442a0742c1d144007103100030450148190740f054001346891244400c200d0881d04490302c43d13030705221502552100340e84100880c011200061082082400108206c1d0044078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 235057086 1250 235055836 235055851
    0x2031608030a020f160c05101403100302151c110304030c05031218101e02070204090b0a0b01140405060a08070c0f060203161403070c0f0c1413090c0e 66
    0x10300d4800131080208036070f03100c8081c0c440b440e00798107400302c00e100002c60710300040c18003030320628150319407900094031025003440c160342e2000001001502d00c80808099400440d80648280308100802d00000a550046039a558600c02481c07040b440180145c0500340e03401c5080811036246442d00e80b0111244201c5100c241d07120b100c104100d001034800c082103144280c148881010604040a40301800c0c00540c1c9076401c03045060208620383e9100c1d8070398080c04812418001a036680051001c500038010310500640100900020030013280d40540003024001000d0340c0d4035000501c00c200c408660301403409615000b10341440114216402500c0e20340c1c0181207420800141c0040b035560b210300202542c821921300760040240104080400301da61321000803420b21110715030015012101c1c50000500b48403c100321b101c0400b040c06a6400c0c00c45515070410b1201201945990100b50300c4c02503208001d01450880c0003035030075008103110b8043c4180d4028045d907a001e02e0308201c1c0740b88040282c07101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 235058336 1250 235057086 235057091
    0xb1e04090f0507080d2601091d0313170f0c1009030b0703140709180209152b18030c030e060703030b030705040c02210d0609021902031608030a 63
    0xd030105404100140060105130000d00600514410050001e5118024455010f442218100748038640d40501415155450780c0003501c50141820201a0b8003c156880254007000070419010f8030000c1d13420302070380d01c0301500070706004007030210503600c00707145a0056441c0c21602854055181c2031150803000074440c5000c0c504a5166143c5048142d0160b43c2800401d60325003030800cac104c40c11004540c1c400010704000241518000307090280b1a0116000004541c1c00201401260b455000444404215400035074507211b601e0a5007000c03449105034003070002c08071174140b504014940105c0c00101d084544990360a00303140e50980715408040c2045041c400b54503c400c2050f11008054442076000340d0303012440c000302505050401805402c054002d27402c025458009540009514002080034101e075158081c074a42c01000341c1c000d0f08000200c050920200140c25410f64025020f01030100c20482071007000b2140c2030341d0700c1c17041d40904200d048a0480c0000460ba0741005541d1054400c1c002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 235059586 1250 235058336 235058363
    0x91d090d050918090102030406050106090f0b0d0e0304180608030906091210020a031d070305060f10030206040608071701030b0105010c080904020304121701080616110109050102030105040b1e0409 86
    0x1100c0040c4084131301e03884c56076001c403c00040c030040d40280c50050000e03040100c41305e401d01039200c1c4145018040e401507610001015006034a50b40d112a0218007450b090700d0311a903e4a032120000320440389800c1c665401c14002080030742d40841140c4808100070b240600c3c041091060040302143d6801c0071050b0700030607040c14a20b182c540000c2c01c50541950300010510100341c0c0c0241c0c1034407120782e80ca40941c41014144002900020384940003150f001c210710041da2a0300c41b42100c04c40350741009400c901c1c003003000111260000c001c24000d81d00d90322045200101058400a180000d20024050714403a100411103540a0142042e409000d64101c51500400b500800c0c203903842910b003142d080b241072140d0380e10503910103c03110140c40c85000d498829450580079698441002c0d100e55003803280b000e00d641e0894060000101c0f61800340c030003400590814186a8000c1d0130034402d041c00f4038280003800310b0a15000c0003400080c400c00030410740d10903411081c0030080c040100100e480e081c11400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 235060836 1250 235059586 235059619
    0x16030b012016030813060207031101270602010c09150f18030206040803040905070203130501030b060c01050f0106030e010b060313110a030803010911070506070e01030f0c091d090d0509 81
    0xb020b0145001e4030100355900c1e00208092411030081e0301c04401c54018200600015a1078681144800c200346807141c2c4071542111028544020340c0b251a400c003000240010342a601900040f41c4000c2c2921160311311030355060f49601190032403c803100010b2200f400300740310074021911401100040001160000e440c0e90204140350f1050b00040182e03880800c00700014406406012b42c4100755201550402400300c1188100c40c01c0c500920741807680341e6992002507241e01e01a24038a2001d00028421410485001a1242c1c0d080c040c10380001d060000d010032800050080455442d0050042c034559a10012003818421740e2650803074103901e5200a80030580d49a8491038065806104a55900c0d407600c0d0035002182d126210724000050144a20008034002003480c6911000324102110060785200c0100c0082c000da1616107501d0345480311480c031040c0e004419a0035107241e40c410141605c0825910030115504580000842e4451115620003a1062014102814001d800c88400055400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 235062086 1250 235060836 235060873
    0x40f0b03121201060336060c03090c08340504020703020304061701030b04060b010e030102030115090915120c0b0a030915110405101b0b16030b0120 65
    0x10140701102000714021500c040c922004a0040c035071410300700614a032034260b051582001d801c00307070b0040c59542d500300e000c88519140c04405a6010004100f80340c0000c401030000c00034404103440101d8161800b0441240c00190111100081014464000c828055844c07a000ea020981350980c070b441d02c0700184945131030015140043c8287c0195464a0601c0c00080081d40c801c0300c030000000b140c1c00104003140401c803040d40c00c903401c02c00c045454103900d401a162800814100c41e0558400000000c0300d1209800d1032404420554808121550300c0840e14141d03000141542c3d2210352800040003404d021000c03620441388116074082d2415981d014000302a00010150004203413500000410002c0c2404616242603248904200c2e500304c001c071f000c05030b0007107008640c0540c00d880318040c0c40038012409205070007000ea1801c0c51300c03255440c040440d00c0050b200b050150070301c6c07105011458080e01880da9010700c1a903900f5440307985403040c0c040e00b50303a080d8030030214000d401c0c58201074035851 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 235063336 1250 235062086 235062103
    0x3051c0e10202406010c02040f090b091f05101e08010203010303030203010e090f1203070c0602180411031b07060e06070207150f05120c040e070e010801140609040f0b03 74
    0xe02c054041d1000390102d0b1144042c03e0840c141c8520000401c0043c0c9a803c410003010700354040c2c0300000c0501e00000c6800041090074005090080b20808000301084000b54282e03800d01c1c0040c000080241c49604a01991002d81d203240c101d40b4091404d1084011041c524010004500b0850702075940e14405942244c3c4280c100364006178000005101c140c0b6450100c1f03422402ca040100b40d0803402406107a110092000310000d401c0b00040450001392040301c461110a40081045584035040344000c084000210306260056040030001c0b481d1800d0780060300c0c0300d26000103480312480440001074000d50b1141c42d08481155071501c40c089010010080d442c815030030f0790000c0c82c070782c0d052600341c440c2040303280d2600f003c0041115060400c00d40c040159081911803182ea25407584034010490304c24040d9400c1000d50410410401c04e00fa9407002c5842c0340450281ca07240c5043e40c80302d4907007850680018a550300100c0030800e8240d02c1c10503030b100e880c1800030a04002100c00e4084002030810901e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 235064586 1250 235063336 235063397
    0x60a02011e0504050606060702060a0e150f04031205040302090f0403020a0803041a012405070f05160306050a021204080309071e0303110d08180a0210030603051c0e10 73
    0x40e90b00308000c002082252035001082107400d6400c00d03147d580081c60360710407140e10b001080345291014240d42c440d401c4000c40c025503005966111210000e00d1492900306200c00c1c1c4280248010001300300b8000d808441c01c0d2900030b001580266150170080062400c0640110b007184254481c24010484c04806036000328450342884582045240780c4507540c15041c1c1010008000c120021940c06902201284440d01c480c101183c031840c00b81822034900605101c0501903000b01d00d03005110340c200c14030102c241d038440c03601084651200c06c02c4c03070100e010340500d0004002c0c0740b0000c94082100f24024585c850441401c40e100310fa02e50702486821890089004107529440b1010f004154102d02c0c886145043d9000600341d5200400340102940d8029006041c428400d203c00740e00002c0602c41803220039005443c0d10f01c0c1500400300200100320728481600c140c01400a16150711a488514000816403a6541100e0803865400c129141040d110031000b40510402e0141c1e8143c542c000c101804500e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 235065836 1250 235064586 235064591
    0x1802031213120b06090a0e10090c0b0d140108030a020a06020d021b010f0e0c090402010e24070c0801050f01030b090f1902010f0f0f1202460806060a02011e 68
    0x9044051001101c401b5040a002d9410124000c845500000c1c01004031121084042102c0310300d803c010344100d225170083c00c0120300010b84c2c0c034851469a0001596160101d2400e04142c1c0d9401c8920340740c1c01001030030401030300148100710110345290042e028000d40e40400524000340e5170740340d03003141c5009410340709603944914240e242003001e4814526200c8145003e050342c95000c40015601d0400208002e040c0400713000c40c00c11a44403e4120010795032460350714445503241041d6000c09070050a400c48290075844008950010103006d4980241c500c030780c0d81304050b400e5550344100035000070701c904024480c1c0c1890b0214401e00300b00c0268040e440d5021400d2034015400018141d2801e0750b00358090100811001c4c42240c1d20504204000c4410710308070402c41c01c120b00c010083d104a05011480c000320400259402240d000581c440b0348078620280c24800702d00c138a00e9400e004103040d0340041a58400000c4041c2820300c01440c41c50021b10000607030b00848400400c0301c441c00301340144c4080c4d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 235067086 1250 235065836 235065841
    0x4020102060604020c0703021212030106021507090b0313020103021e070c050609030601060507020f12060a0507030b0f120a06020a0c0c050d02090a02070c080f0d031802031213120b 79
    0x1601400700940012040d1000d602e401d038005c0000b0359a001c1841300034006c0d0409001d072070a00000380044620048100340d019507a50b5640e00c020f540302c00401509074800402004904001d000700f0422048500d1b4540b4142140d4038035080070040080c03040300740c0c180368081040e88240701980080b03025150b90000f070980c6800c0582410b11542009422080c01045c0810010600341c1c2c00140d928110392282c0780180c1d0b603c41520104005030343c8541c820360071015408188140f142c01080051003500108000c000302d82e21a0411401e50300d10001582d04079071142c0c0070599600785000200c04655080040342e900001c19501c0300201e178004001040000c101c0424007081001c944001c200805088a452009108507000a4004bc4d000340a444086070f00080c5507040103c0301503a00b000b040c1d8002900c10f101d031021202919860b02c40074010002740b41c608104d80380442c00e8030010b145a00a0001c080d50401c040d18901e45502200390200303a00340c0a880068446469003148070b00f603128085403017403070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 235068336 1250 235067086 235067089
    0xe0d0c0602070f1e03150906020301180506040c090b070501061d0603071d010b0c0a171b01050c090409031b060b0901051e062a061608010f0303120b10080402 69
    0x502003074001031080410111210044001d00358202c091742c0d0840c00b0076602e100041c0000005102440c0021b02d00360011000181c07800c9500004142c3c1800c022090090355504400c110449460111000100350001c03000d01c44020420060040c3c03500c03500001a40c00c0c1c4911200390312511540900c03809252000c1008402d0905010107002840c840b003401c0d0b449541c8242007915031f48140100080400080307a01c0303096660802c007a20510790482c2429550080509113079070307564481f1403180c00c0342100500007181010144070b900d120700a40326400c0d0400d8148400c00010780b245040c103070100040702e1040310100782502040d0401030310400c0b000910040070380600c20103400c1640114441c45204e2075200822544041c42555404101c80b0160703101c40540180c0c034411903049000d1500342c000e0709003410326200041d0185c05520b04058220b03800045020480d103402c82401900c0f108683ca1408100181c0105003403c0840722003003020411440030400304500000281129002964001c20710056 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 235069586 1250 235068336 235068359
    0x405070302030c0d0b070f032301060311070305070807020a17030909160206070f03020f040f0807080f1e0705130203041104060b0a0e0f0d140f1c0e0d0c060207 70
    0x1008050b0b070001108003130b68803001211440100110b0a2204600070a650305109500604a5002d4034041d000e40000c503542c0924070000034001c100c082460210301d6800d820f001c04c29240400c1d0305940300b03440d01e40183d03550040c54001040032604810303c00e5010458401903036400c404800203400454440f09007104124005c00c0c0a00340d5000d441c2c0314600400207660204103690312a4880c10850801d244c0b000044009201c0e00003c00400c00c0c0c00724000c50b001c2900498041281c0044046461003a262100715490b602000c4100a05901520344c00d40c3c44012416201c84403c1c0000a030758030565039101080c105010704009400599000013000704002d04a80c0030285d0000a4800300a018103051601d580782c4503002c0c3d403c0600c801e000c5400d009650340c150440b2100700190905c0e1100c3d0b42864841c508075411918a030742400707050742c1e03507004450006000320f850380030904241c21005904c0050f03680e510300c50b402941040f00c02400c0000301c1c00c804c44440050485900a200c0746140c051032620 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 235070836 1250 235069586 235069603
    0xc03120f07020f0d08070b0c1201050f0a09020c0c041b0f1107080109140615010f050c1e07051804080d110d090b060a0b041a03070c0501060b09090117060c091503040507030203 77
    0x1401001427145900000108082d5810b6680941300c0303410b4500b41c64002101034030700340d1100000e14000905207402c100085000440b144080c0c6040c00100312481040d415415245500c0c000149410310740c0044510484914041100e00015214441d0301d50030078500b034403044041914402907500c241c0d5001101040050386c41001482140640000b11000811605541d0540c50800c60007051344030718148203001c01d004000d900943da010307052084907001d0325400144580d80c810918903103600300720751403015801d1041d58400a03003841c03c01069001c8000b428210762010707120781c003401116240e403224420700070020301484101940e0b1500c101040300c003501076044030500703a1060204118071242503088018050301040740316201e0307a4203182114070482444000e0030740e40c00d0a100241d8424000c004141036802503c00000750382c0ca80c4440080315030010742400e6594031100015807012441c501800c4006401051140d44603020000031902d504140d605454030b8226520820851904015410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 235071942 1106 235070836 235070851
    0x60103050c040c1b0201031503060f050108060601020a020607060543050c19080913020c0705040c0504060f050702060703110c03120f07020f0d08070b 66
    0x3551081410740550142c1e24000141910620441d804000c1c80c1ea41c42c0f4040c40d8041e1382d40114010500ca556003015000b0b03c22010001030640d0080c51074003404410042a0341d4141350f941c80c00c2c108003500711819580410306400c0180c07504819282116003208002800d552022451581410482c4406031b08101d02c0c40d0b83c0c8110460800050b206900542078515042c545c2141681c241c40b52880020851b40040380c2120006114045101c2c068401c0024070f007048400c2c8041544040103020103c4603035000325000000110402243e8020041240c080c0140d075070105000d489840345d4051042001450650040068095021242065809086196034040c0d50034004c01c131401c1e442441405024818200f0305910f00081c0c0c1040500780c06070703403c1c41d01c41200d61030084e035448140120307041a800c18180c4000d0b41e403c0d589560050159850300c1d5202060714201c1200c440060000 = true := by decide +kernel

theorem cover : BRFrame.Cov 234892086 235071942 := by
  have h0 := BRFrame.cov_init 234892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 234892086 ≤ n) (h2 : n < 235071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
