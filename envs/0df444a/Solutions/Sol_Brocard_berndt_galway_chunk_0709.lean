-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0709
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:16:32.211283+00:00
-- url     : https://prove2.me/submissions/bd48a96f-10d3-4dd1-9ae0-c93a3362867f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 127338129 ≤ n < 127517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 127339379 1250 127338129 127338137
    0x1050705031812030406050a0603060e0a02012c010f050d090609050c010e09060607050309040516020609031306030f0e0d090f09090c120203330606030f061002010b03100c 75
    0xc0c0314442c100015144249884501c4400e055407601c0d507503c005410058543d07040b280c0c9601010004c20130922800c9a030340300c0c6400a11810540d840050001c4500c50b010307100d030060054499410320110046654455000d10344281c03074844010707007a1628001c1d0243c0400091031b0400c0782080184135840010624080c40032940034070403403001152560f8202d07030055007188400e03011540604110001d00130141c821400c1c2c1c1d040082e1000860b0880c0c0e4101c0e400740c000010196102c640304e8050009513000600d1001661034244201562000040144116010140d648401c100c212002d5800814582d4807903094414110412400070040344070740c00781204036003050398006501084c502c9020492944141d0381103010340b900080034100b5007125000d07609400340003110542c0000a0f9510a2401e00e41c48184100f850143d401009024000300502d008038000c100748501c1c04040340003268415811503e0702950388240300d08a000d0a21a866103030503220f4001034080c1d951050700500c458050743d0b91 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 127340629 1250 127339379 127339411
    0x31208040c152a15090b31141c0f0318110103060f081c0e0d0204110409111801030204030804030b06011808100e030414060c0f0105070503 61
    0x4500200c04080c4001c4010903d51040720100300036a0009503e10614019040031860311600c60308104030114000d50b8000740d540191104009580c9021600954008801d84440b03003103211202c651300500141001640c13032010340a04011006031100501c0c550b4405440c0380a440000082201100070402000b28030419044e6422500c6441100050400c404c4100720061081e103072000015840c400a070704240d260080420751041c00440c2c2001000d50100404031200b00085e6480c43e9014000080100007020040101c9550780401c45c00103190100c400107414548200d8414071446183c2c8500031241c148894103d142801c2c01c0a0700b040d412680c0d8132a403e49005004600700e01c03850200030f003060024002030000c954060781d0700c7e0380700c131040c1401c200e20314071a000e003451580d450740701c2c0c1202c0d48801c1c50380e50f6650650044c032007004001c40041d8101410b290490281c40191108507000f00000300d020b501b85181006081140340c41c0da0000c10080c00e2426000704613600407526810072121100b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 127341879 1250 127340629 127340639
    0x40303051f08030903072108071406070203041719200405071205090d0822081c0b0a0b04060f0c060903080402030607020616080603010b09010801050a06080c0604090213031208040c 79
    0x11007402e0041c00385011f80d25100c2620340e40d020040d00309500c203982280980d14840d18031b0350104070f0355020700400d030001c5171182d01c0c2460440054003101d0907007000b07800500c6414030300d036079200e07000709907c1d480790031450040c04c400f1501c4000d02c03e0214150b4070078100001e002050340c100c82042860b01d40d80300140019607c03500c0c401d5894010041300000680e96000243c00001c00c0c09951810b81043d150030003606a00c0d4a981620350020314189840b400c1010002040e14803d10981016410665601615a140070f81d01072041c02148110400c1c800c44900b114100d40c40391030142045c9522080070440e45c1c02d01d08005240c10310459049000348a1600820400d900000d0000d200700303040c1c254104164498403048807041d80c0a80042d030550b490b14601111a80d40324132050107031040500016070b274a060000c0701d0560318558007060194001203019000e5403114412282079070328045c4090380d1907030005120445801c01e80d002401d6000e40b130076007100050388081840c0c003580c01890151209501c0d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 127343129 1250 127341879 127341899
    0x9280b010e09010b2703120903120706021b0a030906050904021605030a020706020a0f02040b06040305010c03050f0a0204080604200a060e01020105061206040210050d0c0c120f020303040303051f0803090307 90
    0x14003005a05910280d405400301007007c000345a4140b01400307840303241003140810701c01e80e008054212107041d004110555100440801c64080f952844000c149008403510090b08001840c040c4608110001445c80056180d60301102c0180b410031180004072449801c3c096120b07007045a0100060140007000235007070b480044d900a49982000310241c80088a600300001001c0d42060ba0f0740100d0b0900000002c50b07028401ca103030b0300c021610b020071355180100140131214002012400c000d0701c1070005100e041000103032503910a510074018080c40356207a40c03045a00969100183d030118a0103004198180e21070007004582d98203030024000e9485020400025024036131344683e043c0e020b04001005450148003e441203031860600340c0c50b20100303003c503806903106100390360302203031110b01501c0411903000120f403070010707061400d0a115817041000039200d2002a202504068959002c90f031303110040c01d080708417280381d100e001042035520180642c482d00243e200351f101b40924540041d80c4007517 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 127344379 1250 127343129 127343197
    0x60b0a1809030210020a020607090e090a15090206130f0504090f080304030c02060315090606030f131704061d03060403020c100504050405040f0209280b010e09010b 72
    0x548001440951498100600070034290009404503c918801301c01d070443d5501c01040b140480350701400803482c00c19000f4110144076403000708104403440030070030300744d4002c12030b2180140d01030041c0c8001d0490248000191042c0040a07611440004000800658540f010001c41d4020015022039690341c0b010802103610700c036409400b2500e468000ca00045014008640c4644642401e03c80c0c2c803000d8010500e43d4104881803441500800010170741031500103849074ac044400c9990900d10700d0403c80c010400034010700407003541c107204a0840d0030409000212000b1181c152901c0c1d48480e034030301000700408236000311016001c8600e103a0001c141000700e1030621594242d0001c00010901005121200040080750b104002042c00f000c24107660728000c540c0200e00071816082211610b00411007a02c1024243c0701c041d29100c81840640c03100701290050a010380c4100050355580400143c44d401a44001541d20210360703070021810300107110145c00c000c04042681d1601811201425407481c00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 127345629 1250 127344379 127344389
    0x1c090302010e060c01090f060509070506030c090904031707080a052d1302040e0f0606010206071b031709060919020a0506030907050306090a02030d030c0804030f090b07050109060b0a 80
    0x101c2c41d84480c140080108420981d80b0000220054641c84800002040680c11141c540c7c9803014072403100c4041022202801e412501070380b079400c080342820642c2c801d12400e40d00503000c0100290600d805401c00b0b100c3d05d9034400804a49241800340100411421154600d6a80c82c11000c5080e45640c82c0c030340f0001101c180c2079165400840d05c80c0100742c01c0000d001011003102c80b2403c80050f01c1c1d5014888511030808000c0c40100c1c040503c2c141040c800601c054110b520038010000f081e903000035080f01c0200064514092000d00d424125941d00c0c64404a0910545090030701a41d110001031403481054030300266001610a00e41d090710100d9030560103507200352070304c10902c002d2502e07100035600030544004484001d80d86402090412004848111150b040759140c0da0039403c0901000c030b100840352804000c8600103203030207010400060400340801071503d202004990158078054042c10080c0346558540c05a442c1031400390424401c1254541d0901016901c5401d001c1c0008003070726 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 127346879 1250 127345629 127345637
    0xb130302150c090a12110906150717030103030810080d0e120307021513050301050c07060b1809030d0e0c031e010b150304050c0a05030d050901030e06091c09030201 72
    0xc1c0c26605030341e41900142100d6a03006003000001034940d1381450b01c0004210241545a403446030707050084829840d168a5401403000c1801c012450f514480e1a010500703007200e00a883e940035081c03401218040f640010911600080080141508107404620503810402c1030400d0700c0e1a045c2840d2140c031282000c80225500040d426031915100d107144070010ba00104890a10400da00002c1c030b00f071a4442e050350003000002c0c0c000c0040d0000380765200946401d6000b80314a042c90342400c0c5480c031546002601ca20b641b140d41241e50b80d1000101c1c03500c40603844d070a800608041c425592240d0042000d1340c2da00b440d1495981c44004003080711182c01070010080d101007034501c0c2868200c4082801600b05a560742c108003c0113646681496900220403010552a483d062910380d14000b540400c0521890904108020607500001c204000c10502e00c0d219071980740c008010b0700582900750610803107000e42c0f410030544150009030080c440461070750150345191070392000c1c0c40840c21030001074000303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 127348129 1250 127346879 127346893
    0x2010203030a0908070501110a14190c030e0907111009020307030308040201050706180c0e2a0d0905010b0301061502030d02070305040b030709090e030f07120201091a040b130302 78
    0x1080c80ca0f40710b411118050220a854206581c0e81e079400c480845607406445140440c200d411207600186000501d20800c0c402807034240000344000341c10116140d00d0003008030100d011000c16201d4015180400c05c007030710034905410039440241010390044400103a0707107c1c1c10b1007000740ca4210300498181e5500a4040c00c01c050071910200c51081c00240280c4c12700a04005010015044c0c2c490007000d40459060490a0702951602910074a0300c0c1c0c0c000c100a14044080c410039460b4808a6802ca40e0703480d004808604045100511600800c584098083d00d070056090074003030103400030700414008030000c0000503100d07417180f00101c541007114801a40300740011504010300d40e0040c000140641451800c0c90358075420109141d1046454100094000004002118071401080c104501c000041c40c14594200403014160240351000f400141d4071085180c050b0b0f00031352080521a4029148885c248550301d5000212074090300e08440c510b8000c800202d0400c001c112042c0361580c550301412807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 127349379 1250 127348129 127348141
    0xa02040c090e011823100f080d110f03040602150c0403080703052a030a030e030301050d111207030321021e0a0e1309050c0405010f0e040501060306020310090c0c0201020303 76
    0x7480400004140c0b411742d9810f00c1000004015980f00d2070440d03503890044686440802141d510009500080000520200502c04c1d41c101162201350310080b8a484907014809000c1d0a20700200450f20000d41c0c0070010300450304035808915110b90300f00500e038420301500d921540900c144598172001d0240c801c140400301c0024854401807001e4202440192014220312424030380406161514a1050b0b000040743c1c0d18454050290b00d4815880401841c1158035001c0801c03602000b0036401001e00118181d00f07442940c1c2c070300740544840d00e03480440d94540c1d200c0c90080c2000040560713101e10722224003d80e410318403450084031100c4800c03c00c042100c4031b004501d1900da803c84201003080c00898100440940c80302001100141d04804000c2055400742c02d203103051042500c03195001c2c60400d0300500c54229608405800c40c1c1302c3c0160b02603a941c0f141840d074010062070304028900303400001070116122200700a0001d44a148008200991100c003094131500d112203c0280543c00034400201 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 127350629 1250 127349379 127349399
    0x220f0b03120f030a09061103091608190203072d0f060f080606090301241d0103030f2705010908150f060d1e06140702060a0b0402040312020a02040c090e01 68
    0x31308502804070203d49864240c0c1d0b88001d4841e03290b8020014280071080000103c810004110300c8403a031580d440060382003407546510742e4403070896043d0000301c0056500440d101001810018000d03000d20000a03c52118002181c5000c81003d403664803100001090030152240f0000451300e00c0c4e264111101e90800c815280410001d107040da01100c18080910280c800b8061203640740d15001c50084c0e02024113a00404400050300b04081c6500c20140d441c50503805c05c00500d0569070941006400320a003540200c4111449000d5244007000d800d5429080361345515041c0c0a803013091f03c0762000291589280c0740c2c0c0c2c849000c55170700f10041c1100032900f20a46030040581020018114413031000741c544950191a0320a41a119a40c20200108007800304a220b56450301980d00d00122107400c0c4104d0003503a405002e011081d0050303466104a406960720342c102c400031684020031403208030041002079100c0b407500e4416030145040002c49903e0621421242c03055601e07481d480c41d126424980381035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 127351879 1250 127350629 127350631
    0x60f090806060103090c0b130e090d020a0602160c080304030201080a0c020c01030902150f1b030a020a1b031403031006020606210106030b01030c090c2606220f0b03120f03 75
    0x510b0841c910b10b070204007c3c100c1401089102c200c00034211809281503c001d1051342d00406466003508811401c0d82c28640c0400d061074869000507000d030b20350003044580031007041c184000500e401c0c0c0351400014444d0300031018100301c9000340c84803402595040030010990314048000390058110a00000540d800790b405568224005440000240480c4640c56202d070b1112a001c6001e2030082003540c0280202842d00740c011380b4a2000c3c1d0b0504000202c040d40d0b5043c2c10308028500700424403851981d11071110b14500450b00244024030350b0407d60006916644103441c0d941c0100034280001c50861300000c0c025000c2c0c072016004c000040848110300d5840d4214012041080d5203428001000c210185601d81c06140100c80081050b45010303011003c0300c07258031402040c0724070801000c0380c170000e8a0031010400383c0885d445d016940c4802c0050a0020380030100b9900345020b020160f0300044640c0000c41e121070704401001060040420117640301038111404030462030400c41c001c54108440095 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 127353129 1250 127351879 127351883
    0x18040501240524040602010b0316030309030b0c070506040b040b06030a08030105010c061104030501061e0f0b09011101090506070201060b090901031101021e0d090501080f0606091201090507060f09080606010309 92
    0x510945070508401c83d5075005034031100040c3c0d12408400e0f00307440c0c1884110f01c0e2152400c140c100c52480c41d50080c0c81c2c01594400500700f404200001400207102c00100c405041d40b24064801d540b82c240307407004c454503041c0d8068401280c1400000c025003400190024100d400c80c004900b143c1c1390000440300c8100c2118100c1c0c40e41e80300c20001c105515a035000c0c202442c4a4000852003900749030510b600c80808200003880c0003c006000c203e01d1404510031420340b408103400654031402480140e0380800e030f0407108e6103a036181000e504180b0102082080c06412541c0c02403042070386d102081e507010301502c0d0009500841900040000400051100f000d04006006444032030903264070240c004883c41c4607c0c1c0715908481e0303000390203ea01090640180109007041c144505140280b0b007403003c80241002e000d060b0000710101641d81e2001c2c43c880e0f456019000f84200344440c80c0183e207403000340c4102030104031128000f81a06005030605020765080d1001041996501030044019044107082 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 127354379 1250 127353129 127353169
    0x703030927050c070203160503012007020103091a1306050a0207111314040c06020105010608040f06050606131d0609071b08130602010e0c1203040302010815180405012405 75
    0x540700141c030700b8401c0c040d00b6205400b001c0021441c141c181401d460343d031007000e01c1c2c2f025411181400f200f41e00e4287c494050302841d000800c89624a03003030100c100000b80710300f4100d0040f81081041720607144150b25241c030072842440b880e00c45001c01d1059002da48401043c0d03801a4015404a0504501140325101600400305042c00c50101e106142c660070f580c00e84180707800902c02c1c000b154090040500410341d0389000225850140c56000c0f10b01c514400003441117480c0c40c0403403403580d03500c400d444000c881248030009407541c40c4450448001415040d61a801046000464034500050b4491080080c2e4039080382170281e50315007105034107007040100c1751041c080c07221018403010004180013070701c1c083c4c00000d020349000c1d01d1185411990314941d4460303500d088040300403c1c2d01005843c100d95080c2440480b035107030b40441643d0403080c80201e680220091451707480704d0101d420210702590040008100906c1800c420f0098688000c03c64a46032020540412450526015a00c1ca02c114121 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 127355629 1250 127354379 127354387
    0x212040f0e190903110106050f0f060d06081c020705040506090c0f0f131716090b030a050f0109030f1706010804080d0c03150506040f1202010504030b090703030927050c 74
    0x1446100322405040183c00040c985c020701c40910a09200d80e9015210440f20b161041e07842c0c20009030203000e503520b01d44c000c0c10007180070030111203640c0090019040e1841544c0001604140340180c85411900e00c500510032044000b506041911525004440c06401c8240c640c0e90f104440354254001402215003d0003013140c40791141c00d8202500c2c20300c4c040300018060501d031061040300040c044106a480d90001d0b240900301c40e40400c0c90300c01701e4200c66008600400c03114002070407c0c6034440060180d02031488107008040040d840000700754031a8407420050009410704454400b103504002c08070715400008901e0135801602d10a6006106120031450511082d0160f07061380d0343c3d458480007003074a620700b60b00600f5450f244000900410b035801d905142c07805801407c0c01c03402d80300d680702c803110103042a429640310f00300316009150464600d5480d406e11034003041d501c01c2584070540c00a200c0d006c02051400d4400c00c4a100c02d5841980011454240b8008000500c0c002c1c0614980c030310204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 127356879 1250 127355629 127355671
    0x90102030d090602040e071d01180317030108070b0406050901030216060f09030813050c0d050a0f05030c1207051c09051306050907110604030e03120f09010212040f0e 73
    0x3001d80c1d100b46104440140c1c0351860b0036141d05290744082e104900b44240301952030b580101480301942d03000303801d00e802c0b5180f0f21030104a54401401b6000a010f8000800b81880003044500c0114100c1719242c045071a4640c2e900e064800c0e80c0103900a0000060003000007012030762003a0091300d420001038030143d80d5120301d580ca0f44212051602c030302c0499601c1c3c000220a040e00821703441c3d8000351012514903070310140c0c1ea40350f0b140c0d01d03010200307445609245001c00070f100040003281c041a030f203d260b440c2c00c03804e541002c640d0307a0480b11018460b8480c1a03c0d15a58641180a88000c03540c4600102250300404c402419100c00040d00714040040c15100064560381c0d001c00139114003200d0500040050410003030016a400003444d6800b40441940c0c0e040b0260700004480c0d40c044c1d0145444c6234018000170001c1e0500302c0e140c000783c10582d03002c29662030004612006002c0c8910980846c2c503900440085400c8078042e6210b90b081440d00c41c1030421900c01062040382d0301c20000500543d17031074076103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 127358129 1250 127356879 127356881
    0x90a060921020a030e0a1a0d0e0f060f0c070209160e041806060905043302030a050115090e060d0206070803070203030103020a081902010509010203070501060e1920090102030d 77
    0x240400c1c500580c88640041e05060300181c14540f400d07000c3e205102040c1c01d100d5100380300e0500b083c000000391030005501030045180d0740208000c4140c101903c0300604161001903403a034003074075544140d98080d0045013096100704c08071040c09501404002442d034030324680130003107039058118505100c0c1c2d504155038584c1d03840c4200180c8040020146500f0403032410850119003054010000d014603010600c00031500c40040c201241c9002242e100b29040d80b1400c8010940c084205420f0540c0040244000e0615940282e41070381e0b429441c8504d207a456440c122484051441218106031002003c0703100d1342881d9040b82d0801c1c3c00506218a00415607841c403144d580100d03415001a0000720060045140c038201020051000000400300341400040383c1021498205009041c42000119244603900034030640e100c40e80c104c0300810050b0b40e00c00480e510a0400c031851810f0f1840b8a071701c26220905445100700d5035034100a0850110201342d10a41c2ca076100e40c0350035041d44011310180f0554121 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 127359379 1250 127358129 127358183
    0x1203011a07032f010c05070c050405040c0b132c010611161514070b07030b040f090b150103290111070605180f0906040911150903060f090a0609 63
    0x500f80300450010b100107001c508440c1650203c40030814200960070205600c4007040c0241da5080340e00003040c0d111341c1b0f8402001811580209400385012901d941d07801410300c817000440d400180c6101d010384904c81082040701080e4204902c201e800001801014403545501800400f6602191920110b4520100d102030050b4001c11071400000b548175462580b04190340c43c2c290a519600c2d0921400d59a09000001c000f0040c0d000c040c1c3d074040002203541c2e90b0f080941599440c200802200e000d50410703107207061044601e6200c44400840380c0440b0352107445040e841d2010500c012001030301101c210004000341d030b00118104280001010714404090010800410303250320b8075a6251a60740038403201120060710148500d07246602c2440d42d40b5102c03038040d8409401c59001940d0101c2e450b10001c6070a480c403000d0740002d0f02d00d5103000d00b1036240009200142e011007c0b076210341d560109030010410100c030121420b400105003140010155041120740030310890034110b6990454005001d9061 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 127360629 1250 127359379 127359437
    0x30f0f07020406050307260a0f0501020a14090a03060e100501060f0909023408043203120a0507020301140a150503120f0d110405031203011a0703 64
    0x80040d1040451405100715001042d054020b41000e61900300b0000c81d0044280f611080500b20b84061190080c0c1403080462083d80110240400c1c040c606200c0d000350480340c240e0004c149640760400810300c0d00d00645c0e201c00c000400220846040d075807044080d103c82c0180c8005031095a110142104041c01024040c04486d0780c0c03810b0304400007600514181c2e0f19482000c1c03d0b88100504000c4031900489039103c0e1808415401e003601036100700c031000036541c000191802c000131902045c0c041000f41403581d0085800360782100340c1d0415904042150260040c5a4107034014140c01030000100b0b0060450400c040c142503041c0141038000c00d094500142d000d41d04280c5480411080c1002403140d54400e0f180300041c1150f4a08000c0031036610400d00490380c16404000c940d034111440c007202154590014000148000180b82d8454460390700f0500886110303002c1c00154034000c10140040d40e049544d8803158220b1882d8510b400346155000c65003d40400840100007003008501100c0121140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 127361879 1250 127360629 127360657
    0xb040503190302030c0703030b0d060c021b01020f1c090308040e01050909010c09140a1e15050708070308060f04090506040618030c0b0c1312050c060906070f05030f 72
    0x90000407001ea01d400a0324055401d0620510501030781c0800c800035190100e0740f50800242c0d103010000021018070110318003c20f09820040301070742082e800314140e01d40403101025003145440001c01a07071076040165514909902081c00c01c8560704095803488040001760515048071612911081d215a115030000c0807040d168100400042c00c220b0040390b4840a114000c001654034018000c0005059115100d200e40d880c601403101c0383e4542040900904000380f4450b081803020003844c001003050700c95588000d083c40c4d050391549004900300c4048960194290340f800312156425580c51302c000d4801c68202d4201404131180d900d0758815000003502900c02801603150a20309182a19501c841038070a40c10b0041044000a03041540c481c40c1c2a8085105c2c40d13295550110004c080c012405040ca6800d010b03080002c080c5480500391150502800c03d4450b03000b009010f11400e40b1510082c0303508110100044000f044002c400c009100d441407080d680b600e502a21040e450703400460061100d6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 127363129 1250 127361879 127361887
    0x60c06060114070809090a0f061d09030717070615030302010207020f100e060d091b06020601081b040b03010b040f14100b03190b18240f011101090b040503 68
    0xe40c0c00c0b901540390782011464162810003c1eaa13070051034020820003600543c41980803501d540c105402c00d00320b1091001c001c0008994440c040c04e0301020800740031f400c0d000504041071101c80003008540e40650060346071803040003031005510b41c940c880d0100359005a41d40303044000201480004000841c040c1e400036840302c203a8010001c0c3d01d511880361910401010011440c41500a40e031482007110440f150307030311042414400409000c0250f00104561103207441d0300b01a01c19480d5400540301c040d400c695071a030f2204009071303584501c0044402c402c990354010510925058000150080e005800400d2500801e40810140c810800740600442d4640d01c1290207203042e0300009034003000274010303d0046e0785440e88000061201400222100c2c60030038002c0c404941640001e0001c0b04068420301c910a250442502107010a441e1f23110b0601101c00c141c2030749040d2008114490f18000c2c0040700c8040000019583e4011050305900c0954071a070b403080202d02c1d02c0d83d0180c403890141000d1940d0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 127364379 1250 127363129 127363141
    0x210021b010506040b0f0103021b01020c06090607050a021203040f05010609020a030b040b0a0306050c160b0a060512060708090f03130f0815270d021507230a03020405060c06 76
    0x39904000d03c0c0c1406503240c01242c004554503080000d000c0380d000e003001641d400c0c1e0404c1c00351000101d00d9861120390f000141e40200c900002035154400c014801c25a0515181c0a1044429118242c050b80050b800290600c007001100402540c005101d039924a940b018580e1300c9600303559055001c039642580c042140c0c101c468050007011456007040700c00300318802880300051102d1203140000340095070348100040e00e101c90070b801c0301d8410402002c003c864908900c0d16240d01c190488000c40c0844c1050000651170401d01c0720500054442c00107401503a54101d4110741040c00203064107800c0c480c400c600c000703280d000d00c01443c0c00000f81e46400485e41c208448a040c04d40540e00c1840b00b5486444114040c1940200d17090f0032008808540032420f440300350102c4000e5122480020701e0003101d040344096500017030750181c02451440305007215a1400340c260346030954610403002002d00e503441010031401500017001203011600340142042e0f20b60001c0358090700a8003100c0d10581c4070b0800d01c18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 127365629 1250 127364379 127364381
    0xd050f010603050c04060620011e05060112180b10150c12020d02100b0406050a09140714090402130b07120810050f0103020309010b1903020f030615010c030210021b01 73
    0x710980d0117890038889685010170042c0a100d041e11524160349400c2d2000c409402e080d0000c000200d01c011490b000c3c40c5045060340000e01041c4d070400e001c1800300100c0116180302c0d00070810713041e0002110049401890b10744400001c1c0041c80b02e10024105000491804401304901e801a8104e80e40d1280d40701061402514410545060600b036600c5807100d000207540c00910310040c1c0e404800089112451807010a0140c4401d4012550182c0a003801290a00c102c0d03203d8900c1c5200c111007800d00da03d500109480c51070002c08030712604a0100004840d84c2000c0e0028040c90380038113006080e584d5140d0302007000b03401c0319004071b40c01000134020300c94142e41b1580e0580c005004440400003140380c0000507440c0841501441e040c1500070000858903c170130b51016102c0080a0000d481c0c0b44105203d0346444121400100c0c8501d454002c4003406003000140203107e0b4180380050820040380300c0c010340c2c1c0408115011800c503c505110700308003185c24006089269500d02c041a80614030215141c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 127366879 1250 127365629 127365643
    0xb090a020403050c1c06050c0324060301120f021305061009080601051e030a030e01030f020702090a0504080705010c0509040b030307020d061a030a0c03030f09120602090d050f01060305 81
    0x6402500600c02400812004202d445003007100712a6100c82c8105400c402004a94210340a0304d40c51a010400403c00710710702c0214414190004007a4141100d5000140f00d604900c106a40015040c0b0050000d848001c8000696500034111030881100a0340082d802141c0203026025a07901c2d030084c08018103052801981014460400c00d030420b0401800701c2e61400140b14980c0700e081000c400101910345a41c4503502c0042c060180e41012180d42000b61605402241280c0068031f0103184072410409442508c0450340e0052403912541c0782e1410b8034000c1d01c03010300107454111080011000240091084143c0e0041c692102515102550104030031901540140790003a00104490300c01641e075106000307409584070000140614218880c05000e027017107240c1c41e815204865181c07061100c4c0b642c0c0242140c0c8284e40fa646080030044040f51076010f980304071400280031308860000190150003038091000c0145c0081200612610749501d40a001428149030ba503441d074081c000e000c4207001031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 127368129 1250 127366879 127366891
    0xb1308150408180d11120706080105040209030f19060501050909100c0905030f0703140a02030304030609051f0e060c0f0403030305130609051c02011109010305060a090204090b09 78
    0x58000c4a51194280c40490001000100421400903810901c1d42482080407034041c0301420a4090044a25101c500072000d00c825a1140d86c406a884208200c00945103080e2049980c440e00d0691811017400f02035040340d00d402c1e07803500070b00100700d60001c0c041003410031300c80e0400c1000e4610480b40c01c00a045842c181c00031030041d110b00f4100000c6400004e403907501e51000100018166400000454240358182c110701d502d80102d00840084c03000c0010a502643e0241c6e00c080c0740380d110b504d00355542d2120440025015003090004101154441d484410294061025900100010314581d51aa07228071800102e035582c603120381000c04070400001c2e070700058101e00140f502c020018441c0e00780c000c0303200040815032981c0001e5003150468511842d4a5404503040c410001d0914200e0340701d4682e404031081c041418016801c0c01441400cc01006c0d40003045414034040c140d8004501800300107203126040440c01c1e4000901c4070003403006200a08040f100007406240700b4042052801d03000d408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 127369379 1250 127368129 127368133
    0x513030e06030c0a180302060f13080601080c011d2106150603010b070302070801090303092a0303050919060305070201061a0a0804050a061a0a06050c0709020f040803040b1308 77
    0x80010400f40f44080714503004c0b09040c2003c00c0c0340800c2c0408610001a04000e4005102065002d04091803001038a0705910f102e20550020703840300c0041c1d0b541e170024030a40000f50710410550001c0d5025030000a40080007955001b204003c14010411001000340c0d02c06003525040c544800b03048051000580000700c0a071b102108400c000005072080c0010701400b42c040c2000071704c0d00c0406008010b2000200b2075a0000d100300111403c0203002400354140945035540808551000480c4160001c004c151640c000d0349a21421030b00c003162140c0140030b009821404c4402007015120004d160a0010806030781c004c1811b280c07011000382910083e5024a000075840c590003060910110292420090716180c0041e4513540c6080280c5404040d110140441c5c0c50880415210700c01030f01d90f180c60201c19103001c0401541ea250441e0381d4411680e401c00e0b290002e510900410712181c00a080c01c481c1c0305041428562a00059030035a40641d01070103011a000400740c0f002240e40303003000c006010440c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 127370629 1250 127369379 127369381
    0xa08010c0e1f090b0a020120031501080f070c0218090706022104150c0c0e04060c050a0507120e06220b09030d0c03030906051603050a0605030c090406020d0513030e0603 74
    0x20015021608034001c0c52441c61380805c5c1c18500c14801d6000509402c001c80040785514088007046a040d402a2030300924010502d081d40300319402120468010340d051188040540d65102045400c90350b90581280d101c00103404050001a8445078203004186c20b40c0502481482c00c900a403400862104801540b4540000c0d00603410640c0f09680856100710040445011b0300803007260381c201c41040080020208034004950034440b61450f9114034441c6004206c465500a8261868001e004900c000104100000c1d0001a441000f80d40764070440d0804070020161080002e42541150a0404007402401c803540c0004249400704030003080c0b2204401c0c6000e45540210b0303201c1c0420010901480401184030701014441d500c11481e2940001c010041810140b10030140d5501404030000000d00f40808030f03440f664507120f60812540020010310764007030210188140400018001c1d50341c075509028032502c00714240102c6104260002000c031700040c042c50040d0002064004503405850140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 127371879 1250 127370629 127370689
    0x1030c090306020d06270b03160b0c0a02030303160201050c0301030c1a130603020304020102010507110714010c0c03290702030a05160204061e0b0906090108060a08010c0e 75
    0x1055606598202d10090b90702c005044103a800707032000d84c2c40804a0308444940b082c21a00900000022800400041c0030b2082100d0805d580ca0010600640300c004a11800300034902a040040c20f8a041d0f1310107070740c0030040a800203030560700121020180c550520b9042d03104a0380c280300310360344400d540d04102d00355415620345c0c10005030540102d9241b001640895010343c1820400d44411203100c0b144442416151140200130b03400c1520f040303002d90b0130040443c0109026654264140e000c070f00040100c14038011068494100140f052418800c1c2920702e04081041010400041c50150084454000c42108021407007121109088100ca08100510410581c0070088608418041c5003150300c4603143c001400340da03100d4520081d0b01c1441d1010018003055130745412070058018030b404003c099030320b04440d08ad41c824102866070018041000c841d140d80510580d5420a8014025550994075451003600710ba100d4a8942c0100751380b0844100d640c0b49c54044a84406400f011800d2440301507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 127373129 1250 127371879 127371887
    0x102030c0a060c11030301090f1103090a02060d092909030c0712080405040c110c0a0b09060a030b061809062e020f0316050d0806010c060b221a01030c 66
    0x2070700040c082500c925400e00418443e071140300c607000018041d60380c1c1e075035204180c42c02801d92080d02c2201d00d007403840403034402e203050095034491020807002d0b0a00100c19420091a030340000031800b801691916454007060f40c0c501e000c401c544c2841051016000c01a22529640c02c1c01070008400382d00401034035161034008a0180d04444007038858040c035115915080c48540500d402c455000382c50440469032095000000084041c1e4007003c1e5003001e20360005100042d022405610030710030f403c000c811030500f0500c0042140503028600001c4001c00f0400042440d48000300145400400130400155880d111001d140c0102085484c00c0c4a4034010151501c40004024008400015006500c02c124000e00aa90001d02d1100550ba030701d10320a810800c501180310800d4415100d925200c41b03849004c0c84650303000c0c0071705031515100501150344500140042ca646d217908034002049418401400d1125404240300460b0f021440e99288400601c08580640220341014144000c0b66445500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 127374379 1250 127373129 127373143
    0x50a020a0f1d060a15200d020a11040f15030b0606160303180b070906090902031012060b0907120b040c051818010605090102150f1602010b100e0a050102030c 69
    0x40c0180c840710b26601c81000445102d810b50240110212000200022a80c481524402040c0301c44141000b4241500f0a980e140f1694040c100907a101c86108000304021402c2100e01280003000420700800c010400d4096910000e20080c807100002800d00400c86042d6240e40d001505450440c14203c0403c0450081c03c910304018042c17554481c3c3e00030081e90b588640c0540250400b01919040c248150001c004043d14130030310340002c40c00040429011910300071603000318224102d0560703217070911340c0f030994890591004480e01c4d07030b9800101e0059220144001d10614481e02c800c0c1540d041d00c040340c0240c40e20a54000e02c254949a41c2c8480d5541100555003034103403902d45c0c01419400040403c2c414204015240390360943d020000130b40c198010b00500c070401c2c003a401e440300102502140c603145003098501d100f140c0d030100005000043d100740b2441542d18140700224403406c02001080c1c00c0e043c141840400581c1e2900d114400341000c0380f5202c01400e01b8801185131140e001c08031034442030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 127375629 1250 127374379 127374419
    0x8070504060f020c191a0313020111070806040b07030e0307050604060f0e0601030807051501031e06061e050a05100e060702030c150c1513020d06020d0603050a020a0f 73
    0xe88400c2e003034400c000c400c0401001420403000403c1108483d09a00c40910403110382240701d9506d004002d6400c0190790198642c3c90b00441c280e41203074015a0600c4101607001064443c00340300188050040008034005c6d0300500f5840401d0812100040640d04440624145030740700308802000588001121944903810800018002c2054406007000d00000c0701000114414280084244440750004145542c419401c031501042c2e9082d0079481509c0900c070240840541810b00c1201960891707041da590752044000098050311030b54584c00102c01010101113214520b4810700035424041c40b21406054100d0308584130301328451005219501500325180240c0c8081001801c41d24100a00303200d00c4d13401004000040e4552440031815008511154014842c849501c12a42d18080d0464002e40e01038520024603038181d000c1c8028402090012030f44158200078000f4041035610418010754459006069062100d004214550100f074200104030b180c0c0d9a41003082c0070050821101441e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 127376879 1250 127375629 127375637
    0x61906050d05180708030d0b0108160e010e0a08010b0f01081611070e0705180a060801030609020a170a0c0902040e01150203040308040f180b03120c0115030309030c060807050406 78
    0x50b651244540100c1103070f032080c4100341324401000c200c003200400508900b035080c460400049009100458007a0015940c2d0030b204805890030100c103a1084001411301801810b003500d00001600128201503200e503c4003c00381d40d20f4194400e1742c5070500803600300110900c2c1c80002d904200200000da204101c800c44107200c9052610484100c1c00d10104005007010004c52020340fa1141026000b68400400c16481c0b0030a17403000f040510300f0544a4041d01d40e07950307900c0c0580c1e0950751060014040c03032b50180c1c3e10041000d40002e1450100340c9441d02c0c100040003401c11806189003c0f90b1842142d0040801d641c01403006010481110304aa411501c12115000d01181c16000c1607007944607030703040680407010015010500c6ea42141141088036000c107203d0440c1d41d45201c03c402151329030361045626800c211711028007508504050491140400000603c200d0f090081c00d40004407a441100403444243c4101305200345030b13141754010105030610300c0c0703d0315150400426600c03490041348140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 127378129 1250 127376879 127376881
    0x40308071713150f08090c042d060f080703050303040b070c0b01030606150e1c030c050d0305150d0201021002030606090406080d09120b04080703030e0d0314090a15051509040b061906050d05 83
    0x900c65200124880da0111084c03641400409d80300400750000e400740b0704c030820728070800140e5a1320004400080366048009103045d5159a55610200500a01100100040310f02c182c8040345a40c040f540c02541309880010744549000c619144802c0e0f0400107006100b001050740040345c44ea4654401200c109110100b11030047d4030b020780f00b2031070380c01016104ac07141022102d800e070b42583c0301d01d006501034002c400559400b80b0400180040304a00280140c001400383e20300040a50040c50700308000600350b5050614a0300858110380341035212103825800184000f1031960000d207640c000d044076911a0107901500d40310b501c7e40403400380005041480004800052511980c0006408030180f415107140350781030140280602050760301782c499520103a0205103961030000c0c4500107603610030705e014403c1d4102d0304a10001d2500400c12240d54141104800301981da1110300b07489a8818204241c0c581001c5080c0110003071000b040c42442e0700f0500d418031020303402c9015240386e11180381000c201c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 127379379 1250 127378129 127378151
    0x11a0301030f080f0c06150d110f060c16090f0c0504060c061409030c0105090f0709110702100804060b03060114040b011e0512090102040308071713150f08090c04 71
    0x100d10030202d04280c102c00203d140c070300c1c17010081030044c05000d0b01a045038007908060b0400000b0b00c5072090040c0200c0e01c2d044603140303e05107a0621589100300810700c4c2c0c01c08034004031180c10701d11041c0300d0080040c0343d14400d100001041c03041c83c00d006200e813000c01c000202c540000d0270314441c5004d40000c1c82030300e0405000700455600080b1095202d12500ca101d803d09080082c2c1d80d170400042c06c2055420040001d02007000043c0340d22407076030200010161185012041030041204603850180c54508000c050301680f1808490500c1e07981d2603542d00d40c80c0c500f904000c4103c911100c12184650800c81c01041800101d07542c11480c0441281c00085240032280141d8111040c0d4121030f142030325005050380c0c0c29030800090421012961a0201a5076900c07075100e00b00d01c2180002840384c2c40074000440030a40c030f894002090114039080324030300300420403150180b4000e0740c480f01c02240024240111507a008007041000344071403c0a005900700b100c0819101c4281c6002940130300c2c2d4503291485 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 127380629 1250 127379379 127379393
    0x30b04060204030804170d0305101205012021010501050901050d0f0e030a0306080a0c1707081204060f030b0d06051302060d050612071805060d02031f05011a0301030f 73
    0x15035001240d1a40c03035546c0c4c040305240440351101c80810303024071361020402c5402800752038480c4540c0d0343c030440000d052240560350305c03440c008183c940359600c0c212007480d180700390100c01644a40c60307005134441268003288041c0b2000003140d20390100700c1e840104001d0340c11505848200d0000d00b045629000c0c801e50600080c81600244641c031800d107e0140b86144d0044024190300103240d0b8180441038984d00703203540d43c0d10704020042c80c00c9030004040000d2440c034102101d04001390300a031140c196880303114070718103003515007025001a0002000c0100035001b544802c1c1005481c00d00b40107200031800041c0110f281380c1400303000305403031300c0018800c00b502d5480d010005a0090a55481d4080c0180b500011f01d42202d00ca802680c41c401d280c070b0884000168401142d8040d00303840c00c052503101b141e0024042c00342c10a500985519015401079506001340140101005000042c0320b900080b610291001039000c180303412290b4100c80e840c51504000c407415250804101c440071806031410340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 127381879 1250 127380629 127380637
    0xc0f030d080a02071e060605040b060408060a1a12060709060306140f0102030d150f1d2d0403031e0e100b0310060e010608070f0815150a200c0a030b040602 68
    0x450b0b29070316111617010828154880400e031482503900300724103002e80c0c003030001511a0b4000d001c800e5004100041041c0741036000003121405904a03a441d450039400030902e80300c01c80001c4120350b08000100080140c3c0515400020314061a00b84100d92030440c60b55120200c540d03d0038041c0390a41e842c192640d008204869540130048800c010700d90708511620005091030080210558901c00000384141c04517228025440c20801180c2d2a070f150180400d8171070090f0480d18422007400400c400c59103c01c040c8441c0f0480c002d850200b02e941100704108050042800410691172a00300300c1c07104148001006115508036101c0010544150700000b450309015002c11450703d4140040410307070110141515048414a481384059174079100c06c20303911283c04a0350440001c003040700040551a1250081040000203049641d607182011909540e0764004148007006c10b0f030f01000c103c4265040302d078150300c202c003010151484101100c0084c1103920140700180c660005000860244490380e4115 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 127383129 1250 127381879 127381913
    0x18010e04060608030f040315050c0a050c0a150903030e0d020601090c0219030c03020f010207030c020f1309080c07050904020a09023f010e040c060f0c060e0c0f030d080a0207 76
    0x1ca803174001d0800c0c1d070380301d81d0b0080c00300300e81c521500d111b940c070000094010f05026000d483d02950900704408400c6525400c006600003081c0b18048501000ca16000400300d18200d42c0309000c80d89222a05010301070754620041c440706a480110705a05a55000c11806d0540d20183d101281e860f46e13018040340b6200d124400d894020b80c0b207412640c101074101100501c0b0b14403030307000c1c0e80300d1a020070b581d98200d00440300302501040b00c2d84800d00061400069814250000400d29a04200099013900481e00c06120844241000181c003800c3daa4080208000078041120414020714040d80494507990551290310405038010400392a0100c580189100112104441140868207085c0547c009031403d00b00c0303084070950b000003103000cbd5024248544075a81200c1c0704149a403500d0821aa20340100c20b09104000c1c3c45151880061b82c00c1c0200a20483c9050003004e00b600080200900c003c4640c115038030030341c4aa0b844560300ca410050042e40b10407501f1005845071880d00f0701c0001d280340710180c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 127384379 1250 127383129 127383133
    0x5120a0204140609010605030108070b07030c06090309090b0420070f05030a051305010305090c010c1704090506090a05061c0c1a030702010506100e0409020609090403050a080618010e04060608 84
    0x100807040d4520340c000303500c43c600c01c0710368020030390380d4030340a5805120a009814090700002c8c4e06210482c2000000e1016034401e1902c0c029500058817030504039202e035001100050000030041061001078018100443ca08550801c15001e040120b880382984403400203405150204841d81881503004617810f207107400c8001d8a60762030200a0003130055000300146002c03d800b00c80c5c0401d955101b4070603648074100c0180100000741c001d03030040d51400802a030403185561003154040c48090f2840190005105821021070582801800c0200714403008000200182c40d00f420411655500e820280c129903008a404840c609a81007041750030065410401c020b1510b920f00000c1c10300060000c41c4980e441344d00800003521100d04002c3c810105004160009840022601603803038aa40202130192006200900d419042c1001c01c0d07501104035000c4d400700b44080340305031485821482541e4400001c441e80c2c4c03a03035094186100c0c88100107000f400700c020f0071080050100805a030042d030103000e070642 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 127385629 1250 127384379 127384391
    0x10080c0417030d05101802030907180209010201240b0f040b07030c050613020a1e030c030b0f0a06030f0b07050702090f0108071703090409050a0605010b0d110c060105120a0204 77
    0x104040c1e0700c0d0b20403407101983d00c0c42c21300050700ea644940000000e4031141070422100482e518038110294102800f03c1c1241e0054541c0040d01e509a904240c3d03203039000b0303140561510980303400642140e404601024803061000784c0000207141140d441020b48000c450001d07101d22980d0210b000070300031a0001a480303000010b104007819046804219030754403a808455050b42d480d00e0703c1400b80074100c0000d4100f58280c00600145440320f0382000745c0b000c0d030501030380e07015541e07101d2182003038241e403040d110910040203002c10000c82d588420381c8814011010f01031145540e50304030351180303181c0d400b9100310040c202295000c2d1258040301d10064000b404103c5506110345078290b154401e106808051041c0c4030009100540f02c5440d504280303486004e1030400040c441400f01a2140c00d100f01c8160040001d140c001900302d116450190031b8025185841ea1980e00441c02292080112041200d40c1400030301c0840100050040c103442c1c4c10b9407030240440480004601c1d000011307800940c4613041c51 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 127386879 1250 127385629 127385669
    0x170105030a0335010f1202031509150c0706150b0708090103061706160e06070b060f060406051c02040302030d0e01031d0a021e0109062d03051803030610080c04 70
    0x20307025058504040c1c04000c0c650344d4160034038011101b000c000707402d900401c46503ea1442d0101103c0d500100500c01e4401c042c80701d500c0c260800404541240424902060780c0c81440501c0c41041510085448103007840f904080c440005409425001041c0900c0000d8420080e4031a4008034014510301a5038142d6030102e001882c0c035640101d51011980c0c000725000d1040e6841410340125469001d8a101c0c90700701d860306c3d030200340500100300325009290812461038130744808005100522a0b03076912238680d803d01c82001103a48041786032040e024014001807015940100e00364080342040e0904400905c08000103070050450030301f04200c94101c0d1740460141e00340c00f08080043ca031088555003a0110031030703021001d0150b0848441d00040348102c041c071900c0d001c4c202c5000c813800400680081d00c11040c05443d203686880c0034410019496506012820070001c203104483c0004030051402c61a01c080070030b5401003441c0b421020807803c00301003400c2003114402c880241040501400e001d601507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 127388129 1250 127386879 127386977
    0x20d0504080a0201141302060318030c03030a0b0604050a091503050706030e12030c030721180b09060106020c010f05040b0c030301030b0c03060d03050708130e07170105030a03 77
    0x56100d642c099400c10001207280c402001070316105c0d44070f0000d0003410184580902c100d0b500010100241c00c091a00d0741e4040010130801340c140c0c008440003c640c0d83c50000582000d0385c040089841c00390a041c40b06002c0740d038460011100b41c8554250000d41640480c0381e40b10b1002c0300b0f41c8080c14038001d0400214000e81e0642002d581c00c00324004070b50a1300e002690589d0644000c80c2e04140441c824400b16103218412503203960025910b00301d0f140d0702c003451000310007110b26040e01c540c203a5101500e604104403040200325404086000644000d600d0510040c4d10740740b0690119040209401e00120310358011010794000c1c2c80280d454030303120b01c4d21213460380e500d074400c2c0026114a0320181c0000c41456091003160322981e070107840421030008c281c1e001d45668101c000c04031084078080c0000c030000c0003503401180080c2802c42a03080b0307505040360701800c610300e00d1404a14200028005020035100000e0712039086602d1728100e0000050134444a0300c0140403115010403001107001500e5a03001c1d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 127389379 1250 127388129 127388137
    0x30f09020d0506010f210b060a0306020c061503010c09050114040f0e010503120a02030403030315031208150d0201020a140703081201080705040e0a020409060b04090602070b07030c0206040b0a020d050408 89
    0xf004145170103460b291010407106492960041100ca0501c2c0b0b4a8800101c1900c5070a410400c0500400c440c9502d03079903403806980125040d182183c0c81001008a810401c0e03400000b82401030b07000b04902d0a01c400300804a4481d03006080c107000f40d21204107101010841190002c005130b101c2410859210021119944d5080c85024403034030960700c800800d180e0500c220b501e082943d07000cd40c41d19245980603805030515070b13045909082084000408582840980154144035680e40c520514040c40085109190055903600030b1003040c20313400050340c0002d0810405500803a102d8000c0d148510903606c0c1c1440d0740c0004000d2900455016003901c03980e604070341aa40280c054400050301c0f1350611044038404031020403c0c0e0f004003103044c050b00f07082c1e00090300c070b50107a1408190074440002107003d4400311030341194015400034040c0c0230b01140042e0705800c5410b902c4c0074044841445402543c502000e00064152681c680100b2005901e9904844000807100800e0260749020b0901e00340340c0e00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 127390629 1250 127389379 127389389
    0x9031015060509010f11010b04020a030c0f09080a080711061b06010b0f16031403150a05030613080a170c0a0f0e0604120606090f0504021816030f09020d050601 70
    0x4001402140d03190055003600d0343c4040685d41e5507280c406800c02125400c80010904041d95624442c145640e1547d000400d0314403a41d0f1402302c1c000d0303074820300208000400c007001d200f08501000c5c1804418400b02c3c4440c04a0b030030502c030030749507201801c2848100f111071400380e42c000d83c006942c0442e00900742c150001078032500141e52480c5e03690202c501aa10407460042c0c4141c5040002e0000701c058003c030713042d07400d00070304e4410341111400c444150250720030348001c09100350400000d041072910768141c2d409000c00b50081d0055041603035808806d9084030070010710555011981141c0d1511a003c09001010600c03c41c4844c0d040020741460254094041400000e000c160840e80b080c0c001e0300314050189000e044649450718040241c0e282c01c1c104007044031402c3d140c54002490410380d0040b40c0112090400015041c2082d10420a240d1040c58070301301007070044410007140c55140002641c40d05010b0401040004408168400400f81e03a44001e5202008210810078090000f0745281615 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 127391879 1250 127390629 127390661
    0xb03060a0e0709090f05060705090a06030212070503130b04060c0e060a0903110a080312010501030c180e270d0f0201091e03030b09150103050112111203090310 70
    0x500d82002a0041d81d102941c070200580c400d0004001819207a0f10281e0b1550050142060080540c0e4515080c00c009881c030a00090b03011540c0c84040c41c1a11420b801012281000c602d000d404c26204450007000034403601c2441004400181456801d80b0f01c509210ba01c0b900486091400c0c0c42c00000410b400e0900d10300140030000301441904050044410901c80c40e00ca44808038956a10350a6025850080300d4000e03100c0c3c00b00150502040015120038400383c100c42c64250b0500c000101140c4852200c03108108101032314401030301090408005441418000407916a24403a28410403007860020000546214540d42c01003c0c0c0400c004000174896900c4c00d40d0222505022803d0341c1c0383d1800540a03200c82c042400c0200160b06841080130320034240400c2080e0f4050011740410070468030100181c69164492080d50303030611500c1d026201c001c42c0c003191150b05da00c0d080241040207410134016014404800004902001500c2521200508a4a60039121444500602865016505c01c0e03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 127393129 1250 127391879 127391881
    0x12021c0903060b120a0b0702010f02131a07080d0207080f040602031810050901030510030204060f0305010f05010e0a0218060a2d02060f100812180108071b06110705010b0306 76
    0x640742160303104000750078135001005c038855151100d09000314040c0000c010b565030703a0340c2d051071111307180090a00c814841494400162601a5400840d072004051507a411010012800020300d080c05849250940100040e1a89514070700101d1920a152101e240341ca0045800580c2690010050800045500b09400f050016030144641d0003000d28060001c14002d002c17003031295101e80d000503800034040c205140c0d002d40d03036004501119440c0e080800c60f00011402882400401d0080400c8182143c004101c1c543c034041b0141c0c031851000d09000141030700098004030090700c94000b80b4a044d00100519650f00b002d807400b40c0b000c03145402007154410300071840900d05032031201400d00303002c0310b4001d441c0556070b0084a401036a0300502c2c0c94a8540100f00124030f021040003042100c5059141030b0b0381e00c0280d14090748500c5148400c0b281088000d00c20441d007554024035171511f00c011084001d200115515090f40a442220040444560042800002e00005400401c840e00307041d4162401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 127394379 1250 127393129 127393151
    0x902030c2502152206020102070302060702060403080f07020a1407090c0c0203070905090a14010b0a050f0a09110c0f071706070806241303030806030f0a12021c090306 73
    0x42000303010070203580110780844112040240700024922044c51324000d48040008001520309000e0301d401c80f800503940030864800300b680400910f038021105000401146c1b0700b951b001806420b008011803030240000f408a22058000c11500c0031080d80180169040c04001d132030283c1c2c45d0304a2217500300c800e0a102c44170054070f0080b10711080503600034028003101400c0042c8600500300207810031400c0d10032002c0500103d600d8140051181c4000000030464102e4401040003001c400d03040359100b000b02e0313a0000b05690f60031460f94101c4401800100d14458403100552240c000c08440402602a000b0005456100403032140300340d90200490300106076503000102d0b41c6040845111313010805010128055241c032490000031454441e00082d840c3c40c04120500441e08a890380e0900e50103220814010150020a2682c1c45171058000b4091010301442150380c071150454054610394003040040c142d07030f20a100f0300340750466070b581c3d5455800d40200c005081010522082e94068908042440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 127395629 1250 127394379 127394437
    0x5072d171503100c08010902030606130621060620100c092603160c050d0b0405010507050906072d08190315090f0921080a0902010c12090902030c 64
    0x4d01d03a0780b250344291070b85c0c2c24005e03044000d50020344925030208007030006815400809007150701420044da0b44140403c01005550086a4145a41e802040c00c11030107111255110320200e00c041d84609440580d50710744030610342002d442103176190030309080226003600741c0d030001ca0030030480301e0988852208480c07250301420742c2440719204840e15081007200302600071042164001480c040c0c80b155501950741c600082d8007034038a603401c69403890000208010312000703124050740072a440c1800c2d450021030000140b45803041e00c000420001c9104be824000c0687c0c0810712104000000020407201424106800c1a402518003c03c80801c1848040700d618070a000d4071517400c101d224080310b501c1c20080400040c1008042d5150307410b95980d009004158100c2d101480c40220141c1d010a15500c0c1e1070090040c40c2c020300340710100d03080000001c01170f40d001040b082a40c2c0c01c000c000c040046a54400c0311404080d5104210250012042c0101e0340c03440402800f2201c040040e503121903412403900d078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 127396879 1250 127395629 127395641
    0x30b0f1009050d0302010f05011205011503050d030f02090603010902070c14010c02040c02100c03020d060e040b06060702010537020d020604080c070f0b0a020105072d17150310 77
    0x24002910031a002c00003800c0407030207021071501c240000302c1c10107603c0d403903c42100c20991001071440b500202440a100080c130079106400007948000043d141140c036001d0780d4003d01d141e514101603564000e05079248203581650450030f001481182e40307507980d40300400071f9004034001742c8883d070704007200003400310011860340b52019040e1031f08668100b039a000c000051601c206040154016184034000b00905881400038250341918010380f60841c0d8481002111103d810038005070029205000214542cad0765091340c00101190798565480c0c951004884074011400d0325100b50940d001c0d005400e520101c1c03182440320420702000305004410100300e954807a000c85400c0903801610101c0c0110305014010301c600c081c041d0440c0c807055580c80218211000982c400f5084da5004160040f151740d081c082c50750810820314100130a40c1060407a104024141e03808411002c03030041c20f02a641d401042451185401001212400d18004055040c2e80c04414422480380c01001d614500d080e030144211 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 127398129 1250 127396879 127396909
    0x30a0215070e030105160306080c060412030302070209010b040806060409110103150b0d051509040512090a030804091d06090a030c081b070806090a1a0a0b090106030b0f 74
    0xa000c420500c0c01000040d00d000781c050800c00100c1c1504410a8a00f400f0740740c002c82d04140310350046100b10400800300c03441c580008001d17401941b403103ea1542c402c0c05890540348089050b032085402da1070241c0092164000080d0810000f2000088007050880540116180d81d03040c0c03020360382c5030344c00c00c0201d60075124014020140c54004e00302c25486540401c4168000d000090155a110781c40441d4030341062070300d0400d560b11f0303008101401c070190800421020f4150340f000f407182090f42d104c0e82c13694058121500c2488000c54408040d980341d0030781d0b4000310b4026031600e17a603d85411a65018120740613801c81400452004245166400155180b0445c04100645803651083c2d42c02c460812040600307440710f81e0107020f10081c407401203400714804001e800003803c03a645400d11160030500c008210503650740000c58140c0110f900e80824003008041c0d9500582540d45103400d0340c0c000c00c900303103a454110740200c2c00411a241c06a220020f884802c955004500742300500701700f0101070031022 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 127399379 1250 127398129 127398133
    0x100204060c0809040e01060b0a1106040c0b0315060301030f0501050f012303010617031b030c0607050901020129030c0402030103080708070807050f010b100503090705060c1e030d0509030a02 83
    0x44a404100b0000107802c82c41c000400102d150b00c0f011600034291603541d0082c10b00b040000a09000080d001000a1514881400944450719141c0c455820026092046503d0b10f60008005801842c0a402da8071079040300400f15610381d6143d040403a02c07510400c504441a40c03800011400b04c800750a0b80d68100d400560401013502400b20100c00c001c10244000e81e010744d200c410100740d4805080c45c8507440001000110380707607004420400154440e0b0760313510490303420800655000c1c440204103c2c0d0f2010250030803070b41c0d4110100040380140f98074070020b200d8081520a40c228001d100031115804c15044044034554041002000101d10082c071001340030300010400200011a600c001d4902503002e140c0503410301c94241c9a0a041280d0740c0920411b82e55141c000501c9450816144151f0b0720461506509600c0e0a1001942d284d0160046138070030080481c00d500212802c201c0781c030030001013000b22025250783c1c0d40d2141c0d8070340103905018441ca00f400c3c000381da02c69000040e40d4103200c1701e0340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 127400629 1250 127399379 127399397
    0x8060901060e0303070605040803160f051207110d0c0b010609050102100b15030c030603120a05071b0801090309081216110d02090f091e250914040510020406 69
    0x1040c1e902c4100e90b08899010301041c0540f42c0805d110b8452688201d0140001903601c1c54244044071440038003180702d03070501a01d501d0350019580d12000b61260050517801c100b072980c5407808150303201c001d403100001091082c2403207501c2180d07003c0300b4103071960720aa21201c2180d032580c6050711200041d00580d40140c0c45a00c86a01465440e00050b503d42805800c810300041c0600b64a03c10b036108890104294a0000a1000b203003000c100004460602183e440d003420542007000b08648510344000d00078072602d0004c05041d0380000c15101c0184501802001b402c2c00c0e51501070900ea0840c03151b4041402040070810780c6840482c121882800c601c020102c41d0140ba94401c4403c40240101617000800345402c07800688685010501034032407644c0c1000300b450801c400f0b624003c850242d1001551504181c10080700000910840c0801b8808003020310f1a44006102003203045a40040880381c1024940c4400c00803041645009600031400c0c0c031001c0e0003802105080e4410703403103401c000a943d03030b07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 127401879 1250 127400629 127400639
    0x91b02060610120b060f130504050f040f021503130303061502031b071508090606150405010c060b04050f0105090f04050d0f0507020306070e041d0709090f050703051c08060901 77
    0x60300321980c07504010000100c1c00c45440100d12542c00245089000300b00018200d1f26005071000440001c100c120303001d11141c84d114030010b15014018000401c0b00061029202c01c55072054410f080105442c034120340c403071400b0740c182d9561005904040d804640741c44400704042ca900445048081c2d401d4005600c1c11140701c0c501803c04030301c3e038040b00090150100102c0c11062442406001520740d84e03a04800d8202588014180807010300741a202e5540003260078903002d01c8c401503a08882090814000e10601c504100018207003080003258007034584020080c00a1855640700d050b108161480100c9033b44001c000001d444055502030300d990302400e4a050201c3c4180b041d144092900c1c40c1c07a5040c44060f0f80424034041d4292105404500c0c41002111642840e01c501025051104001c11300c03505020b02d1540c4429590240e03100c06078980c02e40c44103001c11f540b045c0036440d03440303c1125010f42d903900f809a1200a08245088a4050101d907030380102e10450700c407405001c005045940c40e0b482c01c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 127403129 1250 127401879 127401887
    0xe040f18032f0114010819080a02161d0601020a0506160507020301050a0f2304020f12060f010509070504050319060e011107050c04020301080712021801091b02060610 73
    0xa04182801c0480c0318000c00c241482c40e0901030902010303100041240488046070312400741050700007542580c02010b070001d1904450700698085030304030700107513580c02c903400c1c4c124201400622086640e040b021000160503140381c1600c1038140ca1541051156260306004980b150703003400019001d54450400f044160014103100c882d807441c10b0030500e00d0074126034040390a643c411561464450790324805d00059034220300402c2c86014403200703900c1a5052901ca03540440c0030113000070303010b080c050364105c0154540a48110541038404111015450402c0598100500c24082ca40c082e801140c0415291401755060300d007a20030090142560141c2d03140341d0b0485100c0c3c0380050324441e03210b541d0001002000c0c420752604480070b03500107585403070b5400d04600c0c0c80840c0301140e0080f8410001000b10450100703840c1305403580116a00040c1100340009801e07002c16440001c24501001d00005205207954451559010032400315070540c41d41d900180c0e01c88034110790950704001000c0c4124403040c45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 127404379 1250 127403129 127403147
    0x10216080d14150f060922020403060615030609090804031101270602070e04050c0d060b150702040e010605060a11030d0903020c011106090d0518040c0e040f1803 71
    0x14400d0700007841002d007240305540b54001c1d41d01e00140051001c820699040409010700c00110135901680b50101280c04a103005510078409904d00c044c03161003d0b002c11803a0110343c0255000074040c4011503c0f45840c00f11240226088000310340340000000700ca4219000c1d01c00c100d0380010506043c40c3c51910340c40021500710b90a503041003041d03000e01266560490f0b400c00607041c0c1050300b5a482c2d051900284c03800c0c9e0f56402000b00082040f04000c0003440008001038004021b680a40d0001c0f01740c90070a0140601c0c8424640c040ca00c030a0020352598044003400d1481e0003214188038892250070b49508940c3c0b64002c07540c110a041001880180c09410a481455100b104507403410011250030002c03505810012001a0451040c042c42503a01c60302c0034408911002c041c16840c01d00d0003540b5910444424680144800400d090785c500e81d0349407500d1407002c40a841071205041c010001845403400b101e205200da480c011828130808031710b00c1007107003030300f0343c114009142c10341c1e0b86040d242800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 127405629 1250 127404379 127404397
    0x30206040e041104060f05030c0d080d0e0313080d0806040c0c0b07090504020f0d050907060c02220e0f0f0102040303020312040602040506160302010605180a0f02090d050705030f01021608 82
    0x2c689001c2240c13190b1080c10014034207240c4612041e8185410581881444d40c2110b1140f100c43c60310a01180c141c00442c0e0050b405468000b441c101c00d10f20880c2540584000ba00d50108800342c0040c1c03800f40841d5055003008165030f00012075540d001080111400a00c100000410982c20310000644a4420540021982c140380b51015541d50001d001d076442403c81c00391400001c6950307491607040d402655000104800601822818094010180440008041e21a1480c42d1030010b0749107904024014240f115401480704160380381c1c2c100d66a69504520604a20459100001146041c030039101540d60645c051443c00b0900c0744064030003c0c0141090352400e03400c110015096503100020305844512801700f084440350360402070308589561380540d0003100a040d02152a80300c1048041d840403500d000007500030341c01c144050003401078a103034503040010100300c1d20a000c8002804011a0b04c1107040751895000c20810500340d0241c0701101e1039000b0502c41c007200091018003c0c0950300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 127406879 1250 127405629 127405643
    0xf06010504080129060405060a030b0d0b0f0f0105041b030b06041203020d12050103030f120b0306010f08012007021201020f0a030519060b030c16050f06070801060207030206040e04 79
    0x50315461454215041014644100004000b84107820074044d407406403442d2045030720301d0900c1d1400d0080b480f01d102d50010700701056525045c2c0c00141d501c055410f416103802a52143c05841e00d4910584050b00c2962109030b03010004000084070320742030103401046401a0f0108461181a510903006031018040f035a1303101d8070034000411103004200180543d02d000354010000055454030280070314200c8111118458200310041c80070079000104100c00020900d018103084256600d4031000307140d183c000644c580511000060070a21003850300090790941300003000b0001d542c215548a20b00c0d40c4000052004051010501500c3c0c00c0070354410300070090002610b80564990b00030b140d50b101c2043c40021072341d62005c5c000c08a0740c003c44800848805030081000368141084071443c1d0000805111512a0000780f0501c12065086c40070402c0b607101048039610146a585140c0f120350803074010b40040c007010700004482d44009500012290003030325451030310b800c2940c40303071300c1c4200100241c2d03806c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 127408129 1250 127406879 127406887
    0xa0c050307210f050f040b0d0e0f010509101a0909150f100603021303080f1213030201052503020d180302010b040501050301091e020111030c0102040603050c040602060f060105 77
    0x40340d0440c0c00300e0307003110b00014440010898114040e0422900d11204001c004003400100d900395503072000c03582601c8213011600d1716035012501440151002140011360780c09400440030302d08805410007400b525000742500c0c0803401c1240f00c01c01b142e0301d072503e070700c0000f4851100719a00e041c0042c0d520340000801e011344103100c0390602c0d40000300d8000e550107525182540c003000103a230381042c0c094010b00f10500d01036280868619416012410f207010180a10350006030b1444284220012545401c0c1c548285002c60700d8000c80d80e01541d20708940c01e074095401c0400050040c00d403885004082c02d0300e1407600a11441c202000c40c0290800d10b003003900e140d654001150b40c00e40004814401c144207900100310b80030b2078010f000c1030710010f90200e8060780c1000c82d0200001d05508003640342c03030100c83d07440e05145201e000486417529031140d0280c44d800002500c0f80b012506400a00646100d81c130280031680715110745444038400d0340b1a40006810500c007003a2405401e00e0400d0300400149409814 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 127409379 1250 127408129 127408133
    0x11d0c070512070b090c0405010311190503101a06030105060a030c0210142401021002220308040306060503030a082406030109020a0e04060503031207020709020d02071104110a0c050307 81
    0x2c030341c041c0368141d60340c100c10410401e00000401c8051000ba0040e03906011a5265581e04000c55400d401d0281c0728403040100707071805004905880000740b000400300c8041d24000c1080704006c10b81449107150481c0d54211000150400ca022241203401c054040c83c07610103000411802400e507040c1c0b03c1c0c2140100c81074400c1009043c0a06540c2903201c1d00383c0300c001d04141e4640940c1d0340c0036100d050462900c00004800e40c0c3e070045042400d2540d85800542c1e00c40c05403030004400c00840c10320148006400001009100000c07003d4801d4078407400c02004059101c8003016504d014030808000042d02c2003000a5584203211080c54104030307003a0346084a031211400140d02c9030426005004c40c294042003804100340d03c042c02910007003055904100e4036040c2001319840e48034444242204a1140000c1028030f8402c1040c6402400000303400c540b1041845800f00280d8000a01694018041d0480e48182d14003440b5280d4041c490702d400a1400b21101400d0f42e049a85030320a80751070005000c4000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 127410629 1250 127409379 127409413
    0x140f070203010f020a030c02060f011214010c050a20030403030e0d060f0c02070f0302030304090c14070302030a120b0f040f0e190203010c0507080406031107200306011d0c0705 77
    0xf0301201910096201c105100001782251a00d00ba648115448882801250080040001d05403000a0105d140910941c03c01d9100ea4241d00e00b5100b0540c130300182102c140c1d81c40b0001e00b054240d0307540d0b080d02201e801071030204c8803c5000c001d00d0580e0010401040002d0007075005048060b000f4020101c2016030b625084101c950042c480c6078050748482004c03890300d030305001c1c46002e030511a03916001c89045401290303a07400346001d05907020f076940495a6140e0700500401418105100c9101e0f5a00701c80c1c90029201d0f04000e401c100030404111705c43c0004601030155180028020707102c401c9580b500b40c01c000c0a407032940ca01240b05a524076030001402814004521062800c0c0001c1c40341c400140305050845e00c019503240c0420006100100002da0240105c8040322014500444e42c0403016603078940c01d2180c40d00060180d100c01c451101003046100c10012400d004038107850260f039868058402e4517180c001050449003030040040c164190010141050328000c40891361700c2c81c5154a094 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 127411879 1250 127410629 127410641
    0x15090606180b011107030f080711100f0201060b0309030304200a0e01081b0102030a03020a090f060f0305060102061e0c12090a0c060516020405180115050a15140f07020301 75
    0x144189481c1d804110382c41d60032011301c4190030003000040c090341e403442e150041c80000d0494004c1101e500050000140321682401c4a41040300400002880c1950b00d405000744039560f2030702001d03500702800041c03809240740c2aa072281c00550041d5107075031303915a40c0e240d00551007102289464030300211100c0513103441040d00d0107000041141160303941007501c84c920b460494403041c00380c40f042c00b43c80907569034040300b502c5030a0701070f0902580329503041409031803014058100f64401c480e0854001809540180a85200360017520100f10f41d0f1600001242c0b241c07021a05012492004100c0650074409001c42a0340b0280750a845801c0072004591007861500c140da08500551000e01c1110500900160140003001c99040c4203103044540402e00c648007640080103440b807a60b0f44000f0300c507510550740040e01750b2030000081101061b402c4e0302d02203025450007151701035012070501090641171f410100c0003404068a4507548414441c05100195014401c00d034114a0280200310044e01c00f40199 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 127413129 1250 127411879 127411919
    0xc0312020a091d15090a0603060207030c02010305060405011a0a0302090a1203090b03100b030705090409051e03030105031c020a060f0903030b0d020d02010f0201091a040c05010203040315090606 85
    0x601c4210f1824401c402d41e0700181c2c20b0401d814480609000d54803040d013800d54032030308080d50500003981e1403840801c01020346134005480c0d1800000c1c1c072401c15511802c2008801d01c03d8030f0801a41c0c0300c82051000300d500900948001003c1c9055102c12900040c000d00705034070552401602c0c020b40440416140c1c00940d00c1900040307030300907420081541140501c0041d250304c9800358110300c1c258214443c140d0307251040035608800040454000c0384923a044a2115002074028804580305203030280ea1041d00d100c240d2125224141c07400241540441200d04a401c000c004103201d00c0041c00c0060b4440341d61210800b0b42c4102e620000c00242039018401e84682c4034000090754a005050160a5443c01c0c91064400c0c83c554080e10010703500c1400e800740290302807900c0500030f00d0014050340100880754002d80160084003180c1000041000b481344a0b42c4245624007420769240010390703403409a40002007050801c10b41010706102c05610960266005101c00f050090f941e021303085640e002c01d142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 127414379 1250 127413129 127413137
    0x605060415120c210305130b16060f060303020c1002150103120e01030608030a080c090604080a06060501020c030304090b0a090509010e0c010f360b031b13060c0312020a 74
    0x740000f80701d00c00340704400130800804946841007007403421542040348010010b080c03060224000c4c41903402c444030b820242102d0600c86a541c07510b076410b1131461110100c00c448150a06c0d80c0c2c1403800100d802504e003203d0345038004000000c003030340c00c0200021840c07188100310f11841903100401c41145a649008500444070b11000f1824054028942e109100001d0305044c100785003040381d10400002c68140c140340d03240181040c1c807642d0082189101341c41d40140d1009000c100480c0700307100821284501407141404201e01c5070b440d0016600ea00080700944d0341b5420a000070400c1040070b403c0036010031001040c2c8426141c94a03582400c0307030700a0310069010384d074407200c008049004100e404203041003420141c00d2000711043c01030140d11446260b05c00c580041120a130b410381a11900c00c5d203440d02080b89480c03244c980d103148406801c00c46140c103002071070b20640610703580c01000b1101c00000040482d110301e0700303016043c1da040106c00310441c10411166072126052000341b020300080460b40c1d031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 127415629 1250 127414379 127414409
    0x307170106050906100c030e060c0c09100e040807050c130903032d0209041112060310021306030221040b06030c030106080c0f0616060b090c1201030605060415 70
    0x244608403003041d04043c0c081c580b02028002c0b159280141040b501080e8a4890a41500b0b40760803141c1d010b0072000030303401c5000868a02000c183c00b00c1c1c0e14204007030982d40c4204075510201d600402e4180c6104410846401a000c00d010518490050213268014000c47d9018801000803941c010300710248010320990b149400000c05900d4010b590380300c1020156a05001c051405100d40701c0700c0c4441c070f0201140d0004103000c02d500c41da0410700344090041d01064584920054403044a0303c101c0390944240030354110040000d0030b41c401d4440807201030345268082c1d03040001c2034000b90b10a1003403c44007104101c180307000a4815004134403d91003002000e0721030400f40245898210106840d9101386d042050502020360006100034003a0400c903003136841a9a9240030443c14450b9500c0101400d403079424950611410b60000c644840007950380c2070441d032f00d041c0c1040301402074080c1c400c0480f0420300108007180058101c1a004200103200003000d810300260025004410307806480c42c562400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 127416879 1250 127415629 127415669
    0x91503061a07020112020912060a140c0301030507050906130513120318120e1504050f0a0302100c08040b04030311010f0b150703050f18040c0306060f05180307 70
    0x7607400c50316580028011418448240c0c0041c001100000f00c0079840c0317030701117040c40b89640d42c0d18040100c04134140540307409003010001f01001d80090f040d10605004c1c28004075011610030000c4038100d81c1c020000e801d100e400c100c00c01840b040702500060340921040c10a00700942c640c0700d0140207141440e038184141d800340c034204405412010f0b83d0014149030400c1c60201c180000341c0710036220b80c814074403500781c040c072001640c0340d01880b40303030582099091141d4403082c50200000c106a540445400700c03041c041d07204028400c0000d0100a400401c8262000301340c030301483c41d510f2518410101d003410552943c0c404034090300300780d00903000698504014840b501c000e1144200d044508281406020280c00100d5012030200c0d007081d0300b001d00000c00c04285803181c1e05803201c0480c1182c0e1290f071105030b82e015051801c003500c2d8141c81245000091000340340030344591400c039056a141e803030410660b1381040d2441c1d0020043c003c415400380e2510b40003a5401e010303a9015100081030742129031001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 127418129 1250 127416879 127416899
    0xa0602010212090705180405030d140f0c1c2c0304030303050a020403052e060e060306180c06090d02040504030801030b010b0c0303010b0904020d060335070201030c09150306 76
    0xe02402c81d0f03a04800001d00050319002070081c0201800d8101c1d108031784417890160b00e148158594070f00328624100d07010000c034003402e040034015540309000704040e8540c409001098815000c84000004061305400048000303074201644188403482c000d45021819628000301c50709800825410303070000030b0144201601807090540141c05071008601f000d0075541e030982c0d56905408450082420045100161004240030f8450003400c03a1052103001c0d46d80002522103402951614030038007909000403102c480c0c4040d540c0403c0e40c6400105100360520040c09001d501c12032840390801010300b15140961201d00409002d90700c00d41d5568015032450414100001d0180c000440e206402c2154000c007020000c2541e0658150922655031030f100079001400a104501401040500b4480e00005110341c116a0805c0341c4007400d0148401c5602d000b035040c000b00020354007103046e038060054201551007a8440e44045c03080d400c11003019034466101c64003803410143c003200003035110a000d20405880c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 127419379 1250 127418129 127418131
    0x2a120709060918020609190b03041509120f0c0602030c04080d11280204050907090e0102040f18020c071205010605011407060b03070504060b091c02010207030b040804050a0602010212 80
    0x5a1401000070342c40c3c1c5203051072019107035400a0300c10b04020941c4040c50791004080001c08100e04d5801c48020760f200400305890708100d50070359101e0040c442401d01c04000340120748038564810b0302c644d0340c0841c4040550740360b41c2c0c4560b900c040000c8008160001113076880114010110800c1e22074440b854150414606150145028200651041c0d40300500100040207030031030b040110703200c7e410b10b54094010f0050440c0c100107507000741480b042c41700d0040040368030300a4580c0810207105086440d14000e00740e105a02c100072002161101c20881810b40c2c05200c41c044002200243c41e011072562074503e08130300c41c1c104584100c11441d0690412001f48074010040c103081c02d180034a03200380c0d545008140500c7c0390203000642c4400400e09159410301500c8007504005108003c0151034040000650304242040b6003c1e55010a1104540e900700d840740402071f0341680100501801d555601031501ca028000b00c88120052002080590752003d444002d8900c1e6800140c44240d0f403e040b9041c80c40c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 127420629 1250 127419379 127419389
    0xe24010e15030a151b0e0307090e030406030506040905010e15070f0e06090d050f030d0b0d0203070302153f0708070c0f0b0c0301030c0603020c2a12070906 68
    0x16550125222500d020402d80082d0760842c52071001e4144c5030913150060b00c11380300e01c480041081c030308040055030031410301d28100300306130b085481c41a00c0b029035804844501003000d880b40d0060104005c101e02c643c00080d40000040d0005c038501140344d41d01c600b901c0c48183c54504940104900d1005201285001580002c10346481110070b0320341d0b00c01816451440c0981405441e0000c4e800000b46c4810050f03448071039124084070661841d03400510b0b2a42c000a64a80100c1d04162030390040e803800c44006507407641c0050143c10514030716801c000f058000d074100b00c881c5072814048500c0004411044026400f8403520b503090001071400c1e130000000105800255500b8070b01d0612102552000c1040e40c046c0240c18650140344a50078141071030940f020008040c03103c2c0c030b0301700224141c50310055070480f440380040c80c0b40340740c481d4415010781c0284086400141c1c8410188000401c001c04104502416846a620442191004100200b81420465441d07610078541003042044034498400281 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 127421879 1250 127420629 127420651
    0x1c0609030f020d0e010309030509030a050f0c060414010503071202030c0306010e0d210c0804240212030402011808010e1b030106050102030f0c01140103110102011116060e24010e 78
    0x14140b04000b07048541d413481120b04260f603c5114004040c007131070403140d0f419002400c40e0301060745440c02980d208120311030b420b41409034040c80d40c2c482c00c001090b5004d81c0c03602410580b900d50390400440d40c80e00018500010405601038103036040b10306200440c00b900e41e0941541d52460940005014021041103040c06a00003840310408241102c00562200c950403c80c0b08081003c1503088a0910340040007034640500060b00140203a4005070403090b103c10704003920000148020203a07142c2081d4245043c03140020000240190f205d0100ca000520940c0c101204071a00d840d03006084800c0c14a480d010396001842903140894483c83c2010b10340403c03402400043e04100000707440c1d000c0d41560341051400403400440e005020b412480034504d0a640300e40315907941e82001600d4102031200e00f4055468000c103100c88014400c2199001f498801817090b1003100c0d6034600000380f01000b0307049a1400f41c40e122015543d110301c2102d030a107049540c0014154180440c2194540b0302a001e60066 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 127423129 1250 127421879 127421893
    0x40b0d050d0309150204080c1002030708030a0b04090602040902070b010506040602030d0b0303071703100608150f01090b030112020901080f190609080403030914030a02031b1c0609030f02 82
    0xa00c00106200c44804619003c18007051902d000301e000300f24800790b0138100f4004100820a070f100003c1076018a002101c024042a0180328141d03180d101d203020240c0510400c10021b44000c1441d080307003800d103c01400024442005440d51012030b003060704514602c94002800506000c0004c0310b25000d004112503e51800b0300d0f01401950324869403540da0b040c1030f15140c600860b40d40c24416560175a4200c0d4419290701e4042001040701d90088660480403410000081a050300c2400120702c600308611140b05480703007042c10000070800d10074208d410402d05070310108000c00310702e0207103000380307a201c010503400c3c0381510410142c26416000f03451290b10175a00200c00d00302c0041d920102042d003081040d0521100d080910140200c0385002d05000720000d03000040550040055007150550a10b141401030b8640401d61106002c440195059000151810001140000303008840c800200704540003e40013a85109911311140241d501940d1007100c102456049468076135441d081340b01501103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 127424379 1250 127423129 127423133
    0x110405011d01080114040608060f090616091403030c120405040c0309052104090c1e11250923010806010b04090914011802010201060506040e160504050d03090302040b0d 74
    0x24030105105500020f840c51704003403902e403900d60003140a441c94206a800d03620303000030300000d040d00640300b01006204400000304000c0c00348021000c4224659141c5000c0f41c0303009003180c48024101c1c582c540c14041000351804110b420807203200851805059a511a8500f0f020041210b03103542002d010315040c070306404005103020440c030556451030882d104040c0e4180c58160141c0c029500242d941b9171070f040c1944519500110810fa490040f0181c01d00f100c65203500441c2e1580009a2489456009001510100c8442d0042a10044002000c100e10590382c40b84070007542d11810007500d1000d44002441103415030b51003214094a001d4004100a5241a154890f24410341c80b0f0210219514003042c03040007080310b00ca0701d40d021130000034410641e88041e040610013400e00100d0156180202c0010079060040c1614200c0e22624220000c0f91b482031151203489000b803251078100b00c000c00011805a65006030010114041d9581a0360b143c02c610502080f1a400c2007000e00c04e030320344404000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 127425629 1250 127424379 127424387
    0x4020906030a1518050334031e05090a1805012907030201090b04030e0406090605150306040615021b04020403080a050a17161704020906190306110405011d01 69
    0x60151040e000084030349404c082d00070740e0030300494001c0113070000041480014280740580d051124469410701d8408210b0b440c003880d0034060030320040c0810743d410ba201130302e015100c259460920701ca080c15443c1c1000040000c0c60b080081d040b00c840d208074080c0640140310b00784070319805040740e0074442d22407040c54802d411100d1151110350014803c00034949041620170340103008a2a8003005000050400b403801602400c01509a00d0290340340950000d40c011681c0144400c8600241107240c1100c046031890b0702c02e41c4010101234111781c0761b2900146540c620a050311110a1a0b400342a20301d011a000c0d1121070300f02c00c1c80302d03c00d600620080c408510a0012660460201c2c00c1aa548021041c01a04e818008041120001f40c1c500100014a8844c1c65181c0c0d40309819680c200041c1c015501500381c010080c2c6005c0c1d00411040b00103181420440401881c0d4285d6440d1038461170380d640c1d2144180c4001c00342c64149100007150401665030452960301c4c82a2901d03103120f656a4a28000074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 127426879 1250 127425629 127425653
    0x1003062c0c0f0f0301260a08161a251403060d033c030203190b060412080405090108060f07080601140d02040617092d0d0804020906030a 60
    0x881018070006291094000d44011220305200d050107032900c943c2e440b4219548405400d81c64550748402401000e542d02c0d000c101010503507482030800c0d04014022460b00c0350001c807132004890040d0251980d811103264140301c541304405501461204188818251040ca620310140001b88a040ca08004110300395038141c4c2c0d44540e00740d403409010007043c1401c0b5031031408540c50000c170540c0c0940003002d0b00c200380b0b4013844400d40d828a40f41e200b40e100400720203d100440300300da410005c400b505d41c05100e10750404501c1c240010402820640c075404421440900c485084941010000e800c10040c00c00d806c296004080d26000f5142601c1d245100342101c901c024110030030019080c0c00201a6801622121142c0c0305000e061502d03160040c080f50000c0d03000d07003d41c1c00032612502921140d00076154040340b042102c14080d2917022200100003290001c078152030404601302900d107071507101e000c004000325558241e40303038000d5041c01d006024810300302621050007074220496090100d01030380d040c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 127428129 1250 127426879 127426891
    0x62c01060804020402040312020c03160e010902090102070312030605030d030b100c021c030c060501090207080a08040507050612190203150f0a0f06020607120902010c02090a09021003062c 82
    0x110030076a8882c40000d00078880c60300014050303000010908a40366002071004191542981201c128580100700c0e503060209520480d04140c070490b0041c089402290054060114180121403640b074603a5100c541e080d00806010700020b80e01c08080001c0d103020080c611280c06c0754102001031050140100d411b100c030b001c010500348103904a040c01151200c40d22016840ca8503011414403150b01d00d4020074066403484161891400e0a00111751114a8400c07241159404440d00b031030486030381c001b40c464180081c420744190040080000d0a52030b8031005211844010903040d42c40e21b0403211030041c7d00419641848900d106104015014035140d0920141010445051038200d101c24001200020141c22a401c1110340d4a0000764590300000c1681c0145040d071250405d0224000d0498116a00000082c0c0002d048542d5240507007002411644c100d0726200000c40d0003401600410f00c000d041c0d03010503000035620b030420030480d18680800310505040312240d10750310515002c642e110307020142003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 127429379 1250 127428129 127428137
    0x2030903070303061d0f25110601090c0804030804060b03100e0d0315050f06090310091a091203090a120f020c061204020906011b03030c0e0301020c100b0a08010906062c0106 76
    0x800c01d40d8124034844001265187c40070717508402500b0b00100842c007030407140394440c89020300100d600d10f01030040355442d04080d0303200c81c066552500c08581c5914094000d43c0e5507030380c6110411240d1401d011011031100c448601040b21000104100d02c3c000c1456040350030585445460318a0304000702c46001202e1084070802e140401c043c000600b98030440c618503505104004d80c10f607032144103030000e203615070080444d1920a8003174580c801005004441200140c0c1088190481c00026217000e035030031508103801c4074442c0095a8803a840b86690740114404660580c4e103d5010796810482d483c1c44000644003c3d08081c180841c440603e08040c4c002407007107240c00c0006549910600541c50032182e8074030400c440d841c960401800074485011300c1d20002d0b040b4050305515040c14000c40701540a8400100441e480440b08807001704810b49240d5404185698002090b003001d020300c044550060100040180c07800c600307402031368042500745000301e88140303098118280040305d044c11507a442c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 127430629 1250 127429379 127429381
    0x90f080327030606130204050301050f06030f0d08130f080a0206090606010507170f0f070807170702031902030c1003060f0f0305150c1908060102010b03030c0703020d05010f02030903070303061d0f 86
    0x520704006e4021500a50340562800c02041031803541344160340d000f0a0260107448100781c0300c1e240303141c88502d150211404030300030304003144101c207031070380102c1c1094010b108600550080b0368441c0070641c0314881c0740005901c5032050003843c1c21706205640c0c00c02002d0070694500400340d42c51191152203d040704056071400f00b04001481d95103403c03140903040b0413001d40d640350341c40d252003003c0e5080b444060b500480c1101d020702020911a0440d207003d40c00500070002a030840e5404074012038120000ca8040c0205404229540c84100400d1000d40c003a49012800f82c4c200600d01c0101921070744000b8140c209190104081200032402c1c14512140c02d6101d4125518101c3d644031034480c00203a20401c007898102d00715020340c0254503900030fa200741d000740714980340501095900d0242d0105984c058212450410040ca80303401010040c61040d400403c0864401803102c040380c001701c0c1c8102282c0c10020b401420513605100d594040c0513107080c071269003140c00a1290035030000900121910702204 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 127431879 1250 127430629 127430659
    0x6050f0925090e0d0f091a0717030a09140d081b040815011404050603060601051821071203020c01050307030902040f0c03061403060403050a090f080327030606 70
    0x45480c0e0003070449060280528036410003891356586000d4041c500242c0c3d860702d200c1c0400c3c03140e01c4a008841e28250008150105451100c4c903d900204c0103e905515a0400d10461b04d9680007451141048130f200103540d00f81820f010050380a8028010300b01d41014041a00d01908000070f240c12407225030000740c07003031310180c030712806c5101b141c00c041092f00c22031000d1b00e10b000b15010114144c404025030981e86c0b1502c4414030080c0c8074190b0b40c4d07541c035800c66400103910354400c0f0090610030401b2400c5890b450b940390046030304d07203034030300d00d54241941400e1601c1c940b000100500b00040c5001d540c0c0740003412aa880080d01d500c44084014108900013020500303003440381c1c100b100b20b6500144100480c245464400c0c00030300070b420198000c81d0901c000015107031036004400605503009000b4003029603031550b0444544c2d06c4074001c40c05000e24880c0118071803800903c0d0b6805010010000e50303565030700980302408010364100c494402d001c82c018110350340e207000c91519004482940c2c3c81c1c090f040c0380 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 127433129 1250 127431879 127431943
    0xb070515061c0602070c050301020901020d050f070b01030f020f090705040306051003061b08011502030904050601090e090303061801060e010c170c010b041a0d1b0f0b0706050f09 78
    0x460b48542185030b001d005801481011390050880c28882d00403942059556401c0c14207034000d9041d0300f40583c010301c940f8801180604001c001a140805441c0d10380b4405542e4807942140071380094505240002d90801141000203292240100c11125005503180c292401419417041c2c3c00000c01585d00c1c1c201040c3c2d903085040b2001c0141d5402202401107d92020701078014038907100564000400203000041c1c8422041d14590b800000c1c1d5000d54601400001400040d00c00500b0050400c01c0341c850002d0a0b030b040040d0306004260441c061035580c01c282081100043c1f80e401030450600c0480c0c010810560094070f00062300c1400e0802c41440c4419003082070103000908481c0c40515000a60080072410650040c811900300300e46c1041400165840c0c8900c000d030a10071240c101030550300e02404113003117035038015180c420b10410214198076012002907100704c0d644003858071000442c000e020040745018443d0300540303008055400d4034105a10030380d038a205070908224600c580c0c007100c00d04480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 127434379 1250 127433129 127433149
    0xf2004020304060209090601080601051812031303050c1f030c14040f030c09051e09070b04030f02130504020a051003140106080403020d09050630150a0b07051506 71
    0x402001151a80307081d0078004041d40c400d80402c0d03c60035010000412542c001c8040500581c07040e500c0c64103002d1040c1500c180c64280c0740071542c1c03140032420340e07c15000040004045268907500da868540e465442e00300d281c0360030f101d800b9104100f881e05442e440d0740452002e950320205482c0c08a418800100c0c03d41703100707080f540e503030690020004001c681180c00144813001c0341c2c0702c0c2c0203060010340d558a032a07040710000d480000044002d241c03c00005006024074981007000c89090b121001d950b40710b04401a80240c1c4215040c650039071610341549020002d618400c640414203005a107055030011b80800d180707010b65031098028980b5100c0c050f10a0b030000306103480300c121048041d61100409841d0b0241198100d0051041c502c0100740c4a1007224040102e8401400440c2404420581d0b0039449800e05010900804c0110004c0201e02d10b403840b0328000c2c0c0c0d070f406070041038200700001c0c03114060b0560449501c0700d00401c2030a000600008000f040d8280040406005844010000e80d501c51 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 127435629 1250 127434379 127434443
    0x1a030601140922020c0706050f03010306110c0706120525030f020904050c0301080f0316080d090b070c050f0f03041202180a1e060605030601030f06150e0a090501030f 73
    0x250000f61041c41c2603998000c00d940000d45044540150b07560008445503c240800380325070140920042000070700c4e942082d680722510a4042f420440c11245a52030550140d02810010300102075040c2000c446120300d5411403c080a60301c0000c04001004480f031610484041c200740c1e542a070400c4004896050741e210184c0104203000500f421100c000030380e002030080078082c1c01401c4105090b00d10000890380c00d01101c100c03000b404003142c2c40317440c841c1e009405a60740321500e40950600103013100f25400d00c11211030310754060800803410210318202d294142000c46a00400c04407090302d8001043d101181c03045181117995207058408204100f80c0c01807504c0c0309459150034080302c1e0800350024500303103610109400c0c81c010018001d03029200319101c0d0318041042000400c03001d51107500001c488400905010410581d0360b10703143e21001c1038000d140c000031150311b0300100e1860513007402c17002004116414886541981c481100301035200000034802014007480740c0491413000c88201ca005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 127436879 1250 127435629 127435669
    0x605120d0e0102010b12010e0c04090203120d0b09070c030908071d0604090b01030f110303030717070e031b0102011407020c1207080105040809100f0806060901021c02071a0306011409 80
    0x40c80142c6031901801089011b150380c9d0041d40e15420082c1010322403140d9071038000b0024011405000c103181d415501c5031910b0807901c1d40b00c180140da40d488007848140180c1c0c0a40c0c80c2c405100a604009200745c4980d000790900780c100a604010b80c000189051149008000c43ea1941c2c0c5c65402c0024014068000300414600c0b50070000024000703a1900c050903640901036001981014104042e1680700440c2c400020034803e544c11a0300c40a0b982c2c08550000d00d40c20010900601040001c0c60045080307081c406055448490341050f59080c010a0400b940c0c01140115508107200301070340f614850040c1c2c5024203e150400c0d40e804a08000e03c1c002000a40001c00040c10b103070802c01d06503800908128080c48103414507241140c400e903002ca1140f04030381e07281010394907075504001d84d992003c08040e045101d440190b0040c400b46a8020060f080b40e90002c101c003d16042040c81038960003a400c12440f0b209200f04143d59811002412000e00c0005600341c1e1015400b000502d40f1201000e100264 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 127438129 1250 127436879 127436899
    0x3070e100608070504050117041b030b15010504031e08070b090304170a260f0313030f08070e0118120c050f04020a090302060a1e02100605120d0e0102010b 68
    0x440c00e20064203055a5550380d4040350395680701010fa401e480340c2e12a05000035825400c4841154a94125a40052050400d5440318412031410240d002e0a50020b980c038038103c000b4059030700310310300108007070b40c0007070809609091454440c0a540c080b140e02010128043c1b0300c001040081000131144500d502c01c0d4104030f6424113070300c0c187c3e1720b800c0341c015500e07032001c10316111030900000141c500204e54400d040d00305d080b44140700c3d0002c1e4010015012890001071203190380400e84400554890b170030321014041c02a00c10306000308000b03051201c0c60240b1110b0400c1c0040f40f9800900d4500329103082c2024048014072228002d8201c815902c03006099a040000e43c0400445228203011200c003111104604d010100c2000704905c6000e48050218840100130001401c000029014150580c02d04034544409003001f80c80928410504500680240182c4600036605204070800f90905480143c60b5052068019a0b2a1000220070044c025012201511680300b50405180120060045884 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 127439379 1250 127438129 127438141
    0x3080703050c0304030501090507091b0c03050405040903050306040528051e010b030702011b0c021311070c0305010f0219080603010603140a20010c080309120304081809070203031503070e 82
    0x7030040c10b008564030302502c0b01c00030382c02003540603800b4460344241a00c0c24804100b80c0680e030012137030004409101051000052a603540d206140c6c0c1903019458295682c030b0b210040200312080181a9520703401d03241c80d060161a8a181a070b1490501460700254585031080e08004000040514066801e03a4900104903406190043c45c000e00e00d640081c441e603901b801e02050038110031520302e40018400c054070000362503e0083c00c1901f80b010000012210000c4903150340c203501c5083c040e1130309030340c0c10000c10811009100b9608a0b0195400460805007a4044d841c051000703188200308100b000c80115010382d40030343c0010000c592110024410907000c00b00d80f43c60b010100010780e10341c3c0500c01b00b40300d2140b60040c4884006c1050f07403034000e0b0030425980d490040d000a81019001d208529514400c00d0b007240045000320f009010190316a802c030010107c40030903641c0224010f0f841d04050091403500003085e207400003007c28641c10b4200360f000110789003801d568441c1100b48021014025 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 127440629 1250 127439379 127439381
    0xf0b060c071505071b0e1e130c080607030203011802120103060b03010e060403120605090f0f1f060909110a08011415210105030610030303050a0b03030a03060f0f0e0103080703050c0304030501 84
    0x2181d1004140b80c0702e07547d41c8245039810b0012464020b80b0b9090940c002150440780e0507a00d40054800da10340142d0355111401c49140110403201a00440e50000041c40040b18100c811001200708110643c60141013070310910b08500d061100400c0680c0312032642c4041d0703078290003401c0d00013034590031149030703117030034107008281518003064009034600e00003000c1a1411301000b444d2044010b8107450f0340c55115104039500d41e000082068002d1440d100414068520140541c0002c0c9001c0d5600e40b005e90800083c0f000f1901d420a5016100a003009540010b5800000050460741e402c00801c06101c100c81c00300707280c150031600401500d4030004e0060480241d5000f81d64208a04080724a440ea880f0f5080c150342c2c81068070109502054003504100103032090b040154400c20711200400d008440342d010030301e0b642000d09a000481d03141c80080c0f03d828880589940200f41c40740c00300e0140d40c070302585d80340e500c001800301815007400083c90400303060040382250309503c007000031a0340e903d50300e041c881c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 127441879 1250 127440629 127440683
    0xb0d050d0905131107080703020c1203091801210203070504020d090605070f1209030903080a050a030f06060f0c1a0907080606040c120c0c02090108010f0b060c07150507 74
    0x51040d480c1c4a820035074644940301c0d00502039140c131421490840c06884815a5801052081b4110320404210482c01c2d1129070204201002d800025074a0f0050036040100c85241c05043c440d800841100403c521490b642c51f0610582e0614200d030150151400400c1c1005242e42000c1e411a000240320f1a00541680c414540705020311400c1005884101e0211502d44840c1c3c0c02000164a200c42d4207460409541f042031128468100f9000e41c694950700c000064100e2414000840c00100351809030f5034040c00b40c28018242c1e4001000390030b01303041d0003401c1200000540c0c01048124a490820000c0501e216280c201011000340c8480c07625206440e5120350f90b0042c1c01c058042c4c04046001424603000b800c0c1c10220036200e150b03c5000e605070900003448040d86006c00c000854046201586600d110103001e044d500c40040b4051681091050645840e00c00c031500078a400c0000781c0c0c403242d02003003030300c00d5440002600c09282c9100f4002c8515005078540542000b140c03090344079403100ccd010040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 127443129 1250 127441879 127441889
    0x60e0102120c0304030c05120604150f0504060207060e060c0d11040f0b040303021002070c05090c0d0e030c0c0108010509010b09060d020c010504020114120411060c030403060e0601080d050a030b0d050d09 89
    0x11b0b0055503d45090019441200c0e1611800d54010000f1800151043d040c940c96107814a1000940f07510a00845094500555080d01d21590005002060080d940140d80d2007031203180081c08181080c3c04612884c0c400e4003000196640d4448040326080d541404039002031003a074914100950702c070310703d55101e540700348000c801501c83c030300c0c50b0411104940242c0750f0039500180e00000b034500d80410b02911100003040003440180c1000115103040d61441040041c1e0100300c000d58651400c0c1c0c01d09031510040000050501c402c0310010000c2d903036550b5030581521404d07481e203074441440c0c44c0407c40350b0165503685400b240c0041502c00b456401540302d1442039000760394800320753b0386040c0103412920450f0b41012490041c44002030105a1032004c441844101404080c901803201c0c45050a503007280d00304450745e40d11104660302840041222038050034003400545003c0400b081c01410034803a46072000c0605031a00401d0b41d859441240003851300c4d42280a076190000e0000c00100700000d82c4c050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 127444379 1250 127443129 127443143
    0x20307140303070f020d02032502181b12040f060608030705030d0f0b03030d05040206130320030c01120908040b07030e01020105090c1e0a08070e010603050c03060a060e0102120c030403 81
    0x40759100305d100140170014001203401851400080c025011181c3c842d81c524411111403400c180d9005840d80c0c003100d48003010b003210f401c1240c103007443c0880c05142d941017083d01c3c0403010b1000484814500040940299100c065809950502e01c0c100016102a610a904078040032850b0005c2c45000300043c900d01110240c00c12480800e00032020407035203101051a01507005001000600707899a11168109000421050601028802c20f9914101603001103034601c4050480c01183c2d401608481000c150403005400d18091010008244002d00001a021a501d52070144144401e1500301c801604c00c185142d9030b03c0040d81000750003011104241d50040d0b19040000e00d5031100441c00880c0040002c100545404203850f1050054000c0307080164800100b060000d2500c03410804100101418481034103550714081c4c01404488004100c40f154130b904004008980d6102031486094031082e0421490842c07240c00102d251031002401c0c4a2460f100140c940c40a03200080540103c80c422a8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 127445629 1250 127444379 127444397
    0x80d03020d0e0703030f0e09040c0501030510050a08010b0406090603030c0f060216030f020f1c050a110123010605030105150d090c08060117010e030301060f0c0f0312182102030714030307 82
    0x105100d44281c049802a00d414200d41c0d02f1f009562098011a402c507185040000034991a4400200003c14a0340518982d070355540c0e098445041500070b0000906002d101000014595200035183c7d1440032801020444030000c5c5500704405513056074400350919941c80c0c11000c0c1450050321003026620308070098401c020503002d091300005054003103030115001c0041c0000704004183e6454101d803041c80180a04a142c80a0041c8244601da90038140c0303d400411400110040007646070341038000e2010004204018041601d4420400454007807120b02c2c01c2d550301c0c4502402c402010071901c020090044840005180d0400040540c16100031300e19103640c0e1048181803a088038103d4401c0b104a400a00042103818000e4005413090315003402d00d441c2d1900559a4465007424686040b4049040c488580707030701c002c9a00c070381c060403140305480d5100d814968aa49200840400c1c000020030501f9070b50700d0b100f91080c0f05441c4195801003960442c0028100800d440b07410403511a000107668039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 127446879 1250 127445629 127445657
    0x60e180a0b040f05160e12030d02070606051219030302090904060e060a0c08040b0601091e06021905060406090c05030a050703050c06210c070b09010902100207080d03020d0e0703030f 80
    0x8800c06004031450380f443c90198488540646d120416564450f03400b01e0440482200c0060510007021500410b1134010303a0f0706001d03d0b10200321080f94008030700500d21440000f4402e0030002d02018600411201100f0001d81841c0131400303881031a500c5600140b030002440104242e41d0058100c8404003000d4441c20b644515246045414004000300041d21800106012850004100e600700b4010302d00581341e0382e00c40d2210345011804418086d031200095600300045039050210b07010641c5030400704c007241400c0c1e443c0d2942d2940f010700301500040c5d484401800700481c8000704402000701605444000f0403034142507440340c0f01c1d0720040d50507000b810b200030040d05d0000c04440c0c020804004420312034181000c01c80801c0d00c001d040002ea045c2c204410404564182d05031351103062240000300d0b01340f0303040c4140700c1650300310020242075602c810400c5c030600c14080340403060074120b0b140050300c5119051105003c2c0a4201829009008458011041c50782c03140e80110345042984070aa1000001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 127448129 1250 127446879 127446881
    0xc05070b191e1b020406031a010e060102070b0f0c0a0203010f0f05010b04081507020a1b15180b1e0307020c0108010e0105030304090905010b22060915060e180a0b040f 73
    0x400d8090380001d1901030f4a070a581c42402c3d4034400766002900c00684c143c2c0300c0d500ea4100558003c05d040d009030014004009050004c844c1031b0340400c003031000d001d400b45881a0707006607010f95074108608041c0031407008000d41d8100700d01c80350b00740c00800034000072201d08001e00040000c000a2450f241c02d2000100382c4920b0f00d4200c8044032070903001805130040550754400f0141002c2c01003001c502420484c0c03004110507035509007040b8050807461494515040e000040f100401d410752003800803541e0f806010705080c40e0507108030768070600786590320900014180800c48440c0b0000948510110611a0381a800240c8100c0554280c88040c2e540c1d80350902032036181024440d465256008200030b00601c12207400c12500117101341d001080a011940008e020608501c0303850b40100340c600403c20310760056000b150000d0441103070070095544441152841c0040a0040c17005110003443c000005442c0c01001c1c5032180b0f8580c00300d40c024102803a180c0058030a00801912071703401c080c00c41440c0b40c05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 127449379 1250 127448129 127448177
    0xe1507080a0b011b06020a1205010b0a1115060108060102030706060803030f01060504031104020a09080303070e100f0c0b0403090806010e1b0414280b030907060306050306070c05070b19 81
    0xf070f13205143c05505541d50f6100103980480e400740d04001d00360a01c110130525601a1354040c0c081c0c4c4440680b5040b000d0002407a030140000103007000e038841c0159185400c6c1d2420704a030800070a10b4241440d0762201c0050f80b4501c40e40300024003080c0741c404009480340022010310700400b260708911006981e6190212501c1c045c84c00050701c480b4200300c9840039131526600070007242d29a403e240b003080e9034600c91103041d030700300f182d039040850100d4490700228500150240c0c0460810f090100d1882081d0700014110054150002c01d8803078000041400d050107141b038900180001021200c80e580c440481c210b00c46019513003d001094140605491114510b003542e06441d0503042500c0b20004580422140691540032804800b0241500c4004030109003108405440801d402c1940c1e424100007240c40d109042c0c4c80082007516040b0107222030759021481c05c2d04120240380880142106081250a0083c5070740000250400080d84942e5038402052013a01003090f9168059407900d240c0c0007012940c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 127450629 1250 127449379 127449407
    0x61d01081e07090f23060306240108090f0d020a030801050d0b071b060203010801020a0905030c0913050c03010c080604050702120313080903100501170714040e1507080a0b01 76
    0x1001c4030910003000f8583c0083c004103455040030603042c144e4110000c00752908888039003080b540804100035404c3c204071180e0020102c13409904400c40c52402080e035003400400d0035040125842c04a0030305001000f207a0b21801c803880070340c1c08070f411148000e0359800480300b0840c045401b0000010305883e01079807905801d90802d0100301613658044048803900d100030940c03054850100c2524000c070f501440518082d10082000503030740c9203684406080c480c0325034005488bd901007000210385848030300c0c0c40c54109404a010b640218082d10f0590305004030a090107415603e0700c1c1c1c0c042900e0f544210002d00400e0190b80c00c01454540c801e080341c07183c94200044e2018002007012072550b5017210b00140405010311492418120301800103404c0c500c0c0440d140408548030401440f075903415050501007844c0c00c000402c012482c0001c3c842030194140c03416441140c0e41c0c0c0311071104030400d100400c411074a007001815140742c00b0748080c059501c05d50b265160720b07141422025140d40646010181d80c0c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 127451879 1250 127450629 127450633
    0x3030603070509090a0c03080307020c03192306040b0610050703020a081b0712030e100c020f0f0405040b100515041e0f080102090405070306060c060f061d01081e 71
    0x142c200424400c54000c09014415284142d20140000c1801e0700c1410000e903116075421a542d0402340002441c2400320055584640c1144000340f0000b61003440c03108500d0750000d0748800070030000702c280d504a41a8400e000c0030f405203030204403c0049044500d486423004940b0a00c0d02607201500b21018081d5200003409a84050514008100510f01800a0980b03183d11043d00060f40810075061041031790045896a4a40d002002090381000000195210945a81c111008070b42c0c07008100d4850075034064004c841c0090f0701107154407080200c0e021000050001e022900f06072174280c0c3c141c0e034200c403840240b8000700c402140a182030005003d088121080050810b030521410b040c404c0310000d0381c600c4032a4507400000301c441d403105c10f1400a2000780e00042c1c45040600a1005951000f000d020801d85488014001a41c0007101400c2686d001080080d4900300704810720020b1003c3d4000384254880901041d080607210420b0605984460003a50089000100e441c0c40075030040045030b4680e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 127453129 1250 127451879 127451893
    0x6140f01080c090603100903080118021903021e030915090d050703140403020a0305070806010608070f030f0f02030a0e010e01020405011704170a08040b0612071202012007031403030603 81
    0x510f0900d1001340c0002004090700ca020021484550071039201500803030120b694480100800c0e015a050901250b01c129010b515190085241400300c081e010607031000c0c95070101d07103074014500d2207001241c1800f11402481d90703400c2c0392600965541d1a0718082030000503032400140842c2e00440d0b0044031104c107840751400d050040d5810ba030084814130080781c417030708103002c000050ba4590030703580d001314044d07406410028280080302c1d0500a05070800d80900c40c91005100103958081d24080010070b16240015950030414030110107403001445800c60305001000340b1504602c1c0b580101411062a00200204000341c032800b8240c1c0281e228082c0440e8940c4103206819200780011079000f440350b820b140c90315200303c9242400340c010b40c49180c0020b100800304000c200d5071003c2650003001c1226030b1910b10711804500c1d0b0f0f941c4018012031104c6849980c05804590080004600d4182c0501401c842d0310403103414580d552a0510040d41d515100300f040785030245020045030b01842c0702802030994 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 127454379 1250 127453129 127453153
    0x9060807050915030106030b0319020108060f030313060905011b02030304030201210507021518073008120606130909080c0d0c0303050601170f090a020d06140f0108 72
    0xc19041100c00c0c0d5004006007072080443c900b184000c50280009450000b500100e0100345454810460f2100e6242148102c0701400350382c1006035035070311860856031041e2403140a03010908601031082400c00e41c2207055000301d501d94001da441d605844003a030b00c00301c810301c01c1880780501ca00f030520080c0d010b810410040c0050352180040e40001c180150305000d150b401481500110303142103030b010006070006220250400001c42c04d040d0002c2e601c146120b40410349402403501c2c0c090034454450031100c00c124070341c0004000d0707a06000329040c049000083c0d007241c0c144071720b195000c003420004848a010004560b86402c4044d02c080703601c00c4c80440042c40c01c040e8030500a280034041910250005e0040d8424030380100401030b1020b0311980c0d140d4940a0718500034044c2d90002d0b0803d41400040b82c2324044014081d211a41d00403213240045c0703070701e8407120780c3c06040000c03081002e500b10398100807000078010300e90080c00000c00007003405000c5e5902c20304003514003c1c00b8000c03a50720741c116840c0030107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 127455629 1250 127454379 127454387
    0x10614100e0607030f03060506030c1209070515030117120a030c1407060902090f0c0a0e150301120309060804080a030b01140c010606090503010908030601080c070c0311090709060807 80
    0x8451031550500940700469000011029000384004500249144055550595141c094480104000d444003400d504040030308003024020740c1c4540307820400c00380000c0c201000c10000b180c02400d0241000302480e005007403040d0958000d004103040740a80c1d0000d080303000f800154120301903250301c248505202141e00d0440152541e0b00c200740030005502641407007002e42e140180381c15032044c0c1c40003a00e00900c0c17050203841d036001003d010030154240100502d0341c1601e001c0f1412402c440c80d0131442c0d00d18002c0043c00700d01544000350700c2200080004103000f640c406008090600a07100c5580b41541c0b8503049030340710000c0354020804c0344280714101806000760071440c1407040c1410b016000030305600c00902181c124102000007030b0b44034201081440d801c8226203016007070580003805010100c0e214200103200140c0018100411100001c003400004016074141640c440000d10103207947c0c1c1045203c0350851405140700340e1862010814282c0240c1d506004c07170b2030540b2901c50711799039042c09803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 127456879 1250 127455629 127455649
    0x718092406200a0b070c030f0201090201021e01060b04080a0b011401120f0216030201021306021203060d0c170a0b010e16030e01200301082a0d021c05010b0f03010614 73
    0x10300b00b44070b22540c400020301041d0469105170a10313030303c0ea44003800d91304008011741d400480180a42e4035003000303003026076400314030300c8030030361000d929440c407160403000c030700c2c0107003601e03404041080000b29002c1003070315022610400c9180100d142040c9070341c84101850030328441224590114520031250750004010f07400c000c8442d5038a440050600c81c2d041d040980d80401000c0840060758001000078814541c1d0f04e141c00034019034402403501108104013156948005840c15106111800401d000c0013015103401000d0000304240c200c1e420443c49850340d951802d1601110007085200c004294a4120030310240300d14500d020b040e42400140348140e00401074000d44900340d541310794203802e842c98a070300004040c2d40f90b416480d0340c0b50b15080b001420500c0d03520b1070205030000ba0119040940048020304c951446c2110b900c1c1c580c402b036100160664094451400b412000d00b00e12406005065003d140148810795142100f2214001010301300c0d010380c024401004c008120250641c01d0200d482 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 127458129 1250 127456879 127456937
    0xa0b180907030b0604060e04031e1803170c0a0614060405040803070c0309080a140c01021f0509010f06080c010201050708092802090f0a060503071d0718092406 70
    0x1418548a07c504006200100c4056003c81c941109005481e2100c0e0160002c2d4455443c2081d40e4103a020b44161003a02d15220203001c0c040404c65000303680c86000215500d0307250804c21a04050074030b2030094043d0103404584850b81d01448001003450405004891141e0361114409240d9076440c2800d6988039140c03401502000302003100803070210020000b50348003900800c203013240c001280100d00d00d042070a016950440d0490101f021504d6050841c024100b20b15160200b001d0341d0304800b5038010441064111079050a00b2000510014041202d8441c1142030b4024003050b1b07140c0340255141c000c140c5944540c0d074440c540d01c0c000501c1e0840401c021341140140110800303203030f400080d40203e0580703040c0c0039204040f091180d600510310985009040507005810424034042c4504100d9011403101401844c905000600142c403807071a800c1e60718000d9003e09002d6803540301020082c08107100c20403001440c04441c1035916204642e560488405680720407800c11024100405070410080c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 127459379 1250 127458129 127458131
    0xc0d03210609090b0114090115050d0906090201030b04050c040b07080c0607050306030f06010e0c030c070f0813050f06030a0c110d03090c0509191802090a0b180907030b0604 76
    0x103000350042180981c10051100034004921886030342000c5103860130603440714440e11203d2220003003c0c0ca0786100b90341120781903460401040343ca18400e407660b20580f541506d60704e1405003860100003c550102c41341e14002c1e42c0800c80314180e4030910088031419615031210204c2070104001d00d088541c014060300748684c0388541058000d20146140c07180507120080459800301c20481503090802c00000301c8150317a001031905500d81800805010740181211424650000004402800c10401c0f01d0007141c0c07124640d0030324407840c20021100c2c0c1003000134407100c540341400001c441c0307405c22503000082c00c01440d05284d501c1340341e041c2c00140300703050302d2405004070700c0e6080021140600041483c44880d44001c24000c0191411014040703464104500c21024181800000803083e40d842c441d1320318002c00029090010410812040c01480b402503102010004202c0c8080480d0030854100105540b10b403140b0000100300c1c04064000c40b040c40c526440403000308042042c0c00403c81c0c0000c00508 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 127460629 1250 127459379 127459427
    0x15031505072a08040b03040515010e0c03040c0e04050a030e010207180e190b191e0c091502030414030f100f0605060403030819020a020c010e03070b22080c0d03 70
    0x901c840c2ca641040d0300444117820048100400d000d000d008000c4071030300c040044141903050840005d10680f000c1d0940c2405c0d41e0102c005003c002d015803001e40900411000008580742601d80240e81d030314940002c40005520100c6120305500002c1c0030300c20384083c0b0722900241030301c211002e0300404060046860074802c1001d200c0fa8044001c0301c00d03000034060943d1214038540006040642d050601140b10001e140018003008003011082075a5400300e226000b05942100308002c80c0d2100e81a00b00c3d00081c401c2c50140e10800790008001c0c01241c8a411254040c080000209511540c5c030180303403071a41e008240611040314403684020303040c42140700c001031542d4803000410301c0c0e500075400c104c0100d401d0f01e083c41030444200c00021000000e64074203620f4141c40001c000d40710000b40e82c030107040c0014108104250781e018007803040942000f010164642c030314100d0301d0f9040344480050b000068070310280851101c4012894488400010340030001003c01c0c1c2da802c94600c1c024200030f45e18070359400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 127461879 1250 127460629 127460633
    0x910030201030e120a0c11010221070f1202030904050f010b07080f040b0a1d1f0521040b010303140f0f25030306050f0307140f03030d15031505072a 65
    0x10103082900c807140e481c0d5072606d5440c50a82d112442081d44c1c58199440107004d00491290b07a2065484c0f01c4000d810540c41d48818503102019107a0800c00400101d00d1842e070780e001c5640000a410b2030541106d050000f600c40d0b00c1141e01d41c2c003083c09000110b90003040a1004034074640014000d103190025241c0c9002c2d51000310f0700daa0b40186a004002030500c0a514a10105140111030000d404903080789041e108080c5502d070409200a403003040c000042a20005000f003045003040e002e030307001c0d450500c0745040d04c0d004d10681c20034041100828440c2038521480d811610540718408200d400c5035280400082c003483c0c040d008201001401b0311031032040e101e4070421008004041c2e1190300d0114001d82040c04000c9502c200300d00d4580240c1c03040d401000b201584844400b900241034901c1d00340c944030600442c0c00c61180164907003890341402411202110021034000403680504024600c12121480360380c155882603c10740d0016990326038601f100c25003d00384600840762030030100c40c00c1c0815 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 127463129 1250 127461879 127461913
    0x12090a080706120c021b090601090504020706021b0303100e100803070506070905031f020a0c0f11040506012c0a17031801030e070b07060b04050901020a02010b0910030201030e 77
    0x40e800600c005001061100388080d464001c003981c4d07141da4000341c0800002040d210380000e100b11551803051078000c010541030b9000700600341c00703010094001c2d560b400c03503070800e00065030000744155544107a100004003e95008016039001300170750511041e150b4986400000303001000744c0412010f05021800040e8070038104000c0140e244508054041458051405030469510342d201501070b81041d4403200c0d5514082d100c800c000800c0c90700068844112000480e104003603004000e11032406181d4207001d00c01140c0c108018410122418000c9030f071414011218a001e10301408500394000100311050f5000c1900c045100383d02924500e42e1990300d81d03d207414580e0500500a29400c00903184220005440d8803400110b000c1c201408074852015246640d0506440b4a901e10300010a2040c204072a0b41c001c260250b40080c002d104509012001c14000e5002c0c0000c50099803808081d14203605260745000d10840c0c00600381a040c914507001500a001c2c2d5854110450191b440480b0b800250 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 127464379 1250 127463129 127463143
    0x60c0c030b04060f0203091e0313030818061b0d14191101060f080c04090302060c070521030f1003030f050a02010608060c030403020d020f1216050604060b150403020312090a08 77
    0x24000609566007107015400d201684100034207a15040ac001185030b0203030760f8011a086951142c11183e5031343c01007010f480381006d00810982d104000150582144800c0382c0b07012b00003242c0700155941e0b818040c1c02940d0380c100201d0490752804082c00564900001c1115041d1100c0f1a81090410130a500026508451070f07600a8940701051450a0203c44000c00a080d074445003918200000c1d0780680307020b59101e6000f0030044c07825200240d01010400140003214000400810594160320140380c06025034200300c8420f07107002003000002d42c41e2403d80101000703c070307055210250b01a0040108680c02d500400c00d0b10159074035520001100344081068a21030000861070307a480b410240b800a003014841c030a000219880b803520b20f00c0d420320120b41710520040e464174042d645c01300e040a400c0403004030305004c1e2282c080c00341000180409038002030007200c4110b803c4650398109120070a00c50042d80030281d05640056a0001503840a500409030352800501a11034156100d00e81480c1c200c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 127465629 1250 127464379 127464391
    0x17010b030702010b03010203040203060112051005190b011704060b010e15120c0a0f0f090305030d0902040b190b03090102090603150306070306060509090a020f0d060f060c0c030b04060f0203 83
    0x4000030400500c20750a11802440e060f08400039031441c24503400081d5600e4041c0900c00b50501d80038070a0f81001003c01c840300040381e44400078001441c12246a400300c0210b0358460802c00d061030350a00c010342c42074041c40d0411180d600e0000c0561100d4403450010040d491005052200a4080100d29079490320300748440400d01480940c2d82c0d118403140b4000b094040d103000c0712641c040c030404143c40c0e000600c0031122920751400e4852b0742c3c0c401800302d803041c0709a44094180e0100080c1415500d031a078129102d86030085d40e0038007c491411090102c442000d404a03a0034810103c01407141a540300020b5811905400001d410507541c0d400041c01036100b034403260751080d100d074100b018504051200940c404420b00b0304001c450b15040b4003804c1407003455110b80c0b16904100c002174409100343d05417103030300c08106030399922021001c85500090011f40600c00b0202d1031039a0020b00e0324412000600815440340811043d2880d40d55444000d0070007500c1110b2154440f11407030015001c1d403001d03502c960 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 127466879 1250 127465629 127465649
    0x506041e0b10030506090106050c010b04050406140702030a0f0503060301060512060a0608010203010612020306040e0106121505010501050412060609050411091005010f0c0201020c030303130b0a0504050c010f1701 93
    0x11940810410b095500c014001c0a05080500b0005143ea56010742ca0443e03129041045d03135041000700550040191049403540140740106210600060742e01143c09d0001c448807440c26501c0308901a83e4a00850782c51000081100d10420401486100912780164002e000403d103980c807040003816984504580150b81d41c402010000059101c1c000c06e0001c180039802140f440d41824401050140101c90300902c0940000110310252166404180b002c0c10b600000c00c144e0391114600d070340760b54544000f503c20001010441c40d41a61500c43d00741202d02c16198540b0b028074182e1002e0581c8007010003500c00d20759452001800c04d006000d460311031481b81e05542c2402000e10b04026110001828211480052103130511060360800d0450500581d04d00b03040581c4645480100c0c60305100c021100d4040c003020062100200700d40b004041d000b840707404100f000d0350b10300790003c044600c2203c001d403a076442003401d07800d554002c4040c50003541e01482d1003084030322550f80040980c40203078801c1c1041c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 127468129 1250 127466879 127466891
    0x7020105090607050702090103080703110105090304090b1813140f03031b030405340b120906100303050310210507090b01140c0312040606050f0f010c03030506041e 72
    0x500c07410322480358040007504109040030300c1c03030300030440d01101400003d09c1c81c2800586401030500643c410130340054000000d000e0303460040030194507a0454440c0c406800c0c140511991a4a08000020300b181510404001c8940e1a0b50486554200c00c1509032901e002041c00b92003031401c00d2142d034140210200066a0742c0c24255005450500319511002c41480c003401407000090005c5006600840720b18403041c0500c6545181a030410460341000714402085000020154504406040780068a2803585081c2c0d032802480c81e1155401c5a4411980b0504a81880002d01a20181da0051402c2c6840c4c54581d4494603000250030401c8800e800c54244401803008101c4c041024031302410304810f00388980007540c030010b844940000d29029079642d01050041454604200baa1310040c0041d0007180b075801c05003410401401c0d02c2c0181c2c2c0c00b540080c6260354a5007015031401e8142c0c03074103039216440204140c82c00c800034000584070790b03801611742e41060952648000914100000e424002035a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 127469379 1250 127468129 127468141
    0x42a090c1803030509040902040609061d06040203010f1203091208030f090705030c04020903330603010c0c03081803030a0f06050d02010507080c030904020f0705010b010305090d03150b0307020105 86
    0x101c00107988650002040460902c0003960080640c3c200ea4070543d00860903c0403440014058002d540003900720178940080000c1708a0784890203c4525040150807c0301d0321404184000d80c8824011814a039480040800403c1d81c9108d0044030b46000346842c0b01940d44616004426560003c4103460400000c02030100c00c10002d461660003070040c000604109192a010a803181c480c402da080c42580d0108007120140c4091020307080c0400c0181650107941d08000384c080055040d1105c0fa03060041d084009001410144540c091605054031200c1982e42e0940e0102c8100d0340c0140302c0031900403240c1e200c1c0c1030014100003940c02042000c1000ca4021070049459044403815030005104502c038040703000c0542d80000440b0251070f0404541d613a02d244421b803c900d188074101e0780c80e400501c00602e00480312000302c007600305544500001d021083c0c2c0c0d40c0c01142525400e030b960041a42169644d140e10034040e61180c540d401c0340048a00c01640c1d69004070400c1d4108869100150b5120740400c56 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 127470629 1250 127469379 127469387
    0x50115081902030d0f02010e070905090d090f120503190f0f0207030218180304090f0507030203041a0a0e030304050102310b0310080307050705040609060e042a090c 72
    0x40790a41c003500c0d45036001c6503000079603224000030799a42841444544070712001e10039000540c014000c0d078100c0d002140d07600303ca1b5000340b50446008403140200e4a1514103184101c08003011915000342515205081c09904500750340380c603104071141e20040050340c1e9000c3c26a03611640400107912400c010303842800d400b03444a5000b01a840454002010500040e510119020140200d0b810706000640d95180c010601d11100b00800c82d0510000c1030018500c07a4580041410f6a1100000d11003929003080a9007640000e4400a140917201c80000d80e0354090051030b43d9000444d00b0012880f40c08241d070490840e40252015506650001400e4858902e201e01000c4440785500c2040520150072851100d1610079008501640d60300101283c0c42c80ca0303400c4440c010b080940c0035259580403038a01039507505510f12489015a05240300024803000600c40c40c3c2c215208007841900d0b40c0d5032544c9040c000350f00481344c02242120300c40ca10310014040079031580505501300b00001c111070140c1d4090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 127471879 1250 127470629 127470643
    0x3021309180b1602100b040b0a0b03060307150816120204030f0209060a03030f03020304020d150507090806070c2901170f030f070f020a150306090e0a0203070b0d060305011508 77
    0x101d03e01c00504000c8102c1135001900c071122260403e40042e4860109001a004c0c10b041303c00036500050030343d4003140b40c0e9100c20055003e07281c11004c0701d0b50250303120921320b8840000384402000c640850005030080d940002501c0e08095546802c40c3c081c1c0820920404070380084d00180c3d2606510841d0f0000c5003020b11010340c10020032110a00307514510758008000da00b10011450030541c011000c6011034a68611a010450b400008401c0c018441d81d16003008050880301100000c14000000601c010003280c160b0255081d9035946084007290b49401100101c0c1c082240d10705a10403580c41d0006078960140c0d406020800b1018040c8410368800303600e01000c2c10441809034000704000c0c0341c0050320004881c49507130700c481c2e4100c2124260000461406055000c4005940c81a004c44030f103079855441001603610040e41008050a50005a6950300414170000e4041d07010003000d10144c551880a003107007803403a11000c0b03092926a03a550342034400e410b442c03c840d540e01403004d02912000707000301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 127473129 1250 127471879 127471891
    0x20705030c03071215020c01051513050c0d1d030c07030312060b070b040503160605090708070b030a0b060403150b0f120604080a0e03060430020303060103021309180b 73
    0x10811a0305104007003400c00c0d4614401071010341703402d40840501e000340e0141d03410140c0110080000c0c0c60120501440c2008190481d17120306110002810b40e180b1a01c291406003d032054440d04119035291001c00070030101001d040d03407490000e8030210248080000f03002d103500100250000f01d10b035150181c407a024261b0075510719030070201c046c401185c500b4191110690402c04400e0203450300c0c240320741107101c0c0c030b92040c100203803039071106052207926089240900001e000b02d0340c41503515040503441c3d14050103804d1107000100045040e41c043c9070002c04003048020720f040d02c1c09035a5a0303843c100000c60b0700da500d0581c5c0c44140310440ca151031034941e81008401d48010100301440603120340c403514014030090401c0700106030005010f12070103c04c60b40d00401750840c1c0a07800e150400403000c42064006424072000c1495440707446040e0000002403070b0954004604686031030005602940080074503007030803e8001000074002c0820302862803001b60107000220b52407010700b0504404d8900500c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 127474379 1250 127473129 127473133
    0x305010f060e040209010519090302120d0219020f130e010c090501020a021e28090b0a1712190905030c0a031b080601060801061704030e01111c020705030c03 69
    0x820442a074200900c2c6460350400c840c016503c0b1417040069890780195803003e03114401100c3e591701025007040d41401542d00845d0800ca182055882242c1d0701ea0b002500e680050b001410800c0c00c1c078003c0b00c0c2205040e0300c01000d100c480c2035110081030340c12403000789117211141c4070032580341c06002c28032405800c5a150314006c101d860612001039a10b41070018001e000300c1007007010503070813040700700b1121300710f40010a44550055071b141801c00c02070100b0012000e1090817036000403500060b101302c400380c1e03501800000800703182089031440c15161418142c0b1600805584401208030500103086204d840d0b140f20440b05400c80c40100082503035008107000e5400b00d0803805251766002d0b4150106d03941b003108010030200d180c208050800340c540c45070b5a540b1031900007190f206d4000809605a8546540e82c4a446030035051076a05036005030380190115540c0c0328500c00651164058120010160080300c0042c413a6072110210b0b050741014075001600a804244454038040c01000841442200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 127475629 1250 127474379 127474409
    0x80f07031406060c0c030d09030308090706091703210a0b0a050112021b0d0203070203060a15030f060209030f01060501020d09030507120201090f08070321080109182001030501 77
    0x101c05400040c180b01d12410022035141d180c1001000001e20401c8003400707031010081414409020030304140412800b084000c000182c141400181560460700c0a5460010301071402c00c1c031605105050a408506000801c0f140181d00003400000d55402c5901503010401d24050309403008603454000550f201d00c00c0400104031a86e0300414514140d8000d100060b44e482842d900001006003496480707189000300505501d41d03a03004400350605500a4050b07858560b00c00c41d41804803011058a2444859005000c0c070204150b02e0342d032003685109200040c44d10702540300003032910008a08148032a915001c050200b564143b000703120b020680c0c145070365442d04566070709031900d00714010300010a4004007a00c1c01c0da807040e803c4800a200400c40300003810340710204030340c40d40c109002c00c1d50700601c078a000034100e01201007809050b441c82e0f0345070b00c003690a0000d1500030f403c1c202c4400e440e006007003500b607005c00c1301001680420420318a2500c2002c1c51a400501a0340c1e05900520070303000552 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 127476879 1250 127475629 127475651
    0x6060b09040b2e17040b0916030525030206070b010f0605250f0210030e0706110c042f030121051203070302070b01080a0c080c13090f12080f0703 64
    0xc090110284012a4440c0340382011a0080711500360302105480148010810300051210703064000f8010031426023a60881c40d041d1508010740c1d03841e4800181164050a80c2c1030803146504010070721b684500c00c909450540c0ca40004441c0d800c2100705580701540800100b250b80514030b0080f0003401d16041843c1080d5031802002c40c140408040c00300c0041055001e5003c1003528206140506da000b04280c0b807502120360010018100004165481d206001021510b1801900d03e042450010030060504500060038407001d8103c0b071401ca0312511303c1203828520201c08000402c1c600c03502404180d2207614007460a8040d182c041c42c0130744140c02084204002c583d0108019a140d00240b06550380d0b5203510000310b009110764003001d0520701d003a00001c03842c200c010464540c424010700542d00107940b81c111441e26400000682c0e81d01182d00d5401142510680d08000416030160800c89552241511030282007403501c0d40400003e900b04042040d041020301c1190340100f242d02d8100114004d0f1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 127478129 1250 127476879 127476919
    0x501120b1f1518180e01020d050c041403070b0a2102040902130e0603030304030503130b0a0b101103031906030611090108090703020117150d050609010f020f07080f0706060b09040b 79
    0x141d480085583c41700c21651000a0035011204d181802c10310030040c1d4607100309001c040d5002030140b5031f141c0003181060304040ca0002004020b403000000c40d039180004039402a10000f02c0c480c0707038000380c400308502401c062142d44060b000510714001c3c0035075140c0d400800300c0c6600000790440300f900d8000c44203001c41500c0020540382e200380d04d4100156207846084048684980b80b6500414440403401008401c2c02c0706d420034900903038140c5559218a040460942305040c2e07010501250b607109200080c0000b01114840c0143e15500d540000c2283d1203455450684031480085c05841c1800600341c441560700c4031107251300c0035048010703090490541d40024070741c5a10013446e8490150040100700e001103190420000700e40020a4528074007900e180032030700e802085501074013551074401c07080d170310710642e000715502c50501030181841c01a1599036000d2030740000381320a048a41c184540da0000c2d4030fa204081c0500031190b0840e40300d42450782040192070b440103c450198101044101c60b40c810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 127479379 1250 127478129 127478159
    0x51308030f0706020309030f040906140609010f0f0e0406090615050f0412020111010e01060515070b061216090203060f040b180604020c0703080903010f0501120b1f1518 74
    0x40440f002d80d494441c1e83e03100e880d500400c0d1814401c48000140060f5450303440e440101100e0300c0c1d2903d94064441c0c5400c01c0f1141c000c041703c260100c0c190701494000d25200b03030000558428181081107400c00000301040803601c85400c10402d5655400d4280b105c3c0c0b100750581c282c10170f224600907140200d0038075107440d60b00903032065005441904019108681c0a01d007040140d040c180e0003000103a46480e03220740a0102c034840d150140c0030303c1c40b0805400c405117003141c0c22075411103908040c41d15210148403822410580300c040500450420082000000d03600c42e0081034546400340c0c503070800d40104070302c80310780c5150341e4401c518025140280391a882540514120a07107602c000b00d566843c0410081c0c40b400362040c041d8043e445001c8100030001002d8100766409900801c010485d00c011075089070003c0c02030704610b00390002c10f140065442100d0b207610041e000d039046659011000300b030f01e00c0203858011621814111a072010f020354801e281c0e086052712261910031440c0303802090340c01028 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 127480629 1250 127479379 127479383
    0x4050607060b0a0510020604060b0603010503120c0307020d1b090203070f0e0a0b030903071109010509041217071101050f0609011401090302060f0c0d02010608100e0f070303051308030f07 82
    0x510707088048015a1843c0800d4000d00000d014100a912101e9009403a440115805c0701c0e01c601e010503020643c00c0c0340e03007030320305a92014004040c0d0480038040c121454005086250043c4810403603100182c0720158440c40e828420316241003035002002c400903403406590070484c4d007a0b205004010705c090f40941481ea20b04000c3c01e003001c800b00b42101041500e4410f42042c4070144001061004540c400002807142500500c16501c1620821041041e034003c01e204d0a07a00011841c04280442c900c0300b070301c07d81c070003203820016042c0c10000000440c100040b01e400000c1083c2c03c091601452080c000da9900105d644c4901c9504d25065000034118501800f07121401015058030420316405188400301464000b0222511111080480c080d241c0c804400c2400d00d002d070800000c03143c0d005010343c90654201d40064140036403154003260040c0140c5682c0c1100b4450070141070f10011007480301138081d40c00ba580744c1740d4441d021020b99030250195403103d01143e002300b00700c401c4900100c0079101d080e5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 127481879 1250 127480629 127480631
    0x4120c081203040b04020d021009140303040e0604110412061b05070c0e07030e0303090a03020d0908120f04090e0109110a030c0e090c03060108010e0607030506210f1906110405060706 80
    0x245172400841c00c42c92407414002d40040d0800c642c258450780201a04007102d4000c4502283c60207541c0605850f4051071040c1d03002042d40902203942c502e4580c1212140565140b80c941c20240e460025082860700c0f55015074070360f90745503903a001f000034a80404180d10400c0c280320b0f107015102d80d60071518a0451050741b110561460102c1c5201d44a0740040d07101205c1381c42160748a0408240c403d46400303910b20210b015104001c140c8400a0042c0b00c281c080b510702c5000350202002030030714507060781c0c0078000b568000c07241040042a036000b50320819180303e80700b82c0000381c0610a440c01d46001946075541ca84641006502000025030421017203081c3c408060f192001c07511000d41d0103180c0380c0c02542c2d0552502902d0000b00307d948055101216821841e8120341d030039241d9160582c21200c06990150708008400b05c4031014035000c030fa0204e5021a142e04441441910350141e60030880d10007140c1240705d48840d80364080c03011501640c3d0301807680b00caa0910382460440003174154403844100800311 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 127483129 1250 127481879 127481881
    0x51306030203030a120b040213080c0910060c02040b100804021e030d0309050a1a0714040627050405130203070807051c030c08030c03010e0f062209060204120c081203040b 75
    0xd45c025400c02084103c02a00540d11802e04440c5003101004d5400341e4112845450b10f11141c92400c50422401841c16044400100342056001c80d0f01d0522520705136005030b268024001c0b161150100c800b412000d5503141642030510b07104000e6041e21304406503048480404101e02566000b28010018107014140080d008043d0314040e800c0061082c806041d800c04d003080c0040e1201d07201641d5100742002d584d0021481c030784a9041c842c40c0640c4c007501c0300240c40100c21960109202c0c80000180f107402d9646011107607500c0000d02655821165150640c1821000b201141001c00c40c001c0500039074009080d103581000007103043c0360050800405d41000c020392a00600d030041c3d035414440b40c0c010000341d903203181800340350070341e54420705c80c3c0300c00003c041002954102039491841e000d03410091032259042056803100301151f02c82821400346039070761901d400000e0540d03c000c0000b401c651854058220407800e0110001c0039a5029251580016002c04102651101141c0c0d200b82d01032418205 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 127484379 1250 127483129 127483157
    0xf0901030908030103050604021f1d01030e1b040c080108031e0d060b03070806010c0201020a1403090d0c0603060503030406091526090c03030703120b0111030a030204051306030203030a 81
    0x9440400005841d0b804000004400c0c00320101d074861040e402910701c0030782d1142441280190204584001c8002002800000140d002800c03289602500503d004a82c0c5009150503908141032071004c4061134007515035481260400d4003403918404014101541c071507140c04401c1d502e0f44035811030103264076508040340720030390030074400d8410302201c080003080710544540110030164030030b82e4000b01003540c55001134807a43c0f040c0c05400109606a01403c0c515502c0c2d0b80310110503841881c020107a00007840754080301d44442101c3c02142d40200c400c1c542c5a0700d03051016040f02d800d60000c9000360801c2201f8011986c01802081c2110440c8410440b050301d0b400084449541e464071070070051100e00e52940758000b1084025000700c500e40280d038a02203010041540c0c92013401c0006001c034844080d0104249007503070164483c00d10604040c07942004e00c0101310305581c000001540070903404038080c0501c3c01c055144072294517603000104000ca04540000c0d544e8010154610b0405c400c2600d1000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 127485629 1250 127484379 127484381
    0x90f0e0133050711120a030e210a02040c080603061902040306020a0c0c0506040621090c030503071406040f081c050907090f0b0a050904110316090c020708030f090103 73
    0x100040303200c8038503041100200014002e42c003001050b0b400140e51424100e4903d043c4005400417130701d40e80140301d034a81c180d0b020b5a241c40c0368200c60750f2096007000c0ea07011040d88140d12202d4180300f03034058032400304144100001c0300d0540c042001088414000c10030140c90001d00325800007440b000c1d001c0e00c009440810b80280c840c503000103003100d00202e80d841d502034001900381c0c0035510a166400c407250310703241406014082c0b40f14840008203076030804100404111704288524ad98440003151102640c3c850700100c0906910840326a030000070b030082406074020984401d0200c08000d0455410241c13075005134420386400203840f10900252141c41c1c0d149a13400300ca80c9800c0e0502c1840280b03070500b81076448451900c61551740d0380c03c1048880c04030201d80f0480480407001400d543d422820001844600d03030006000710ba80c102020320b03903c06682d082202114249025000502c941d06121240003a90081d403540d00956002c1c0c4c0b028001d2800200950b046810b600c190240c80304203a1004030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 127486879 1250 127485629 127485689
    0x90e0114010330030204092016080d090503070506090c090a050a0e07140f1903060c050d020d0204050f030a0f14010f020f070302010c080f04020f060705030c070303090f0e01 76
    0x40001841806a5a00783d070b0141c0290048610104041110341406d00c0d0885030b03001e01c0e00003408401000c010b02c41210616406003c40680260401801e00e2084490315045a00d030503010b860550000c0745a404000c410010141c0c410b0f40d4101030b01b09610500302051080cac5000d400220002e8607800010801c1d8404ea00208003c400b500c12680d410359107a100003132084502002c203014600c8400d5016050800300141a02000000d1804112070b140d6103908009260105854081080c2003104d88004a82800984003039103001d500140c0c3d0310b10301001c000ba80302400b04541c0c082d030043d031068008110080b059149050300550350145500b00b088105004000d528052100e6910129001c014440507a000d020041d119400030042c81b10181401d84910100f190000b000598a00c001001410948201c0400500140c003d5050035202d03074485007542c01055212f0499404080308106242d48241c00c3b01c003c0c29000309100005040000442c05100140541440d8110380c3c0050004403407000211 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 127488129 1250 127486879 127486943
    0x40b0304020d0b040b0615040506160609291803030a1a0a0611010c090f0b0a050412080d05010905160806060408060f150319031206080706020106090e01140103 70
    0x40c500741c4c9800e1916103034001d41903884a00543c038905e1902070780095181141d041e140000e2038142006400c0c400c000203048034000031120580c6400610000401e032540b108401d00300301040950001500640e48504c0780c0090506044403401d10820701c00000200440e60480854540414940e10320601203200308690760510743c0145c01c41200180d4694041195000c041d003040007400012400001110341c0d083e240a401c80020100340300f04800b40c40c2c00028200010389040403801c060703071500310304860310381a0000c0c0d440e10381c002090440ba80441c031900d0301400550038100030720300f010345c00301403005246500e090601a2000120302c540d594a0182c50050112801b15407103490316000307500c8264825284039072a003081208050030303848d010500e101c4800c84c10600070542003594608031074000350640010030341039071384101041c410400e002500241031260004034519107030103601c0781180c0c0240700d0607259914001e003003244a0b100031445030440fa0031400c0320000925042100081d11899084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 127489379 1250 127488129 127488143
    0x62721020307090b01080a060303080c0a03240503010c0c030509060c25051009081b0607060c030c02120f090609031006030c03030806030a1205030c040504060b07060605060c03040b0304020d 83
    0x80018401a0f680248004100a996068032a243c040005080c0d46403400028049001480001c050301e04580140c0803001443c0340200d28920088480303d108080c40200c42c0705850810010f00441c1424001e5106940c82c0e4600004803441c81d460040040c060741e142e05108003800130724004200020081c07801290095500d22500302550ba064003c10100c1d031140c2800303003c149862040160103006200200e610000c060803280c000c00d040d81a0a0380c03003094482e4132440602c42200410f4140c0b040068007403490700c0c0040c4840c80180041d141075051104441c0c0b10f0001c00c203118131b5070340010a80b0351809040c0e80d080d495800740000282088810303403a000060b40b8102001080c0120348102100b220b0080e2200380613a02d80c0c000789501c2c0c1e21b40c0c2c1d40242a2140020400840034441c01c003c5520a6180c2541424540c84a0020b0705a03076150380100c02e0941c0129601082c84000d02c81c3c14018602150042e141c6508207401540f24092485100c0c8010000300c0011305540340c2e0005411f21307940c4910 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 127490629 1250 127489379 127489393
    0xe0316060e0307080d050406050c21061f0314090a08040302100302040302131a061936170102130e04030309020607061b030209010c0f06020c160627210203 68
    0x1707140004100498054800c181400b000c5445000602e089034a0300388480a810f00420181c10425211000603001c150424a07108030302004098843d200050090b80b0f079400303d011712100300001003230b880103010418203800903100a170015191000312002c45c0e0f030550710251044e00d0403006034001d0207240d201039001803c80c61001c0110703200d540902d900480f005001d6090703500c02d1052040e14001c1b284a01d107007140003950716003001d0003408155640340138404110070685044003c0c42004803400d9000c11400401902489000c3d080352010980742000002107007048806054500307000c5d45c61061420300c0e1b500b10f0100301490f11a8002a10090700034140c1e5030745030101d107403240081c8500d514440e900342d900e2401c40d085030b1107030080300d401080c140d580c003c0c5011292500115070000d10001c454807035003008541542c0005104251401e0b028240e51400d691404001500c0540722800d011810158000c0e5201500c200e03070003110644103d10554440c0500c00c22034190f03030010805005e941481809 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 127491879 1250 127490629 127490647
    0x6050406060b0703020a0b0c070803011701060323060108030c0a1e050102040b1206010c050714010e1002070512070b04090e1501141201050603030a030c20030d0e0316060e030708 78
    0x80c2e684a40340c41642900320f08c0c0c1c0c0700ea6a00113240103140000b000c1d4a0208010026854189402d80c000e00c04100000790700d907a6a039907030395040074088901a000b9007207101e078496030900b0b212135401006584040c1d803401d0440b102aa44a07440396070028221003041480005240301003070725000701d680c0b25000b10354450700d9170000740150704a104044070340c00d481c80001d130715540f140c034095920710b41c00720080003c00d045c40b402c26540039407448440d0401c040c1800c4260035560700030307075019050425000350480c0b03401d01c400d01000c85440b129943c02075012090401127245a402110116601c40c00700060b8444210030310f03030a10340c01e4002c00840070082c000114031014201d0440a400c0400c4582080f080000120a4288d030003c403241a070680040c401c10711079a010b038022003008507840c54001c0b00103000b0750000ca4030303c1c2c040400402c5a8800700f0403c40150562046520036088180198104103001e0408484042d41c40001081180c88200b0f601e252072080064600c1581d0015030f0646a01f040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 127493129 1250 127491879 127491883
    0x2070b07081315020c0907030b090f04020f030a031d0a08010c08060108070f051204020a08060a0e010c08090d0e150a0309020406051c110a230a0e100306050406060b070302 75
    0x201072610b410a81d07140001070fa88031590b40402050f07000f9006860703000019410030000000c01004101031580b16400301d00d2540d24146210b2048681040c1846241401c2c01440103440c200d41d003140c0280e002c1000b050120703402c203480c075002d0000000b5210703e41c2c0340f80d40462042c0741070764040140f940c20140213282803504180c490384284000e0361001069a40c10300200c85150101c4c40c0301d00803900400120030400010404994404d002614002206607a001c8080c94420100c2d01e48070003642d1980000700c1d65000303000c0e40072528510718100a42c1e0602c00380310f5480d83c90310761040e4140503018040c1d4070f15072034605090002e108002c644544cc0c812200001c2c018008014003244141d00c3d0500200313040c0740100d900101103241200c0a40c20300001d554424a030710038500b1032680441d041100154800c510684100c544082c045111494000ba9082c8000f5921540181d403071011940c0c1042268452107000c6400c41381c0021021546445908141000701010340181100c3c0000083c1e0106250300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 127494379 1250 127493129 127493137
    0x31311130f0b01090506040303180b0a050a02060109090b011202030a02120d02160e0f19020316031b080a1508160602070605030903090105090102032205040b0d0206071202070b0708 79
    0x1071090284020030301c9200440e420600e50041d180d014401b03002c1800882c1c8900105069076203400ca2042409441e0b40d800306140d0040708864002a00000f00c0800c030650510400d401415043c2c01030100346840d0340d800580a5050295000c40c10011f001001590303400c100380d44c41c4a4019290000540c14819040d0701c0301d00c0402c1c981d006d03201d4104071420080c0041e00e40d101f01c4028212940781922031003182045031001402421005071200245201581280300641c003904403400c200282c43d81c41c58010b0151241c030358400300c500c1050030007000c0302a0020096a440466a81c0004d500501d400ca00d00100145410020191148442800781c8d02c60080c1050151a5140c00301c03100c1c1a60ba56085886100c1100c60b0701d456042800041d01950294025192003181401500d081000d076410000d03010345113084175002c80302c0d62201000320382440c1c843d07200428016520713001c0691454002c82c50394400c00d10000c0c090459a4207031103040c2e10900122001d0604000203c1d40d03080035060030210b5400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 127495629 1250 127494379 127494401
    0xd060b030a0c14120a020f01080709080607080a06050409031202030c041205150907230103061d04020406060e0105070f0c03050607030c180e06100e150d150b03131113 73
    0x1000c800c01044c40005400c200040e8011b00c0003520707550600045a0949014291505010010340c0101d40000140001d5204803280c1c0da6112907131400851901c141c5105500040c0124540481980480d5208950f600c442400c1400517a694030380001603200303481190f04c681407400c1c040000c0c404020004c0b45003c0460914a18011541c440d089800d440b45081e2207440e01850402c504c070403a030b072980720402210b2001418001145592004456a0310700d652081e150085400300c02c000462610384241000340255142c603c1d07044c02d120001030810308c0740b0b03280641100c1c50800d0500030012618404400707554001d0a0750018142880060701402240741a400401c0062454099615003103920300100c44014210550710b031911070510060180c0c0800000801c000300898280c50344a01500347e1000b0b0588204030b03a105040712041080f5402c50075108900c1198200030040c4000c9102a0790704505c5022504018504900d80a04807a5154006e6070300844031100f500b080000c070350701950000e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 127496879 1250 127495629 127495639
    0xc181c03080a060509100905150d062c07060c02120d020601030b1b0702040504031206141f050a0f0e150403020f0406030206030a0b0301110412150204050d060b030a0c14 74
    0x4d0710b890400110380821070b00207440262105c1c1c1000105020741001da000300343c0d80c1c501302c9003619103004510003503405d11044d42c4881d00c1f091729502031100780240c0f0b04101c440c00b031050320034000028003c1e100c441d50700c64001003040c80381900c425540d4603404d04074a03c030740354200c620400100030f0103500d8034070074402921a48200c00004841c1c0017400c038880248411400b030070b49880c8095082000829006d001034040290803150a4140c6010b84214805002c005282d02d12040040c020040c54141031020302c1403d40c3c3c0200c950b14501d4000c03041d1648071050b0300780908890007443c6e04986110380d4004a60307001000c0c03a454429800128010000d50780241c464483d0b0580410502003a0ba509200003508254100b00164141480e984005449000100049064948401d6115058100303400c10111613402842c04030030844e411080303a9005a00d83c03015030030649014001111b000c1e0030035002d401c45407101d080c0c4000b560203224016000e40e010507041061601e030000784629085a1202c50702036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 127498129 1250 127496879 127496891
    0xa11040c05040b1206010f05040302030303040b0a020c101e0614100c0605010b0a09060203070317090307140606010e090c0a030f02120a0c020709290114070b1605030c181c03080a 78
    0x110f215071b08449c143c03074010380203500d10344440d035451b002c1c60300060841d01120360a121042c89002c05215120720038502c1400810f844460414400c0801c0c0c559034829044c0d45040e500308a07145001e80e402003520811210f50b0081000038100350b40d0350300003a900400680c6000c00121309445002c014158102c095511a10407a44076081a41e59206e00803020f80400e076955103602600c4c0c412902c01e68841c0000c0f081c1d904050032641d8103134840d4841140007034150803e40421609580c045200340e8002021101100d050518441c40521882001c894604250b01c801a0b8001c04616030121503500181c000850341e03e1905401031b8006004469005005020f05c0a0008070320350745001740003a074402c40c060340f065142d020429954007a83e100b81141030244181e0380082420100c2d0141007100d001e0260701285140070a910309820f001700c003d90092140903c14004520090015206920200303840244584000740005129090f951101ca038182c038056058000c141e40300d0015030080003948418060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 127499379 1250 127498129 127498157
    0x60d09020d30200f011107110a05010801060302250302032d09010e18010e010e1e0601050a140412030201110901021c0e1c030e030a11040c05040b120601 67
    0x5042080031601c0010300300f9541c95200203c100148920040a40480307103c100020402400d4421724221003850303200106081c0d00b4071809084800300030008a90300d103202030a007000030342030000600070035041640c041500d1003144200103c1c14840c0c2941440c40e13454010f5454020740c0d981c002070728048444007130083c1049140084040c20041510740a44e2420840036100443e02d607620301e44840e51140b072740035903d903040d144c3e124000e004e0150320349500ac0c01d41c100240009101030107880840102e10301a1800c51034840100000d410110911340f95580307641d4048202c4c0c11000c40000ba07810017400140000b0850340103040c52a0302c6100750006c1c80000f0f442841c02042c0c0c09030455282c0503070000844c0702c0700382003c036585514041c403506021841030855030106190304150300c07640e0034243d41d0850f070300103040d0005003009411000700c00621144c2e16690310300c4400c2407082e0740d072402583c03176561400c6030074000c2e0180c80281c00146201c90300c914507151030307901607030098400c540807661006401031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 127500629 1250 127499379 127499453
    0x20613080c010c020f061309020a0f0207061b020103050402040b040606030b040b010e031507021906061410090504020c071d010f080307030c1e0f0c1503020c0c060d09020d 75
    0x40b10b5900107103c0748400424009015203544031040c13440447d50500d80120301800180701034145881a543c641c0d80c1c1c035a854201904d0032110380c0181e01400f00e0101402c030b02802c0303003039680c005507420b28011959443d06c2c808140038214054019a015091207000b040f0b89a06a008500c0740f20202c1b4107001c1c800390f50f001076a03840501ca130701c140c040e0004815861034958200e80d2a8001c0340c58411a04801c0c102d02c030111415180f40003c0302d806880308030421030000ca1005480800c0340840740728004020344040500030091512a45024036004240001010801e00c4a0001011102d0b8a4440809402c1c00c4140000c0e00b4007a4480c3c070fa104170400310b40810000300343e0340b0003a45601c44180072061760b241c0c2a00e0303c0a00004e110400c460444500014040300c1d106140140310354160315015041c6148100000c51018001042510520100c0d414607000a02543d000c40b00380d07501951030003e42056800f80005d90b4010b07422079461800b6504100142409669140c041480301d107007400f80c50000c03c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 127501879 1250 127500629 127500647
    0x306050409031704082203150204080a03180b0d0f06080a05030f0c0109121d0108060f0409020a0b0c030307090e0c0702010e03070306050a140c0c03070b070903020613080c01 76
    0x10b03000500c03119940c941c00990342c0c0140c1d0401d00500804d810908504000861016101001480100d400204000300040300346c60440d0340d4000441941008d0909080b180c1d00d151b1060050200800d1424006951144031509406814a0303a000741c3c0d50418190803401030244640c071803221610300b860000e1845808203060365a00c1e400030146242040041340c0611a40007014000722a56039207005500099103891145100841c80c0c4404105000d40703c441c03c259004400c00c0390501006500f00049a5956005103164941c2160001808555400403420b214034641110203500d5000644174078900000014620898032561490b00030340e2101440d408220381620032034441e0b4010700903500150b000d0807902d4a41c107005402ca480c800e0356600e9130400e84000f035403000c4050381d0360f440107107228a44084680d4425008041d040c0b03481500c082440e62842561000307001d031071605c80804c0f0401d2055140100454005040c9a04c4c0c0380310043c0c210454610b0302c10098540704003c0d0800640d400341c00c000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 127503129 1250 127501879 127501883
    0x12060108070305120a09030f0c050a0603140a0c02030406031e0204060e270105120a061a041a0901060806120d03140703090b01171501151803051906090f030c02010306050409 76
    0xb1b462010300d5030707441110700e01002d00704454840c0300701d20101e041e440d03120064004020b01c0d500032a03030340d1031030041c094603000c003500315201d003418895404490354001084404a44552900081d150050082e4081402c0d040c0f1002106500028000a91990012900d444400103d42840c5000b480c0c0c400110513076144286040f80c40c4146004100c00d1814900600f0800003136402e4990344942961900200c603e846200701c0a6040c20b4103000c0035040501c02c072924a90740c40010b0b0180c0c0200713000114240c10511440c001c00640c00001071641d01c40d0008841e5482072281140c48a000c03194004e0050b20010300f00049140380c200000d00c2d07045c4240600e104031500064611110790038030b02400001420004200014414460341d156000300396000d06000703040c600d0280450f800c03031003c020411615480c807081401c01200b0140007242d008039041c1e15640c0c4913030310b00da201c2c0002e207004c2c1701030040b8038006803400150300110b5041c90b41040c21401194402d80c1d00b003200070f84810400080b20141040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 127504379 1250 127503129 127503137
    0x80f150907150309021818070b0f03040b0604090b07080103050607090303051b010213030c03050c010f080f13020406090b0111010204120f020d1b03110306220212060108070305120a 79
    0x440b10b0014001d41c0300c07120305800030b031003d8044000c500140380c14550503a0580b0350f0142c902020800f242040c4409000740c00f001c1d802030700c1c0046200e10601a4000607101038100051040800c0b81035449500c06640c465009600101d285401e0f040500350500034402034580e4012480041c501c01d10401c41c14096a41c9a21803c1c1015100320011180402444520310310350350070401c03044031144880f00500158411400041d5042c10b500d03080382081051010541400403030040c249407a0780022081e035000c0a00860048980d0310a0310149001c5012030b070107500b141c601000403a0b10b00903030f00404100d00382a03d8944903600039156803400c078490341c802c04496101030007030b1200141d0b800c501c210800d400180004403d10789926030791002e000c0000c03108068541583d080041280c00c0c0e849940c0d00304214050280c510300707140c449425113503e109030a01810544801411580c599001403140351100c2c044403c02c3d03844840c03150340c44c11540819110781c45848042a002d92205d02260394098050359 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 127505629 1250 127504379 127504409
    0x20c0901030f0c0b0c07060e0607080405130605040c090914010303020d0509010302090a0f0302150c0318030a0c0f08070b0f0d0509030403060213050414240604080f150907 75
    0x64041c4000c0b42e03480201da4101c0042000130381c041200b0042d0100803512409804298034140780070f00b16003e040a00ca0203504c2c1800401e020030040000d541c00c50381c085c0c50100303104c5d0071302e0003c3d0010b060301c2d0000365006203040303e0190703010352000c0c14100f55808103000b0854000481800390200b0300034800200164072104c014140144140090038002d00181405410724200074005400d203452600924404513400d81d080041d0700c2c042c0415031012460303a9281d45000d4042d085161288100250b5000043d10f48658460f951000c21107950030a8002d01d00340030954582000c100d101d215031140700c45504c144503012504040c401c00b200c4070590f040712074174504254a407101c0003804008140da0210300081c4400008107016000505403550301507400c7c20010705040801044a19841000072141800c00400c5a141c00c80715003410740c500242c1f010900441c01c0c0b00021550b1003684c111140c640111401c0c40191000007132040e90100b00c5810070803040e40d40651341ca554036024803d0004424980c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 127506879 1250 127505629 127505633
    0x601020105152b05030a0f05030103050a0b0c09120703020a050301021c0c0915054b1603020303090c060313030e0a091a01090b03060a140319050a060c020c090103 71
    0x801d1011503280b41d4400310350b241c0104042034a043c01841e09070303500e0700001031002e1002d5100510440c00c2c0e034981401411541151a029a59801c8580c010510740340400401c2504499909a842c44074000b4201b02215201201d600d481d02c00e0392204038043c204203040800c07140360600950740c81800c02601020b40c010800615005001e00d03c01c0c00003030000f01040130640c202000300c8010710131155184d1030341c0c03000b840302c1c0c103a2141c6243d00c031010703640d056a1038004500300340340001c01040c0c00c034500c1c00500c001440c214802481411003001d050b6040d400100b0030150080080c506c524000800d4a418003469028030100c0d1000b00c0e0000317800441103441d000002c2c081c4560840c1d0390f40c042d040b204c01c01e440b2088902151003c6e408011180c0a211070035038990b07403106000e00034240b200340301070450500d103000c038500244134090302942881c0080303000a191130400c42d802c800d00c004800c030b548000107420030984501540c001651700034140000da40d600d600008240324811030243c0303400d10580c138603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 127508129 1250 127506879 127506889
    0x50102061306020d110307050c07060503010501080106030510150207050f04090c030b07030b0d031106161b03030f14061503070c060207030219051f06180213120b0f060102010515 78
    0x1402c0502e4013603902d0484068a20490010314469405502e030b0540da8480341015920300125648400e0410004000610981e40d1000040e4119035150a0202c0c05841c0c0e088142d18a284540041c214215651440c1e01450303800104507040329819a198169415858207000c2940e0a000c4003400020450008000003480b4074155075104426150001d550040400080c0071540750200690006001c05000c07980030900340883c5410080c0e015200d160004441006072407401881c0b001201901e41410310010315001c0c2d0444404040028020800e0006000004400586c107503003441c080c80041c200070740c41c003582600710303270007020300352101d40a06426980d01ca0283d407040104800718003a940ba030b181021542c000620019200e40081c0009100c0d4a412006940c0ea140070b15140c141800d108200e8a18101d081802c0880090700c007503520b01d9014485500e40a00c0e50208103070302030900c0c0078800c2c8100400c240e4028880c204060b903c13600c501004a007603038000c1d5801852020a8000e140d041d10f45 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 127509379 1250 127508129 127508137
    0x2d0102031003020907090315020325020604062003090d0906050c030910030902100903050d05090d11120303010e04031e020606010e03120c0102030a0b0307030302031e19050c010605010206130602 85
    0x1071480d04004280d1295110511203060741c1c18641231a030040184000b4070030006400c1010744d00f5040f40040e600c400c00300259500c401902c00782c800c542d02c080300c1d400c12143c580c11200d600c0f5100c1740c5a035241014240300d503898a011003090000b440340f400110740203100e0011a0711078003040c0010350400d400501040b041b07080d18050a03080c103a03500340c01030050310340f40340090030f0702d116482d01102d280c5141809820041c3d80da407000104102007281103101d07075a481c21448803541200c0381140c144000d401045540704800c907180000d11020000040701000442c02900c0f40d0f11980c4d402079541120082e0544006007440e040015801c00b8000405952058014501d040e00c003c00b1203030140d1090207003281c80e0388641424035107070b5000410000c500344540128850814180c004041d4240795440007900c80c05506d40803032140f052a10102000e90344082a5089500080500c000302c42215402030040c2d4041d5480d0891942000b900082c5907001140b66442100002d20714407001000303507901c10081d84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 127510629 1250 127509379 127509391
    0x15010306120605060301050105040213060804020d0f0f11060f0a05031e090a1704030302060f090106080105160f02070806130203030d05040b191a1c052d01020310030209 74
    0x280e15003000484035a0701191026080c014800050700b800d04100b4142510030580096000310b004000d40040c0d075020780c2d4039004807400c920302000252070314800501100341114020b00740b00548600351060048141da2a41440c2c46040c80c2409100071100340241400b0b04000d44441320400e220004c0c5450280d402141c1c8806001000318034130100701d036803002d41c0c0d44c1521624122344c0301403892030400c8204034100c80a4886018914102855030303074003e54a0300300403c0c2d034a04070840320204000070000d4110b400a448140e00a00140c0741042c510140002c41d1159231000880361001080b8480c0042000ca00b540c003035501424103a03942100c00441d401200004a8043c88100218500b03045544603ca000d1840b5401c0b001881c10300360700401e0001d003100c03180b6141d94a007150704204c4103145215022018000e1b00c1c1c2c0c1440c0e04043c8880000803815070741c040c102c1e01807081140034203102020b61080c2c001f074441f64580c102c64000f40e250308174041140c1010b10803d5008050015103003241d012503102c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 127511879 1250 127510629 127510631
    0xc03070206010e070801030b190e0c13150b0f07060204090c0e04181407030516060e01080705030417040e1504060f14131104060c0606050d020108131e08030603011112150103 76
    0x448149c2c42d45040390071b00901184a1340180907804424580005842e0b04000780f0b0b40144181c4031005003a0050344c050b842818040c030b50000e0402c0101902c0030a492b0410b8000c84215180c681c4d40300181702601030108000d00190800103501a1482d091141010310020032030003c413802c00a40d0f540105915100c441c141e40c0c0f00394000003001800400240382c100b0309040180010516003c40036149040444055060085080c200002260b005040d60743c002e07080303071091030509001518041944590780011800c1e03860700081211120794135044408001050701c0400039190b4032180c0c0364070b10480d0302a6100340312500c4401070803860995602400315916420000c1e800d00d4040f07480a071540107070f100102151480643c2820300280d4882e940c0141025610007000c82d00d1940002c15184000b000188a91418403010080c0020201c0d4542c8462040301c200400d1100f84c2080c2002c1d400446070346100e98204207154001c61540d000340d44807500f41040b556402c0d1145000c0400c406d6416040701e0400d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 127513129 1250 127511879 127511911
    0x1090305060a05150a0f05090711060c16020a03081c1806054305040506030105060705150112060510030b16020a020303030c180a08070b090f090c03070206010e070801030b 75
    0x2952814050001003590703200c807031b59040c0380900f03211000b54020000700500c40c001d60580340d61000810481e034008182105e1654541c01c200c041102d0854070100a508110701c664007004008210004060441202660203001007202c0380d00000e407601e40b4081e414030350302c05445600003840d980085803c20810b040d816500b00c4400c10043d12100710085280714049034800805520b010101a84141c401c18030b0101d14050a010100d59a440184105400759000207214820b00500303200c49400500340712901c04955940e0031109034000740320b17502030300c2c55454600418200b0007900410400c0302c0d488180600f050365038090301c81d404400c88086000f940500e000070320041c1c3d81400294807035034100c41400d071070b803070094403142508001040b00743c0694038040d4240604480081c0c2d403021078580e80c04882d528803400020900f07a518200301d00b03030001502d4080c0061a80c18201840c400c007415400c5450316030b03880000c0800340005036442408144024010310125140581460b8005c1c418903201da20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 127514379 1250 127513129 127513171
    0x80f0f07060f0e0301050a0c180509010b070201020313140f01030501030c03020609032b0e040506013203010306021216140a09080604030206010608060a2421150501090305060a05 78
    0xa5600469109a202c0c0c8d4030080c0d014001e801100c55000b5130140e280f441c800a0400700455036840040c001c140311004003207014011a0f10800866684101080403203200a59414880e058a051021030500c51f120b1114000d510794442c6c480d99040326000900a010f071485c50b0244a280e0b0310120100c0d815009003d5600e640300c0c0141c0c04105440f0300324900c000301030708850004000c0d00b66815100d110758244030502034a82c0e030004020744003000e62054102c0401c2d040100780e41d0703421160300140c04040003100010602440e0703030142c80c10413005050b000c2c1c40d54603201044030005030f03015441d0219510b500300000084e0b50201a141907e801e003455540d407070316445603511b840402c03074040b401684540c006100c03c940c09401e40740c01010940d101ca61890410410801101c0100c003040710145000641800451240c1c5840e41d181c01034107280040c41e200029001d018100c10b1300d4015001a80c210b001515501c0381c4504030440ba001300241005d40c588046190180801030501d0590280d0406450742c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 127515629 1250 127514379 127514381
    0x40f020903070803040608012408070203090d0819030209031011121302030c04060803070f0606051206010602150c12040303090b10060306120c0302010807110102030103060204080f0f07060f0e0301 86
    0x648410001162190b01e1b25074001c040b40816040000c0880948080c04c46480240340000d6102e0032a0400d240c60f9960008102c0ca14081c108001d540100f440c4d80d50381c2403001e040010640d41030300510507e180b000c0c219059080e4840e130031440f505540b106030400340481c126807000c1c03483d8516862280c60030f082400801600c180c00e480d000d10440e9404140c10440c501004284070094041c0c400b805954a400100c941b03a0040e9800a865000c8801c5900e040101c03d611101c0980402840c1140200045810b269030340340c240252400342c440c08880d00001810808018400d40c3c0c0084480d180000c00058174606a50151084090684030035028000480c2c24419a200d0414503142034050742c541030b0700805946403940800c41e0307002640000c6021803406140c2070103494080c03c24030050348880c001203490078030080f400c6c8425440400007000b0000f980d0014002c903600e640c1140e034007400d103980054407200f4107281d140040c0d1110b41c0400c865801913a2048912144d800c2600d054280c01d00030138 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 127516879 1250 127515629 127515643
    0x40303090c0e060f010e130b0a1706070206090615060a030b150a090b040e0a0506010909050a050103120509030706211401030b07050f0a03110c031201050a090c020c040f020903 77
    0x815000032001041402e0078071413903d5403080801d18140b6441d0035030700301007001d5200228030100015203840030f040300d540301c8402c031134000c0403803e41c8003c084c20000a0951201c1096802c100140580e40200f640010b0010340c007405100d00708039003413920a0440802c0203c0d848085008103140c0c81d001c000c0e00c10366424181d440326010104980c1d40d2600000d00080c81c0e1036050b04010701034003060005200c8014054840e550000c4c04003c0010161190001620914010780c0100f411030b04040402400710340ea600224102c134032500c42002d2444181e8020f440d03a020302e58a26070503a002090402c45588030342003108a9141c5925007403540e40300758105000f81c880035003e140054401600400400c080d010150380d000010b40b90182c04c1600100d4820214440c107042001010b441c1c001e0f41e04a1843c29045900307014815003200c0d42c500c4022321101d4110802d20419200e2110880c0c0091901c106018180c4840c12075405041031b030200204000042c005240381e04483c035801d10590417546ca0030810340d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 127517985 1106 127516879 127516889
    0x52401030204020f12071101050121020409170c01021801110a03111906090203010e06090a0303181407090b0a030b040b0a090b070302040806130c0e040303090c 70
    0x41c10442c01455241c0c00300301170010600c80d401c1d41044440743c480f511640244004d81e42c3e4914041b240100485003007001c181000c130300d00185405d03070000081c9072103981c03102d691005201e550000c0c0c0d001035002901d941c0d4000384d440e00f070380c13419038200c99801e4003480d1010400c500000d0443c1c403840030311001001e12008081c80141050140700400045003038010000c618801d03800e041014000146082e8025440c28800d07118030440400c015104ad8090401800f00250030f0340c046004080c44d00b86040182c0015003910002410580b01040e036108071001010040d0800c007030720003151a51f43c4224070441c0d0f11441000010b41c503035919640a5000b000e6948030ba0b64414401000d0b010303e50000301181e845004100901d505036014109803481d407421621140e03661010054820725515000c0d00404c80e294041004c0c1d546699025806031086c500410071194543c0c0e144880380031f507006 = true := by decide +kernel

theorem cover : BRFrame.Cov 127338129 127517985 := by
  have h0 := BRFrame.cov_init 127338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 127338129 ≤ n) (h2 : n < 127517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
