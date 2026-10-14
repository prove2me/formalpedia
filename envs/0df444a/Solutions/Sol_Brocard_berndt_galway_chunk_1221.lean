-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1221
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:50:14.041884+00:00
-- url     : https://prove2.me/submissions/10022c9d-f64f-4dc4-8deb-fd5413e9aa52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 219424460 ≤ n < 219604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 219425710 1250 219424460 219424493
    0xd08031005010807120e10020f040e070f0c0b191a0f0102010b010203070f14070b04081b221b050406030e030705060f09030910030e1e061603020c071d010b03061507 72
    0x3480020222004014400078ac007c848400403048020350300c0e050b040750104100c01401c400310740d054850700700003001420701035401150340d0003c11030311800145036801d0b07070141000c0d980c44071070320314400020303081c21072a01000000c00c1c0000d1009041d1400001e503a40f00d000c0c4040d040124203448041085402d02c02503a81400310400c41e1319690300c41c050022564083c1c410820316114404440461030760380e088103a41c80400070039081c02061104804184031203041156030b900750f5a072031816080340851074034070100980c1e40e48868940e401d016014003212100081c00840ba8002d1040400149d00040e5559003d14540c0d02c0341c1e400d407989410701f40f443c00f0360903950342e2103081c032014001501d51690091210b03620410454100c2a54503801c03440841001c0352950450b000500092680602000c5002c034000c07191030010f14244c2d101c2c844500381041500240a003403040e4117001e41c4440f4207012103000d0300d0f080e9210740c17560401c14002010a103000c61080302d1220007103000e40c02d1014400a03568040d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 219426960 1250 219425710 219425743
    0x3020d021c0e07060e030a022704030e0a0e01030803060f030f0109030201200c210d090c051206010602250905040f050601080307030203070609020409020d08031005010807120e 77
    0x201c9841844001d403003040030103000c910408200250044c031840310311440040c00742c080d211100b070540a118481c01c0e400b020103603801050700c03410780c0740444081d40303882a8003039620341148020b074004000d41004650311a4541400000040c030100c3c0352841201d070002c00c00c032030040107502c40e1000320303003441c00c1c54004a021b5481e000c0000141074043d000b0307500001d000c0d600e02d8100a5000c001003000d029035940d44040c2d501c0854030421054003500901b07406030032088000c0c200884c0c045040d040d20b245240464640794201020081801c01200c030300c240e0100240039206070345c14604000d6441c40751070310410b01024401c0d840c0070781103811507d003400740445030003e001500c1d00713050005c4450503940e000c650602c0380c0d200000c0c031400c1c08419a04d00940c154041c52074140245c8031840a00420b0001b40c0e80700e41d450007014016170300c0c12841411540728240c150b4603460019110904040e0681c00281440740050130003040d00e03481803a005600c0310340800041c0c001c05551015103801d10390180002c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 219428210 1250 219426960 219426997
    0x5150906010801050117030d090201050423101b240606020610060905010c020d02060c06070f03061509050405090c06040803072105040e090a1a070806030a050d03020d02 74
    0x20100812240c1c107a41d6444002c0c006030b41d1303c280ea08400b42c40150200e50603002400715112546494000000d0301e030052412a0070326071205541040710042e8100040880c035900890003050510740a40021010140bd0040c07050010041e2100c00000024000785500224a8001c0501d00c804244603000344400c401001400c3d10394101a40d1003c041c0c6d0417036483d400c0e071040000e545104140d000240c0d2810f0f525070b8150600c550910441e60550b40b81260302040c1071100c07500740101000306c1b030301c00d0f020343d610881e0501c0615005011540c142e0000000783c1880480d002416410000c1141100e401340c500044c41d0b40c0c0c52040b03c1c10060b052520b05d500a00000e400204210f0000140075041d0041040031802a140181c142800084000394030205109000400c040790b14501380a41c072220348010f5500040c601d80d0760800c19800000c0444125010000b0f00281c182d0110800742d1211007a0024540800107172142d50f59034140d0f013000800c240d00051810a00b00d0143c050701c1e180d201e00e4074607006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 219429460 1250 219428210 219428221
    0x303130602070c3c05060d0b040c170108030301030f030c030203090415090c05120109090305040b210112020d020f0a05090901090b060d0f03030203310308011505160515 74
    0x10041040c0c12581000e0300350414080d40104a941c1060540c60030304d0140c0402e803811050109a070400500300c825903a4030060800f0903250f602032000c038010695036a01c8401d0303c00c181c1c1483c0340d03410707004042c3c40d07403040c4018030004d00c410024421668050400301891009443c04a203144100a016508a4180701c0b155885211900c0900190f030700350801400b550709076281c103d40034010b280300c017400d2851682c01048000103075032010a031103020749000391811380c45080420141d88081e0200000c84402c528101d031802c06006d609000d0072028460104101041e00003910b10469030300043e02c51040414101c180fa030b02c0c031200700300400380946150040d14110001d94002c000d90b0f4815a00c00320710500152840c6420392085422a0780151640d138140c4c81da44048000717400062090000b074030b03540d0040004c18a00100000d00003904945941d400009140040c004501a88484d00c02c0041d1a2988022a0031000f924a00410900c0e01e004809140c14010729204041d000c0e00c0340880032009106 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 219430710 1250 219429460 219429479
    0x1a070c090e07150c0c030f051e03090a05010c12181d06090603010c02060a0c09050d080c070509011a07020d0b16021c0503010312020703080a0c02040f0501080303130602070c 76
    0x10203c460200d0400084641108140c60050402e81c004001c01d0b00c1d0801800000c113020300c032a0489000c1c0044400032000480500700040c000550200550b201007044615460701016000c06050280383c0244015001e640b002640c5003410b07032010030700140481c03465104440609800040c11038508421002103211500032040c8001e035505401901c194000402c14201402801d00b070610550061400b130f645c2c40c810b00014194205a5020032000803400149580c0d801c90400445002d00c100555402280b801d032494911541d11850080d080000100807200390211002d800c00201511140d036a4040e10010319003881e0303c4001040d1580c108d092000040c010002e22070008806c0d0200c8124401c01e400502100110741e03106c1002070340410050000a4110000442c240424011120f406859903201c44070340d00008107245c00240e000da00306040d4079040c001c01082c1040a40c0412081d4140b000c0c890b02c1c1e20008000495031601c55014004003d5107134100ca2400d6080304410301e0498480d407128 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 219431960 1250 219430710 219430723
    0x6050703090b040501090317090307030c060f0e0a06030209040209091815190e010b030f03030703060e1003082208070303110c0a03030f020307060204090e0f071a070c090e 75
    0x10380019401c404007241c251142e030300b20740586205840c1d0040c801d281d80d44421030710410b03041c00c9908260620049226031010040703030000c0c500c00c0c001d00090300e04100e4024210204290010100000c1100302d08164841c8120002651014135001d82d82d103885801080c081d10441281940002d409800c002410000005ca032031007201d0390b130a1718048011700388081c43d0182e054414901c6010002c1c0d500d9200c42855000341154010b040010a41282c41e60000e4100802d456203c1420741000041140161341031003440003a0441d2040c0fa41542800d030608080c003041400001c00b00100054402c41e0542000716044496840710280200c044e20343d5080c80d01d800301c500c02140401d411498201a107140441c03a5801e862020b044600d0b070a2841d10304407002d40006005105602041124801140b072900060002d848102d0340030aa150981880701e1911601100030005a044003100b4855900d01c541100c03001c4954803907407a11071505003810300100e85242d015000e41880d06076504514880800d08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 219433210 1250 219431960 219431963
    0x1f08030d0c0c110607020d061a0301240b03040302030408061306050a020403020607110a0504020d06031205030c040306020d0209100201050403020717030702090405030d18150603080307031802040501060507 90
    0x180010180001c0548030200300c40c1d002010305001600e01d0046041c11009800f820380018a12100e002c0682c48603403c9a259242c4c1003044422109004640c0c00c00b4080c4051381d0607040c103d801092032030b41c0c3c03104004409010f0b05910340c0740040414203241c401c10589010340a108150790701c5042c2681d400d0191001c8a07412100790b401e0134006003450000d03200761400c42e0b80260425140110640c3c80070740d09488090100d40c00580e41c80c0100e01c6440d54400781c045808426030010b200d900f10700b032412030b8080d0302c402c103004c00c4010020014465211401c0e50200d9072b07c25400358888480c2403c82d03019005030400550400c94024084500603415040310740124042d40a90b42259110408500d44d1060b04500406961041200c4001030070810560fa0380b06000c2c2054a00307103001c8010050640394610b441c0082d48120405c1c42c8144607041c080a4440b06204100b000064175644e62a62a804000c1018061541c4c450401060160854240801c42e5000340200225071f102d020242c2280c010050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 219434460 1250 219433210 219433237
    0x31e020312132909010207030b070e0411040b0703110a020d0602071e0201050a050a0306120501020a17190b030a120801090b010e030705150f0c150a0c090e1f0803 71
    0x140040c0000c4201c5140d0036120800e9a4210041c1800f51159215404101264114070680300c0001c0800e076a07528690241e030003a951148a0082a0100000d441e2100403900113000100810010510f01c80d085600260303250910406d03410b01044500c0c1050300200c006508038080454220070002c041c2e0042a82c2d030b120300b0380c1080d141b151500c03044125480401c000e01241080059a24480c042c001602c01002d01c0c0c503011074244d4540c5070650701040207640441c0c0ea41e4021651003243ca8202c04944007050880300d1011207403030240301030000d458400007000c1e441170b5518160005a141440f1074141581c000301c010320b840c04c2030309001700065801d204406e000c528040d203149003588100c083c515040b500400030007410b070038241040090140d4034101e0301e054408011400c008001803020341901d400d807502030100740104074144030328020001c1120880618005103092030700e0300a041c220a882158112810641d90042d0b030342241c05099040c056100841440000e160308000b008048030454000b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 219435710 1250 219434460 219434497
    0xa0506041b080a050706110309031e01112502040207080a020618030705030304170403170909070309050a11013612030813031202070303090209010e0709031e020312 72
    0xb90350740d1607551140b03000b0140d40142000300001407040e00d001c11441d0403207090340e103002504400a894250603019a40380030806a2840b14496001c1c403c0e2014262100d60b1180b800e220041309a10340185d80c2070071110f2108065220041d500c880e0b058541396540141c2059541c24900700c0030755103650445560404907040300e0b42e5840e07100f003c402d0b142100e0f4400300850a545035903407004482c06504981c1c804d0102e00780800404605421880500300345030407034140e80c501003030302404503a0500400c1c5200745810480bd840c0010310000711320803800e80005400c0420101100100d84039001e9403144088101c04009541603412007030180d03d03c41d4103000310600301039030b034001140400c7e24410018001c1a54a000100310018200c410001c091080c54201580c00c0285145812604600700503000680d03110305400841c00d00410380d90162540d400851400e180c40030000b040c004a0340002804140c0616000310101c0008080340b403026070080c00d0b5a0359900d4043d00c03401c59048110500840e6031600b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 219436960 1250 219435710 219435719
    0x20a0f0305030f220f301803150b0f0a0b0903010b0301090506060d08070b0114130b1c0204060906082a01080c0a120e0d170c090904050a0506041b 64
    0x482c0d030f0b00c001041e403004140c0104980326810701380c00c040c20590709506800e50090916200500d03600d84482411154106c04162090060100d404862441041c84c1d10160600108007a0401034185480c08040812000b0280c0d000c074501d400a00400e5401c00c4000c440031480c80c2211018103171850060f402045400800c504242c242d4020f103001800d90303080540440c2032401d02451600b001c42c01a403043d4504030a80e0f58001c07064100b603000c1c00707100c10f4180e8035203070618040e44d4024880400c0700040c48401c2501000402c6d010440c4400410781c020301542200b1900c1e10f42142000344501a4204880c42d660b10400b5241e0410448018400071a452110403241c101240e0f4441e403c81039540764620ba440c40308100381c0f984071510080078014080007a00707500c031450044130f00002004c4d0240007003aa0354030001e00f8040451b203031102c0b600b05110400c400000e03060b0507207001702d004681e242c0d003984840c10724030f0500c0e10218001c0c0860040000704014894401e41e5a0300410081000494190b5103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 219438210 1250 219436960 219436981
    0x12090106060e0312120705250b06060712030b0a03020409080304030314010e010b0304150507020c150703080a020318030a17061e0405070201060f06080a141312020a0f0305030f 77
    0x81d904150010f05000c1c01080f1703a41c03d09545d80c040d0444c10901c2c078012068500645180c21074020400886c1c1d0106170504112114542c075411604c290f03291402c04500703649031556000028106800c143d568020604103031350701694013005540190040004644506041a503648203c8050780464285456030100710ba0b40059241264198594441142d00f040380d007c40c254006032060703441020704800a000780c0d4070303481120300440a0360001d001030b600f10418001e01c2511800d1104040109119290109230001c200d268081b40140c00141e41b41e0718184880b0314201d826804e81c4003840085810300030507802851030701014040006e01840d5651724030410040b010114099040304440c050781c04018146a04035540040141c00042816034555400300380b02e840d0795000c1400915410700748010040248607612050701503401030302c1e55181c62102201504d40c0400d00a000d1150151300d10007451013804600c003c950b101030b860f460b030801800c006005400565450010178006408554100d41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 219439460 1250 219438210 219438223
    0x120f041a0c0d08040512030a151a0717070506010b13080c0d0308131e02010816080f0405101104090b010206091f02090a1e0f1214010212090106060e03 66
    0x1d62000b0114001204030441c0c0c07580c405402124a485810b5155221105030f502640c490802c0000004502000e112040d580d8600381e84084400109661155650080313801220451034000d40740c18405103003103950143e54411b854015000d80900000400d141000b04000c000100c90030030b900d08207030344840000e0349400d44401c105900c088802e080304006402a0f44266011120b00408504049142c0b0751406050051090525013044032103c4003c568101c1c81d01604400d41c0686c040700310700c0055029241c41c43c0075210500e090310a100107000c12204000420038042000020f001c10300c0740e41c104a1040d0814000c0c400240d04181e4008859440055034901c0f80c40c03020000e120050300f4208400e100075480420a10b42502004100c1d140e4075481c644000500c440d02e02140c04000c9242c401007801c02c0303a0011504084030b11010000604405105030002e5040b40c84000b5030b10310380d00541e00a2003580e40040075000200d0401075070030410b500c124211541d41c0c5442c0b20101d8001e0401d5100e20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 219440710 1250 219439460 219439477
    0x3060102070311011806050c0709050c0403110d08071101080c120c1b0703080a03110c0705060a0908010c080a0e0d050706090203120f07020f010302030c030612120f041a 74
    0x7481a10304002040000403403112129060500c080541400544035441c803d50ba0051740100d01c00041c890103170784003084200024208840704010b10b091603c8411010b20440c80090704085a1003841c44140e583d02e843d4803a41948880d815955100502d003074410314078002c1c00140491441300014000500300d0080798030704600c1c81e21094950351441c42c0503015400c02c50a2410090684049a82001c410042c20303000c2c5001d944015254400d11000800303503071079000e905503155024401d8040103d0001500c00603140304450341c0c0c0e01c0b40400a81101c60240b90352010701150300705282c0e81c42040c0c12400f09070046501d4001400380141d02c110300b0750780c2e0301160401c0300060001c2140c00e006c01d00c10f50012161910080907248455282440d00030310380c101460704036010700c000807110114a454404415103402c203003400c2d0705501c0e02010f05415404000d0146000340fa101d41c0d0075030310b280f0522030a01380300101c4200d85d442d1748001001ca540751b00180a0408420070400c9000d40203560041564501c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 219441960 1250 219440710 219440713
    0xb100e07020a0f082703010e030406050301150e040c0309120f14070203240702010c0206060a05090907050a15080901060e1605040b040b0901180501120914030706020c06010b03060102 80
    0x269195603d00b60a600640e40035290340308240841450035410441210300303c0302c00101050a03464400c2010b007180c0f412214580540e00401c07040200c2c1e604002a00d044544400381001800d603036510960311190402c1c80280d009223071603562a2010f8045d4004014030303018508581040c081150160f450407921035502010541c101241090b144522008010852000c2d0956110f640d1441c02c000b10021a0f8141c064004a858100320701a5424444c1d01800d0031030384010941c504051000c900442c600707000d164018218640016184a8104560b900500001d00b4400e0140d079610710341c1c2d14101c022002c10700010340d184040b490141050080400340d51030b0719036035100340c0c40f0300402c2e03c84c4100b40d0307185200340842400009101c0c03403c40301410040c400c0340e8145940d028024001486418101e040a0000c0400c400078446a6404014000f441d08142c00000f8010100c0c02d01c04049826030b00c20005511000405008200241e00542400c090310f1b401c03207401c0c0e6200c00c51202e160004aa070f19006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 219443210 1250 219441960 219441973
    0x30902370e0a11090604081c09180b03031207050a030b0411090d0f0b0106020d030516021e010b030a0f0c1212030b01111501081b010504030f02040b09040b100e0702 72
    0xb550310507803000300703d8026541c1c81403030001e007200850714a07085036112000c1f5070810508000c400105040034847c0d03801c01d28100d4005820320100c100c9046e00b060266000e00d50300c00c42c0801c0350300c0800407111300300140c50000c1d40303a103807146005015a220201d4240028284681c04095090600504812610801029060102e5107090145c2955410341c00e48205d8801c62007000400c0c462040580030301090f90180595840c04140a0180c6202030403d050941020180f540704944c00300d0a4190703c240c0c2c01903105160741c40c0c1c1c5c030300d40900000001036505001340351007642000480141d60403100d03c100055103010355903403580041030249000103840760380d444040507800c510941c441500c00c48141801c0c40300c481c80b03661042c5414500500030b08181003050040c00501c44c10400c1030181c441e51a405080500020f0000300300d4003c520000b0134494940128404540e95500518400b110140c0400442e16060801c0c4042650948800140c41c6000c940401e8000d05211100d1007460303075070000e056 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 219444460 1250 219443210 219443221
    0x7050d020d0e0d110f06030705090306070e030a0f030909110405130204030b0721060e040312180605101e14010905060405130b03010e160b030f16030902370e 69
    0xc03a084688900d948000800f41061050703540d0f2010b5070081c0c6d0103503942d0350ac030310816050500e040c6000c1c000c001400100806401c46980028203920360580c002c004c8880410945019200c0c401c01c0c1d0080880117080c20680c0024006a0000d00700f02c5508585100360b0000301e0010304201d1166010240c800400c480000340f440f405005402d203160b072903864404010523803221010841d40180c0124401560300d406200a050340031742800006c20140c041000300c001d2046c4e5181c1c8000001e02c0003400291504002040300c1091200a030050072084180c003041c40b0b19016a400c44029030042c0b1a0300d40f1402101e003095446030b06030800341d13030000e40141e140500b0101040249034074910034070b9085456800000b107030345081c096000d9004243c00249500ba54099858080d41c119420500b0400000d00802000d0480505185c1e00651201003010428011010442c01303040e00142c0070b900a8403019009030034052070070480c02002301c5140341c1d51b5582031191040c42070065921403030300300d400108046070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 219445710 1250 219444460 219444473
    0x6060203040b03091c0c0605060f0901090f020c0f06060306010803030c1b100908041802070f06020703090f0f0e06060a12150f03050a03111c030b060f07050d020d0e0d 73
    0x42c1c1081400084030900c020072039803c190500624282c5d000245500c140504100c598018641c01107821915000800c6144010441d100c070144117003005140c4231078100c082a01a82d0444085403200c4050710300300303100340813480d5440038242c9a560080c4204800010080c1c404000e0b079008400e00c0403402d1a0030544891a424200c0138000c4540e94002d03000b41403a000d00034030a151009105846464446190404100120100700c0410b4100c0d40100444000104044c1e440c5609030b43c02500180c940485003021508007c07140c010641c0761040b51000b15680b1322414240c3c0403501c0c80982580d0075034800c400d2000c24003809c1142804620707860000020702045030002e0402105099442c020141d940800c826102e00c01c4d071041e01c0ca900038801d118249039015510f040c417400d0b00030080590b0744d00311007000408904511080101596407000c0119661010b0496101d8681a0207054481c00f2500b451510350f4044424080540b040c221199503046c0100e54240c0004002080741071244c92948804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 219446960 1250 219445710 219445717
    0x4030f0504090e1b0103060305030f0c150124090e040f03020f03070303020403050d1815050f030a0c030b10050a0302031005030f061501170105010e0409050d0c021306060203040b 78
    0xa040c084240004500002c4a02c2061001110303d0010b00410846800f00c0159600c07803450103040504015003403010800000850b25000c840108641d030b03032544000c1c0036041185080140c000804480000520600c030f45901000c2442404220608100780240c296202038907881400e0710b030580840014082405007030303e2811305000b801510803142c3c0c002c046508560242c0c06c00c401181d80401e0902c2844020412054950345500700080244c800c5940c0c10b0300c007602d80c49401498140916a2812940300303806035482d90340131b04145e58480c01c08115000280231819070100002c0e140001c0308229182001405c080600309407100d900d07040740c0d00e6040b00690300040c0481c8012001d03200010302c548041020210000c1280c02401da142007610310900e10f10000048241000890410101503c004101140c115642400c01d500040042c0b00401c016168a070006061405698a0310001541100015400c2d500c01c0311203911005980a000f0103c45c01030241400590040c001400740d0044940203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 219448210 1250 219446960 219446987
    0xf060503091e15181216020301051503010b041e09020f060c160602010509120922020a020d0311070b04080d0608030913021801030c03020408070308091c0b0403 70
    0x5691103480c0980110080090400388640b0030390058180e00c041c0e031140305005820003400001c01e0205030300d52180c0c958a40c1032206a003c1c0100c00140c8101d655801c6e080324607100d80c06030007809140b0305004081104419200404c0c000d50900c52401c900d440e280c07190042075140c03680198445c0c150b44090400402c41020202c0c1c1103200901004443d0b034644020b8401d41000340000c003140309103115000390446d01907200da01968100002e004100c0d001040220489080760300c15030311080d18400003540b1001c80020780e01003894640f11290b1031481a00140744201064080310f500350f040241c220f044941084138a418a4428000d040c0050051900150030500840c40c0300d04000c4440c2e01e0008445e01941300200320b070700008049a040c14042c108005801440d0b00842c10880903507007907407065071800582410103589031140940301d0b000354152400b0305010811a821280c50307291410141e4840c510781ca1050320f24558014015445a440c4031a40340e00159101d401c0d1116a42a2800e035500f004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 219449460 1250 219448210 219448213
    0x30909050a0603050304030b06011b03020a1b0510030e07050a06090e060d02100503070206010b030c1b030d09030e1c15020c030910031a031b0f0402040302060c030706050108070f06050309 82
    0x808188204003900185005504450323940c1442c0b0b00150a9440c0409ea048505001e0325100d404a038021428001d0113811906414070b1843c180c1d44004040540d03000303582d0144041c161005542c0e8140d000103c070ba040c9108130340a4544407410070516034054440c040010344030804c2403042c500b15801c45908031101070f1611a401000c0d600103807003403246070750480003c0c40200c1004004c82d4100050f90040c0b541a400c02e10754100781d15001154429400c2e00942454240d0715005200c9007081154a007288a0711b00300241e45c1d40e450024070003100d016181d07224445500d01d20b8000c40e02c48940055242d030081c4052006c20b500c1384102c0c040c2d0484545c2c4d0110340024400d80a1648071084020990710380d582d0300180c0c0c200c1e10f5200554000103c01d00781d000341c1c0284040960210440aa03030000141121780d4541d030f21083c00002c02070710407500003c0d004107011844000504001000e0400f0794491300007840540e0f02e40008941e94403440c070900d14421b025080c20006207003e0001150000030410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 219450710 1250 219449460 219449471
    0xe030a020706023d02210705030c0307110f0313030c0b03070c15270b091506120a0212031b0a050a0b0403051e040914091c0c05190c12030909050a 64
    0x4c0101c0c0c12005450a0320304802c1900070700441500c1506a1010a5080c018114100b0400703042c654000180404240190341080812002003000342c00c00303038030001d8201c9995000a134842014001648401c490403240480003181c90b5041d44140c81c800d0044e0b650340c0f98036105588400c034000380c0005e484441e0a47d28400700b00b28010740140b2444656040c0719806859200b031130995494030009102e207025410030011300c400c07041c01c410100d40003d01110200c0f070a5160704101420b1030b12510000394404114161003000b1100800a0052148042c494110b450001a406a00c4400c1d0910040c1640c2111011000040384810a1600107000340340642c1440c07980b050000b800c250a0215440041c1d000c502004541d096014410340d0300c03031554408081e0708164144039601c408014180010905948410400364815600485200e41103421a00300341902c0c0c0c000e00610000300001d60350301c546c0078800315644c802d01c1030a4402a034181d5440c16581e01c0c002d0b070707a001014040c01000002d5100c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 219451960 1250 219450710 219450823
    0xb060d09082502010e01181e0e130506090d0906050f1902300301090e010e03070b0105010801061d010804050f0708100506090405030d020d0209040e030a02070602 71
    0x110500e05030071512502d03071003180e0b0baa000241003011180c640c43d04004000510110342801011100c045520404404002940c0d004c60004000116044023411107500303c1001010506804c450340d032540201c06550054841294254940f105070282101103255007108010700740c800d50007455000c4501112a0400d00d86051501d44041d19040d80c00040c0e01041d280d00b1855280f007580c82e5240001a0121174000c6403c03001d44190205201b07a0b801c2c260760b0654814050f0b029042410343e0800b81c03042d2a5103540030b18041c02201e00c280101d40c00503002000104480c2d0281d1703800c121050440d80d4100241c141070b001100c1d0204020403c5840d801806070700f00514a007080018090803081c40074001820345640d8200c11144020801c0d803044610b1004d02011500100403624078803503140c009a920200203520381c1c040c4c41271b051101c1c1c01ca840e04030701461449010007d0500000f069081d101a25514842240c0d15108800300c401500c40050b035040c5901545001c01444031180b802044501011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 219453210 1250 219451960 219451987
    0x50f0d06030212060f01140a0b070203070308070b01080d0201050c041202030f070605040801050c162a031103010f2007030309150204080d080c0a031a0a0314010f0b060d0908 76
    0x40d000f070100554000001d2000100b5450b01c050302415056031403801f1900000005100b0102c01e205200764013070001a0300041d5241404080301441d044001c2c541e51318441c2c80e1a0416950074824071149014100c01140958410300486005030015001036080038104101e1600000759210103c1c0d0510946580c2c401c80e01c0103002c3c0d4002002c1e0303501d60503116490039030802c1c00d50b00000c00e90302d0300c440c080245a801d02ca02c0385800086640080140c0f95030080501ca0b003105054442108141090311480002008038610150717564640c207030000d00800e48076070003200a980a131201c180c0d200064040c294800341221022b41403450184c03801181c3c0d514070380c459a100c0ca4451514014903600040c2c184805031042041906091a03483c01c0306152822081c2c01420b4000c00455100b050b0302c9a1a5030f45e03003001c19015060220000700b045400c9540e0b480c080c015102c1220700c010455003070207070314a03c1600340e11a901c0c4142c0050519032a150680c0501c07001400d1030f10f800c640b80031013807242e040511403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 219454460 1250 219453210 219453229
    0xb06060702150301051e06120c0c07030b0a1406210102070f05010c1803080a0507170a09030c0f0501080f0604091a010504060e060f0103092607020a050f01050f0d060302 74
    0x48042c8115542e50402041c003401900301940c0e1080d18001446194071505c032142241e001c490503041d5001d10703450b0080d41c00b1940c07140300080360440c4100c2e00040203004040000300d0089100244c100007000741080900040c1e203040f920305600260100810414001003010035803c51110f000052416074141c1d101e58001c08091800c0d600741e0340da08491400705411100380c441c00d00108607800703001851903072441468498082c14908005002c40c800082041d2030740000744541642142c1d40d11030b119004010040581440240c420a2910400141071250840d1035015110180c0d920a96955081c424001d0070740c0141c2981d4009039181e003480c01083c20030183c6040b16107454400900e81d450f220400080e5240f0350032400c3d1411900080c4a0b0130750300d141820344158020b08020071400154200f020760400c0290721032904174420320030303250704c5c944840040212030310840d81e006906440d201480300540c01e0196813800706004002c6500c03030056070406407070410107140d80860085d8072680482d11280 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 219455710 1250 219454460 219454489
    0x203090d050606031b1003180b0a150b040b071e0c030b150a060c02100207180207021525060b1e0909060c0316031506020f06010b040b070b06060702 65
    0xc10942c10b02c4002d240074081800c800c0412000c1c10807207003101c40018014460586200c00341580e5800100081c0308001300d610344a5003041d0110850710f00000380c0c001800c0e9100b011062030800000200300c505000044c0c405441d01d40709054144075081d5248140c1e0005030b103040040e030f6101c11124001540c600810f9000c0c504c03a480e100c03c1420035146103480594100c40c01403240200d00800c1c0b09560780121031110316501112002c00c032000102c8140e044c01160340001c04407400200100e0082405500103143c080e1081c0c40c0401141303049100d050143c09032101a015002c91a40c20b000d2807003001c1041e00c010ba000d4440084d11285d004001000c10182886180080030110180070180c074100041030391000c1c4000280a451911031492200c9101c000d01d041c0700700c10380c8102042258800d610007007400c01c04552220440d5100c4038041c0d42d40005400305000d0740300302c0002007126800301d010b50741100d017801442828003800783d0b510080d07000c0c01420250080030902800c005070750fa600030000182d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 219456960 1250 219455710 219455713
    0xc0201090f03110d03180b06010509100801080f010e03180a091a0405060603090703150b03010629040e01091a21160513020702120f0d02011b0c02040504030203090d05 73
    0x8803800c3da00181841d2440c4822818585800e200321490307000032501164030760740114900540d58032040181d8860042c1c0c6041500611a801c2a0300c4264000c641c00c0e060301c10041c119600141700c40100c070309884004408550540003170014242006400e12030004001d0000c2c80380800d141c484004004658002c8110400900055044034072424a4451541c01a0081e00c074580b45140140c1d4540c1e407004a4030008000c8101d014084105000c1a40003088000004009005840e82c2d2000202441c0d2800070003d0207075140304108510031030840407641100d101c90074001140e0b02c0c245000004001c12940804d100c04500f2840c03503556519418103040040501d803a500d240230800101d4a080d00145c0d02c0a40610380c82428040b0790388280c4042401c0c100e0100141c5c4d00c03201803000c6910090b441c1c0d0040010311036203030f070056070480c0866040d814444540c0200401007241c401e82d49183c13142e062131000709410000c41009814260072240d4000c0c0203004691800d10341c50040b912100c4c0e9078005071880d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 219458210 1250 219456960 219456977
    0x5091603230604031722151104080303010311060a09120c2714061e040908030903030a0f0506010503040201050c1e030a080a0606090509090a020301020708030601030b0108010312030c0201090f03 85
    0xd10344282200c40e000010286c20a410004a0301c240c2c05118910340060007141107030f9140d0449010b01d800c18000b140c090307020152120b0342d8a10b2280e50f504280811203003a40c04503801072641c20034405a4540e00705640d290f110240c540705038800ca003420b0b120156a90390cc5105c000c2355444a80040f1100d2502c00208100b15080035a012000c4a04019a50070410245400d000d01c41d9100460440018000061381c100c440031180090001d242c0e0000c001d0000001004004100700003001031072160030a61410710101c0c0c2242c00d6a421140304071500c501242040c404a0090f51080c1d02410200ca082d50440f107007601c0a04206030495000c00340c100f1a45d00004107151516440300d00e0300d8004200302d10038410030b824101c0c0078182c5640b40c0a414000e003d804009524000d0030418402c080e0b80140003190307501045e003000102c81d4802c6460501003418101ca0420b9540b00b041500d040703a070001d0040c0243c0c038650904801030084030340090119034072507400d0783c04078109410060b0005d210f51602c001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 219459460 1250 219458210 219458237
    0xf050a0c1401020105040b181009050114090307170c01021b07080d0504150f05040306020307031b0f0c020402031b160b07260a0204030803040501050a0509160323060403 74
    0x5009141009072030441e410581031100040045428a070070221483c10f012131501040310451a04104100154000e41042c55030402d000341907004a01000482e400d02015580d100a45a83c9120b4804c008141c03000c900e01c20200340e05568060440030400a00241c0340c440e8100028004840c24420070400780c00c0030004101c4050104210004603195060842c1400d2034203d006282608008040c402e00102c01d801488191045045602941c0e001108544900303000740010018002003103d000e07a5107900c00050b41d200c0c0248070482c2400300341c0d95984d20300c00e07281d4280000303508090501440300340503006d406283c1e4000405000786917041c0128018441050401400d90f41001c6d00c150300b40059200d00c0001d03a9845841917101c081b694210a61548404103404020311803a070000d400f0003804024841004010740106029412003c001d203d26102c3d0311030035884000c0c2c0702c20006046480002000010504100d0b00344480921440020201102c0d0455003401c0040340c0490000306039280c02c68 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 219460710 1250 219459460 219459479
    0x5040302030f010f18020d02060901111606030b041b0c060b21100c080c0304030504090504110a0506090f0d0c2d0e040210230a091415160f050a0c 64
    0x1400359610400c05e601e07081c00741c2c001c00c4c01c6900000000e8040e03400040c4138541a402010020400781110080f150042d4040b0798145911030a03008050009050084102007071826014030034414140c9003004c40b50700c0504405403011002620112a0380f500c40101e941d056403032410654144080d088548412010155051700f8074a040064100440ca01380300181102c0e031002c60032354080a5613071029900d403241d00b804d850500555124808071410901080304000411079100c0c0000c000751403400ca001d0711007081260034018040825040402000c1c512140d10300b907640c40001e94040c0c1106148252900c1000e501c0b403410410302885110f07071650403009410784c090354400802d240d010706100350410358002040504510042d00c1040704824420b1410450890900d1403032490100643d522505c8441c00344c045013451041e80291080154890300c82c1c00c1070a40003c3e0f0322801e62610380740c490321003140e004614401d00d0641d4a028002d1801c400034100300016100d0500515401e0030080c9050440d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 219461960 1250 219460710 219460721
    0x7110909031e161202010b030703080c0d080106080c1b0105131a06031905010e1516050403110603040305041a0310090e0a060c051e0a030501080a0f03030b0105040302030f010f 77
    0xb0000c0c070001c011541403c4058000e412516a00481599407415162030480c05000300d07001c016414004c5100005c1006031000080499104003416905412000c010986220509101d1070022882d080c000580c484040c0008110205052583c40340f01030440001c1421100d0072103180314200d83c0300038000c00380134184580c41800c418100c076095062511102207621403140c0500c40b449281c000c10181e040020030b4010303207100345025048602c80e9000ca5100c150450342503600c000038800d80c160701c6000600c10b608540640390441d150560344404e420621000f6030000704180c00300034060002017155101402c1c91030704841c982c80c80c0346d00d909009443e0f16010031554460b04007645415255808041c010484076031942c0c0140000030b07000c00c43c0070280c03414494842880800b20300d10841c507172031000c0500900b10748400ea980401080c0e884070751143c0c1c1c0f69488007002d05419041802c8000192003034005c25000310040c034000341416a69404207107404059600c001c01c44c0d442c0c951141c24080644a070307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 219463210 1250 219461960 219462007
    0x60e062203110607110105070c270b01021501030803090304170304081501120212120703030207050c1009140a030c033504090209030a0f0b0f0a090803010501050711090903 75
    0x2a844c220b201c0d901c02d815000e02c080103d06000b0b01107262814881c0422070b89000b0070320212498000c406c40b42e886100600941c2c40400800e1400000c03d9055200003141c4040c1481d140c035075100c4e039086450741e000a820081c10b000c540d101c00c00001c01d4110625400c94018801c4034011616181012050341c10700c0b404d07204950041c1d06103001005815a0805554000341e0150f41080070401103a94442c00c11a210821007039240c07001800c0d1040540c903500514040b4086d201340c3d03181e5284001044540c100111003080010300700d140c140120000200d08031b0828200500c81000e4580d60342d600c0c0881c24240d40162501d529911590640c604490308a07480200c5411219a41104018114505000342e000d000b2a1a40c0454094082c1d00e0801210b4610b98106102c41585666803511036480b80301128100f14401c008400310301140d21034000d4489941d80500b140c0d045a0801303004441c250024078054a443c1c6c0c040c588402030341c1f980d50495000e101e410020f50717174812100c00120030354401f0080d07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 219464460 1250 219463210 219463219
    0x1b0204021e0a020f16060309030306030204020a1110050103050c21100c080604060602100f02120f0402010906050702060904180b01060e010f110c010309170d0c0e0d0309060e06220311 80
    0x1170140d010802000142d0320f981c100051000d5030380c10100d0003440e2540000350844d2001802d00041900311601500350f108203030890b4001450414420166542032000410a62107085002614585190b50321184080d45078056080d180e070a80b074518000f9500ea0030102d050795100d10451142d48606500c0d4400300a0f50305101562070884001e5603611210183d081d1a03a07101400078544d442d41d011955110800306022003d03003070245400781c0d04441540d08a0100300d81c1400001e10314000c200343c2d0181c603002090b581c00d00410405100203815081c103081c00300c808d54015000060b07041c44005018009545d00d10401c11407100014000e04504201d120a0000e1180001d0341203030300051010f0003100a1801090440c1e59190800242c0525034003480401e00100d5011000c24196000c0001c0c542103030313201001086c13120240705441d498054041c00003902c02005200b11405003412000078600074003003500c0d2144181002d02c00d2a01d04440515500703004604006010102c001c80b241d0308401c0b074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 219465710 1250 219464460 219464473
    0x40609050f07030f0b03060a0b012309090a090b0f040204061e2603040b0d1a2d03031204020a06090819030207090f140a0506011b0204021e0a020f 64
    0x104060340c59070004202c4010141c650369a1211070110f90000609000301404407462030802c81d000300041c22031124058009031010a50315910003180c0351030300d81c2d81191080d65250070004400e000e144030000700900055900c0740e56007000100d800e04000d11458203000840c0b0141018070400090310410380c00402000015010070003a66401c00580c0d04a80e4400c00750030901c8640100d12900c1101c516028005010204001511484480041020901c42c074420080002c0c0000101301c00b601c40403038990803c0315400d0648240950002c1c1d5682c40360000c41c402001c42003040003038610340c020000150100b11244c184011401c1c9211200e02074600c45c2800f040c2541000420350b42c03001c00d0540c0f103c80c417040c4109081894002d0050b403000e42011042804900040111107021b00000b41c80b80701d06082c1000001d038409107038410103020b0b01c016952100c0650b2030031216003040e003115030180d90141e420880c0e80c014842400240f41c1000c0103440e41c0c2c2d1a40c400c4140641020b001078140b480541004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 219466960 1250 219465710 219465721
    0x203041401050306031507120f050705090d030c080c01020c06061807180f0b1b010903020304060e0a0506030901061802071721071e020a120c0203100204060302070204060905 76
    0xd0014a25a110a1810700e480350f0350000000c2c5860b83d0341d0700801c4480302d040c0921000692000e001904220380082c14802281401380e148122401250b020f000501c052141e000b10b8600444802501d5001c3d25091a40c40d00b252a4006550b000c031051090f181e60000b00300d4401c85051220325031100c2c044035400242c070340c01c41001442200050600d030070400c1d540540207400240030801d40c00381817407806c902c00c100e4446000440550022030f81c19a04004407200103601401401094519a815805182007500e0f14800f036610840f08500941d204152030f201040e10344a56000d035110381a010f0011800a25060302100032070b80d4003460b42151401003140f00302281c4502c1c1103018521010b0b4460303035218011888044081c40b01c2404090300031503a414490507540c803000c41503030a083c240d105940c00200e00000d90760f5244100c00186024881c0c00035400303060152500680c440c2c005401d413400d45501035101c8003281c0c8039401c000f012982c007190307401c15400e0500c101005000348020420450410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 219468210 1250 219466960 219466979
    0x60b070213020903030c1005010e06100207090f090203010f0504060b090c040e13020319170a091404110409140f0f04022806080a050708060d0f050c06070807020f01020304 75
    0x298002070075503640001d41100e143e1810011601d541207501c084d10600c089403804000989000e101c0c08009682c0c40340031407450302d03002c040b61025200c00c0d002021014a8518000c02404d140e00c80c80c10615921094800941c0f000c2c091030b00510f031355100004062500d03203403440c22103000010300b42c01004100c08110042e18407108a07001c0d20514640c84445546900c00007006d00c810410083d0076000d1284c00400c5440070400c1e0000c2540300e15444504c0d0148017808528a003d9010180c0000700c00d00c5042040c0361000740c10441c052005840454004003021100c031031944590b100c0d842d03113580c504296884443e407540c05500240000c0c00c182030350a002d00c00c88400d5001600280c4188850001d1090710f003e1190485005214550900351082c4c1c2d401c00600402011900840c080b410400000c1882e880748601d14400d8400810311803080390592141e070348550746491300700c0b150b100e140d41c0104286c1d40c04d0301070290f803446441c4142c4da80b01d844c410b0200785845800214103542c8180401d1042c06613 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 219469460 1250 219468210 219468229
    0x2120f0a0311060f070212030916080f010b06162a0e010f14010c031d0405160206090a0b1611031c0b03060106020316060b040509061e040215030a0f0510050103060b0702 74
    0x3009801d5030301ca0f00c0c1c00f40d1030780c03c040d00f00c001c100810007940c0b000612f004010900d01c4a0700b847e83c0080003844502410300c07006103e401c0780000da00c41d101892000213403017581141001c03070329070b480c0e4000b0350754002c0d19030705c42d01c007d401884001c681c0100400c449580b5103002d901a0008241780101e609203040060030380c00000c01d0050900081d201e00d40a180c550380c00941428000410522240c10410408402091008a4507006000313010002d800d00000264003d420340c3d00034440c80d005e540e105894428048100041070400441c2264010b0b4418104090305a040458501014a64800300e0352000c94002c5000c0c00d00a401c0400100320b0940c0101c29562100c00c000ea450521518030f140c0440189095030a140d801340c9072405000b003118001518034419600d81500d900c2d140007001e5032a46140d0102d5009502501007090703128880b0f01308018503006450050040340c51a03c0c070343c0c00c0007595811240500c03400c05140003000baa6078540070b02c100400750105c0c02807400903142c010944004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 219470710 1250 219469460 219469483
    0x2c0a080f0a15240501030c051603080702030d05040507170a031202030a020708040807140d0506040f020a080f0a05011b08012d060c0210110a02120f0a0311060f0702 72
    0x80200b4190b4007008554212894042880150704a81820310404580d281180e00031540041c2c505039010840900540440315000050009185070201d507030741c22107c0220060043c02103000a05c15035054800502a01c0d020b1803003900600440c600303142e003d42d8841c3c0140304001007580300103139800c0480d420245050341c4000104000d03a40f6500c128001019104286005101c9000014000340002000c503030201652002e0320540010710b581000c00c8030011600c41c0141c0640c1203100450009180450b41403007042c4041e182c028801d0746d842f041800c0989030038440080340c212021517010041c0c01e11910798404180d030314124969910090007080700340d05000302e28803c106501013082080001d4000c101c1000e0004a5520860300c0d400d0080c50342c004140201d000b2a950f21139014801e001c6c4c2d0340480c7c80b202d44002441313411000d8007002100304c01c40d001948580a0310210050311602403180d030480d1030103901c3e5401215015040b280c0380800044c91140c0e10405502070000b05640030580440c0301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 219471960 1250 219470710 219470723
    0x3050a090b150604050a180b03012a0905060c1b040219080405070e070c1b05102102031e0901050106050301032607031d010c080d09032c0a080f0a 64
    0x30345180120303c1c24070403078016136400141144001212480a585030495403103500d4240040c6c50b5120506080e034488219030640c0c03065052610329003110758000144000000c0c942843c081d640d850110f44d855100c107401d840a03800100780680b103e400c21262038180c007400e4404603c0e03c00f030340b0018200b02c0e100d0864001017010035808181404010007800019184010011810f030078250303409800c4061142c002c03900d2a441800c040d4500004024420450f0006080d540c41c03803414800c12621880412020400e1603480f0250710204022440a18402c071740c06150a05100d40c802c43c44440e4810081081c01260304110060102d20703031004c1501e044a9005040d800703020040f9880038000d0103824203041c0342c00070100e0900300341640419060800c9006c09101941d0350b1f85d000044800d2454101c010b0078818003000040c002619680c02442c2d441d00038034040000c17580041144181a590300b501e10710b480c82e0201d85203c180f6104075901c00400c01e0100a15040601010711503c0302a40d81000d0100d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 219473210 1250 219471960 219471991
    0x30601140102011113050a0f03030e01050f0d05010b040f09020405150a170702030d050f0f07050a11030d0e12030405060402040f14040311070603060b0d021e04140103050a090b 77
    0x507070b4001d4004059040400400703d0b112885c4007924000e5034410f00c1010b10400080d84002112501c0e40c0b0440c040e01e4043e600ca068131840c200c0150303080d80c4810702540b040c181c01c001443d00c0c0642803084034083c003084202190358a00d00908040b840c0d550350456081e60f48104820400e81e41d900044210a454082c40a0b442d882004070030b44020505c404464031400345c3c2820884001d07404030041241100811040100d5110806003210b6080c0440794202441c104001148155028001805055185d0325148030084a680c02d1542107812640e06011201c0c0c49082c040e200d02402d10203031124034100da0312542580740c983c6445640d4070303000c0e01c003038000c0f561400b1081082500e900800e90307290390320144001c181410300d030080c615404100e451106014824011410b144607020b980111103481002906280a030420000254800b02180740e46ca115014000b035400c00f101d01420041440300114002034580e2030000d02603480c000c1140040c0e52601e50b035100007510280d9126000801002c80455 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 219474460 1250 219473210 219473249
    0xd08010e0411030a080705010507080103030c170c0102040f03110f09040303090f060e0a0b160527030111070501060503151501020c0306191805030703080c270306060f030601 76
    0x9403441c0b0014150b030507019460200d024016032034000c28459104070000c00c010b607240d100031141e03844203010040020705405807140c0450310501004100809001c4114507103544089007508980c010343c0050302c00300c400081001480034213480c901500d0000e03210720b03840da02010009503030303410b00400040c185035172080c2c2041480b43c0748002000c03913580020200714880c16180300b00d82d101d450410840d0141108800201e0101c0e003004600030144041d100c1e5400c00c1c03000700700008902031941071a42c1080314603040420a035002d0140a4101500014955a03601305007001400d48a00d03030042030182d4090030207003c0c03c0d100030401540c8821425103160403101510300417820300c0c40000c07400d42d25100700814088482000c2d04505d02415400000300708002007a800e1800360100c01602030007641044c410080868040c031009648003030814030b0315207000580d844180e180b103400320300054aa01e10715111a000d0808000c11074110301d0455900565042c40700010341d44170300500550491403140781c42c000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 219475710 1250 219474460 219474473
    0x3050301170705090f01050f0a06023304110a090b010203042112090906050d02060307080907030f05010501090e010b100f020a02040f0207020307150215250206070f020d08010e04 78
    0x6450001d00b01401405c140f15040c545050a0180c0382c840c0c28412142c1050345404c1600da8100ea1070764014004041c2c019100034a078100d500204030204a080804510588581a0051065105021035200b40002600340299000701e500040d080515040b54016240c3e0000b06a50403119051150010302e45002080c0048460b40d69008100c00401e4460889442d00004610262910131404000807555601005601c0901440203074100741d0030404a030f039243c8074441942c0c0c0144c031203048852584d966920305886071019202558565520401440350f00740600a102c04050708400030321180da1001c00080240060402c078006004040d03240000d030500901006c03030b41680091041022800c000e4000d0043d600c00c12080344280646003000c2121603200c3e000c2c5007101e100d54020030800b00d480c0c00c80c00300910068030910103c5000d01c80f80c038181c0d5149030308d1026181181e0181c901420140c40140054001426003800e54008030f031035000e03990b80720444604440b0800c10800007a00c0d00d041c40c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 219476960 1250 219475710 219475723
    0x30a030c020f1503070c020102010e150a02090d170702180402011209060e0d0e03060a051014041107030e09150303070b10080703051b010c150c17090c010212070305030117 75
    0x8482001300c2000f0300740343c00c40c036500d000324000e800a200c20341ca07044219854280c3c01c120300c024010360b00d0103d01d011815601070410b4440c06412021580541e88620504540c4c00043c04070503c40005d02c1411800d1103101c1918001104030342c0c00300c038203041d400a000c0c1c0e8050726a42140542d100007400a00c0f9841d04204094010710050790103900398068020491aa00b00e0594040d01c07400011405008151140300c0c8108a6004490340450819078107451154240e402030307501c00d03101d8420340b00d000e44907402271a00034408d441d40e00385141d1400600c51114030040603540b0900542c0b4848810792804412201c8141c0d006245a9003503131441041100c0d800c00d0f4000100c6449800004001c0040005580009110540109010a9852004562503610148010801914080510321418664001640c1c2042a0818140b10b924450010040d00b01c21108208964030210750200b107035805111398851005c2c4208910302d401d0031910050014403061203281902c1401ba140400003541c14041d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 219478210 1250 219476960 219476989
    0x12030513051e01110c0f060d06030204110c0c0d02030d03090c0b030c21011d04030e181005150909040f06110901030c1b0605070c15020307030b030a030c020f 69
    0x10b480d280c0000d002c0c810701d44038a4080302408140c02c4040d12459442c0025005a1004000c003041100000e40301840269048005078074080c0382c481d0001310069459000e41e601011000c1403075034440403ea281e00740b0b8961881d40d610300070404200f8080241c0c901160034200d6103070310b0501003884102c2e464103003031540003079114003503040c4040284003940800000a151101b813074600409068003080300010b5550003031194030306652040740c1c11948984a02e0045a0044c0203040c12140c0050700d4000c22101030741c2080f4200303500d010900f00b14003120b0780207200c0090041034071908421150690181414440c19044611500c1d40c60009010085a5082440d078983c1c0500d084c0102c403c0c03002803c00541141d0f0030503011905001032a00e115100f031510b01c2c0458810740c0501c64103451511210001c08015101c0000c000c0801c24820101e0b0201141d82103500c82200c1c01682c07881c0c2a04c00504448020072000d21940282c00340c000881d034802c0c48281e144d50102c840c01210210240000c00c003903a407000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 219479460 1250 219478210 219478219
    0x80f0906181002060f0105010305150415030311030f0f070807020d0813050105030c0703030c03060503161e080607031e0f0c0f0809070e0a020702030a0c031401061203051305 76
    0x29000300541d00c10441c41908001542c1c2c9035150b0400c81420b0b0f8840c001107403040880751110004200b1584030360401e54100c004171410941025010020409445003c6241c81c01444901800c004050703008135494070055510001c0e60504034680c680b5201d9118141802d55074072408204101401096070032200c5141d802030030207012014600d842800c0f600000443c243c064455140000c1c154080e0302140d102c0c0068803802c500d081d086070713400c1d401040d501608104140e5210030204030340c3c608114411502e44d07010940300034030b86040503c481c0c4040521084e0041c0302051000c00c1801c0d0005091500007070241804a081c228114000d071840e1180119007504c1400d04c2140c104503040d5510410394007000381d480210b820710040c402e40b41e80c1c2c010f490710b00080c2e02810007045a0200940d00c0c1e50001c062003000341c90003007682c0002c0e2904500030070554628000382c03030803c06c0101c544a142115081840288803c6150450810b844a521403014050000c002070780990002e01c10350340d0000c4c20b00180b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 219480710 1250 219479460 219479467
    0x51005010f030b150105070303150b0409060e0109110a080714070804080f0a0209060d0f05030c030310060c0302030904020a0c0218090d05090901140d060c0206040c05040513080f0906 80
    0x8200264150761106660740e8a4a00100b03101c0b58440101e02c1c1000811307150b507881d025956408400826080d0305010710049003200104910314410004c100030700c003c18010400508084507070780030440c10b03403040305502c0c501080d04d550494407006542280e4490300f4032402c0d03569a0030080d1440c00185030002c4603907000040800030450410040c0c41aa00d4210413034410000004525640726a0380f14041e500102c0080028000d180040c11090b00621914a04945001e07030390b9000e195404c16004140c207900080100001411260102c02c020600c618040706111032f02e0710041d46a00ca030b03001940c042c2d6000285c0c110031a01a01c45820131039405001450406034a0611700c2c18058155540c40c0f55004080c42c50074040e2140007070f05c0006000600c44207035a4a401e12001015105c00981e6801c9043d800c000c1022440500c03540c1000d80c0103070003500ca245481e1a00714480d003450340011344210316042c184000400e105104545c0142d020f400b81d0f586001c0444d900b000c038000d40d485e0301c5e400301002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 219481960 1250 219480710 219480719
    0x9090f01051f060216090f060308070c1403030a090b0d091b03030305060d050705040504050f07030f050d050406021c0239030303040f03030f06090908070203160b0a0c05100501 77
    0x41c260942254182038491541d40b03600040ba101d03401480354511101161200741b1241c2e4080e4442c84694140d04000207205940740e5400096821856080d12000d4051000700028041c2c0402841a1070049010f18900040c4060240050455000d070744d10800011842180002c125400070110541052500c0301082059051343ca884155000460000341008040780c41402c03c00c0c00e0110340747c0d110000d004010306003000d00c030007488024410350b8580300e01d50f0b85400f1034005000490140d40900780300490103109003482440c050007000b040b820014100000c21100f6400b048070b45100562000315041041c0300d0b64204c9c540340b40410030085055102011000418102c032070102c8a00d081001aa0501c2c1148105916800112405032004e0000e800c1c0d1170019100f544030030710000750300c2e0001600399100c08043c01210704028081321140c40001d5070106524003002964000d0340d1065421044034203001e00c402c0c560003401d80100c2401891240c901c208903003440f264007903440501c000c22039982d49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 219483210 1250 219481960 219481981
    0x2030a17030a0b0603060a0308070f080301080d02010606050f090d030207030602130e0a0e0c0603040611030c030601170106020c010f0504080f031b01020a05040512030c1b040b010804020a0509090f0105 88
    0x250348000030302d031500f0841d018500f041020b4911480000304414081455511145010351003610102ca104681500d00000079249401450103428404020803144d110800d000c1d003101c4e013a4101c6402d0240600c0714801523204c0c50103d940000054901200d101c3c40c0d403405030710b0240c0540004092034008901c008100600031400c0e01142c41e410300800306602c0310081c240c00c4031085405850795801034604075041c6e050003401180c0107803180d9000a4081081d001940090f0400e58040d1100400001404403542e4031100401c0326018001a0f00e026500d031003000b0703584541007003005061040c0c542a0000f03103805602503400500580b01038506840c00c0707071b10003920f036030204813985001d0308103a40b000207802051080d00c1c48482c4d0307919070f00e24003070030141002400111030600743c183e80700400072001d03035a1043c800200c484000c11905480046490300b04030585448580c40d504000c5903204000140c0da42a160408449080d5001c030700644a4800700c5007440104c1a00c00301d55800d010030300262400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 219484460 1250 219483210 219483217
    0x5060a03020d0c0e15120106030b01051903050f220b0606070606031b06090803030a051009090506060901050d021e030309100809060705040e0417090301060902040f06050301030302031602030a17 85
    0x80f20780b00045d50341c0300c020341d40900902042d10a50021040144450f5010b54061004640c05041582c2000240c15845d8106032515400c24002a2100700703002d4140c0e90511401d402c50000300d81cdc400e16400300d030b4042110062004014065281d11400704401c0d4aa000c12142142c2d041041440604e45038181110142003168100030000c480b200000303142d510070380c0250241c440c00005075186454801030180038200c05403902000040c0c0c940300051810702e40c400c40020300d01c11000f82c003052814904100701084164001c9014002031a8003000695039906a03158002d28420f1b0301508000c20400b01e07155002e030700186a04990340000c003040c00758000c201c4a109880c00d000700d0b0801c2d9103100c400c55044c040c0d803240303601050781c4c0c0d00444d000032584110075071078a80800380c10b4100101c42002a0965101e0f90010105550015061201c00040600040030f0403a50a2261540d491694001d54a10900c0b8420305201e0348160f00a04540d03007848818465504500c0c82c0c141095800c120b5581c5a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 219485710 1250 219484460 219484487
    0xb0112090b06180c0a11070e07020d0e190b0322150507050a09030b060409051b0117010609031502040e010e0a0e1f110904060807061202070c05060a03020d0c 69
    0x43c81d9450071101400c8030b141492140b01203092007405d01d040d01005850400360301d0000c200e180141e040c045410031108583d0f5200780070580c020b00e510686220f014240c40c90410304503020740c07580700178690440001c0302080c0858006161480d038a0b65a0f030700c00c4a1414480e82200707010340094502505021184019142010701c04008201c10b465603a41961b0502c101c00b40322000c502e01445c2000820003803640702d43d02200240011500560740c4d0342e89401c2054048040915440448910b03c55580c0000e1404aa100751002d031881541030220107440080320b4400248604d070940541d000c45001030f01543c00401240103001c4280d6111115500640e1044410390600d0345032004240024100251540d459501d0600e19110140d01c4801c400103001b0760001c060f030301130081060b401c10351100c2c456140108100d4028002050501030001c00400c002005038820038014000700d008598000024802c8448c100c5002d907882400d84402c0d4043c0c00794514000d4003d1901010100c0c81360031002d01310500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 219486960 1250 219485710 219485719
    0x61d01051302160b0403120623090103080d0b0d0c090903030f20030709080f0f0d080c0d0209010309020402120105040e03070807020d02030703021003060807060c05100b0112090b06 79
    0xd0100d480c68400c901441c0000c58841c41c0f11000080131600c0c9020150300507010307241c501495000006c0010a0b940c0c0d0380e100250351258420070715141000203441130445581203848445951450720f540c80d490089103440b140a03035070740c0b600c0308495441054060515030302800344000780d80c0d545a03031002000b5421041e40440d0038000300c4500421540300f0101c8810b0b00300d0041c002c00702c1004503841160001403021003030100c8a5808580e1100801c4065a82d901203070040c020001521032040c10003000342442824042000c3c2401400c507540c0095503003228182c1d20060b11103500c1c0d00102c0152070752900180d0000c0c400501404804014401c482c1a10700a441c2800340060344c0e080707181d480c030400b0409404c0740d50170301140c8014a07180b11a107500750300040841e00704503221340000c1d90404e810307051240030035500c9001300300c040c0060100d240203008908284003600b60540711140c0700c118006010000e1a500c8001d511035070300070720490094641d5040100000c20882c682941c540c0f82c01d8036861300c903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 219488210 1250 219486960 219486979
    0x13021905030714091501120603051c11060711151302120304050d06020c01060306060b2805030613110a0c05071a19020109080f210c1c061d0105 63
    0x1c0d05501d8000f9000b5102c0075040194a50300c48500c4c03003c003d01c11981c1c0e41040440c0c04081c01e80404d078068140650300440240034801146d504038506401d00305458800d0065121003407880e5000814020341c003c0d41070400340d02c0c2c4000c8071005428107040754070010f60040e5940500c6007000911140f08601403080e84e54040690070440c035079a80e405144109580702440382640000a280358010700f441c0f8000300d00100d0034940766074480003500c0781c81d003158101100100700085164194068040c1500c000840f069a000d0f503400010414880208000c0c001c0d5403100001e400744010340d01078116100c078098100e031184185103005090a03a00782c0141c8917032003a010b0100342040e030b1051403a450702d00c210350709141c8192905142c0610601104090541d542c41c04030300041010380d00203105403c01c03000855551940b076228010000a44503c0040452980041000d012990001c89030040b03688450304180481f0b42041c10041c000a800088104611402c60543c00340403c0b9124143d80307044480c03e07075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 219489460 1250 219488210 219488219
    0x70903030f03110417120f0304031407020904020f0112150602241303050f0d06090c020606010c0818130207030e100c08130506070c060318020a0509130219050307 71
    0x1556104100304503c2c46003008200003034840451444440c0c4070400c16200b22004000c6071684d02e03082803c0d03403403103000c001040104041e4080001c4801e5503c42e04141c0c18849035401050030031000400003409030a5890032040d90368041c5060481001480b00c06004000100803808521139891198001500c19841040b049540912000d2001c003061100c0541c02e03035510806c52a9083c10031000d405004080110210211b02c0344000c05503841c264401045140c60580d40c10101d4505040c0c0300110b401041c00c1c0221aa40483d9206a05411042e01901c440080d002d1003407202a8103400c5600c4540c0c07603240c0340302404580290500754003945030a110800d03030100b8080f01901500010700000d0b00200381000041501010b4480c1442d4801103420480c0c4420202e400d55100d10030941c1d10121140301006856854040c2400001c584000e40316060425404a414001580181485054480c000a40e103076000304c200b84419070001d00740307004949880015042d2030030900444e03009000303000d408603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 219490710 1250 219489460 219489467
    0x20714040612084f03080a081503030a08090c0108010503030f030a11030114030c27090109080a090602060c03010303080406020306040e010e030d06050a0f03020607060b030105070903030f 82
    0x4440580842d0410341003180d40b0680c0701da125002840e481d0030a450f0641a0b8900304200032080d2001003400c0c0300440d0f01100c1c480706890402280180b00c0454002170001454010582e0b28180990606041c1c9460382c081404141000c071201d41e0705071101040c41400e05611003501406070b40100180c07510700300d100004407507100007401407c1d0954420402c1c00100080c92005580c00f180d09600020000f02402031003901e60310a83c03003000041010140c01d0580e2a040c03200ca2200f0b01c00b2141141c480c440d050b421034105600d108184007512540b0001511030400b900075101e22a40100019503588802801504440c07490240341c006105010010711803a10b0b683c2200c0c181d80d05074032004c1407507482d540e407903002c0d52004042a03089501c1d44000d40151009026a8203e02d81900c06951181c2c80750b015502111441e6000c07a20921100d0710030048501302208a0080e84e406072600c1c0d07610400360528038040d05440400981541c0707030104103c1c0c8a980320b55680c084d030b4807a94a030702088004000c01c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 219491960 1250 219490710 219490721
    0xa090201030612050c0607030e090708090f0d09140307030c0e090d0504060507230f1014060f1c0c09020403060e0a0b011e0b040f050901080f0a0f020406031202071404 73
    0xb4200c3d4000d210303031040c506d031010141881510034508071821050300004240c00090a50b900000b01e0114018081440b0090210211141481000304001d02c9000801051412288100c1c0b0185891103800c0e000d588041c0031500140da00000c48c4c0388021303541c0a19810300402207c48000034040c21078001d003500d220700c08841c103c070140d50310707142409201c0c0c440c550100c50007085900e42e8007807842c00c6144684184038104600251002801101300c000403088242c40342038041d40d0344592141c0800c40c1d0340d82d51022203140e450f01528000400d0000d20120102401c10000c0a40725104400300011301071000e0b0014010742744101c80c1071003a0010920650f945803110072000b8010442c080c014041c2031040c0c5940e42c801e410b040e0285060070b40c1c0e40b1031800c0e00d602c81e030456003000003002e400f4001414031b08032942c0100003c0b0000d04403a074044101c4c64441880c5031005040e400c02a01000a41d40c0c1e641144001d50f40210344003071001d5140401950302c0400e40b04400e001d805a134401d8800f443c082c41003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 219493210 1250 219491960 219491963
    0xc0f0612021602030d080a0c030b010c0f1a0a020901020d05030c18030c1c0501060f0e150102011b0315090b03070b1b01091a0c0f0a0f0e04050a090201030612 69
    0x180c1030554490140940a5004200c4030303125000312501107000360f6001c01900a0300720464480e0051420448800000da9a40300110310070b050911940401c1ca0b40d009000c1c40609401010b4240700e0000d078680042803a20310b90500c00d80e40124024082c5042e03540e4000c0c00120000d800305c4502c000d00f90700c1600d02e404115074018402905204080d6071006013a012410310800070180c0302e00c420104001a0b404036242c1076020000180c0c100d581c10828240f042c0b2002c0c00301c00303003041c3c401450300c07920441d4a00000c001e038200c48044141134100e64003d4100e811140c0d800d83e0308007120b00719218014000d141008134403007001965900000c0c03440451044101809018001d0000503044c031484522740e038068800603100c035206c4034660147d01020301c18040d41a110b40700d44a6101110290711010032405810420110410452000c4580c180703411102e6000b110f0074540a03a07050b01005031141d01c00195601c0c3c102e8101810040c0041d1203034851030500b4800d80b81000316035154122103000c460300140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 219494460 1250 219493210 219493217
    0x33a080c040b090406080304141c052a03060a0c030c08070905060901120608010e060c2d0909010b0301060f170a02280903210c0b06060403050102030f01030c0f06 71
    0x41030001d66107240080070000009040400c402e50f4940801d4915400750b0701c40d0f001480c002e0380004644c5401cac1c3e08071030a00e006812610400d0000e840c5c013500d41e0b01450540c1c06000b9014001c0d03510024040c2d840c81494802025200140307002c4d0010001790501011100000f458285240d0a01c3d014020702401102665201130082d41450244605680500132150511201c08102c0150030746502070300c00500384030800450404248241e6510301280a00201c0c82c4100500510581e85003034a0108035a840c1840c100021786441e140032001442404580c0b500900b13450004103d459200c80118102c6500d0364039150452003a03007003103c04610903a402c0300c091400e5404641c0c4c4503000e0300a4003188070b0710040341014040000c12444c0c0780800c07000240200d85084020414042c1940f0700e60645022441d050707680c00151917000b0302c100c0d04403100030310240034140030460b1500c0f050242e401640d07201000b10758a0a100d17203404a0341c402440110303050003420f08080f4091400c55035103001c070383d05900d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 219495710 1250 219494460 219494467
    0x19031a04050a020408100c0206060604060c0602070f061b020f03073c05070302040b120c1216120b1305030d05041b06120609200306033a080c 62
    0x8100c094200030304800481c503020301010071110740500c100113100c0c00303c0c0d00c0020006050f80000c1d041580091038188038544c1404104807643d0051812200b0319800080140d07070b81d02910388000f4041100030051300007403804041032402012400541c01c8140e0726000c0302d801c042d091441c269031740700f15000281007140c080d18618198284030059a60002d80310b00000310840c50380358940010303101e0101a074090780200c400704150304003440fa4603040c0805440444121b90380500c003594904450440c1c5c0c0c098412a8840c550010b0140145030910b04880320044003141d4940090300f90300e0100509036200884240448c1c0f120152040303d09505512001a6041c1100e1111740c00080100a000f80c4101c7c0303500c003032094246024203104028140a071645150f1074001d010605c00c66000350455080d030b6141100c503074003003802240400c20031101050020b55a9850001007420010b610401582c3d4040b80042511400400742240015101200c0c101d103507140c13010790840b15603400fa5000c002071030040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 219496960 1250 219495710 219495761
    0x5090f1c03320a0801140109030807050a1b06030b030102030708011a160303050a1a0303031302010e130603020108070801150c23010b010e04110409090c0f09021903 72
    0x6020108140300c101c40403801004604070318030140140e260b80c002e64000b0020301600c035590064902400b411401000c82011b84403040041c2080a040c00091303c1410045403200801200f04008000150f015010040c004c0075580d41401070300080c022080402d0409081d007000b41814030941b44644c181c0e540ba024543d20b44060401204020014654482c108110146071885140341c445005417080e600007440c2d26041c0c00004c12141c5c01f45038103008811440030035126a40c0002525005074100309160007402d40ca10040c7c4454016807031003600822074100400c8010001c0d480f02044074000e0f00e42581a658240c03045502c66001d0051000421000841070f84a6100c1c20000c44528422988400300000c001d040c9000c1406c810b488100903910380c0002f18641d648031901c8482080107440030b000701c80c2c0407900e4040600a030700420002075038900d11003041c4003c02c0c0002c0020002000090046910340000c20040d600140880f4070b81c0801111140801e8464480c21140388800e2800c4440c0c0c0510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 219498210 1250 219496960 219496967
    0x70840080a0c0308090a03120806011b0c060809100e0102030103050601050909030f160b090705010906050a020606060903120a0201090215090d02040504021306061e02030438040605090f1c03 83
    0x1004411b40104400c0c002200040c43c500301041003884a4403010001d00d440d000042200c03901c942003034004520003104030001203001c0c03c030a054034100e081680c01132ba41c4000c80303468043d5603100c01d002d05082c801000e85403401940154184e80c0a007040e10456a00c5005201000c4020f4600102c0d9070300402032a00b19084030000b81083c551101c0340100a80025141d5600344001642c1c42c046070b4122020802c0341d903800c190304600034446420054104100c6840184d1129001072165005140c0042d80d92519601800344400007564416030646900d29650001e0013040103000481c0030304181614a020340140c1000e40d100e20030014110030001d07a50751700340b101030100600101c0e0061031081c1141c0d00d0040c2030040102606081d50b404183e1404203481039800d40b000e880000541d08200418000c1d00b081400300345100101211803d02007040140308055080c4000d08410000c00109000c140e40f54400001d151640f011240140c00000640800448203080c03500c1d00a6080c10b07041c2c0c034000900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 219499460 1250 219498210 219498217
    0x1608070c060f0908040b09090105030606061222080d0510030b130317010b0a022b080702120f0306010314090c0111031c09020108070c0503070840080a0c0308 69
    0x14105003c5103000e2030b6a40c52605402ca40c0200034603850118001d1aa1f0400280071801050110b00400460030b0001c0807500f144a241c48002c40600c520002130103101c211244540c01c500d4449c40d240210515051600c0142c0068901d00405800e04001c949440140d00041058030740044140342c29440c0c0410f8854883c080110407814045402c0d2950003150701c110183c0d0090075440b0b242a580c205030382d4000d080501d0303007005e8459044007402d0321115041d0254407422000783c3c0e003488c1c00c2c00c0d1981d21003a0320b0414103000580c99110000f038180381d0b59000201440c0100d4007030304c041c1300f040071100b940840c2003002c0301c078030b09140c0c02200011130310741c4200c6420075030440c65019640352146c00e1013070680d0341034064134001000d91219495403c55030b214501d030758031211610b041c9093b01c90b5559600e0300c911030301307801600300747c1d003c10800d802c00c0390003040c20b5203031101241c80076480c00c400c00000d111880340e82c40404000030704007000501c0c840210310405c0c056805030070f5171001801c40da960a010b41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 219500710 1250 219499460 219499481
    0x20a0b03091905240934080d090b0a081f0f0902040608090610060e011704050709230105060a0507021c020307050a060c1412121608070c06 61
    0x118820000650b030505808a051590190020f85104ca0b01d0080c1304100040000c81c0500c80c0a8800070440d01410115aa00c034520f01092480744003003840d41044203024400c14455441c54581034005101a00000d840d8899010382e250350034000d9450319540c00c3c5000e4250980c001c41c007181c0c001240351b00a0541c80e414014600d0742e0029032a2120802c14058480c0c1e007001246550010b002c1c4925074020b076100d60b2100040000341002d10b00020a40504d0b845840390b402480f543d0b41d105605a80240c00d1002081c804072280c009510307013410240c2d40da034928801e860026161101c144110f01c100068001180f59840e15056264a08020301004e5844840702504025040c00300b0f01c0103a98a4010300c03003000e00600c00c20310b0302c9042d0040500780002944928440d03c50350302d003008540d4204544120083e01701c814250750196040005041246d0f80303c0b84105090300040214200240766105070290300f450180e44010711404200341d611420a030f581401080340e42d0019400900d60790010484613 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 219501960 1250 219500710 219500713
    0x2b050a0b030a061509020f130f06170a060e070f0f0207140108060a030501021201080705040c080a0b0a09111308010b0303091e040207060c0f0201091e110907030e0706020a020a0b0309 80
    0x40e580e074002c1d10103e82001c24030840c0d41f080081c3e444c15242914103100c024080c04051029007600d042d902070001c00a107000d00d01418025070014085003550350050700201003014880ea91480c043d82c0091400701c610803a080400c00441c3da410f0805d1002850784141c919081110007241130b260b0066440050044c09076030b0062001c0004000100280082d11380d41214a08a0005504041007103040031004c1d046180654500148025000e610900c050781101c0e0440300000d8001e40c1c00041850005550081080e0034144601440661419801055004480c44021010796101c14030182650b64610150364180e01c01e0000c0ca465160040041801c1d00b015402482c04083c0340f4042003d03608140420303204940d4510b4108001070b0032580200c005081880200018180303959050300124910002c042c0300c1d42c2c044c000500b003000041c0300713101411340140102d081d071030000c4008000c1d20301b181c1c40403510f01500300c00080c40d90001943c1c400303503035004100125a03402c204400305c2e01e800041c804541ca = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 219503210 1250 219501960 219502001
    0x3180409020d030201140a020705120f090a03030e0103270204021c0e0c01030614090a0c02011e150b0301062712060e010507091412032b050a0b030a06 66
    0x50b50742c1a1510003152107a0004507080f0600c090801442c10014040c1264a004009190000b500410045401404000e8a030b8a6600031406000e1070b008010440d60080100f44000c03043c1130b0011a80c00d00c0c540242da00b4022460362002d115482c0c1c52103481d01030000c0743c20110000510381500a4a03038000030502a0a11141e40003014042d105440d5102d1241d030001d074207421095034103000b6240603002d40c1c40c40000616248002c114100f500034441e941c079959440c50b4520581c800e412030308541b0030880d0242e40601401c0701c00c000400013000b1212408110a0000964020407402e4034100d420b240ca800342402c1000d04024012101c3c465020010b0280200115188031004100481c0070300a100000b02460340118960840700701500d41d40c10321000a5080141c214001994071603008151029440602c540d44034038598010800480d0112110000c0070600900d0101d1080810703015843c14030060b20790041d079a0456542c0303036885030150410310f04c440c0440d07541c1d04040d51440940071040107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 219504460 1250 219503210 219503213
    0xf0302032a0d030509100309030806010818011a0a08060712111c050f091606050f0c0601060c0b060f061611120705090f0609040321090f120305010803180409 69
    0xc500041e003500703d0100b5030204100c550b0781403c00c4640c000c09480d003002c102007849920050b00e420703c010300d40d81c1044001c400184290204141600380101140e00900c4441c0040c00708002c0308001620b02c6015192126001a800c1030004d01ca502690107901c4203142200b0280e03003000078007007040c22940503800070099000c1000c000701e11040d01c1c5060307520004081c180461011320805003c3c10101c0554084114081030801e00007940f01226214140655610411203090216010301030010780c16000305000001c1b03261f0052004041d1030b100e1040c94807140c1d208410043c2041c0c580115540044041c006190035806c0401058101402500300302c000c8018240011446035012094950b50380041d1001c1000f810701601481e003145c448030b24502a8a040804210a074600400c05000c0000003c0100029506400b440003000c0624106002c088401c2c24030444440c02c603801102d413960303006403409159100b8410181654410700140d1302c1d00c24a00485505028640f188503401580d400b100030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 219505710 1250 219504460 219504469
    0x1140405090721060b040506161b060906090b030a180c0f080d0e030a060b0a172b0c03050901050d02120702060f04030801060c1502070506060a0f0302032a 68
    0x521464655031501100c5041d11240003502100f1421200740c5401d2040520000b0398040a81c0d06486050314040e8880e400c1510308143c80780803801c007401405040b564a108410103404a10503072700e01381c81c3c229685a4620084a102559100e080d40f0084180040307226503c00c0d8110b140003490450100c40390400d6500c1d41070310b07850941e00107071300b00f494103404002d180d605108401c0c41c12611b0a113510780c11024000b2a41700d13941d50b0002005e65075101c1c804400c560760712424802030840c0d440310540020b0403d2034666100d0145c0710200b200e420b5003e001d4200c2c2e00b0b4401041d20017815544400ba00b10442c3d8060700c5603000b484e40103040c4039003407003144002135081c03014210800505003008054205103a029040a401070301c0813807554034004c100408603030084001411038142c6d1070b10449141d904c2c1080266244030641a00340c840c00000c60314244407000890902a81c1d0031222600360310340d02e021030940d40e822440004c4d050703005001800c6541005c0100703241040c4441d100860100102400079 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 219506960 1250 219505710 219505729
    0xc0e181905070f1206050a0603050d0309030e150a030e10090c0302040e0102130b09010203090909030903060105010e10030b030a020301090f0510020405153f2401140405 74
    0x40c03036000020691000e00408000c08401040400080c602d071070b082c0718200c010019001c3e00036140301e407501c0c04504c000b8840e901c004000d40d0402c0680c1c4400600707210060103040b03c0070080c0c00040003c1c01da400d076031400300e20201c0140c01511000d8503208014006078040c0850800002c800e003d054002c0c05400e846004e014900f0b4812070200740101d05610402040b1030181d00310403c9613106209240d100d10704402880240c800c40d008407525414441c004030b1861103a042ca031030701301c3c90007014007440b0107000000d08090701086065448680e02d820045940794241541d580e403085414564208040c065800f8618982c000b4040e2075111810b5000b186c06d4420f502c9003121000e00c40014102840300c02e200078068000000d01c154900b0785004000b0b50181d00c40d2200400b81c0300006203c414040388103420b43c00300003841050314401210440c0001c8100c42228655815141810008030880180c1c00300c4202520189660407420401c4230046840f04844000350450880030400030507140e5646a80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 219508210 1250 219506960 219506983
    0x15060f06050d06090c02061911040b1801030b100f031d03030403320906070c03080a09050603060303160c030501111b030a020706030b01120f020919030c0e18 69
    0x580b65250a075501d814121441c55002c18200d43c98070814046580c1e0104206d80c10031007034880e40301c1211282030707004020290300780a18001040003400003800510340c80580710742c0e032007081c108007e06030000064080ea09000312265102030311940c25900a4043c1c4561000c0315424940012065400985100324909000102569610200400c410103622100440041032403c43c40300512141c2120046c1c03c150b1400c0f8000d10320301c00b248200c09500c40c5425540d9603a04130109081050b96810110001c1e03000000e013400003031a180300824581000e01c00c0300d0023190054019454140d034400392854020541d00e00303d1300348101c2003001001c074409014200302c00350380f8900c05a0f00c0040da004100c0d13519002e64280529001408403010590300420707610111560741c14007203000060400100d486410a84000948900d40340d111061000540d0107005c09907030039986130484a141b1607184189640900c002440707801c1385e01c014044c1d1f450682803150415100508604061005914203040001c140030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 219509460 1250 219508210 219508217
    0x605061201031e02040f0e0618060103080307120c0c0204050a06030c09050903091206070905102003040801020f0414090c0a030209030a0c03060b0f06040b0901110c090408030a0e0c06030415060f06 86
    0x7c005058400c14800e954019181e2840d01040214215049480c0c810501c40134000d01408000102164040c100c0e600040c170a95030100441500d01030003501c0148181c1d1b040c2e00651074000090740302803c610880301a643c2040c000c2500c2490b10b8000006000010803440d00c0e030100b40034400304c0c0d40b904807a0a2740307554414054111440e103107038010b0070700102c0d03409148503140349900c1e85501500013022418801c4203000790f101131100003c8107455807040b54081501c9602c009140b5030300100c07010217001a01d9900d004008404005401c002404030196001c0c810f400c0c0070044020301c5402a03004007014031014050301e00b0300349240c40f101441c03110b9900643d45240c503424109101e140100c150300303080d842220303083c2c2440d00304407035820180074440c0c2d01d606100d41c6400044292070708008000a9550040c0700e00d50a151514001c819038200f46c0b036070601682000c401c1c1c440000007007081004e07144090601402c603511511410340f958102c18905251950715880825480410405913015001c1038a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 219510710 1250 219509460 219509471
    0xb031905010f0912030507140f0406020f03030106090b070309120b0105032a0f0d0b0403110f030408030702010804030302130f151d0906030f06070f030605061201031e02040f 76
    0x4040d800e40c0c5020503482c0450346400c1003140011030421046010750068540010165a100c00545800c1a801c003000030b144c0340454110054645680140140c03070565080c0c40401004112042d070340e0100b80580000311340064421708c400a20a00900300da0b0307001345428503d281d600e0322440952082d001d41a102070034090018030030f5040401c800030a0164486000d085411201200b20a14240c40c520b0781c0301d00c44500d190308091b41c507070408075405604805040000e003458a030281c01e400140c40f261825000d2200c90104049011060301d0803523036108061403526505900440c0c0c4943d00600c00c03010315138203100c1031400f0128100d015010b0103140300d03501070040c106032220203080103035107080c020420a0321860991886e00b07050203014040036201c910b0309860b034200080c20b09040102106462050320100105075031b00001060a000341e546080084980f10000d00c00940b00e000d0040741090b642000400008014121101d400507841580808550300c0c1d44c001000c1c0c40303400c50f00910194840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 219511960 1250 219510710 219510713
    0x30f0b09030d0e030405280b0a110f030d05060108040b04061e0906050103020f12030d091406101401031407140d060f030b0f010f06050f07211206050a12060b0319 71
    0x5d018503155400303142001048611f003038400c80366a00c0e00f40100d9640b401d0128240f03a810b4043e201e140380501118040d82d400e18a40e80c141d03503690700310340c8201442e5420100401c03460f50050528a000d1600010301e0360080e40c036a1943e6010344169005025402840c0314841c98a88040c0320b0703107880510404011849514600411008411043c0d102e4801c81ea0044440d07002e05002003102c1c0b5106a490001c180c1510300d0424908038040070550a099002d8101080607514a03024882e0645440c0c0b8000e8180942140044044403150705440c14041d0311440456a164050240485111000d81110f0b15050304c000f0300300d0a652003940013034055501031a062003004000711100da4040c480c07064122080d031400c00c0e0121421514825a401d2020002b00710001840c0d5608070340c802e03608415074502003580512040303503001c030221f0180c0006205024001103100540601c80071a5801404030040074284143d41901c018040c10071039480740c3d01c0260741800d0f101840310403c4140c040c1d54401c45214035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 219513210 1250 219511960 219511969
    0x10c03081f06021f020301050105041701150e07020124050103090f020a0b090405090a05030703050f040905310b1609080601060302040302030f0111040b0906091210060906030f0b09030d0e030405 85
    0x1d101070b844d220350050006201d980d0788501510200c0310131400301e1a069900030f0035207005100d0710100503051728400e400840d08081c510f5080c0c3c025031856000f049600d03403544054a02412218008005441d003130410819580300c0c0d040741035518001d680382c02c40d00c000c0307900140600c1d1665000d00070661010079682411b05c0c0601c1503d50010900000e0b107101540c0741d0b40d06469100e9030000074107112004c205920100c01400641e405031180100030401c5081510b5203004030a00252100c0905040c0699038190030486903429040c01c0d03200003a18981c0c0c881201505070030240d21610020000c3d1404001513040081103058000c00b9241c0b00142d0300c41c114018142031200f4250801e083da03040c046210f0582d42d0590458044800c54426103498404401c00110688a0407998a03807103940412104015107003c81c118031040c00071013003040f04640d100c1d50601507130040c2c40060403d8050a058030046640c410304d256002da2203006407403401c47e41c201c00c1803c4900104c8886001c0e84081000d0016040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 219514460 1250 219513210 219513253
    0x7080904050916080a051c1e030501031e050d0f020c062a030408030409021e0a080124020304030f03090e07080702070f0503030d0f060b0f0d060e06010c03081f0602 72
    0x4107000580301010050320340940d0b407c1d40d0050303a50244800562500303403034480c1017103044071801000f80004003a00468002c3c043d000a000a488030300080761907610078414090400d4200354000301400ba541015481900c44e80a08000442540144000200c0698410303004241110300846e103001841d00c40100e900d0718121030300404070607900411045c020450004240d60403514000c0e00583c1e0780a074483c00d040c849945035046418684046060341c14950030842c50780c140d480d240f0540036820040340d4441500312001c1c8150001d07800411090012070700c107402103888540a4103203503400780d13655120f10780c800030220340c1540041c0b1041c00b4082c00a905002441c01020003040380c0010f0760500001940340e10444d0740c83d00e100c60f0740c0c8a001e0042040c3c0c3d0400b400a024a40c0c149490380e0340d4801d403841766400260410340c1d05251480c0030503a88025040c50b40520300c1a528000869000d540661f5141c901a00c2e80900c80900901021003104140141010388016070160007141c50820f40c1d5003481d103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 219515710 1250 219514460 219514469
    0x40b03100e16050105030601050301120203070e0f18010605010509010503102c0c0301030b19090c06050904060801020703021207052107060b0a051c0614010f0f06020604031407080904050916 83
    0x45c100140000c5a81c8201130380e06482c0301c0802000d50341c0c55440003c3c039001e0320342c0c0881c1c0340300c541d2001c229207080650120351144c0030204d0806c48040c00d4084013802c807030580c000c2c140454030a02c005100703540f141001d507a21403801100c0400e5641c0791480724884900241c00301384007180709521080c045000361b0700a90030001040720300d8299410750761041d5034000000c2c450604204403000305c1040d07083c59040180d0840c2c2080f40c04044a40300e0788010801d51100103050300a82c2442d40000e40c0d144144200c941c9581c26501801c80c0d002071540c50032441e400001e05a03140c3c032585001c1c11132006076aa03082401030fa004512907032800c0c1d6141550075158030b01f4905118a05001c02081140c0b5550102e480060301c18415040249007881c24030024903a8980d00d06550841c440041a900107280350310044e2403c248060401d5992400103c3c0c0d190003c80d4000d00203010704200800b04800d84000d020b04074460480541000782c00f00c08102103c00844200c030440e884400e9081520751b854681c4030261 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 219516960 1250 219515710 219515717
    0x219021b031209190905100f0e0106080c040b040e0a05090a0b0402013903020105180c010507110d1110030e150a11030f040b010f14040b03100e160501 66
    0x26004040000e03180d0390282c02e03003480d90700c00144103446581d41c0c007140041580031a03880c00265464250040040100f192a501c100d40c0d001404a071040c11110b5100844070041204c41c0168280b40084621060240c88148070110074040881d0b442c401c0303005000030703000204a030b005a281c501d100801740c640c003030b04110454110f400c00901054000d50400d60080d020300700001d92100d40352440d11103e42c03d00b814917120340565140c41c180500040521182400b9074024032517a1169402c01010040a0001610b20f40c042d201c0400e06502501c0640a0140150500b40c10310701000085901d82c0d00c2d042003111a4100070f60320248602e08a113101c201900c461604201d410b4402100c640d90b481d4a00b5542e19045809000400c200c0b501d07000a00d0000340e1604040c0c0381c3c2064021545032950036176007212000d54820005c128490a141364104840f10007100c200002c00c00e10900000741041e001983c1c26000b506c05500303d96500e401044083d00e1070100030500c08084202c006d08401198002d40d041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 219518210 1250 219516960 219517003
    0x50607110d02030c032a041a010e0604051002070e0703022502150c060702010c08100302092203050d0f050f07080403110303090a150506010522090c0e0108092e0609021902 75
    0x1200c0c0300c1c0800032000002e02b4900c10403118203002840d00c0c09290701142c3d110b81d070440d110418544c081000802c84860405018040d20380b087c096040e40604050800c0d12018414424151034024500d50860303800034064184038460700c10800c44c1e55004600902059002c0018042c06e10307824822940e801301e0524001081d42030441e05203005043c2440081e100f08620310104030314162140b0440c3c43c01e0f400b051002200400c2c0e145c0544950000c00b2032205903441c1c00d1241260300001d00130b90f84200c21800220300981e940035000d4800c104090825000c1000c200315002460508100540c0100c80110040c9015415071074074025014004400401043c10302042c85200c0c1d810105407070b00c040c0900040601441c000360011080c5459501c068040c84c208940d01e07079001c0e004483c01c0d10140302030342e65207980d0355100c61590740d601d003c400481c0c041c0d010200c507403040c50030900b040e10403452000e804600107a84080101c10382c0c004014500032036002c1240000f149030100a40103086507103100280c1c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 219519460 1250 219518210 219518231
    0x3060601030c09090207080909131a06030307020d030e040504031e031107030c03020a0b0406020304150b221104090203180607140703030b041410050607110d02030c032a04 75
    0x2042600c03800700c126030042050010800340c1026a2560320015014270014900103501d00c4200d0310b0508107440d0452a1040e55280b400d680d00c24a106050180095140804943c240306142ca4103000c16000c0009800343c0300165540c0e4000c0e40d015500076951540380414040d15840e015000b204c0722014103180c0303001c0c00d40300403000041e100f20f10780500f8010030f000c5080c00c003a81485030600000b8141d050b460200b100b0005558050342c000d0340500070040c00000c0c1842620308039074510b48941e07842807900f42d4035071500c11203550f40c1c0541c02c99043d0105030445000e181401c2c0d0380040c0c2002c940684c002c800c001403100241903180f5107018940c01480c4e14240365402901c80041c40c0ca046903400c600280040c24980203400184825801600c2044283c0400c1c01e8541003200983c0c1b05900784001040001d00c40c44c04000307413080d49400074480c091071000e49041201401c01844c1c2282c240c0079464084c0d2480d50144580c4114140c40c0040c0c0c46904440c0c0c050103e001040009148a90301e4021240c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 219520710 1250 219519460 219519467
    0x14060103090203190c0b040e0411120c120f0d0c061404030f0f090f0602030a02100c090b130503060903030a05060a060f05030603101b140702060715020705061503060601030c 76
    0xd4450031492841c2a40c18401e042c0300c001800660011b1548103400540050080140030150b4031840c000c809008181c3c2c120740c200000c80e2801c824a0400b0791092041201e54600705412031b0500c401da50488035400c2e0b000012904041844888501044100140ca010300000c0d0003042145041800c442ca91445e1503503001e42200d42480010082005000101036054052102074001c0d060080a001c60310b035681800a5407a40000e483d20018051410000320f9188540985500c0c0002c40d1215403400342050100001c90300001b80e001c83c204030b150300014150328103210680c041c0341000c0142d6928540f5481d1a07041c2d6101070300482c05194100000c00c04180c1c0a1107040000240380f405c2545c91700c0785030010340382203c400c011038040c0d032501509100350126081841c2d03501102d501d80500c400d000704440c21003400344490294000c001041038100042c424002e00c024410310080050908441d510f0b001d18040c41102d984055540320314040c0020714081000d04c0d400042481c00303009808402c072004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 219521960 1250 219520710 219520723
    0x314010c0219030302070611071a0f0109090204091a090f0d051603030b03150a1503050d080402180c0a0905030f070e060604050316060f050c0c01140d02030a14060103090203 76
    0x1d500340328001d80400f014403d4048485554101c1d400340040d00b4100784400056005003003c0304c84180061001e040441d2400c4500d1142d0b444040c2200c0c140e1810b8a600003510324480300302d0703020355201d000c0d0000490100b260182a9500036a084041c0340c0a102d26141555030a003048003540501340c0c443d90141e000c000c0b290100102c030000c028810581c80c040e0090700c0e01c03c1c201e03a898050042880701002031203d2540c0702d400900001d120303a091940000345d50007110300028000c3c0e000000280c1c051030140040e10341192015105149140c222a42140034580649d00c440000130005030300d40c03105900c050381d50050403003100580300d0006102a0706507504c0941c861200403c40143c0000d042d507031f0305d40a4500400000d000e540640c0403003454908219018040e00002c640320b11140400c15100f401070710203041c1c1e5131000f02401203d610054422007646d150034408101c003000b05601e209034900107580101d41d40840420030880c40e481003641000010400c0381050725280d1003002507500003421 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 219523210 1250 219521960 219521983
    0x12050d09031104180602070b0403181202150c030f0903010f2927010807060206040308180a0204060303020a050d051e0f09030106030308100e0106200a0b100314010c02 73
    0x2100b02d844ca42041c8612031501001c4d015030310200c0c15609001c200c22046e84560f02c40d5403054166000c0700c4078031307059410034060070303d4a60203a078030940141008904001d4907003d081e110345c10001d06c440e040d8a9a400034549210f4901c010815940c182401d00a41d00e28102d0740c0c01c2440755203029150500341c8201c500c403d68100d1100061410310341c03a181644425224040c0d1480e4480800100c69004242c0c02c0c810085180328108000840900c003040f210300070340d811307a2403660649070b160400c1601e001201045881740540c400140040c2c0c3d4512507500194820303000f801004160b814580d0519184007100c00a00c02d04010701d105c0f82c1c8034811502e4005050540560303c0e4a40700c100400303580130b01e0003119055880c0440200c103145e0441e0342640300c0d400561000703a61540300c6602180889082c40b48001240c0944455020f880d183d281d007880c403041e081d044503182d05254603001840f00059400c00340740c2138050030500c144a40e8a0442c484151420028010304905001c02540d03038021214 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 219524460 1250 219523210 219523219
    0xb09090c0a0e0603072105071407061128080709060507051908130b07020105030f060102030904060303180b2107090e07080601081e011e030602030112050d090311 71
    0x180399071210700030ba4070108810800b401140e01c178503140c4000340c112002d14018484100c0c0c1208003440c3d070b260384d0081d94840c1402d590f41c07083c5000d2008020f5050b401c015011101c10f0b4036030408803070103a080d07000740000e00744080454803100195845504c00701844c0c042d040801c444a0100070704c0300d030080719510494003145065580c0e0781007401c00383d04010310514003004040f90042c144040c00804405001440102c11603241c3d031980e01c0030f4074440d034440c2c81d000a006c90b0040c8001080c8003020008c8a50100b01801560301e0482208000307802c0315510f800031404a21044814400580c416001901409a1940042c03900213100d030058104507081b045441d40005160004092520910080000b440d0505a0414501304480301a1807907100308d52950028001c0750016401a001c1030705240782e00c99000c0b50034016400c0c20b070014454051100c1004841401c2400040000c1403840118020210482c40301781b80c5089281550810112100e09010016841c0c800c2c0040b80300c0a03d0b00040080486 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 219525710 1250 219524460 219524467
    0xa0912080609011707090207050a0501060b0a1b0f050a200a06020307140a12081504050402180702010b1207050a0f0815040204060e070f030b0a181d0a0309030501060b09090c 76
    0x81341c6000010782040c8007140c00452038030100000001c2011005110710020b00649440e41e04503602c0780034201541d0300240715114017160480001402e0080103008448880c0700700301540780c5034604440c8240031aa401e000840b000030560807034071003071100c0300d0480c0c0c404a221303d00100256a0b004020003e81480e110114041c8200d0081045500c070341d620400300388280440c800301500c0e025045844c8a1403104100d440c072501d2070144901445254001c00c03030100a0014048010400f00051400007999030360a0a401c45a44a40b01d40281c440ca8000070250030f41407006000e4510066400043c890280e0764090283c0e40011404208003813001c4908001c90b42e850000402070b09495106107003020000050008a913030055800041c01103548041c8048480d035414000c003508148180c803651011030010540c5c007022a0404210700070381565800303214401000903420200940011404210100310803c208034080c080d90b0004c01c228145e41d41446070640102e02240d4004000404c03034417000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 219526960 1250 219525710 219525749
    0xc0203181c0b160e0a0308191701090207230309090403050f03072d05030121050d03021c02090a0303110f0607030b030f060402060904020906040e0a091208060901 71
    0x901030200000e400001c0072400d410719041c0800342d03c10b603040c0c078400a080100003442c0d50500c1c94051089a80c820001880d103880f410300b002d00d909080c2101010880c8054181c1141548071040da80a0b1a0650300182e03036809528082d00c46444000308800c00c48a0044405000c08010080c0d460344003003520020410741c0c451800715401c1c8648002001380860110034030070925400081c014050500d0911751020f04c1441d06000281002c503a00000090820401402041100b101001e45422113003600198401c072a51510309152051054000295002c80d0b081c4600340e03140100f1400c03031141601145003000100c04502040d0060101030306119145c000c42c0300001c130411444041368071100075100c02c2e00300050010090480b140d00903209209070100700c1c003681d40104a0f00c0c0201e900400c52480c0c00e25980620004e500300301944c076030201e41807000051010b24024403a105007100c0d400001d000d119860701078400c40c00301040340c04112a01040102e10303200c0c441180d040d00d864100005040c100c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 219528210 1250 219526960 219526999
    0xa06020c0f011509050c0f0a020106090e060906010603020a0e150d06232b200613050d060e100c231803011508031c020316110a0b04150c020318 63
    0x186202c21310500302c0014500451a41075001c041912010b99080c04180007032002e0381d3b40c0d02c005880b0400c0980020340100000d90282d0b0041040034200d080210640310310500061001d00144c003030000c0240f0000380c4039040c02d21482500e0290050200c20890070464018a44a0f90710050031103014003500c04c079a05504036090798840e40300780c0000050300c541c0c0d15071600700c00240c40c0110060880c00f07194210303101498900c09592043c4c0d16441d08103201850f0204101c0c009a1003282a030343c5564604485102c520180b101410003135100c00c0104a400b9854401400c54892006a012014180c0072500c080c5a49100b1189504e51200c01a40b0910110000a0040c4000300080740d982200760070011705842c000c0081c104003e09903103909209040064250242e100488140881c1030384003440d1035801c0d008456940310051400120f0341600e400740c1d60080d030f019094a096410007110101c6222508290050040c000c050303102440c24451042c0300700803100c4502086034401d018240b82036054045 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 219529460 1250 219528210 219528217
    0x304082815020703020d03020315090c0f13080601121110110f07050103050f01050a030f0807060f021c0b06042304050f091b0f060f0c0a06020c0f011509050c 69
    0x10000191071a0409411640c0001e521405040340940030f020781b8420350a000b4800c0c1c2c6d20aa070603110303000c6508044010460480801451548001003d110740c181503250344014249821660241796110b40c141960f6034a00681640182e5080d00001c0303030b0b034001400e218401d8a14003015a00340148050790f850540d4400c0b240003140c107081c840c1030940140000001180c2c400c032442038070200480d488268182c04458000d006043e000880c131202000040c05070b4a1003042d03d40244802070400f141a41d4207000c0e00c1010302c038040c09030b8011031107286802001c8490031541024400c00c000c01a011000b05005014911800c10700c110307114070010192807101c84441c20030780300520410840c0f40480031034200402c00da60080d440e1140c21060343e1013031f80007501113034591001000003400801c1135040041d6a40484480622481d06000441e40c260041001000d442e110703040c05605d40f0000240180382810781105d4405507030501c28496400c444203000350054a140b4030001c00e40c1d03500c0c2c1031a40740d13030310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 219530710 1250 219529460 219529463
    0x3071203051503011521050a1e06060305010603030e0d03081b04120c0f1a09060306060909040309240806060d090c09050a110a02030306130615050d0e03040828 70
    0x1400d10704000c0000d5030b207030707821815112074516014046005d245800c3c11b0780709188000b170450b804412002c0100c0c0b200b011403007a11621110000341405a50b850900740c40c078580c000c6586a440c0c500c14400c00d03400c10080d02c0c0226055a45c000107001503100103003804800f600c0d8000800c0e0b00300c004a1203c2d503500413a006031a680d80e000201508a24008100740d515100f1040c48400780700c0c0214800c1c120a455001c9080c0f070700b000a0031b125540041110b207a0000e0405503000c801000100226200c44842a2240b40292503160f0700070725000683c1801d01881c03610302035401171045440d10031604441d190b604104e0550f02c954407403030b00070300c28001803800c610003501e0000744181c0001d0103038442e003059205480c1c0d04804c0c802e1085403103004840340038211820b405604107000003095400c185e188216441d6072071802103269580c1d82a015600000100d5000000354001008100c0049070b00070b1700e040109010003989040e02e8290181d813651301483d00c040150054101201c9103c010f210310300c40c0c40c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 219531960 1250 219530710 219530713
    0x40b060c03040b090f01030c090902030a090c0e0a0e0309010f0804080f041715010302010c1104060e070c03031505030703030c03030b030316060e010c0905060d0204120501051803071203051503 84
    0x42e52603810b040100c1d081608001d100e0741000e0003149581d4072a0040c040c18946d152981202d0901700103006000e1341008020002c04c6944042810109040c0741449000b0144001070011504186e90158142d6500c8410281d440c0d008200300e050f40e0760310452080300c0620702d1500003040e0315a450500d60500c200c00c0100e4404c0004100885c01d003246500a041218040080364078044141e41d4522030004c09210103400300300e5030801d440c081611075200082c0d901004000141d215150302040d00d0107081038074148005014140918201500352003801c4820504042e620032941c6420006660303990103010040410580d81071480416009030041c80c00b890000b8103030703903d41550b06d914000c030700350000c0151005810b11441500c908010300c43c0f402c07046065600c240ca1b0608240078040c1d913500401050b500341d03908000c002080c2c800500c2d0040034501c21400422a828032900f41c55051081c0d81c5e00c000250010044400010160644051101240c1c2000320f001e640d00c0d45a036030a5417020035140e426 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 219533210 1250 219531960 219531967
    0x1c051c0c0501050f07110607080a0902190602010b0a0803070b01210606060507031205060310110403020301020310030b160c20030f010c030501080d020705041802060d060503010f02090609040b060c03 87
    0x8031013104000d64840e80301541c0c6c030211207201400c083e50b1008159190008220101e0102d5801c000c141c002c0310050340041c200080780102c80b107400419500c46e91000300141d54482807114986003851101e00101341880c025400c00a0a4403110700485040c0304184880c43d80e06100a034226050315030745e044075001541000310720307a201d1010349294080881200069400030140004c00130312300ca1236000307020150083c00340176910100b1782c005181d0603040b00c4440205003c00401690700340021741c03050700762241041050345149005a65224050803160000d120582804803030f80d803040c2100345c0c10350080d00c50403181013103140806901203040c0f1680d800d80900c060017500342105410085889441d81e03400c0141c0d0780d032502000d81718100900407030b00503004404100524a010b4010300300aa84e2015080115415540000c0aa61081140032030050f101e0364100400d02e401c0c400c80d8000c002c0c40d1010751800300c0e00400030b0098424174041c40e01c00c0e0364a81c00b5080c5502c5000c03d039841c0d5413054084035070303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 219534460 1250 219533210 219533221
    0xc0f060605090a05040f020108040c15050c10020403021815040903020c0120070501110708160303090602060103151505060307020106030501150f06051b010212061c051c0c050105 78
    0x50003050046070300840421010035582e0145105280c850350708801d2160980600d6801104c1da840b000e44151040b0500d110045400400389c40040c900e10700311f88507580d80707214562200d07003850150003085503041c0c410b020800c05602c1c1d410310506803280020000c50039550b00001c2c13501703c1481000c40c42e0818609400c1104140c0c0005101e0700286091300c40d2509448560303081d1070f400c200c08103002507a800640d0b0400c0554010462105214401400d8401d95a2500e0f0b100345400e44c25103904100f080b02c1081001410b401001d402c1c054202807000e0001503041d03840340981d070380d400c1c11150f80b09507480951440000051a0841c05000018003d07562420b15010090213000540800d8406510b402d206e5441c00c0071184101045600c00a0300404442c41e08009070340c81d41111500180040301c61200d84001c020a200070840085081e03070f1444d0a0071b101041c440070036868025183c044d800c580481c00072407000500614a083e00d0721152500c50304100c1c1c102c80940601c0700003040d40d0f003090306100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 219535710 1250 219534460 219534473
    0x30503040303050a09021f170705070b0a02040b03040f0816060f0c020102190320030406060608070c030c06020f090607050d2a1e021002010b1f0509100c0f 68
    0x14000c81c029a42440316441d0321450b07004030391004100942c404480c2260240645003041e122452401c1030500c0c0005964160222402c240101e0f00b0f900040c0c000602c503000c100d62907020725004a0500021400c160800000d1400b500c0702903c09442501414660010000c00070704880ba102d801007240214a102d500d002d0780a0324181d0100c1500f00d01301480428100d10510039142d9102c5038060299281c105178405800514071000840c005900045e0f62455180345c0e42c006501641c85507400042d0301e4501040103003444000f0b0201001c01020405500100380d20404041c202c6402090041e80d0780500d28807402c0e40e100c0c41c0c00040c1c01c03a8022031406c0030f00c640400c032881d0b241e8064582e4030a0708041c0300b03007010440c13510070380499520109005801151545c41c1d0200c0d00c1c3c084181c42c0f0500011900021400a104076002c00144e44508802100b41803144994802114007140c003a10002040405031480c000c0b0b03650640070340080803802e46245c1c441e00740c58544a0700001e00c50016250390a045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 219536960 1250 219535710 219535717
    0x5010213090c0c0c050607020a08030412060612030221090307080c0315060a1707170c034822050c03010321020c030708010c08060621040812040305 65
    0x1d100035140480c0303891928040d1184030500d070782c00b80200d40d44904150400055802000c0284c0c0c20581603400403501903800c0009002800c492a003502d030f02c8501c1d141101c10b0710031f030b9003142a00182c128191400a5000246042d441c3c000c01c0d06240c101c1d45510120388580034500e40c4039414420a800003800000200711144034807010741c00c1c0ca0103816403d40581b01c0e44810340e00c194210315240307020400303140171800030412408204142c480907540c2d0400ba05122042e002020707480d0b000340c4a24101440d040100c0300410b42804840400c098080c8010103507104501011982d802110f034020304070312551800383d65925001803014107000b4081c070354030240614141000603000c0c0383c100880c080e0701406080c1c1c5c0c1220f6000c1c07104801011485225011064043d2010b0198400d02da07203080345076800d10005001d46210000040c080d001e13060024220301d000f4081c0c0b4000c80c0f041000e040300c485942174640c6038401814400580d901c451508400c54812a54101303102c481394814002019071140c0103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 219538210 1250 219536960 219536969
    0x1060c140105060d03050f070204090320010519021b0d020307030807020708030d0209030114040b0613020c0d180806150906041404060f090516091407020c0f060705010213 75
    0x10032044602089540e8202c8000392003180e0b02013640c00d08440000d03c5040140181c0700c032442c0d00d9040c030380e0a03804241981c0b0483c1c0d08602007181c180c0e61482000070003071602c0202e68507000a0169082000807040021400350210003203540014003509400b06420440410711070800c129034200800d00c0b0001d4030b03900600c1d0203d0000e00c4441c041521a84001904000d07141041e02543c0b410030b20040b80402548649a41505035403520381208551481d03000c0288a00d016104455080c50308804010740c01c00c000d522810301c0c41c41480003600072400000c1c100c100640e64180700e9805400034068060500d0b060340144010f10a540820112503400390301d00210500964000b01503459113000c0000740c8800303504003040001c00c0d00008021401c44d401c40201002400c070005416021600c0e00350810350683d0500524050030001040040018403840034002d00540c0c10740750703030704100200035120801d07250507a115400442d1601c08580e42c0c0407c441144d607000008554503039028802a4014103039200b03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 219539460 1250 219538210 219538223
    0x903080903030f1902070602070e19110c0705011803200102010209060a02010c0f08010e0438040209011205030301060f03021323151608040504050f040b010b0424020f0601060c 77
    0x40080c7c41400080c015041d15011150340c20969101c50700010301050403e00c1401158444203491560074041004007060151403000c1d00300242410b00150101c0124840e40035200c030707200420804240c81407446030180d039075034040020007805140101e01a0144c0c041c0c480d40030400203000e9220b01d0701540482140041c030385070180e42500c500c8080d140f28909104240503840c6000018000402084c40200e8607880e01c07030f140d00d0813150000c9504021448551503400c0c9001c00c410310080d468100500b500401324490302506065145e61a1074a0b0300043c4600018044900e1040414170300907010b40d803803e010080619503d50395810301071b0790784035070501008011081308603158660901c1c007110081498039003901071800c4d40422590080d081006415030307034040e0500021900c2d0f2b4960040742e0241541080d100350900f0113080281d01840c3c1a4003403024003104000410050703001420700c98400814901c1d0314060038a40c00f0690520300f00c02d412010a02598001284181d040740840044600854 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 219540710 1250 219539460 219539473
    0x609021009091a1f020708120d06090207030c080d0605130507030e0a052d0d110f030c06060402030403051608041a21040212150a0e0105070903080903030f1902 70
    0x90642c001c00c01c003c20700d50000b042400d491412003404049404045041c411106c0311039441599904000030303071016030001c003000115490442040d000b010301814141d0400c510300000b80e5005800034981c114010820900131032100007401103648150000e05003e0481210b244a141041005100840e4040046454080c001c00c0440001032180c030101d52082c001c0452094040301c0c1803139038000522002a260800e41c8042074070302c040c0980f10b402c18032502e80c0f2200400090000341030012628603c580c50340140060680000000703401604101e0035940180d0b07070785490600302c549109039a0007441801000d10f081e400c00460310020402c4412000b6103100c5c2d035450b880803182c00d200b019029466120a000070788043c40780c2201d4a50000c2c80244980700c4140c103241c02a06010708014a0b880040d805000c00c040c448407130050030f0070004100c0080089292000c806490001213010141501c40c020034588115201042194003283c00f5942080e12034201c2031200d040da01105e0201001030050303e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 219541960 1250 219540710 219540731
    0x11040c020318040e010902030a0602030708061906080601090b0a110d180504020c0a0f050d02061803030a05060301060f031b05030102040308120703180b060907020706120207060902100909 82
    0x4019980b000d6950740c812800c2141200c100000780100c107501d001c0c15540c0d00c500000580d401c202c010822407284202684074078005001801c0c0050050030140608484441080c0c004014007258080c0c50141c100440c003900d682c0f00403540404981c00c100c5900100190035041503401110003031000381ca503c203c90a441445800b2207008031082c80501440c0c0c1d105005100628040e0003601d04103916808462080b0800d4464102c042191081a00c4039003003100032140031a4103114140d0f0110b500610703511009003291400d0380da840300078a40c200355a62100032502d0b0795800e41000005000c4202a22095516400c0a080c0514540407500c0b414807a00800181d504040c025981107a80142d42282441103915445058480c004c0c000410940c1c0d40802c0c0c0034042042000c044e0a600802210520b45407140900121000250100e03013590b010b19020042c06a02c02c0c04454100941c1c4005620340c145864150041e00b60034000a41c05250684151282c41d44019403e044603405442031142d04201d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 219543210 1250 219541960 219541963
    0x109020a1e061d0d02060d050f04121706010c03090305030f090307080a05030708130306051503011a091f0e090610090e0c01210906021305010915080709090911040c02 73
    0xb000301c006005056010f8015031440c00c8410101081d00140030300d4945003c100c00c46044400071103200c3c46c00781c0500280310612a210025003c0213505080110204942281c0c0c0f1010719001402c140c10072405d28407810815100b64041d030011b50344802240d480b0140306010340c02c01d40160f5040c6020380720300c000002e540100011480041c0e074100300914904040c0d034503541e1007540030542c5804004200c0c0c00000005c1c00741c1c030031684910300c0c07150b8560b40c0703841003c00c150945100c0007825440026075292062a603445555164104e52010407940e00300001c00603110003c1c0c0c1d02c0c1e02100d049010303041082081540403682c1407180703006110741501c03683c880014104603060b103901449103601c4400001055401800700d02d0140d4000c04021401c46843c01d80002900c4070440c1c200c815a4011640340303042040313010203201400e801d01b05801d806023820000400b00848a290008010038640492030460040d10b200b0013034180c48500f4050914641084500d022414020790700640c9007140500c000d910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 219544460 1250 219543210 219543227
    0x903020f16050607140f0708010504020f0904050601050618040f061a0f1818130b060406080c0603100f030506071e0e150f120906150319050109020a1e06 67
    0xc004001c2130910b02151a110708091a2941c44005480b03421600ea9010f0410000d4800400314440080f501c1c0c6864410300c1440e02140703411078044c410700c805000028001041d80743c1580c2c81560303019180c01c480c010b15403201e41069001d81d0400c0c604210400d06c00983e40107281900c03101966240e1481c105c426900d96881140da8a40d003084c0b0a100b08070101c1e00140c40c040b0f02034401820f4200d2030a4102e0110540740701a83c51048080e0f5181c000c404201c403600782154803110455003003104c0c500d00006c9549641c1c14049440c030503800040040c1c418010181040c0242080e1000b011000f5120f2030700700e654200a543c5100810f16580000400c00c00141d117490910034240d4a0740d0006d9420f200780a1900d0540d060390940c0c840a010200d082c175800b2000e429a030101c000c1822103401c03c0500181080d1015080111000380e010800502d6180054041c186505900e50358003100b03190f042040c01007842c0d180096115a03103101c0018200000f0118007036200080750702c0e800103a5039940036140c500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 219545710 1250 219544460 219544469
    0x626060606190f050d0c050c0c0109050d020405041502120103050c100e0d06061520070806060d0804030609031d0301060509010b0c030d0203010306020703180b0d05190903020f16 78
    0x10810740c07407039902c3c4180102c101000160500c0760904401d054842c007900c00001400b00044e201107070802c0d00031010803440d98040000e08006e8129410701020503c9400d03450000303400b0329121004a0b04020301507040134105400d42c141191900451018100c19400a00c001d982070302c5240703011070f51340c41d2130068444002040d0b1603031100052104107001000c01b030403400303136459580d46000046c01c054203220300d240d00307605607980042504525041d00c10301c07118038644041a03006040c01d01c400075002807819009501110313410720000e010b1030000d21038480c54000410450030444d4040405800182d041200103d040d01420400c148038140340c22203030705108141c0d04c401020010009186600001c3c0051000401030328904081c01100a0a03a0310aa004a4680fa070005001003070580c4401e02c449010000f1040d81c803864034141c58550039010701401c092126a0f50f0000c965903801210030125101c12003482800340243c0d40c100603450f419020340241060003203c00b0394600d00c0102c000c000549 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 219546960 1250 219545710 219545737
    0x5040f140607060f0b090921030108060106051309020c030304330c03023007090e01030206090409050607031d030f0d020a0c0b280902031f0626060606 66
    0x20360b07203440d4100a000c00c0b00c1690a2643d8030054080203132202400a84501c1c5032400030802484000300f482c00c040040c40c82c1c480f40c0d50f01031005110456000c41c0e454112011450250b80315090800382d0030500f00150303c8200c12a1000a9410356218040040e502c2540100d1120922080402c024164018421400402c01c0c8502016001c203800992042080203034a01d00142000c2c00e400c3e006185183c1d1889155070050704190800c111004031117402d911513018580391303030030342e01e000308101e1060010300000b84510404204400f568480e540b2004c41e8a82050407a4007030b0900020150040c40c1e5402011024100101009840c0c1c83c000300700c6040b22000700c1d03031603c1c3c00444800707007000750001203001c0c00f00301d003440c01c0c40003003441809141e008203c86a03801c02c180c0c132208404012511800c1e402d400c0c15003010720000c0540d030003080d01c5142c50907645001c0b191074102c41244008041341c1d01300da0002e10001d01c4245950b40640d918402420440381110225241c841c100030b110300030a1180d8002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 219548210 1250 219546960 219546967
    0x60603200904050c0409061205190f1104110f032406040e06190308030907120201080103030807030f05090a02030f010216330b030c1002062701060605040f1406 70
    0x1181420361103e9400700c0007400950402c2e403513048840c00d0b00d0055028840d40039100c9410828060240040d48008801c80c1806118540359500c40543d5000d500d00039266502c1212750415507166504208024003007800c220760355100444c11505203070401d403110400b0040c43d5441072250b803900d000c036900c550070007000182054a4074400e001a1100180202d80100741020220700d20180e17030744000017451281e840d968480c43c0c4640900d01d0300030103500c40005040c903442c072400940d8004211605403509460001c00c240e555110540142842c03107000100d407032600080002041000c00d281241c0d91088064070402c082c00d41c2c801d820303801402154280c030100081400300041c640808440c0d580c450580280446c01101c105115000304d40020840b15a180c0140f01711518040c040d0300d0038481e045420019020000306c0007562580300410f8121300e040100005049104000041c100e505240c100034001244c81d5500101150802d104280008200c00d8001c501140c121082102c1050301905071030a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 219549460 1250 219548210 219548227
    0x150117060708160c050d030209090a020405010c0201030b0414100503010606110709090f080d0f0605090411120c0303041d0601020d020a03030506010507020913150212130206040e01080106060320 85
    0x806030055030f204400c1c00341280b41e040000d501440070440620b01900d006860340546014001407590040c085d105043c410401072080c0e03a04524100380060702840c0004403503161001140c020402c81c850144061144400c2002d881003c0340000309490044d0000d01106945150503501e50700942400d5606070883c1d01b05001c00555540300c0d0f40080d000c0d213050048040030b6201c00b01e41c2c3c0c1c4001e00c0018083d4482040d2199031545008602c0202001c1da005203031880e09807071301d40c4010700000406200396a03a0140c843c840d40c080003001001c00f80207050300d90301c80e5559204400e03070070907450000c1072528402c009601907001041c106801149034014009074581640e00710000c01d80244058180f0030b0601c40c803000b40c2c580b68032642c461600e518214403101e020703040c020f020b500700e80760101840d401089200c800d40701d03501c0400e4016402490562400c013031440020b48030300039504130310004800580001341c45c24054000504480c0036880070000985600e0865901d800d1202c60031a20000030080c051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 219550710 1250 219549460 219549481
    0x1a1909050c0d0303061a09010306050f01020d0305090c1c0b0609010303090b2209150b030c04050f04060b030403080f060a0b0304152a08150a1a0c150117060708 70
    0x2c20640309103000500d6035112102ca1481406202c450b507110071300807400b4442075800d482034901400c07048914440050b180c0000079030b500410a900001c01d030301d540105e8403544007000320300510200100004002d20f0001001c40880401003800e4a002506c031010500134140401d40e107041e6500760b6a001d811f142003d01c1c00d90f80307901000850101c0e078000303001c0720b4074001610b07944005000c1e6400042a070000a6004070810316094101c40c1c0000e10800501500010703900c1150101d84040c1c03644020a002c0000250003402c1680c00319401150000c00c000401d60302c103020904c1442c950740341c804a926543c06001c22a10f0300c1c0905203c9410400101e40410305126401c1c8420304184000b041c00c805038608200103843c4c0560055000c1c0d010f03161209440d800c88c112550001a403000740c42248200d80003e09a0905846000620710520314040e0100e0030010888120b02e04c0c6404071a101c0c0208044411400002d1040c900041d9546082505145004c2004d60144506540d55050303a00c0f5443d03002d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 219551960 1250 219550710 219550729
    0x608010b010323010605181e012303190608060103060e0f01090803040807020f1305011505091e030709020403050c0108130c0531050609131707030306031a1909050c 72
    0x3207c4034282e1a25490790b603901e108080003002c01105c0f00c40000d10364900003410b40b018401c0e864202180901c002c00f01109c1c02d10959900500c00c0c580d158031207450b546144000e1580f43c000d80c9860080c41c1c00802070010a401440e50711114504641c003045004404500321a048407004010f80020008a0b020400040240c04428002230201c0d036600c14504c0028140c14516880802c907a441f00010409101809455400c00c042e508001c0e183c9040c190006080b690b480d0341c5002e05d103109200b00d2503952010080d180103020450343c2195559124100290f88582c00c980c082c2c001041500092041c1603d4022184001d038028000030980303080a0400c21112a4549003840f0f4605c0041000c07450f155001c001c00d42e2031782c0401300080f0b0303040100501c00800c40060030020040000741d05040001e07040101c0c1890003540d103844c00e8840f1202d02e000c40c083c01447d4009002000800008400320390720506050049420710403820b050500049407000303440007000d01600369041030f1106400381c00e040fa0b19 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 219553210 1250 219551960 219551977
    0x180102131e06091208191106150603040b07180303031505222a0302040801050702030712030506030307120203130e0105130b03010b031603050d03150b07030c060608010b010323010605 80
    0x1031500f02000c0856642c075200542c00c40f100001d9030100c0a05041f6020706c220742d003107200c441040400c40c2a03800411401e00c40a84000c000c003c100d030000f0486403182c1c1041e00c10581c1d02c09044c40c5c495903400d00401810500d0380031800400301070b00c006420300d0980310060328440c012003070089040f4544c0400300105100e0b5206140c0281c045070f0b591400d520b1005042094110740c030300607152410051400c0c2112002014101994410012900403a0140c01c3d44400e0403d1891702069540d12a40481d055001300d60001700708112103014400b80640100c00f504010400c0340c460802c0a0f0b036058034205000007071047c113802411003035030300748005003030780102d519110090000310713150300540003103450207610020785c0300300f440c502d0300c10b1040040a2008030001449442d092000c41c1c0351801034088240c0314031602c0b0400c6000500c000070140522104074405800060401829135502071841c007901d00b0340710b4140060720b400e1100c1850100d0031028401c1608480e031002d0640c0c240202521076034001040b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 219554460 1250 219553210 219553223
    0x507080a02090a0f0b07060e0615130b0a0e1f0303140c0102040b0403050c18060108131b06020706020d05040f090902011119021017060603180102131e060912 69
    0x4000c5040011514444d00824a5420081d60ba007000d040c808220b4803c600441c0c0c182c0c11280034401c030707031074251659541200126101d8840c03c00402401c4000c01d454070132240c02c0110f03001c00040d1904c00c1403006200300300708029a4400e9001003401b00401c8210b020041c08196010001405444031201900302c01442c60001450aa1589003011180d001a881240c0e00e41c4040c81d2000c05d400c01a00d62080c000c82401c2c01081da0529000107011481c005042080408292450724180000500404c03403201c10421140400c070303214040207480c2c008601500c07000d0b120358800140d440d88110300b11001c0b900000506c400301c03400c110869000c0d11080034181e042040084030307501c1a04041c8509045440d00c00c018100086581c81480b02c0d80600314501020701c07908120a0b100c20307003040d0215030b0104048a8840d5640e6a100b813008100050800c1b80025600c081040590b0300c03150450601a2001c80c0c000c0311068184880040e41c00444d405035000040001000b0802c1150f2407064000c554030664 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 219555710 1250 219554460 219554479
    0x2100c032f0105041101030b0d033203070c031103041805091204080703020102100603080a21090b220302120c070506030901020a030f0b101206030203060906070306090507080a0209 79
    0x118450b007510010b0b203003650f07004241c0f290320840c3c0d82c0511407460710786c1d010340d0311000c640c0d5142c802a09181c0d01e044c800d2680c0b00c49424984014004140803036410900c9000140c60b41407031a80140b14650058088021590302400b0400c4c4620000c141c3d4200d410101b2004403045080c0150f50292002618440541c801c00034200c02c0c040240001e4000781a03420024481549580002841d01d80034007001c082c0140303485001c0c004a03096000310780d1520440d00709041360520b100541124085444100c001c8a0b00e040210400c10100f610a03034018071400800860003149800e021490302c07212203000700581c1c4a000600108501200507004060220003928807182d603c4000c903480c1e60046035030020a035400140890085d4240c454a0442c6010a8041000e031031382e180815010850904040c0a1101c60b04407440144255040a4049c50380902030790400e0800b008210ba569105441c210302180c1003603400306106466101c0c8170703c5144a5500e64000380c80d2444080c009510100602c2d410202c0c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 219556960 1250 219555710 219555797
    0x4020d11040815012403201804060915030b070210021801110a020f040908090a0311120d0206151807050310080102090d080f042102100c03 61
    0x100034000421440028020f42120104064440c6005070020041e48000c9085000d0140d29440707940c122507950f00340062042440084401c81491803603071004900000626550541c00303000000003101d00030344081c880a41c0b0303244110141c0e010069028424014030008001250400221075080702c0381e070040d1800c0e200403614403016640050361000900280e044012030030b5034400340c1a4103017100384019042d001c81c1d40c1e00240203c1000011544070700c0e182c040b02020310044000322030680e18000d00f0104003966a261094103244540c08070351103220a01d50740c10350390601042e0b072042d000b040c1d40902107507074412411402008001846940241202410110040b00e030400e041c090005074480c145c5034644060340c0e1086140a07045060306900511185806459a0000801e116409940c05403101648994080c0c0e0b4091030344030781e10015500851810701345090641107591030007a00c0c1c501041d03125000903982400c0040c4000c0c0068401145c101e1800901e00d81c5001d034601c10b0414580e9801d41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 219558210 1250 219556960 219556991
    0x1a0909190f0203040c05030316110406080115080c060c1903030902040207140601080a050303150301021c0203041a06090402100306090c080109060905010807060c06200304020907021b04020d 83
    0x815a007000c1664000203200c02d210040e42040000c201c00c40c01580f070903942e0388546d0f0741c1d107110300c00040c0100b5803c0d500398007a6031a40c00110142800314000c00040d203a120360740d540c0c20110b100300c2401d4002c41100540c0da0802504840c880d403018401031810480110b40701211450842d02501003666400788100141d555000800308a4056401c100d0f280b00e4140e620390400c035042c0d201069503403218542e40000360000c03041d258001d2022013800014508040400d0181c0300381705000001c0c0184840c1c1d4409002c580e40071b14011800350724104c0b0760310250403d0040890080e2401588445150300150051612462550700030700c0c1032034017141040c3e50f290302174141ca026021500202e00d400006111045151241030010488190309200c9949491005515400d090088104000d1801130305d03024070050b50004911455020000640c5000000e400c910581003034408034401c002c0745c2c3c003042c2d40340d2002410040728294000047c51100401d01008000e5102200424a858079404081c3d0b00000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 219559460 1250 219558210 219558221
    0xd0b0604021c0507080906070903060510050307180b03010209010903060504170c0d14190528200f060106050c070305010e060f010603060b09060a0e13060f1a090919 72
    0x5500c1400700f0142080740d4041c3c0454030080c400c02481d400382c001c0180843d800f94003075044a0300030f0782c00605a240c01c0001c07000c1100340e8120540500c1020303000501140031070b603100104c071042481000007060083c00c041c280d100d0480c441d800035400b100d052001c1405c1e030b8840d5803c01e01c00c03103441d00419a20003004501350411650340e51b4030740000d107954503420b40010180e5584a440103c840c50403061941c4400784260710b4001100b00304001c00d90701484400300c945018502c2ca807000c00202846d60040c014420544c01d04171980d100b49c504180d406c9000005402051f500e25031003e844161b00704181103c00390028817601c20144070308800080805e00a0ec203000c010015200588018a4582c0071060384510680c458010103180500801c6415120400d40f160041c086884956a40b5580b1040300da030b51944503008d6100b40000f101c40c1c8028090b5005108480d04c01c807000b1902945e4010a041480106070404180d00c010041070200d0300c0c0c19110503901003440280003030381c0804254500111038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 219560710 1250 219559460 219559507
    0x506030a050a1203060f05090a02030405030d1517061603150b040305061b07051504060219090611121801050f071b051012050a0b1309200d0b060402 65
    0x1c0043c018a00340d040c003078000900240c5c444101b880c0d2070311020a4107440c0c01010344132065804004502044014803c603030301d240c0402d205101400c942005006039507410720549492023440700030000014000f09035030744241040200d1007062071a036042900603010300f41500580a010000100f0312254403409000510700440052a0602d004040411480320b584100030b0005e109001c507400250380014090494004c2c0350b0b10f03520139126031401102078050780107015125111000c3d40c4845d0f5030b0108442c01111120f42d02d5540310078902500548032051040140c0c0b0b200700400140c0c040c0c440b0085900d003401410700d0701d6480c1030181f1122040382d07009800c08490101031000c2501180166503900d60103002c04807903c03010b801e4500e40103882e04400c00620f0082c0d0f619a0009242c0c440070740d000011060014020002503680d005000c402000100030488020800746070341c516041240141c3c0b014040050b02f811281c03006074554000d4840000d008960250302084100d480000c450f14100204 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 219561960 1250 219560710 219560723
    0xf121e0903120c03090503180d020d05030c06060109060905061605060906180c13050a0b15091809060711030d150603050f1519050613210210030506030a050a 69
    0x4040080e5030001d03540f03c007400c41c04050404546001040340030044075032544445001c040070b9403580b00031560300c0313007041400b81d402801c01d52900c0038000080300400c1f80861400c10364031140e031050300540b5011900d00546c13002462003d82441607041110083c500318201d20b02c4c0302c002035450755402c0d113010411204a90300e03030415001e00907142c401446810342e0380146009409004e400b003010481070503280c07248101041e111404551100e07078580c0071000c540005400e0b110010a074648045d003a502c80f180312030003266135581c56110524018200c074000c0403001c002d4000c903150580102c9603110324140100321800100242401c0c10024428651a00c1503008429650341c94528050202c0340010500d1420080724410842e207100202a87c8028038002c85005240c0d02c00c4140941c241e11103a0021600501d000a040785504030319034004c0100c1784200c20f0403400c580c0040e815040e030b82c0c2d5000002d4212008000c1024540d020350030690303001a0140803a640da82654070703182e04e81942c140c0240d404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 219563210 1250 219561960 219561977
    0x1e030d09050d080a230a09020a0b0406110102040f0608091c1709030c0a1401090c0b0d0605010903050d030c0c29011e0b0304020a0b0304080c0106060f121e0903 70
    0x189410801144d8000850b020420030070441c00c81500500d5000000d02c0312401d034000014800d20b40036807254896a0300a0710303009449894035801c811940c05805100081401c0301e0b0f0548450038140211400d5850762203140200c940741a0301034407001d4029108660034010f400301d2045940f00c2c42e840340c10010480e6560749007084035600680d0155005818146aa04204140c03e04080001016122180d01240800e0090b0b1030f503103082c1c01044c0221009101c80106100000c2210384940542801e0341e10036400c001c825511801034456451500c4010615000400748450f508e0083c0c0c44010340c04803d007080380d1514510795079900304001c0e00380d203011317003108207410501c1495010b080207025111030303040808404c2c6032020110359072109110b00400e9000020006c0c00315143c042003c40140522080704e03449051910f00300c09103800240d4481c80642ca03010f00002c000344980c11074088010b00e0340b20f1a5003041007006100140c5807203d14014600c1c0d41c04100b401260b440d1294281c2240a550350a00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 219564460 1250 219563210 219563233
    0x3070507030806041404030c210507140606090708060f040501080f100618020d060b03100806160912030306051f030e0a030f05030702010b1003050103050c0904051e030d0905 76
    0xb480710003a045030f015628143d8004602103160481542003070301030034418907403d881d00d0000300395880d40403517008100c01c52034805002600a0003608030300d4803d0000568484046400c103660b02d4040315811703800a0001c020501003805024010340015010740b0007000240c0140100e4240c2d1801c0e44038070010b60008403d01401c810910040031030b10429003046c04007614110420780c0c11016004080c3d82107600083c0b078442c2c44010742c0700d54024a43c18505a85074900003010758101680e9101d000428011040040d0b64207000005000f15400709484000d89641404e99100c0c81c428100811003e260380d40d00f000c2241e030f4030b0541c402902c403c5003012401c0d03c20070100080582e83c002142c00d81c0c544c05140003000184d0040413564846009103010380d101e41c0d030180101e014010302e80071250803070a1013809000b116450f40000d816a4003030401c462001c10341d84180946610102e60181458010880012068001040b404034007242317102141c3c24130501c0f03400d82c811a0b00d401030803541544200c5003941d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 219565710 1250 219564460 219564467
    0x50408030a140103020f040c02030c0604050c12010605060a0e010e041103060f04050108100506190e010f0b030403120c020322150c0302060f0601050f180103060f060c0609170307050703 81
    0x282c0d15004080000b009515560128410361841e00c0c0552045465445040e102c82c42041901d13420380d04001140d070170382410704003162200550003d25000b002801c4600da070030b2105010f81412904058402131070304060010898104080202050401c4081881c1800599940c01480021b00303c3e240142d0b0782e400d201c020007a039a08080321650103142000010040320710040354031440a403590b000401c4541e94000000c2c4201080c0488103040040c000003c01e40d0800d619016050350620860740c80010b4841480b202a03000880c1e00071f000a003a089003000b070301a1600202900b5900f0700413203080403100441c0c05807917040d00313061100561804030300b000494000d041d01000d00945040800001c1c2d102e440003522254001c0562026070f000c0004914103900c200200c1c0c80d0301884c050f000751204800440b11460303003c2c4c0c607692800242444004134070004083c00150456000d500da050b800a0f06555003c050300c090f8500740c03141c4002c040380205a48800009601c1280640d41e501d903581090720b00903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 219566960 1250 219565710 219565721
    0x1c0506040b01020d0801050402031f03031106010905040f020d0503090a120b07030908071209050d08031515180a0506040b0309060106090f0920040f0806090a0c0501050a12050408030a 80
    0x1c40c1158440c101c2d14807850f422000060648805440c0580d0f03039601c1800c03801d81d500071000e0842036282294400014198030510401800e40c110040c0c0d40e843c5d0340c62152000750340d000c0e01c020300910640d03038641c40146041d04807040c403248078105483c1000e40c0000094100a07030307907202e06c07209413046042038104002d02c401c0590000150500300440e0041d6100e0461398021090001c0c9804a110424000365024681d40001070000501c031040b03445a80c0742c4580c2030382084d900a5014441282c501e0040d00d0070080a055a07441206a18242400b030b9840e403102081441c00355030400e142c0c1e600420310391151001403026010340340304282c1e0f07800d10401041c98060141c1c003802c02c0040315041800404126601c840464103003940c0892008490484400001e0704031544100900c000a4006140100c2c65a203034201e0720a2000c0e66440d960703010301d41c0d403259000b010080100341d800d0301c24002907008201902c82d0348480c0c03800503c280218041141281c10680b015101801c01100301301c0c440d2158040d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 219568210 1250 219566960 219566981
    0x28060315020912010e1f18030f0306030204050c0c010c020a020f041503020303030412080a06030203070605090616060f0f23090703080d051603020705070e0604020d1109151303020d081c050604 84
    0x400c0f000c1c1c2c7d056000b010a000301b5100a00b0410895203180d9940d10a4125001464006104000c1da061405035450f0940c440312041e4155400e1043c520781c59400824039059460f005400c041407444d03c0420480200100301440a800d0100c05002c405620204090340c81148035003111504800815405443c2002c01042c2401c118100b0105100603100811000c04030b170103604040742c6030843d900010300c540c001e003d1141c5040880c1202070052100380c0c0c20401c0c80084504042007081070050484040c0d070018100c3c01d00350305440854850410b90450700550107000801540c00080d12075640389102d41c0680728070500d00e6261414001c50130410202d0700890007040c00d0441c54090955509a03d500c028491400151083c4000956039140e80c1c04503511039481d0781c800c00c110322400c02056480d4019050003406540000b110010300c14205088407440c4002c010712090051a50b42000420f4420038400c80710b10300140000721546e05002044a19840303140b00c045041d2070800140400c40f6401e004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 219569460 1250 219568210 219568273
    0x3050f1b0a080a02190b030a09110402090d080304080403050a080a0201060e010e042406090e010c0c0b0c0a14070b04020f0613170f030328060315020912010e 69
    0x10100480382e00054801095079050b1401c4016500b440d040541900c3c640e400305803001d000008000040040b1380c400307413002d840f4550200700c40780740906003c00c074007402400c1a0060054404c901c0810114405594014032449109207000e8907a0303100d9040820460b42201d041c2000300d1030f0f070300f10b43d020b00441002e0b00c4800d0f502d00d0307258509401100d4030300e00500080d1100d2228034940e000c40903400820851030036030382014401141d58850400043c044407011504135441c1042910300b1511502e00000010340010107070b0382d2602d410300480d4050f8031250401c4144000320080b00e192000201c054440d2500940c0c5000042c80d15005000c6942c080c030304154880c0004003d60b61100d1f41c50480881030318008944e60b01800003070a000e91500c01d4040b100c8403a84008000c200c4c012802d590307440e074800180c026030b6040400220500094444a01006200e0004e0f128a4005002641d010b000e0100d40188051114207a400f5650b08544040c010030000350409401c0002240b00b808508220710711459 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 219570710 1250 219569460 219569479
    0x91a070c0f0e0a0b130902010e102705010215070e0d060c080f070503070f0e03010e010e0708011514061303050c100203070b060f0d060e0109030e0d020904080c030403050f1b 76
    0x40c48200c00c50381c170303031060950300c80c040801c2da4482d1140c140b44040280043c903285084210103483d003a82500103038503061041e00b41242d1000c1d40c2c805c8100f204c20680040211038031000181484e8280206140100a00e501c1000502c2e5a07110800240300e000d200c0014001c02c034424020041c01c0d0041480e500e07170310310006202c4426030080841c0e501100c645401001060300301800c440301c0c100c04201c1e40d030540c00d144c1800503021065014582019014040342d809590f1008268241c0e14200161808410070b008100244000c803881c103294010020081d500d024401c41034000c000103070390416a1f080e070000c10800c45d14200203c22f240d04501c24002907041280c50359940355505c0000380064000d00c41000f140f0403585034451003034040ca9100c2030a0001c01e86000d9006d00911110500b0f5000030a0307040d01c0785240c00c0c0710103405035441d00074003880f440c1d81c1d071529000220743c000341041c4501c4c4810400000400e000784028114100c118000c0c2c28408801d41c190010b43e001c15807038910480130710 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 219571960 1250 219570710 219570731
    0x809010216170c060c1306020f060a1524030c030902212a010905010305010305060a1d0a030203040306140906070f1b0b040c15091a070c0f0e0a 63
    0x601d41c1103070695202200240c0b03001c880103810b2042c054245468480d01c03d5005000c920b2107900c001d499444600e0140c00c0d90b050b554402245d4032540140444803581065010030f040f800550800020100c0c1016042c6e036156440411111a413034081005003544481c104000b8015414020050114032a1800b885808030580000d03000120001541120620a044c008030a110600048181c488140110300a10342d40303280414615111003007140c000703441c00c5004190340d8002d01c00c44d4107a0380c0010060105d90f03504031000d401040c660219090100b00070b020100958010800c9007070b19442940916241e03451440c0c440c0c01e480c0440405c0840258842c108000c4000c0007402c0c59001000e460502210030b121001a100d0107111200ca034401d80c1000b00e03c3c014800110715990190340308400c41d0001d15595180c500b0018070300342c1100001490810100003460240796001901f0070105905442c20310a40d9590b200d020041d4400050080b5100007040b54503e003148090f8004000c09041c00110341c00b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 219573210 1250 219571960 219571987
    0x31501050a0e061c090c060807030903120c020a0512180f030c1c060f0e0618060711100c031514010203032806030b10050d0b0a0507140301120308090102 67
    0x6000b5142d0140038013262401140141e1100d146148200030000c104250460074119a00d1a040c058130020500320404100454800d128540301c85825581c2e11045514946020029141802c802c0e0118899950391101103002482480780c4e070043c44400903901c84d1100d025092107402c101c101441048030481030140d80c0c4020900e06aa014121030f04603141421501c50030441c5078501c1e01a10300d42c6000032444180c10315520060000d4036180c00c641580c0d039102d01c1c40c0d0100d00540c415000c0c5030049404228502d0042e040c40c00c4010051042e944640341000540c000c0f65281440c0b04002515010050f03a91440410104c000c0c00400d12000041154240040d68078130010341040c4031840d0002d002908074407890b43d07001542c41400c82c1440b40903504e0a2440361028180d900816000e0200400030302450952100040f2560203c54003c00d075452009070001440003e04403028081000341c0301070300d0607405005501800e0414070945400c2160700f1b0081413910300406a1042da8810003103445401392 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 219574460 1250 219573210 219573227
    0x1801082e0213030f06020405010e041802090601050c010905060103020906090709140103020903010213051f0c06020a090f030506011d01080604061a0315010812120703050402030703020d08031501050a 87
    0x1210016903100300200c101c0d00710740620b500c0038080000c0b4504003c10040160011f008540b02641d95035459010641004222003825005400c0c16040046100050030b100000756400344050400c2070400654901690a6403d41c0c001192280c0102006004601d0010066a040300d020384d0354252034a090400074010010741e004902c031803400c086104803c1da2103030f01100d0324100050000d64840c21242c0e0b141c26041814080d040c8143c648c0e944a2072400c04050000500c03a0181c1d80742c05042403070380c440c00000d500c11354000f007c1001e00710b0b01060b5003443c140000c0095100e0b2004121540c03504408484c1c1142c00710800c12690071001c0100580c600c00a0100d8000340c101030005503540c08140140d10b0003241d000c0352900350080003241c28110443e0305d4464100da44800907282007040705940c020440c80b406424101d17910b440340100e06001e200f07230f20845d44244003804480100d0740360380000d070001d00c2d544c60031502c103a800810171402240207180c881c400700c000c2c01c107581003a041d0100500084c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 219575710 1250 219574460 219574543
    0xb07060213080c0a092703120506010f0e09040f0803040521041a0d0f0516030b121e0a080d1a0d170a02150103050102070512120c03070509180108 64
    0x64598142c0020401960b4400c805441c2c03200010718400b40b10729011b0300f40d00e1001101c401849c6010001407155005640390032a09619650b201c03001c0300141c04011082c0c0c009001524222550310030780c40040d0a0000450049014000401e03188a5101080518090b060058003840c401800f08001c152114044040c0601e091000c1d5030b01d03041c81404d488003c090400750200d1031b034100000d0004088101c034040070003180395a0140078044441d81400780401285040100503800840e050b80001c030030142c600c41d030706920015102e0440c0c49480d80106500110402c84620703a44880078414590341c0d9615540d598002c0e2642503100c4095100d03424100c0442d48854000c41e400103130441341038802d00040036404284290040700f96100d0500900039041900f04582e01e105842200443c80101025102e0702c0c500c0014030328423a07440c1003001d001e540000d070094085c03010601600708070b07681d0340081d000f101040840303c15842d85028101d618003603d0818a030f10340c0200c06001c054003c0780303404c80880c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 219576960 1250 219575710 219575729
    0x406050604090614010614070b010603021b0307030f08130b0103060b190b041d090304090f020c03220b0c0a0813050a09021201090605010215100b07060213080c0a 71
    0x280e640002007005800091002410240b406418203070140244500b9410f0707651907514240b0110200624603c80d12a01d00040c1030b40c00050010012641b085e00144048002556010140711a0581c0301c0e2850700700c80b000b00d020400c031079042100b00d9441114241d101d40b84100305c0000003030940300c0842050301070001521064842c2400382032070702d54104d070307a02800c0b21034030b10032a1179621060000780343c105000d030881c40803504c3c609090841e51580f205d40501403080c0514a044d1910010000412040c02e0346802c0c690240025040d00800f40040c2500320b50846508400084103804010042442c2d017140740e503403a05106030b40e40c603813000a0440b10503612001041e92021026512000e241d03403503011952011414a001c0380340781c2030b0f401401e030029030b4040b005d09503620f4085100030b807180e1b40104e90050303001040e50310782c460b4807490f110b800010310142d01d40341c2a162080045568040042039500e59000103201909140d51540b817402440041c0241502024040c00034000d0035052087c000d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 219578210 1250 219576960 219576971
    0x901150e060a27080a030c021f0915140d090302011401060909050c0c030301060513060c03080604091401020c0a0201091d0c030709181a092a041502071505040e0406 72
    0x241056090001605501c0f0880d40e1078403007846c00900200181400700d014050f0001440306401a00b0794581c8031001948520720f485040888166150b94041030541c10482c0c82a0f02140c00c0a159004004102d0b104501003900c100506029080d51200442c1150f4079519000401c6059882400700040c0c804244001c1030070b46910490f40c000c3d0040502001441c00008000604103420000420a0303081e00750620098035900c110681d0680e104900c05004111980000341c224503050b40402c040c144a0b01c000400310040c4013541e402c98104502c5d440066204803203140a645c3c0100c032040040000d812440d030030b0341c449240807080310005403542c801c81c031000c000b06221a00640044000c2d2414444039284988043d1842025140040005208200201d4042180c1c02d00d208014482c0c1000c89070840509001c1c210240c0c60200d08002c221418002d00002c5045049101041020b41150b8010200d50b0305240100a0989810394280d003402400c02041059a00c000d2580b07910907003000b40040c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 219579460 1250 219578210 219578267
    0x100f112109010e040c0504030201090902090604090207080705010e0f1e100e0a0602070804090b06190f20011a0919051504020d05040507120f0f020a03020901150e060a 73
    0x10a2071082c01c0c541e0b801380c1841512031440313034044050000c40e4001d90302d911099a49000c1c0d64100c3c415a2103098200310108020300000c0380b03030307001404000d1044414030b07d80403c41c0c0341c4c01c0c07c54810102420580c1c100d100500d09007441000a0385075145c1d00b40020090b01801c02000c1e40c9d8410113024203180c644c9800c401107900000340030500c903041d085401555607030703110326206606501c1401814103a516001003080f150600d0070a1320003c1c644200308554030b21030b032042580c00000e074580c09403c1262010303090040d030311914030b60184600060008640009001e2030028012860140ca5004515a0b01080681c0405ca4074910700b4124003c000522a11100c106c800060f00381e42e400ba41050000482c08484156a80024859405041035403062a00c0c4e490b5a55100303030798500a0140c010411030100420300000d1244009440241011304496807580454041c0109a20000240d004440c60080d2150001412038900608841e114580701940002503c40900a0088000b000c0c8003400c952 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 219580710 1250 219579460 219579467
    0x1002010c0c17041e06020111030717040516030b04111c080d0609020406020d020609010506060d050c0705010e0307050d080606070305090a0503030c10060f030512030a0902100f11210901 81
    0x6002c0c1200b01008600d100b4800070131860140b0912034080103601c0c1c14400341c1f9101e4200281c0c0c0c001c041669645249074040c011035461050041d206030390324010f080380d18a40d000350055013030040d803281c0b81c0140a850582464a581004c0c040c48600032a059407918850080f40c0948149050703001c03d40c50348490400c844800107201e42d0308102551440080c1c0030402c5900000c0c0125030110039422181d03aa40ca0103251070076900e054504507008402809203080c60300142e08416031000d01c9080c110b0603c5142d454090a44820300045400c0e40c0000400e0020302006110340c3c5800070540c1000d000d2410403170049800e030f100d0500040c0410101180d000c070140e07182e5200c0320044c6001011641c40310030719400e0036200d403917490350104481d103410800621503d100c02d8074400c0340c0e0050090885400c40351002c41050b440100038448a40d620b4410300c00513511030964100d2075246541e00342c8820240b03c8050200d0180c07078940c2c5005c2d404410401003071a11041928500401450a00d03147d0a0300d60043c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 219581960 1250 219580710 219580717
    0x30a03050a02190c030212070b030c160227010b03090303060d0303090f14010c09050d03030c02120c01270b15010c06060308120c070c0308070f0807050c1002010c0c17 73
    0x80c3c0030088042511418042010740c6803065038002c0b01e9400000d1401003900b5610041c40c0708240d40c0800c2800010340d414114000351802c0c40145d03403031640101081d13002800211282500c40350700201d44044132203071444400303040d02614048182e00d1031820002070107513a80c0001410345100b0450b180e80d0008043c031039000482007030b501102009950003145000f8543d140d0032030410300c01c0d40c40c1190b803900b4035204009620480310003801c9100c120104e503d04601030900e1070070502c154030580c5c0e5000c6103a05854001c160080f810703400060b0050704070444a0b100c0c3c100f0740e0211140c00142101c0710200e0700f007900940e001a07440440511174411240140c0b003283c081c2c240034101d107207080400410b00072048000c00c0b40c0c06c00e840300090140d07154140c98040c0e01a821015213980ba0b400b05c1031001a47c40c0d002000d0503030150204003020015035981e4580c0742d01281048860341c1008084101c01d00340a21142d6415503240002d11103030709041001010701d00701400103400840385107050b2150300c407003c0c100c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 219583210 1250 219581960 219581983
    0x607140307060f0b041104090903230703030c0c0b190e160302030d08010b070b150a0b0d0606111b04150f03211d0f0909010b13020405030a03050a02 65
    0x6498844010b0b003444002804101d0b5044112400d01c81e01018901d828890130100000c1c0390380042c101030911840000074240803c00301c0c20f000340d1001141d03011200f2080d0b151141580900103a40e01e0f010300e030080544122104841c1070209510400000445443d21300f17a114441c40f40046080035041110300c0908442d410086140c0600c6042201500882d4443c0301680d000b54120741102e030340c0c05400c5400309424410b1403500b8500b80001e80020b111001802e40040044c881d803010340071120000b606040c180e81c0940d500c0c0030009000c0c800030000d80540d0000300010f085c00c18840313410720000c0c0e4071404d05d607402070700d050078107010052299225440b1003e140300b50710460441c9a19280c100f07000700070502061325103940a1500b27139504922201c1c045071460710340c0c1da80f001c504180601c0003a070003141601a64404030003940d8481986801c1e41062040070320600108009055000780004a81c00343d0303800c2c9425004120600c503d450021302d0f40308190741881c0c000c1d5540141803049013000072980c0e9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 219584460 1250 219583210 219583213
    0x90e0601121e120e03060907031e0c050a060503090d02010b1005091309060c0207090b0d0b19050907170a020906060702010c0c030524060127030606090e0715020705060714 75
    0x140d01d101103900840a030f08130b2105500311502d5468140c001a5103001c41d01c0700038115010302c00f5455140205113240b82c0214400e410799442c0da501c40c0001198010180c201d100090f1f0040300704841c01204005402c103000450001308070507240c1401141d19254847c0d4040144032000034a032409845000000d840101100c0040018030690702d4007130040d0564a01800c0140b182140103d160444d0342301d82000c21000030640443c11013580d070789641d001002401c4242c1d00a00c2506400355072818051300d84244074005c043c0c4440c0341054000f07a40b56044446c1501680c0c007505010006072104039940c0d40116086a079240c441c241440101d80d20b44c4d256000915070030a00c000001004400100d880c00e03d510f003841791f40c1e041c008403c070959a42d07045900340e0003e4565000d4000010402010030070780b2822048150165480386c40e80350a071451544660030640d500c40c202100500c00b802291f0162484000b501d14150110200950301c40700c50044600c03819000489904000c0c1080200780c844950f81b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 219585710 1250 219584460 219584483
    0x10512120c070608010b03011d100504090309061d01020307060f1d0105060a0501030e06070e010311070b100e04080f0a05040f18050622020c2104090e0601121e 70
    0x300415182c424070701c1680049032000c40003084a030b0b00710095034141c030341481b00701000c2000294482d01c8400702034180c1200b8481c13414041001c0e101c0d4041c1c550b904d0701a48400d004940b8040008000d520300e02e20215003060b013a10812a1030383c0c00301c111040260041e03008a1100701c1504410300825800504041d0314501c0001c48860302d1040d0066441000100d40c8002c105a031600190143c1d80390030441c2e425608401c0009910340d004a0001c201c50350103140c00107031103030f0494681070f80b41d100d110150f60311148001001245d965195220300a00603400d07e032a03035401c4c50354550045000e03231103440c1100c080108089400301c0c030450540380201a44101800c440e031352141c0080c40724500800d0b01c0e41480c1014009034840c240600c400218125402c4442d5000041c101400025040b21019440d81d000f5504116008208000da01c458401c4180046039610f1500c0e8004080354008144400c0580021004000311000c0c132201440c82600503140021309034040d00803c0d4020107001d0004c00010400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 219586960 1250 219585710 219585727
    0x20420071a070201050601090e070e2d060f1218010203010905090c181b07080c06010611010905120702010315140f030a05120903120d05040303050601030b0901051212 73
    0x660340a0300715440910718041c161a010822402c1c0c4108071419400310350030748801c000820f00300801c3c03a88030f40c8a180070782c5d0900b42d03600010300b0f82d80480308894a01c40305c1d86411740740068420524400c0101110054600714451141c4841800f40482403502052100700042c0d018103841d900b4200140d110f0021940c0c0d43c0c4070090032004250a88140405100d000d018031014188a0090001c0d50025111001682e480b01305107003a0180300b840c49401c0185c180f285400141aa0b80901450313000c0d44040d007483e41c10503500a0610304020103002d181d13810314001002081000c80c50807040740e40030050755950318482c0016000b4100c039090b42210000c00200014407119103424140f50345c0300440d02800a01d08050805583d0410a5406404c5030880301c1c08218061405004080c03c41d400f50565040c2101d150003441560091b5076103481c100c0d00c40301000100b582c540f01d55a4424000d09007009188800b101050b81170005010340d600400740480100d072021810081104aa60280c0b41c2c16629201d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 219588210 1250 219586960 219586973
    0x20c030f0358060b0901120506010516050a020103110f070201050a0521060f010302041d0a0b1003050a051b0d0507030216030509121203150d06090f120f050702042007 73
    0x400022142540b4204020850640c0042285d6400e04140d40b02d0054510384030003000140009441c41c0d06004041003801c004801041c80601d07101d01a102902d000400b81c0005800d9030b04041ca886184130040098101003400002a43c03900c940a20740305448030380c0c4d10320a980c10710500607040410303480c6407119800309004da941c41e845060166460150740b2102801034007070380140d000d0000030100420b0001e00145210004a0344480320140200344a580e070004100c800c41c1c00007000b40040e07240e000300501180640110340e00072107044000d0701c03038100000251000d401007655040c085a103032808a000b561081d01961003600d8217003290a0301c82e0480c50f01514580c440e681c01405160880c107920030014020400d02140101108545d140d42c1da0009951039800700c486031301e07601641c00800017011815520552025902c01c004082c91413003a4103007006904490b00102040040b401041c2c0380315540807041d01e4405605480c04200c481320300442901c0c0c0030000b2001c032220500400d050041c0420b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 219589460 1250 219588210 219588367
    0xa0e16030b09090a02010c0f0204050403050c01180c0303050d0608030c0312060603070813051204090b030c040e1009020d0204181505010807030b180d020c030f03 71
    0x192038504218507050388060050105040340c40080b113402c800204000355000d40000d140b018030510031b003c241205640000e00711031043d03509400080b008950380740c80400910405c0146d00e051125080742501a0751062915502800700404210001c00c110800e042c040d0803c0c0c000e080303082d0660342c58101500300295280c1120110850360509000030848500301030742280d0160310f440e078031280740e40c0c1e5007044114001c3c0c2c0040704840c51302c1180c16003403031510000c000d04044d00d1111030104409501508043c90481c2c100025882186844100300001d000046c0981081482080204944041e800010240d10703007000d0207904030307050074180079682000f40800070750395105409800030251100180c0c41100c00c00d000c1c0d52800e511001c02800800d45031030740198450000c10400304020541441075060180c058000005a405504103520914050004030407010300388001b1400c2c81114500083d81d5211000d13158204075550368014101303a03e0361082d90b0071007804100d50510088001c140c405000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 219590710 1250 219589460 219589501
    0x17090a0312020715051506040e22060606030510080d08070f03090209011214151b04120506010f08030a02100e15070c050d0906051909171608030a0c03030b0a0e 70
    0x221141e6016031146440400d480941d82420030042da2a2b80f503c24084101f02c100080014200702823040b040002c2d410b01801d409400190b40210b41424500001c403050303a000d40162007d504070f1184440030b90f500030242980715100c4c0c50891001300380da00b0241c00800000401a400c03190010010440d582070321280412103204003104040d1070130b400c0040752942140d110500310842088041a2700d80719001008020208a09842d031a05a80c0c2a1360004d281203d80119000c1d004480100440034040341d2400040c80010040c600d819900e070002501c40c408140d040091079a074030484541d5501c00c009094014051001c90002400c00c070402510721022030304216110b2060081442c1c1040c42081401d0859503192107450414050580c60b00c0b1140f000f0340b00c541001042c031f00005080e8500091240c00465060241061402d050020311800c0502d401c62034056000b00000161341e0341c0800c00200054261800040c800b44038000120510391030381c0504200a80300c01030060640a04210140300d9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 219591960 1250 219590710 219590731
    0x90203010509010b090102070e04150608010f0b0406140d08250c05190b280c0506060301051612020910050c0c0109050a14030a05060406050717090a031202071505 71
    0x160381e00c1e0a000c801c1c0c417a0ba85900d0041e00080810449800025134a61b0018410395014400c0105000084102c48440d8401c810583d19044250031448061003000c21a030300540c0c06120240c100042c900c940035a44982a0042104414810502c2103201c190b0f160280b40c0c42e80f180f02c500959211129070390340301c0d0081d03c02d1618201c00054900d0070686461041c0c056a1410003c54507141c413000c440c0e00b21102c50b1441c0600d15851a124500d05010140403040c651112401400f1604241e45001002028940240c0c03400d02800002ea1400b8203406110b0a60b141032400c141c2810b001402074011290b030303241c100101c02d07038600d50a40c000001e0090000e01d0b0341120303051001c00c030044400341090321407550401104001403002c051584404419568054104c56489402e5074910b0300e080800c660a5a030280c1e600103114486512000c5400746001e01000d2424505009521907140c40410100600b80300c4086d010b4184403650740c041d1100141c20030781c0000f00400c003401c10800303450111004c4440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 219593210 1250 219591960 219591979
    0x9040b090f1f0e07031e060b030703060b070b0406050c160c05130b0a0302040b0103090803010b091906050a0e0a15080a0b030a080d020708131206050117150601050903070902030105 79
    0x700410711410b00308031018011114000c1c2c8581d0400c0d4010680301c0c10602d40300320506a10041c86010703014800c0240040c21007641e03240f501c00c10007800c84025800c0385185240401c100c50101c1d40b8110810341091304440300299a84410000d08980d110f02d05001d50204002440d2109012498403403808981003551404504180050f1a0003101c8102c001c640c0c0c05464041b0a02c050709150340102004001070400081c00c07542a111401c041d0030980c8000c40c448000107a61250f400d00708108508410540b03880b01d8094188140940b6600814a03104208a84801d0010f050b9481200c06c2e0b0081c801030f1109000440d0501c001412a40700722080e201103400c00400021a080c00905480840d4002400754100394204400b1000b070350100100b07a51600301484003155001440c00205d00400026480c240c01d01304c1032500201350340d416480b030755080c040d841d014001d551000c10840e5200e02112407000031580c82c02c0040c0d0750340c043d002503680c261181100100300c1c009254000c5060340d81c100c44000c41d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 219594460 1250 219593210 219593251
    0x70501020c09090a030e0622050a0501051608032706061806150c0f1c111203010b070201140307091706010302031509070503150103020f120c010509040b090f 69
    0x31a000e0980c0c3c070351000e40c4a020004042071040014441284005000c5841d05000001c0c00050f5000806008007a6101c130100b0025458504c1140d03004100a080c50381c02c00f8245503880558a4071040c024005000001c0001c0f120305190940019400909a01403030000002024507910300003155018003a1542d0800f0030340209030b9020980c408d64000f001618140b80c2030849000071340201c4441215449079001c1050101c0b400d015405c4007030004070300103c0495030004000e140d902002c0407003100340c00011004c520100c0c070300102c034151040403001c00d540d145c00b44012604c0111154404016201c017006000c40300c0d610041c1201120303c643d02c0b041d42d0043d008584d503120403007844025411340c05940d000c52020701404043e80c1c0007021909844295598078040b90920310003810a100780b8083c40c0c0140110700e4100182c0700030030029685c680c6505102000595101c0e081220b40d4180310300131681045903a02c0760081980000b000e0025020380c00c100035aa030080c1c506403127400880015400102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 219595710 1250 219594460 219594469
    0x60e040201080a06150c15090803040b0114090703020a020c04060902091831080c0d0314130605130c1805071805010c110907020d020106090b030a0605100f08070501020c 74
    0x75610b0316000c00009402c1d6005c01d0703034061703440d5004442480e02009840700101a0f8880c40300304c070b4000c00d40680c1c0c0c0c1c40c046c6803c0345030090580040f0000f6105003115a03083c2c0b03034001c8482d4010518100180d44e140c11180513880e00101c090102c0e40a81850030101e0040721a401500701c120307080d41c1c21000300403c101c0141d014002124101065090051008941d1035003c100030141c0500d80d400306000c900b551202c9201d9400850a000d50782d11140030740002c13690502c9041c80362146815024840d04107e5400982d600381404003402158440c00410710804035480c2501038154400c0400b00080e541d580315000c0038204280040c000e170316010010352001d0203012401c49580031200c4030303d41d803410400190b40004013020240c5408600710780100c00361f200c4141560103032086070000d200c420a1080003d00751141070f0810f10075541020350f108000c1e10001030305c60710aa805040401c0c03558031502d003e03911410070b5101194440c00c58400050401c8081074600958500f0303070a4410b0803c00e80c0500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 219596960 1250 219595710 219595721
    0x12060605090603060f031b010813111002160609030b060102061003240e0109021536030a0c1a030c0403110f060a031508010510170c04060e040201080a 66
    0x640104800704080d0310245498001942c2c0180014202d90180500c040424600b410540d078050340c0100b03d02c5844c109613017088103164810f09040d80c01c01e8450a980da10004408e6022072603001d0711390468803105043c001d1050300614101568090380044d5140c10061030042030b07101c15100c10390f10300c002ca4240d510100c0c0740d620808840710701d01a00e0303255a403241c10100d0844040c00490340341c0610003000441c54058807041c4004000082a02525401040501311400c0049050520200005a00090366215030542c80e01e1041d01d4a204040346520000744408600c4050ba041c0900c0000d1010485502005416180d11210464101c1100189051107201c250340f241c01c0108144030030070016603496a540c2c1469406040080052118004149150420801240400d881c2c2e03a0132448841d4200d01100200803200090101d8207100310315089001107401041600e10020001d1812004100805040a40080c208115441d5102c2806e03000d8581664103d0000d40c100380800e54843d200d0062 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 219598210 1250 219596960 219596969
    0x204150807030312140c19030c0e061b06070207030b0703090c090b0d0b04060203240d0219120305030612011e0c0e030f0303060102010b01260a060e070207061206 71
    0x401200781161403da500083d04010607000070b1721050350200320700f050142d49005001c03904180c2d48406003407203902021b054210100c03080500d05803412206035800501804c00d000d094954640d01c0d0800b40c401041c4a4404612400324401c080502200036800106241220300450102d0f90a4480300c03c100e056598811001c1e010300092402805680c0c07044d48440d600c20303401040000010003560310071382c55440403601600d220380c0c00b004100200c0814040d080340c1910200004c50903a00e0301e00080d03200702d0090800780c0504102108802041606103844010342007059803040350072401d19000301940d10459420340540b1322540c54041101d81402030078042400e4038240f410116161007a180140048034440041100040c58424141c078280850030290340c2032006160b49140c19000a401c0d500c41c00c070014100440030003100d846d1000341040c2040714046500004203902c81500d4500944000d4000d015030751b0300341c0107124181c1c0d00060b03024125085034856039600f142417050368040354081c1c0f14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 219599460 1250 219598210 219598213
    0xa0803010506030c090d1208010b070f061a120a031d011e1b080405090f0f16051b21030c0406030b030a060606050d0b1509040905070510020a02041508 66
    0x62190b45882e80c00746500060510005085c2442480007507a0007007402400d503000c0340c1000100c9100b039030103030711240500518501c06250000d41c2da030b160405010154060451070f030b074003007011441c41c807210800c11840000b0604454203100d4207460f501e503200000e0840101d481a09420704211048650000f0f80c0016180d9032045580e85404201c1d00703440c0b9071351004210445468503242d510a000d03503000f0a010f2440951160704000510150000c007809804408150f401080311031005401007503400440700203501e0a20050300400d1702e40380900c40c1d40c0d404001e03001c6031010340d103180064544150540000b008140c14001442d00c0614403095600d00902d4008100034030525019402c0344501180184c11107042c041d80d030f11074004488440c0c20481c0061400104d08000080038041e007040100100e60101090129105141c8503101e9030314914021525040201c0a1020521030303103005101c00f030a02e4a09505c0040001d490b154030300001c91080e45807000ca12000f125801628040c1c131003940 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 219600710 1250 219599460 219599467
    0x18031506010818030301060c0501060e04050a1e0b04080901030b04050403020705011404090c0201061a0a0e010f0c140705030114010806040201080c040b1306030605010203120f0a0621030905030a08 86
    0x24011120418020070383c0101d01c184100c0e0484007141000114006d20b0305984407401c0100c9460140d080d41c1069002464000126081c4004a640401c42008040d07000c8141c0d41035103410005d62240c40c2c580140075103a062500204418800414001c003403007102683c0400903007411074100011220255409001640981c02c1809a54020391014864200001c0d40c1c81c1803a40e6802e42200351903083c0c0302a40180d440d050b00300954001440685050302c04540c1c05400c0040c02c0c0c0004107e400d0706814181049100407070f80c18800c3c00384254906154102401e16000100103001d03580e24100b030701c904c038025881d119003881c032103044034440b07410380f0b51032005044143c07502d400440305090058814002ca1004020001c0c603549082d00a084074031843c0b40076002c0320b24000b0302034102e9000740e01c01410b54008012204134150100165588070b081c0304180c0c0302e540c94000c86540144000e800c0b0758500d20441012104100b64a0f0304a08014481c1d030724145559112001c0c55165100300070020046170090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 219601960 1250 219600710 219600721
    0x6070312020904020f0712030506061e0a030f0903020109030e180a090303110d0501140103050c0901032a05030109180f110d0b010b0706050108010b0303040909150c05180315 76
    0x750010b00c0d01c0c00006001505102044446160903803016204859038149072404111403a01406500d070f1016044903113038100103848407200c2e011b9407140c000540c521030000d00d1441c020b003c1c2d407021680c0e201000003000003c08070701e000f03070090103440b6054010850380c40c9841c0251074079042c1030441c10107100c1d00e0051f603100c0c4c811550241001c0c182c10ac0600d9210391140e5407081100000d0440402c82000218140d490071141c20404080480000d04040c00e1070704101003403034904121040d012080c40d00040104502120401d82c204c01da060388c0341b01001688000c0c0c4203a00c0345c080c5040e04c48491007040440921402603442421050005110004c5654a00007040c03580ca0310541c000340c00352103a4401e000c1c654034448020400d0b000206030400c089400803d03c0b449204441c05040b1100081040300400c1001958078002d42c031940709c903692100414410454000d07030304489090802c1051151055854003e030040c0c000b4001c0c05455040e940b141602440c0004180318080f000b0a9844000c0e21031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 219603210 1250 219601960 219601997
    0x50603090d181e03140c0603040b131506050f030109020f1003110a0309120206150f0619050c0f190212010b0d050c040c032007051501061706060703 65
    0xb07880760b0407207600c1400003141020b1108950241040303014100e0b8150a615184602c001241c51482c060340c4031102c00c0d41a6240c42e01100c0d045500410090b6141e07450502400d004030b0b118400404c032203220301c03401c0c2155410b504000c0a07075204407500c0681d5103200080c50308880900c4406940204003901c0c4040031b0030019202654902d031480c000c2040301ca001c18040c10390780030091210000e07a54283c401d041c031642c8904040c0c14603862001d00340700d007060620366030b1b03031030440003400c1c4112900c0b05410b8042c3d07100c40840c0d00164440b008000b04100343c54000d0170580014404600c5400b807141507031704445010484114007049500703480150b86544d000e00055004215020781c6a43da00c0150301c1c0c89540f842c0344080345601c5640205401d81e418400d210981e2080e05401080c1410f020f46150b011040030000d0041c0c40b244802c0544403011410079915203056071042c0c0c2034404001c4004a0000e0b48075155010140710308008680d5038076100188005842284805000510380c03400543c0d40d17401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 219604316 1106 219603210 219603227
    0x2040806240a1505090d0506150108161805030a060b1f0206130602040317070606230f0303091008060406080726010908031e01050603090d 61
    0x18034101082e40070115004500102d1140111941c26902c10002c2c2d450000c40104006481d00080c240344c0c0d15080c0648901c0016500805850855409400424052203c01d07100700d002003075061040711196100c150304608040e007070b01e0000d0030356401c00000b24054014100015a81c074003400304010203154000c07030150780d42181e000007561034000c5441540280c404a03a40c07806996442c14400030300c100e800007000024400c01c459440300e107070000790070307494810f5404000c000c0d25204180f002d9030180798240f07290701e00b51610110f05c0c1011002110300b8840030301100d05020070745000035a04a440c03403025001601c01c104100702d03468540954001841140c01030002035003002e40c907400f115568260903e80789a81551f01c0c083c0e680950084030b007030b608108034544a040804201d29a0320740940f0316540e511203000041010b14040341140d02500d4030600405460201c0b00c8192035021 = true := by decide +kernel

theorem cover : BRFrame.Cov 219424460 219604316 := by
  have h0 := BRFrame.cov_init 219424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 219424460 ≤ n) (h2 : n < 219604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
