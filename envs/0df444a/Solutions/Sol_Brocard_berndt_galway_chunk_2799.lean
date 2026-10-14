-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2799
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:46:45.777814+00:00
-- url     : https://prove2.me/submissions/55e8e113-8eb1-4661-a9b4-ecfaff256b1d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 503237410 ≤ n < 503417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 503238660 1250 503237410 503237431
    0x209100918120f0804021c15021809060d140c060a0807120b0603011e090501030c080f0703030c0b0403121104091802031c181e0e090717190605040c05060301030506 72
    0x6147c081114811415220180c100e43c03441203c01030a0f490000a6000302c02a0b4690070400d14080d050b440c1c8030220600ca842c003c0c003800381d0044030359a81d801c900f4054002d18035a0241c42a816842e0320380202515a000c60740d80c6600c6141880c41000d8034001ca0904450716503420061070340c42d1521078404417411914200405180102d0040c10594069010f8001d503c606040400000501110f42181c805540c0b032181600d0b07095000c4420305945241500c401008184031a28000c00310b91603400381540701c4d0103800e20080e850321010150040f00c1550407003034003050300468180300d040c1041c4298200c5070b4900480c029180d90f16000642d1760501c481c04100783d603400e01c0c0c1c5011708500c5210441e1002c940c00000b01030351612802c846a40c1042d250004910850700c48000481c41c039103170000c030b004041c244060443c5500304040f100300444901005109440f0300c00c2054402c0c0300001e184100140078110004143c00e0070b16116080d0149648514414a010320060010a5003c250301b40c1003100d281 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 503239910 1250 503238660 503238679
    0x80705040e0c040501080106050c100908040329161b030e09010303080906070c080a0c02030c0604140f060901020d110c120606130213030209100918120f080402 70
    0x15411102481a81c0011010707020010911202c0c20004010303000340d40090300e81c10020703030300c600d4203c1d40380c090030340140140c0e8001c00640307000ca0b030b042d440b02d41554001d040140c07510b922910341c0d1030501142d402c0481001c40081848400c030404103052a04a4201c10031400402500040249030003900c188025030b42240b240300d002058012003c41102a401a0485105d13603504d04028144070400c481401075405103a0000d00b282c2c1c8982a12221168000120350802400b03c0b1700315040c4959030b4040741c00d41302d030501d8203a80d603940d00d025200400a041c2000001166242070200a400041e280341c010070007402400f01d240e801007a140a07040d036610b4407015071807046800078074203902c1400c600d03040290181c050040c1400862403501c0340b0810b642c0c0e008402800c00f200022841030070018110214070020034001494504659508000c1b4900550b079201e031100280d40031220318240403184101d140459000708003c0f001144020407443c00e040d201454000b01c00781c070500c00204001c0c464a40070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 503241160 1250 503239910 503239921
    0x10c050f0d0e0f030307081308071b0801021606060503010b01080f13200103180314090409060e0115090204050d0303020f1b07060e0621040f05150a06090510030308 72
    0x40d030200300703090440411200070760843c40100303031a54400d4813040d000402e02c0f400213001903242d40c1e070403074460381c4090f085140250941380c00c456007444001c060300fa807410b4003002841640c240090b0045a600d0043d61120741850300d804800c4403d19480140030364149060031203141c0e080102d095000082200c4085a0360f00c00d040c0f10165180000010300d6840d5040e0011803884070010980c1890101b0b0300c04100c0329070032010501c01803400319001400226011124a05c02122030060403c0800282000c00d4041a40d030f03402d400d440c0c501c0300c28640c0e45e5446070501c40600b0244c4018000300b50640c001c6140c9402e1002048445c034001d440941071580000d092014100404204c0c2d42c290001005820705a178456201034894180b032040c1c8000548403407580d9480d181c21401c03983e4014401c401c1501d1861003968101c0c000307500500c203442c401c440c0700300c01c80815420301808400810010140c1c00c0352511461003012208281c102950706032a100802c05d19002c1545502c0540f905800c042400380c0c0e0300e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 503242410 1250 503241160 503241187
    0xf032003070c0c0b34200d0c080303090c0108070e19030218061302120f09031215130603122d020f15040203071502151503010e010c050f 60
    0x10713688541c11800b40019500074a216010030400c1c8404080005900c11100c0310444e28018034070200513005119044020161015404410546100162030b6a03ca07600907118000003d100350702810460f00000100064544144842e0407140b50900b01300b84a41401c06004140c6480c010046003d4114200002e1108542d50f074a4001158000d20295001c1c03144e1060300c94110046d51002d003c0c056510703214111080d1390080e03d5280d13800e06201403042d40e60281c0000f5415024104010314001040310303c0014003064141c61150500d03600d0110341d5a60f4500f8043ca8403d000c200c2212245845c80600001e0300e4030000703244280c071625001403844002c00c0099410341c0081000500c1115003110311600075004070b440e02c181c621690039103130903880500e000030007480d0481d0700a5040d00010000c0c011100c0101440b500150184100c444800310041c01e64995082500c2c460110189002d82d146203103000d0042d0083c100c0f40000074001940c0c80c0001602d80d000341500b5414655000c910903804459 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 503243660 1250 503242410 503242433
    0x2060f010e0411270601020c0d0f0c030204110a02070e100e0702070f1d0a05041101050f0708030a050f0a0c1b060b0d1b08060601080411030309030d0f032003070c 71
    0x4002d1203142021a8843c01d0b51100d0405044040c0b030a13509000078100307600110700050b5101c0094228502c0203070035075800c101e044150404458001041e9000300141c0c50310301c80c03102c1d810301e61625a5942d010380000a460109a075011400003401c20f4200094a0581009907040f124618000c0c103050302c440305c1c164180b980b150880760b02c000c4223040006011000c00180d807915200040c2d2882d40340c41e600303a020140c50301100d004d030109048402001295200380010b10010060288141c14480540d40e5000d040e0701c00c0e140c1204140d1a602031240740700c06541c91075040310110318100503024420001500300340000110701018182c0000d40c406000b4590400080301000418404500c2a0b030725109101110341d441c4c60034503801e550b4010604000c0041c4940c0606070507102c050b641d545565485c00903507606500c1d10b800d408103101c95003180d04c040089010642c9592951500c0203058400101103038200c01010341c401c1411803520006050b501d0483e50810311510308400051254100f000c0d5601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 503244910 1250 503243660 503243693
    0x607140120030a0e0a020a060503101205060a0609050601120c090825080d050d0f020c0105040c030314161101051309290603060127060302071202060f010e04 69
    0xc103008812125107440e500114810009500100030703210f2040700da143c3d524021000290003020600301841035902440c040c5520440d85c220b0f0546c4662501c90700c07000c4c80c2e40b01d8001c40f881e900407070a119138422180680c1c0060034250074208254a0140b00003042c0f0912074003100c40d9184c1e00c3c00d2805c0c420384035101c1c41018000e240125800c102d038001c41d07805000c3c06225000c25018560801045e88440802d025901d200e0556465003041e80140d40c00004100311040e0760704150b402c200d481026202806403511580c000c2809035822840c508000d4054442940340e040320351402c0000e00d8507507001c1820391080d1908101d0001c00000400c006035483e224803d003103105d05000400000d0843c1c07052300012003034400c980c41c8502132176442108081440c58000020361008061000500c0c03035100d4000e0300e58807001602600c1000c0c80b4582203c1da040d00c41e8100c0f400190700010707000c0c10310180380010340d503254051005088030f26040c20321101429042c01548114003404001c00c09200302812629041e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 503246160 1250 503244910 503244941
    0x1020c010c0206040c0510050301090b0f10050d0c031503030309140601030c080d020d051b07030213090209090f06180f15180d0905010e06040f1202091506071401 71
    0x7000e0503000c0c0d5104001c850132614031012101c0400c1b21b09152107900701e4440d0355241c0c41c2c116402c0c03040c0c030405001440a1aa000444540340d60300650b5514a52014004651241981c4150020944082d2800d40c00c00000303050804880c4040141e1b40484101240c1e014500002d07007170044d00d04911665400c0b0a00050341c401c0c41c00103c00e00090748502c030211401d840440d240b00406050aa03200c1c201c20032406c2c00f0901c140010096042c00c0021440f18040e030506441c5495102da00049035070300b642c001400c92503030702c409e10b00031405c00d01f140c20381100c0c012006109120500c08100da8034140207190b9000d11116882c0c80040c0d89041051054074860a01a140c821b041511503000c07250040307544030004501602d00b201c200c01c010803180341d40c07400d42ea104030545040200540300c1ca100c42041d41c0d00241c080200241c60741681401d9000352948480e410803a0219004200c1345e080013900d141c008120100480f140ca5660b1011100c0b82c40e40003070030b0000700398002030039401001c60820f00c4650703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 503247410 1250 503246160 503246171
    0xa050904060f0f0e0702070302010e031009052113090216080711010f050c0a121106161e0507170c1905070807080a0b0a0605100f0815010e1201020c01 66
    0x3803540c005200040c0c030550307420f0182d034640d1003560300078040081d5041c0d4003603007052409102551080c1122081001c002e02160851000c00329142c085a04026081d102c0740c01c0346065900e002d10381c00a028a49000780e4020381401030710680c103410b4510901c602c0b1003240e800900700039041c440e40002c419903a00211401c1d21400c142c10700d952122200c03296a400140f00c2c1403500f214a00990a6451801c003850061520b004150f590300b2906552030350100c20711860580001e07010808100b4a0f1283c02c0070961491071204e9018094a0340c0180c9001d50010300008961006495015095514168100991140341d000d5032040c1c9609116201060800d802000c03a801c00001c44c40102d804040e105c1c104551600d40e4030a4a903417598054020611107401c40400400426040d09005402c00e01c100070004181e55180700081180b20a0700d1400e011445d08002e089450b50032008090b40000c1c03005c4a000c645180300e00003410649d007605407505c550035210844184d840258140c58a1001c840004c001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 503248660 1250 503247410 503247419
    0x250201020c07060912150b040207141203010303081f030f061e050705040909080904050f01152d0908070f05030f010605030a02060304170313030e09010503030f0a05090406 75
    0x1035884110446601d02c214000080c107684a004407404441164032007250020007552103120f420950141c02e00d1071921003000c1e42160340d551000f000c46074400d0951507040803ca6040358188031034801071040207001480100007103500305d10100d0384400200c0000080034411a09559842486d4001402014504080d40708000b0340354440c1c10458107020011b030365419000a4003050360411620360002901c180310400c1503886603004030108922075203a07a410420510041811640b080b59221407585008004000100d0035076840042080d4a141070715084004068a0352210f00c402c00c4031001e40b030126a0007a100b807141c50410041c00307080c02942c04080e51405008030101540c065a4881d0050042c0344245420522070003080361030140241c050b44d0815001c00c0b400e80c1005105407504134000b07146d0384500143c2070045104030309030f0041354060019420010b143e80165021540901c50400060000c0e03070780081510351502c207401001e903460f0f541803011503240c06290501034100782060408103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 503249910 1250 503248660 503248663
    0x2150c0a03030507030b0d150c050c0a030f1202030708040b18011a03010b0a030506010b09031908030414010e10051504021810180513270308070c02090109052502 71
    0xb07006504d030342e03014400c0d0200b0354200800f40000c1c1800800017480ca01510b0401d0101d900030750340300521810414101190f19178030038202180300b0002c40000da001030006101038cc022103004880320b115102142586081c040103410704030003500150005141178009220101111814400300308104001e0007400c6000064030000002e4010300c1c4d01c41d50030848200300e035007480c1000d0303801c403030304500180a42d034a000201c44541e0b1141c041660075019400108603e07928035104810340500c110100d580da403409050848401080706013440c0b403070741003590180d4900e000258000e40d01001e00c0c5c1c000f0b9180c994586203d15441c2213004507802500215860039940e5864048042e4500191180d84802c0e002050031202d03a03009842c004103460b6218024080750500c500040851004900005983e40c1e985034062100015003044554032012050b0f400c081583c003100480d0070a40d282001104500305600040c92244140142c0c034010340e5030070008801e90b100b02441d040c2c1c00b14007950b030141c07101c544000a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 503251160 1250 503249910 503249921
    0x607050102131401230903030405090f01060e06041202011103040911071712130305120103150f180f0f1b03050c09150105070507090213060909090206040302150c0a0303 74
    0x10f0600302d410b03070800444e500074902d000b046003500c00b00d45e40c0046001500710054021300c004580601c400d01001c121074642c00500d5001d41c80c0d0030080302c2c0e1507140c543d000303050043d80074103980030341c1c02132004100050042c0d480000311582401c11050278581c2c41c1d0814554002c0b944440d06031401d0008100703851555074020b18030240544482c110354241c1e40100c8415100d1220030482e40c08035000001c80506a40c00d000640504c685861450822403000005802e1402e82081c1e80b411002810704010094510480c1024000c03a0018480b03001c07602c80d041111301d44454081c0c10403100300b601404000721b80c1215140182c0c050b03058940f07440b01145040807046180021900c42c4190442400c00c0e00c0c014406c14442c4010781d20400740d42829100444503038002020848280c45000700101c0e01c1901400581a0081c01480c03405903a807519034014070064403a070103034504901c0c0a038004090f80380c0c0011101503c1d015545050949502c03070340c0c442244900c0e04003004900500544808044d45034004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 503252410 1250 503251160 503251169
    0x509010c06180b090105040f080309031e0d1b02060a0e1f02030f0f0108031c0b030d020c0f04090b06060307090305030c0d1106071e020a0813080601120f030e060705010213 75
    0xf040c11503840000003401ca81c1b00396405001c510700da024080004418100440d0b00110030070540c0d0400c040080c460721107900c0071005020300c0f200031940903541d1046100d1000a0280f01102d81e10850509030080c0d1181e002510780902203807a055152242c0004114100c1000100e014010504a401c403042009410aa40300d000450714100030070015080d4a48172816501950044d62030700704010760f0100903003081446251286d0b1902d49100b100da03000d105081c503520460300030307048240c0d4810400c480d0b1140c4858042c800c074a04803054000c109050f0800ba031090003950400c0d601d86071003005846050030356200920910000800d04180840406c804c0c3d01c00703445864081c60b4400003c036090310350804a415800161010310700d030b020002003549014980c0304d6030050750714552181d02c650302150301540080c0078003000e1000410020382c2c04c0002c00c1c0140005029a11040150360342c5009501c0403000103030401400040c03101c4a83e0310340003107451440d4010000c540e10115107503002e080318000d118 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 503253660 1250 503252410 503252423
    0x11102105180a1e1a04150617070302040e011103131e0209040f02370b160f03052701020c030d020316081e19030c080105010509010c0618 60
    0x4901c0090341c009080c0784042c1d40000c014100e041d0300b5510080d001c19030b100658414011100c030080c1e00780e201a03d03d016034025a01491102d03a640b42420a50fa0070350f0140d180c51b59046800116500042501d04c1070303950441d40891401c112603d12800741507504100064114004140714058414440084003284100001510179a25040b4030002404800c806500216100001000101134031840001c107407000342403501c19800c401d19180d030800400c0c0766403017071900b031131904c60721000d00b40003c001004106520380c40d00202001c0c0d4010408490070080680007801d00d0a81050300400035580c0a008035100082c850f03004131450304198070b5402400703016000c3d0000b942424180490307600344040d420f400031482c01515112800010000c03810560720100309001020103041c880b07020482900385030320800c1d03c035288a01400314102c1601507080600d89041640890103411260040c11511302b424065207414850700142c652200b80c0c1c00040181d844c0c10180504e0f1821106c0b12032020340a4207 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 503254910 1250 503253660 503253691
    0xa0c03030b03010c05090919181b05101d040c1d1816020703020409120917060103240c020715031e050601020a0c08060f0901020711102105 61
    0x410b00d82224484856038000840400a00c00350b81045165141c0100340003c1c81404610001483e0b01244c0e80e9040c14001d40715804032603000d00043c1c09183e5070003a500f241c3c0c1458545031000190303840f0f030b090002406021090b000400707007040c040c0c8035482030341c03000c1c0c028060f200122400070a800720302051011a080451408025820502d0071544106202e0a14a480d038035507500340303915100d00e1003100d0701b148500e190110050f00c070382c064480301030303c103074040520341444d104040d010103041d410541318008820700003d09102e0006c0e0290440c4e400000c0c501c4100b5004007090003103484601501c40c1c00b4106200d001c4615070005030b1000f2a2800c00500b40740340c5101000703d0540341c42e031195480c150421406148007204c60307400503400045c140111600c6c50703280d03941d1ba980c4107840e07840107486401110400101d044041c0a195115006070000c514040b250f80d6020300c4c10356407002d030a01590550325400b44c000e00075581c00180102084110034000c800c400d0301d0024040071603c2c05100784648 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 503256160 1250 503254910 503254931
    0x9060a090510171b132013060c0302060c070309170609060604020405060d05060109180204061713110f040608010e0c04020c030f0a18080f0d05090f090c0f0a0c0303 72
    0x1007503906001c0011061000c1311001d0b01c0401008442d100707254040d0079a61380422000269050b0342c2c40c0d81e100d05032005038a07801411441c5030b010b0034940c81082401030300f414100010b540841c429a0100311900c0c855180d00381342c102218400000c1e08590f0380c1390941d003070051344a0400107042d0700c030b440c0c143c040f00c400340e41e4441070109034000d80c0f003100d8109a060200700e8140946800c41c0d54000030600d80000c0c01c5070745140000001c562a444100312950005003440040c0d4440c0001d00701181480c42100582004800032450900700314000c0d1941411000c8807819954514010180480092050042584480c1d00c1d900074040b10340e481d005031040c81000103480c1094004d0f610320401c0000510700302002c2d15101d01c5150f0201150100700f05200d01c68001c800e0440100802a240c800010708520101003113841c9002000540d01041c03080902505038144d072041c51050012005aa888a5945450301d00c05124040e41425654600c4003003031040f6465804042c0d421007502a0390144140c04a6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 503257410 1250 503256160 503256163
    0xf031311040c0f050c010b0604060507060c030b0105040b030714030a0f0608070305070b0d0f09060204140f1c02010e1e0a0902040f090e150405010501050117130209060a09051017 78
    0x102c80007000440d40714401d03112520b01400c043e22042402c2400441c0100c0010002505039000e41c00110101d50003041a0041c4007062060081085070f43c14100000d82e0340e080060490300551181400320900000090884c610482c040c032203e0920320f59281c0c0f60308003113108034081c003800803080000d00d1a00c84c0c009004840000c042c0102c9802601801d40b031403c0c441c60f0116544200250100d290300d890f804050301c01d06218241c03d00d40501801030712a030a00564015103c2c908200741d02c83c003140c80c4400d50558418015404003050084503d010b500e46100582c3c0088011251541c402c12030b0b803003007000503c885090942144d00b151403104070350320303101c002c400c07405a40a401d449140c0f0110901c03850400c1d5010400600e071450842d20b41c011a03070580b901d042c000721411541e07651100010270a651300100701404020341c00f03145c44d0b02c9207080c03070f014502d0541d165400b80c40f03981da5002154041d00d4082204015250040c8188514545112030070004c40d0b607803090490303001c00d10070f4102a0a20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 503258660 1250 503257410 503257421
    0x20a03180326010b1b0a0b0708041406190b1311030403170c031b0408030a0f0e010e06071104090515010602060604093f120b03060705070f080f03131104 67
    0x200100c0c400e00b002003c5e0361055205008031540d5000303204044000001c40c00302d0401c54401c00307250760350352514038241c5440140b0002c507100181160740401c080c8046001c1101180d174040102c0040022030601010000e1050403001c00c24420f02443e01400d01c2400410800640c401c0d4065181c219101c1c5c0640014007410034201c9490060b07030418030100e2220401949641146100300301024149a00c6260031130459008001c0c400c08503904c558815007032900204070743c0361441d09080c025240d000f81c0c400b107002840703014001041c04031000c011011513035450744000080340d080380440301540408111040ca540d0280645800752044000041c0745150900942c032a01d5403219017415000f0700d040c85400701016072040c3c00c2804485001c20b00b0841e038020b000403003a01c515512501c52410800b00c00302201c0261010742c0c000d400900c10859890341200440720042c0e4440c84602404906051001c680c0c080c481880240140000501584042c1c51092000440c014501003100201c2041008126030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 503259910 1250 503258660 503258669
    0x5150916091b0804230a0b0a0c1107080325050f2401450b0a1a041205070b030a060905090a020307140a080118050d02070513020a0318032601 62
    0x401e5600303110841d000222504d4200300039003220148103403075581c0888031f041100c03400d240a99a051405460382d2210601c004603c0b00c5010b03010041c02c0100190306d9224503075540b80c519071110f159070900302c00a801b0301c5000781c000c0141c0361072080c00e41c1101e40b507a210500071142c4d080c40ca0b1a074031403e42810080f0707040b1250100200a4030449050b4134900001100d01d003c1401c00307110003980300c0d0000000d1111000c0c0c1240c00000c00385581000c03c6a042c525401c0510650101030881034018031042c202c8041d5800f0248210010015103007003445d00010b60070140c03510401009004598605800c0a4140c40400c1c209100e60f80c1d400044a54404400c00040d50640c00b001c000c0001c085401050340701c0720800307080d20740c1882d00e4074030140c02e44003245011805040c5908080003840420712112a0603d01c1c5e20251071210714000000b00c030081d440d08080d10840c1d0024082d03403c503000b40d01241049140c482c0b400011811810080c210f542040503410ba100361040040c0c0f03001d00c07a40c50075130586 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 503261160 1250 503259910 503259923
    0xc120a0b0f100303120b0d12030614090a05090a0f0602120112050c0411090a1508061035070207061d060403230a0f02040c03060305150916091b0804 65
    0x43c0ca07545084512181c1402d04039051965034403c1d0520f80c683c0c030703980848503004644107c8a040305110080454138203920030045451080d016118aa50704023015801008030704021030301e501c174100c05600785002680006d01c0d00100d410b0742820030031550040c1003452240070140140d41e90390100f0521000304014000c000380c01030300c54031401c3d142c030340e000c504040c1a40b02501d06226a043c04644010581e0300013240c1c225800c407144070103030b9008040c10f0b4411030907181d8080d14a00310344081c00c06241b884e0b6540c003540c1e8640c140e2001d403042010080c610380386520f000c4541d0070a140b0103511403006000d4200050325255a0200d01070051015541032800a42103d1810f031442d211401d9100301c80302c400d09546101541011120010484901010700403500242c03900054030402c01220b028071940e00a01d030414404001041000c1800f01c5070042002c0b054809036180300e5602d00b0081c90340c006010351442a01c010440b2001035000c0b52001003a1000c0070014144950251743c109021100246070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 503262410 1250 503261160 503261191
    0x40e060916060509311404120c3801060f2312041115030f0a06030b0105040b01032004030c0815070f05160b0901051b0d0e0c120a0b0f 59
    0x22840c035207400442210741c0c0f04128140c417203945100c2c2035890002d61845401c1d4070205000c1400803080004a1451a40c10204c5003848950b036040d13854446207000c980d41143d800015500c488845c40d403002c40900c001000d05880d070311003401510014900703d50b0f500203580412a14007001f0359507c5200c611700f0162070141002c120b80c0c0100040c40c3e000700100d40d0104404a15001c1d5142c54031800f0301c8022080c00e0617124600094086020280203222284c103a0a16401f0070115030000010790546205490201d00e902010380168043c2c400100488040c12420401200001545000d130080d00e00c500c02002e005551141015500e02000b0200315001407104042080c4c43e00070600c044071041d003420464104908a4100c041425001c0800d50f84040140100841088284211640800c0b8103a251040004404121441d030083e041c11040d0710b03940b0828040c2100c000c11440c1013440c07004041c840000b804a400544400c1c52480440385049035001043c0c120b100042d0b00ba02ca5240205400034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 503263660 1250 503262410 503262439
    0x12060507020d170a0e070f0f1707030f111903030207050f04020c1e0a05010e03041d070e040b030f01020318010b10020a060510050301020a02010e0d050a05030114040e060916060509 79
    0xc04425041443c5c0340700344100011030300d44900e60080105921103481c0021843e06003540d2004602601c03410040d00a440140002070210038440c481c3c07038000d001c400b01d0008410119146411141c0740c503004c24040400002010b5001030020140d800c20303184a9002105803080c40264012802d0740451500301840b41d65203907216800f400300d40d8498400311340040038182c40345421100c0d180c1089aaa0b0000507051104004100c0080c865000c0050092400d24014500600807031125845074819034a680c4d00c02142d075030800c85285d4080d41da1000319500d00308007030314910403016001448215407d00d40045020b192004880049101302d8024150b0301c44c407651b5032801400018544403a036004400042621340f02480a00340c0340c1d0290f00005290091100317100d283c490554a100c040150030000b4400e03155100003030b24111500400084014403181c0000340241800030030188440c0b1409007040b1550100242a04803041c0481c0e80e00d19146c1c8542084810740301e1141603a0b002b01040c910300b031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 503264910 1250 503263660 503263681
    0x9080f0304050312011203180b0307110f101406190902070206070c2c0c16080915040e090c0913022809060902190804080412060507020d17 61
    0x141d1042c81a0192454000ba00400d0486440c080e04074030322940c0880d5071502055004100c03004410b448540b204c0c0401d1600c4030a40d100e2100400c810104800c25280c40301016003040b10441d05501b19065400c21030b03c41814400404003188110100c030f645e2000314540b820070b500300717070310070b60800d21295603007820300300024003030350010908a810100400100e80802e02004200003c0d10041261242c3d10111300c0c217500c1c440980111342c0c951b0013081400c0c0510100a07070119003000c0502040d0001c0200c0c94144a882c2c0d014030700050f50014440400c15801c000410000c000362610701003c09079546070743c00d800d41c0e41d503180c80003242c00c0540107010511030412070300f002e581c10348000c08059030b07103c40d28072200c10001456010040001c818105014000203400b45c14081d24150908500384000ca003000045100242845002d0213203507004101406500c500700c501034440306c228405011081d25210f00103107c1280d4040c01030081084041803d03209410300800140c1800d45045584c0303036107800302c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 503266160 1250 503264910 503264917
    0xc0c1b0a06180b0a0e01030e010b030606241222120503090f120c0d0e10050c0f190c080312010b0f041a0304110303030717100909060e070909080f 64
    0x80040b14000b0002012101d40b4014580100c940d41c880b10b15518000002d0255101c1c1100c00d036141c2d0410b1000e01141d2400543c103a848401225070726146182550320b03c0d00340d12412050307402e1a0000a02d031700d02c0d1000c550620f01075249210006005800b2203d030030380c4c2045a5100902e100c0382840100d810341c0c8580043e54000907601c082c0c40d8500301c1419102d2424054281d803c0706081c4c041044003010710244102c1c0d841c2c2103d402d10302c1e5044000b60005606400301884a014424080b0b400301070701c5000c1001082e0480340030101c87d0800d0303182000f00c004505181040b203c81000500201f54590301105980b02404500d44003050359003015045591904601181e0010000500002809115030f490355052000c001410366900d0038142007541854001000e02c0780690320400c140302007030f1f5000d181c5070a1601840300d509055110b07606d4508603402e58ad4821001c150400c10f05105101c00755000f1004491240c00321500e4682e03454a000503240244800b4003002d0040c003680d0a50f9103882d004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 503267410 1250 503266160 503266187
    0x5090f161e08180307030e0d210c02090c0a020a02040b0622150f0804030e0a0312050a0e090606070605060303040f03150c080c03070309110303030c0c1b0a06 69
    0x1d0040341c201c1c072048800703030054605803000925400c091040f2200c503c040d401156503100041c62a0400c25203018110031001089607000d082114074600a01c078404441c80d891039550b808111840c3c00d0010001c22444102d60140d01c03440150300460900000070003115100d130311710b4015011504641e000c220080642c0310585410841c2049840c1c000c00c0c616084080041010320384040b15818550f44021403400101c1c58028032510084504020740c05c210700b00d40c0143d061801c510070300750810109002d4040c940c0300401b40c0c55135001a035a03080c0c00c02c01a012910060344c9480307440749801d040207007103003044d11441e8000c0010420791001c2003154020340e038003034405001c4a29180e640c05032000484815802a100d03025040c01c10700c1d003410103000c1c58a1290365460901600c0c280b13101d03840304510002c0d10302d01c2490340c1e8503440d03030800094055103445114000d003502e89038900401e2806441d408101040c1c1c040c041d410380e005100d60310303524001803100d0203000002c80509003007050322440b040510707 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 503268660 1250 503267410 503267417
    0x20a06110106090e0a0c080a020d1401020f030c09030d0305060a060c0501020c0a1b08010b060405092d060a050d0515071107241b02060a200105010302030705090f16 72
    0x2010801030014041c007042e900c1c1c400c00800464002c2c0c240711b410100b464001c0c210640104030040003503920809140740710381e000002403400e480d110103a00d009100f20644c0c215070a40100c200182200074002034040e010058080d00c490b103072400740490403901c003107c0c0c8a0b44402c0810082c03110a00c03611070302c82d66511940006140280c40200b481c80c0c08500e5104503804c0050000003141e0190000796040144000c074000d00403440050f0014181d0300a40c0510307402024498000f8040c01894204e0821003540c2601c00e4a0401510a00b180c1d020340445016000d000d07000800203e0b410a402d114020ba034000c17001d0040c82481040001c902c00c005010b007010042901440c50340c0f02c5050004000030308801d0246144081905500051170340031000c65814001da40c00c4030036001c1d00b000c04c0c3d440740583c11180c09554048941042d110511401500102d202488510840410741507010905880c000c40407603101da695001088061074080f11610000591207001c506039200a10340002642c1c020304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 503269910 1250 503268660 503268671
    0x3071e1a131703100e070807050a17040b090601080a030c06021803120a0207090605130e030f07080d050609070c031d220624050904020706020c0d0e01020703020a061101 74
    0x121200d1034070580d0300c202c2c000108008184440300025014840007844411000181132030201005040044001d00110620070006204007000b03200b0722008401d070b0070030000009141002d0030110f8150382d049601d0041c62281e00c00100c0c43c080000f64501d481545943d84c042c861565650300c034040d4000c280c120903070b0398001000d01a940d50500c60f41c006c1d02078512240d51078141c40300c0000d00c1c24020b03a01c6080440e261020501054440701e50060b03c2404480c00418203c10b6145150f18510818094a101840100b9514108205c00c802031850303200181043c00036898134000c000308600241d420002081d03d595002e00000c3c020700401c1c0c030b10802062800c00454050002c140c08150f00d030000085884401d800ca00391f03070414454907000e03103000899900e4107620052490f20201521000308103102c030101c0c040900c0d030740d150101c1e01e41c00c0c0e220030190748405002c0d2001d40c1e2008484054004107c8050b00301015505c0001c902c0c040701d400410481c200303840e08a050303403000c00c1e91048540c20f5482c0c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 503271160 1250 503269910 503269913
    0x1c1b02030712060501120201051b10020a030603020112020a270e07030e061612020904090f0f0201121a0907020a1b0513052703120103030203071e1a13 66
    0x92021000801d01842c01901034000ca2401c48100d9605070041c441c55a014040e00002d81d902c030017956006410020031480011240343c0c59441c01c103d4900c2e0300c0c4d140d4000248105115071542050003128404e89540589070321a500000690055400c0c6000140784500455455906038035800010b0906030301c0039071010746503485028200030448846001c00c2c0c5441c084c2003490010842140d005633070030200301540c0c11084c001001c914489040009458010404103403070b5a03140e224956056011224215141041c40c5c0008010a0250140c4c00700340c1d03400301d01c00c0030010f40c020301d41c14801040d8001c00c03023541c0f0002c104102d40040e00e040700b14442c0250b403100003004140080210314500070000c2020f4540010000115a80f803069500b480c1884240424401c1c80e0904000811011000d001e4120414125070f02d140a1040c20a010002d168000422b00d81c0201c020701a40e40609080c00c0d1b48180d03c600030803003698111008180126507011310380c20b21400c0030300b1900484440c01510450b0010b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 503272410 1250 503271160 503271163
    0x6090105070b24030a03020d031a2205011a041514070501090b06030c03071211090f0703050121060c11012306010e0d080a02070e09030306040e1c1b0203 67
    0x8440180c10649407082c00c483e1280c4801444101c508128001c2031084119a0020744135846441100107164483c6100380002c5074042e0643c001030360282010b859400341c2e69490003da0030040e03100c03200c6032400c030000c00d00180e101c0c802d50390400384600c818076051070500ea4844d0200010a00d400700080f5006010171001c03000002e010301c6001d5000410103c445040c00c1d11340e058040c0c1380a201c0c0d030006d181602c1c207880115200d001c8408152440032000005c1c1411002c0d004108045944510840e0401c204207216203481405103801c1d03541000142e803a04101c175201c20000700c01d50621211100080e00090158102000c00901d910300440d2000c0f0101d985802c0d01c1003060125407132000f150300c00b40d01d41500c2210f80d03840102460413400341e00301e02e03004c03c83c0317030700c2060004e0300b1074070009000c83c0024020031804000f4076041100417001e00d0b01c3c00400d0740340d42080e1210381c0306d1414112880b80c0a9030000300428145d2076556003482c00c01c60341c0d0301610701600c01c2c031151030804008081070001d60360 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 503273660 1250 503272410 503272433
    0xc011b05030405100309020406060906170910020a020607021605090c1b010e1b040207081204030e100305091006180f060b030903031b0a020d0f051b0c040c020105060904020609010507 80
    0x4c06440200d00d40c08944104419030f240c50300280c04000b242e120402600364040f61818102107003040b41a2941c035400c4c0c000d801c2080030302c800801d66000140394903041d07500040140c807400659098412051a40b0340e0460b600c0214400c0d01e5020210030041021816084014224a0100742c440318401007924102400e64000c1940e0103255005040030786005540c4a81001a4190845046162103074075a40c000d10780c0940303440507906c005501c000404041c01501ca02420201c002d06061681041d044020090300301200ca00e00700c2c0c0100360842d522085180030b15030a031612640d4601009080781e02c0d202c020128104040e103d1525010002103901c3d100009601038006003000d15034a2810303403688c00440c90040c104850445007000f40f45209540480c03072003002181c4e454011241311035003404039428080d10303400481041c4091041c06000400003401c000d0050240c4081c411150200c40680c00c0712001c540040d00003211000040042c03030000d0040010010504200e07050001d281c0313401401c41e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 503274910 1250 503273660 503273689
    0x100c021504030f0e01020604050714030a0c2619060b01051b032d030f060109090f06060e010f0c02090405011b0504030201031109061803010609020a030209120c011b05030405 76
    0x81e0f00600069002c0e83c0320341e040184200030700041409041c00e5a0f540e0f41c50340148118800c030340d4500585400c9a50600040b0307280e5070400e5a0360600c1d504d0b00344417000f90622500304803001c00404992450b600010038601035030322410f8480401020b20751560000713401f00001e45410020100000181160768271201001c0c04030400086448488000300490094092001c001c0d0003801502e60146465440007101e034400c2d03440c05c20b20b00d03039113420005892989040c0c000200340c2d42090840c410b4048154005022111a51741d00fa03c045a258010b5035030442c0b054224000820120040d000b40c10560310454005101da8000120702e600c04c0c41450000e03c450f00050000344e000141001592781c9401039560700c00b101c4010510388219580041d80500c1009445070b0702e00c00014182507160340079030184005103241da40c159a6124201c900070000e600c450400ea22548850b40b015016010001d0215803125060f1500c003445104482d25010b10b5090080454051101300300104031b64031518030746031401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 503276160 1250 503274910 503274917
    0x4020c0304050901051801180207060e0d1d030a320a14011e200f070b010905010806070503091606080405060906090d050c012c0609010905100c02150403 67
    0x264200003c0000d52041030740140e205000308010262460380c000b66403411620104203050340c80602c0c0c40e002c00079015042000d05101d00c1c050001a00c1c280c0401c1c0003101420a590310381c011072001c02d800c480601190352081c0c066100002600c00070b80113607413100c1040c91005100c15001900e1851440010b846502d100351a046011400100304498034480c185282080080c004401c0c14010440780004107803101000c207465104018280540d500f00048078a12001081c0c1e80d001082c644458030350111804444100b0308400006070300c01603124040c1030341c0c0000043c1400d522170010441d915003014081d010203000751514420702001051000c00140311681b0341c06e4292a040c01d046051a20003420850f0701e0700300104009000101003040c00f4641221f04045450b16200c804540c0100403520500320b090889a195a014882e003c422901d140b000030200d90203561142651400d80e8200f60340240f941d4440c2d001403040745000e420240510801d48100d035050103c0c503000c0e088038007003600c003900403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 503277410 1250 503276160 503276167
    0x120302091c06140a091511090a060302131e030609020111030d0f0c03050f06060a030f02030c18060c03040b0906071a0604150302181510020705090f040201080a091104020c03 76
    0x1d0324460305115813204e61000100645012612485c21207400202c100c04450790341c406918031940d85106039100c10784081e00a00120703481d40c402400075800131a102c0308400c121000000c5c0655101080c82d060003080348042c08807032540e0748070720141542d21001ca05202002441c1c00b840c1c80308001400010f80c0d9200080340510501c1c0304441240d42111020041508101c02c1108000c0d01d001d590f80c11150036908103588014012080f0001d2260108010303600c1d0002040c4a4480c0840700581894079842d08151940c0c0300c00340030004644105030310704070035400c280b004200c1580070001600c058400640310602c3e0056660b101381c1340c10803d089a8414407440c174280101410701e48501141035109610740c0d036101d0f05540014005482542c4007114841c2071600003083e000340103c071401c180c2409030002886c0307400010003035100c1c02c60340a92030290041a000403180305017070880368081d540607110aa900c0d01c0d101107000c080c0450001c203851a00f400d401d050600d84a6200805440000a011303645 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 503278660 1250 503277410 503277431
    0x7081507030b060f0a0f030209040e010504050c0306010f06110c0621010f0b07080c03280f0503010b1b0c220b03010b01141602061207081003120302091c06 68
    0x84901c2c089606008400a020646000b10000100c40c0d00401070b00300b2030350184d80444114060f200712640076800c00d081080c60018008150003580c084c5109105a43c40c240380d00f0b060568a080074400c1d40440352190004024441c01400082d82801d000d10684902074481d0010400d6036000d803a101c0140862f05a8a0502c4000b00e01090701500741c40c0d025003a981e00e01100e08034503000e14280540384582c00103207a054050108200c0741110300c4480c01d00340d0352200c28500e6101c84030002c0500041401216015903452207041183e058580c1c11000d2402e000d00c0001c5a40b03c03030501c8030b107a00c061280100c1000181c0d105050005d0745c1c8581090603080c41050403001080d1908040c045020303a0402c2d143d0328284c1e81100040c103030780003260700c0962a82c0385020440d2442c02100c0c2c029420260002d501405a0341010b40c0521032101038498030500e486e1060300c10340000281c480074140a64640f400047c07117201c2c3d0000c10102e08004c000b9a0042c00e99016614030b8100124110b5000d540e0712070155 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 503279910 1250 503278660 503278667
    0x10519020c0618010807020f1231030209070504080601060f121d0706020111070f0816050a020a1706060105030702161701050702061306020307110307050d020f0a03120e07081507 78
    0x50703115055101070400780b5080301e0129500d000c10022003480340b0001c40c09040499400700840c45080070803d10380c410900d0ac90403804210070b07a0101340d001d81800c4c00000c11442c014422681181c54410040000d42e10300300044541000c011280c2080002026180e40f1062680c05070740311516034075039000c0c00300402000e002d02d4079109a00500540e41840d90061843d03000310240c568058200741c0b4103501281c82d04c1c2210b1300e071242000490098401503540c10030306c05c0026010200318802d072011900c058448140144188500401501170f6010100195595219101850300542e050044440101c1286400c1d02c48a040d42c0012408500700c0c0010046d00c10701340a080e81000950020748001e0404001d14a012843e0000107031580340c0000200704514410762841410700501000d07640c483d4a140380c001c0d01d07a202840d85100520801c46090440d4002280002001e41c0c1500e8525050107035548170070107807503051600c42a50040d0100011140382c01d1280800d60300030850140f605103022113000c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 503281160 1250 503279910 503279927
    0x30206091507050105220b060402280c02090f090a060b040b031b1023090f040f050a0f0b060a180509040506090f0a031436130506010519020c061801 65
    0x101c075644406c40c2000c0401e804000f440e4101000b80c030056a54450100e81180300f41c0086108844990700c1400c8110103070b441240c484110f44201c800c0c1d00c585d143d03038180001d417031029581c1030f4081c5c001d018080000380995204581400003e8804078107076210b540040d041c00d0100a41c10f80031101c4041c100600c0c607090078403c139002890704060314850314003d044503014007207003d040c04e10400080e02c44a42e999105211600840c010000d001803040c418021024143c10703030394072030420f0900080d400c450800c2c1c00391602544024040c00d04000f00007108031071a5075030a0b0008004445100e0128940e02c0d4184214443c1e400307803005084504065505500d01030408087e4126a00720702107000001e0341c040110b211102c0f4240c069034545060000c4d00e507010020038000b01c10303c4c3c8200c0e00c000c500c20f140c1200005a9200319480812081071340048015103408903503a0780001c0040004090a0240708800b4014400d0b81c81212800040070f40882c0166102d90f500c19145160403031445410340c0c0c8199807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 503282410 1250 503281160 503281201
    0x9061413060b03030c0d050310180c0e04060810090804080d080412080906060d03030b030f010605011803110d0f050307200d050d0809160f090b0603040c030206091507050105 76
    0x394035000a00c400103880b5501c06c1161020040c000001c11032004500403100c3c050623403000c0c0e01402103c1241c04a00a1000d000a08085005002c403e05185003e00c207540480301000081c1402400b444c1840c4000d001c030000c1161001e0003400041814403007044a9002001caa84840b081401e003404c20100141402c0e90880030810b4032000c01c0410000812407a0300315009403070116041400303240c02d4020b061417a0301540c040c81040c80c0c448035070405400c15800c845081e02c0c0c120301040e0015800080c0d00080c00043e003801501c051901c500d0070080ca8520029001d841d14452546c0c46030b445d2402c640c0071640030385060f03d1825082078042108503a00c89c800d030007101c0905040300d80c2d27543c07652100c503203842a8090000050000d0001d140510140700400c01104103030f424607498000d842e82000c4c0c540a285401858400c100400b8149641280e009a4102481c0d0000a10f10750030815543d100308612038100c80500140f411b550603040140110038819000070800341742409504130003034030b035059 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 503283660 1250 503282410 503282413
    0x3030f060a050a0b0a0c030c021c03030606030606051603020703020a090603210827150f010504050601020a0605060d021c02030d05030c072a081501080d1209061413060b03 75
    0x80020b0341c40c040032151070300717058282590300c488942000d5401c4044c204002e90003216009410103500040204120780c60312a403803c01505849100c00c81c1103c400d030054030080342040001180f8541d030b059103a60510310920498011035241d501113a00c9ea04603500c018984d0b070300c4540c00e00400074841c203110040603460340094103201c1d0803d00101000d002900b01c1c100411554101c0c0d4015480c04200d104031568101100d008103400110300086610865000b21002002000070440340f0b45401200d011310300580c000c3c540c4c100d0503110b01008000c0500415442004030a05c0c03801626a1408203e1701c0d41410411103140f41c290040c542080400307e0074804007c410030401002c581288280d0b0702454101c00071141043c3c001241002d003100d50b0b800381d0810210f4100000c1e40388000200d11442e81b0b20540c609a06999501c0400c3c0c0d100a100303004004590380d0155505014450f50040d50128040d01020403184108541007100310010b60f000e0f10004401d100d101e0030300000b4042c05207900030950 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 503284910 1250 503283660 503283679
    0x703030e011103010e09070302060f0a031b08010b0c01021c1a01030902060f0d020f1206150a050703110a140c0316030f0b04031e0305040c050103150519030503030f060a05 75
    0x64800b103c2c84140144010f00e2204400708101381e038100a00c201441e8003400c05942c6d10300c80c00100d4a150403414841d170002c1c1c1444c02c3c0d401c0310034400c100328240d100075480740e01050742031017a04d1401d81c10910740520340351350034005d407010b0540680c02e08421007800326000450304007a18400c0c4880c0c903010b064506150902d4200c0c00141c84800444003035004c1c0c2c3c81c0c0750b5115185000b0020203440b5513001c50381e9417540130a0502038000701c404168010340381180c0500c1c5000c0d200c82e8000c1c40340030303130b4200e480440e07010f000c4140031902414a2421800d03041c42a105418540e50f5075003d881030f4444468495840710090800900f810026000452580d000403d4180d180d9a260103068070080c0c0028180001000860100344c020340f4420340143c100da50140324900c0441000b03008080c00c440a48042d80f40000005c3c8950081c450320340040521082000c03210f090109101000701c074a21680da07032059405002000c2402480614000d43c0710603807402580c200301040050403841a0403192080b181003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 503286160 1250 503284910 503284931
    0x40507030c0c1103010603200a080a05060a0c092c09011e0c0e060f0702010e1c140c21100b010504030f080405042a0206070212090d06110703030e01 65
    0x4140301c0e40b85602090120120070190b0101e0b01610045d8002050301c2c40c11540b84d81c0200510000c81e0390300c2ca06690207000c5d00e5460302035a513510200d408c007500c0d0741c00001c0482c2c0700b244150041c44c8011400e007000c03081079988001401c0d40101c04034110306810540a5400d49842406d0704943d00704c0d0110340280054256036189542890502c410b480034903644400a040c254000e03d903071a1b020500800c040e4541c500d04041c500745500c5624100e0004079007510b0f44002d0f1521031207440050038054856600300046540d00c1002243ca507403031404070321600104c5503043d6a440440340d61081d24074040d00078000e00302003a17072900d207001840003a194102100d60761140d0f0700405403801c89400550964800d8200d040045070351189811542d0000d0a10322140c158030103108000e0b0354403c1e180c404041c86100d543c8201d072a07200540c2c00d007005030030402c9803280c2040c1c020007910b62404024017034184076481d40d5803a000c41d04050030142003032101091031007d041d010300c580c000b0b6035044030003400100d121 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 503287410 1250 503286160 503286167
    0x6070809061e0a0b0907020f0c011d09040f050633030d120906021201050907030b1309050c03010609060e010f030b070c05032118010e071502100c0905040507030c 71
    0x2e03401612040d00d48440054400e03900354001300e0300040c000e0020f190034207103414029292001c3c0d0312442c1444c481d00d443d81c1440d503c654103010400300c0548000f03c5403000342c010081c070b0070310107042645e46138040815180801c4091201030302400c4058412031405c10050800300005d0281c43c52009110001c40e91203030551008a40120710100c0c510f0f00080720520002c82c0401050300460103000e1714400b0401d101c1c0da0b04a00c007041e0607240c0071190340300c0e250b446c110300700d0603a411090000e4204015858845010b601030708043d0040d0710500030b9070201100e8102203402c42e0300e56442007001d940c0300d0f0020041403003208801400340c201003140005c0e0750f04640350211001303c003405840820400d9038200c0c3c24400280103550102a03410014503d070310310003160034843da0041d2a903403001e0100350402d0b040341005224a254030141e11001c1c0c00702c0351802c0200e0340c500e0304102c3c0800c1940613100a8042c000d03800c0c411900c201c0c0e815110004000d0520045c8011218028810428180703070200840b00b03140c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 503288660 1250 503287410 503287441
    0x20703150207050f070603020d051f0501050d1122051206010e060a030807050717010b0904061d030703030f140124020f070b04050301140606270604080607080906 71
    0x110114003580e0b840d403924081c0e01e0000d2078003981076680581040030418581c150001c05000c9080c110a0055460303200c10140341294503491419103c0c42810104065401030001d4100c0c1c803aa0100003c2480d854120781606a001062400c081c403d00010a0140203131040088003030034007030310202160004000229a90001030250034240100c003800030b5040e0741c1e04070240019680c8004002c1d1940440e00e45141d550b081030007950700303000390f5480b410100d00051061040c0c40c1401400580c0a44854840700000d010046140da45140d8240742003000b458104000c00c42240b10b5a000620110001c01d00c40c100c0c0e40701c001102c331030042c800041008c1c4503e400150b50260f40e00550b01c1c500b6086c00f00980c6404411a074150043c05000800140340d600e03640a8070850f00298001e020f00001e000600100500440c0c00b180e0045d42404070414440c03002d00500a07410141826445402c01c1e1400650103410030b074001d08031a0b010a0410185560101e19960080c0701c80f4001d107480c2c104582c7d6890240b5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 503289910 1250 503288660 503288693
    0xc11070801200304080d0e15060f1e0a030c030f1a0c0406110c09010906050a05030303070212071505040f111207060509180403020304060206100b0403140c030709020d0b01020703 78
    0x2c01002240034060048200c8000d15012041007042e80d001840051300c5100c1840001d8003c1c00d400000f444c1800e0020b80840c0c0070703030014500700c81d03c0020744c0b14095045800d40015000b90010070b0100000da40007801c480a140115510184103c003403030800c020740c0d401d54401c1d0154850b10103102c0d0000da0003042e1410b98040b82400800304000140340c42c5400c80941c0d070503a001900030000542007816038414000e0b0b680980d804650740f502c1b003090580da48001c1d00c0540040e4009035040c4000303040500a0111284038074004407000c135903c40e103502076400c2542c050b11203840c8408840204150710f030f04c9a07080c05054500081c41e40d408080d06488503160b10070103043c0600002c0c0700c40c00c2d40e1554001c49002c100d1b85001e480301c1c00c080c02e0083d07498009024020152041c94041002000205404001ca5100c00f5009140c2415aa149030001d01d543e80000d005110745081c500e41d958060041c540070b0f0941000040c1c0310580d040448055070755510146066400400041c00407560000e003a81100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 503291160 1250 503289910 503289971
    0x7030903030e01030902090c0306040e060c071209080a0b0601030f0b01090b0a050d0513050c0109031709010302040801020c0d090f0e040206095b030509030d0c11070801 74
    0x48000c940103801078034600343d001351f2041d404001c1000a4080501960042d40f081d01d0800c051815100600d42e0b9100030303625074101d40c0c4248100d800041030400c00310780361030442c03508011031650303145900e02c0d10301a060704446040003901003052650307040c402c4000316000441c00b44004a0300b180042c00514450191800020b0f000801395030640c0603a044504601414404201c0303881e0224802003291202001100c0e10b01402079440a958860090982a247c011441580c0103410b0000c040c03441e448485050b050540a1000058540c028806004150032010140c0504204c901c00100507030819004a08104a042c00600c003442c03040300d446a00c00d5050f19960303031700c3c41c2210014001031050f00864a503083c2c41500005c518001000c41030780c0842d1104420380341c14100f92644038104600e909120a0800300200c4850350780300f80c20049e000350078041942d2401001000c400d0a8070715403a01400030a40c481c00c3c80503441d100b005540020091f10000f00211000c041b0340b585404800320300142d46 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 503292410 1250 503291160 503291177
    0x904080706050711070b120a0203010b0412021c03020a11030708150a090206040618090c0507230f0a05070e06031207050c04060f0815010317071b17120703090303 71
    0x1c40340200b6004e122528450220340c40d4660765111081d496102d50148440051600c011030401a1a40203480c142ca40c1c00b06150300f443d04004850034a0100e99400380e07800811052103e9940c00e0076103600c0803d5000c0d601420703091009086c047c040b00d0080e40994040e0b031048004100300358000c21a80c003002108010b500711504c030b580c40d103800b07884041e00c040d501140c0010002450390f00f0545000c8080c2e480340394034600c03e5446074410100e483c007400c0311010500421502c030000300020005030058030f030a001b00322800c828505c1640340041c48001d6070b18941c8030720b00c56024000100b12240041210403507080c035500d00003000c6038494100003010107041d20081800f0041101c107129111211300c000c1c00130414140c0d101902d400088261140508601501cac1f00d10001c00c0800b20400d05890f00505440b07000542885505004d41c0010420f45088640b80741c41d2656500241c180720003068400e040b9100000908e0300d282c148103180c2a80d0b80c0700407040003c01c000030f42100b0314804172a01070500b00003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 503293660 1250 503292410 503292421
    0xe0f0f01020c101e05090343080f010e300d15120302280204020304060b0910030309061202040816060305070e130902030316050309010e090408070605 66
    0x1800344150101980715030f810300b41001e02da901c0241030184c81e0101c0c00078038207022045420b071307004d109125504d41c16030414017034500000d181c00141403084400d0469071103015103445041c02c18881c100c50a003425880000d003040590000c00615401d40c4009000b0051191103200f01c03952060a0501c184070250b2100402e00e11080da86941d0070f051030724140581e6a00c41c2c000b0744a000308110007900c06900c10005c0d000c60700c0d50801c040c0060290b45600104801034416100000c21101c0d03001d01d440c0d50460214190058880b40041c5005903c03c400200d02d080c40035080180c0501d004182000d200100601040820f500500e543c0465540d03041c8400782c2000318001c4400703481160004181441421500c2540c1000c0100d040e048510603501001aa141c1c628200c641c50000040264054041c620280704100030b54050550644000c1c2100e2404000c3c1d20100c182500da5101583c2682010900ac0704958028100c0c1000e480119201d110380d00c0c1c240e072254164015030201420a40d643e41c0000c9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 503294910 1250 503293660 503293663
    0x70302100507140106150309080324130f0b030c090c030c13030b0a0e010606020c120f060717060916051b0601150e030606030a1e230105070e0f0f0102 66
    0x501458002e07460101c0140400e0246010341700d10710070180003080302034220000f1442442107440141d44098201e1440e204c00300c0580305402e04102925009595928002c6c980d941e00c5464515807400000104880f43d03403028803403c5807818030649000740c1000140c0300c0700d50780c0c0b030340d045a120161003445603c2e6240c0222195860007003180128103881c0b111000700a11600e441840e1041540780b2041c0048084181d40034280c820500c518005a8080110130210b864a40500e0a50b17140200803200d80240b08480c15280c446c043d10b8001c0802e1940945042c40c002205c422a4011415202030f003103410042c6260441207030700c0085008010f40860300c2480f40e180c02e8a401100b001c2c8100f2591107586840c0f0b480c0a2041e44029200418003429800d549801c0104d2000d00c2041c00034080d104038141c5403244101112101803a00d61900c0e40341e82d00f030000382c290b110100555084034015900800240041b421540c0c081c01c2031040c440440f20780d840590b501d50421447c03240c10b03036401c210400e0600c0181d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 503296160 1250 503294910 503294917
    0x10c060b0301061202090907051c08070804060519020102132102030a060506041512030c2609010807020109020f1003020f0705010b03070f12200402070b0a0f020c0703021005 76
    0x140d41542003d10008403044114203d07030340705000b224800c0300344c4c03140320b20541d03038914611400e5003003040212410a94039082e01c0590030345000310344051500e58203a07503100c403030391080e0404400b00d100814107004410302464610407941c054002185004220211400c8884083c800e410380810341d900280040c0c00816400303080a540a82180d6007404149045d00203490112081c5010f24030381104003510f18414810441180e0283c011151001c030203071812034202080d620150f515104080d41128400c00c001035800c441150445541d0320f80c4d4010000604004014111004681c1003500420169440b980000c007004400c0702c1060600c2030b652010b40203801000c0803d1000034010401006010040d0000c00030321804506561713425032a040c1c520034a603d107019403a110800080b501e40000c0c4c40320703101c8407840740c40c100700c640c034051080000301664001b41e804c42d04034071050180118540705001d40982c104811109609081400743c1e8203580d00382e544800791280100007001c04042d40140d00701e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 503297410 1250 503296160 503296181
    0x30112030903140d0305060409030e040b0103140f010e0a0e1b01120f060504050a0c080a0e0c2d030c03190c030b0f100e22031e0207061d030c010c06 65
    0x1102c03e808054029a2940e00d050380c8000442d040078009420342c80c144c030171014060ba0545441c1d0070721203284244001400039036500c6060541d14420415400c92060042d0b02c6104003e48a140b290f04001d8242500c0c040074040881c51400c0c28000c04006001180c6000030b46c1c268820301513030100c078100494440070030b40c01c080c080034500411000760340030903006901030714016a000e01550322042c554104980c0c0700840007000450400c04218808840e030049800e042c49001107a02c2480c6410020701040e2040e03254609000042400590b004c8803e40420b1684004401030980800303990b02080d03c91410905620300c2c1200148000100440c0440c10005148c0010582001d03284c01d404030072020006840c0b0b181c0712074102c0c20007c1c41c15000d180583c0329850207030314815401c0141200541c0117040c2030040b002e100400544215201c0901002c4070148102c0e0f0040c900d60740340080142020310387c48042e038181024040007845507100001c00210005007807130800c0751080c403070800307000402c2c10454 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 503298660 1250 503297410 503297423
    0xc0b040810060b04050d031d0a0611011a0906062802010209090c030c09090a0f150f080f1e07081b011403130201030b01030e06040c061b0503030112030903 68
    0x10046801a000651801207407040c031000c0025640b2490001000e008602c91142d100c0e002540140010788140da41140005d081101502c44608910004440e020260010b41c00910403414181c0f0308802400384407044211316496200c20b101a1021801240d0010452400b03000000781c8040e05411500041155014281d0001e0b010190584005e010f0350229a400b885695028007194480440000b141e02900c15460b01e5440c0078000018003040c0c87c0000c04c140c64840d40e44071806014040c9000311141c0030144a41c01e0700c03c0c0d003000c2600f0100d051541000c0910351000d6a65102c07038038000740c2612852032580c480e42c0620644130322140360400c2070f040069140034001c207400c44440e002082810f80700e42604c4900c031040c0d030507000b228103000407540b4000d0045152454405940283d02503902084185804035510810300d642038030307001d0103a070b044403183c08030f807020010540c1c031040d01c500340001581d0346462610aa216039590b80018010701204090300e035a100c0415025009000041d0b60140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 503299910 1250 503298660 503298667
    0x305090c150a0f1106041502120415050a0605060306040506040908040602100605040507050a080705041710110a090e06060706060e09060105040204050a060305130605250206040201090605070c0b 85
    0x201c0082580d00701140b01c60100300c0030315102c8191400780291016541194000707055603551900c13100030840c400c1c2c0c541c1c52415820006c42c11031100002c00b0b40d00c69400780c466603101c8201c143c107000807104020600a649440c10f04140460f9480c0011030b50041e00c00c84000c1026140d880006009020114009011500020300081c8641c0c010411544010a4a00420030070366550144401e03510112407050001b071040026240071401254500d40001c1c2030f1070060704107619000904c801030707204040d0100c19403112042141c0e0b04424010754804002d03104a1a04090418034054603411450081c14a265010707000241240c90742015140c030035420140c1030045507901c54801480b034000742c81e05482c0740541000401c007800e2500880f0200d5a000d44040b0b044c07031801d0740440013800080d0131b40400e030000d0410040410401d0080c02c0c02684a100891002001e2040c48440301c2d01c003901805c20340d0804800c0101507a00500e8500c201d41160401654030b40461400c400240070300e40184e00d5401011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 503301160 1250 503299910 503299939
    0x203090d11010c0c15060504020f34120201091a010e10030206030106140c0d020d0801270e0f0601090e0c030111040504110c070320120c010305090c 65
    0x1503203a500c0e001648440c0340010020441d5420b0382c07030529400340481d8400c05203a00040e4400c41ca01c03407800100308006540c0381c03200d0020701640d20418030f0702c0d400c00e00400c00864400d5040c484028402810408602e424029142424000d0041e00094008030340b19980f0b0300341c103000390004c581d1aa403011052542d0f0441b40040d50210000b800781042103118400028620410b2104000940b50028203281c2160b103818411a00c0314100309510424140a06c207150099a040005c070300e0042d0190090301040c48024030081c41241c0c164800c0f002004031042d0303201d0554a403400d00308805019540825000f00c2030311880d140801504111203144652000000c0e008450b1b44501c4a08019400f030311101480c2c581014280d5400c02c040c1d42c3c1e1103a04201c01c1110349820390212a004040104c040d0500c80c500e81c1003804c00c0040d50054449240d100c0e6441d403c0110854030454048084030a82d90013103900002c03a0b52000ea030645903040c5035a03000460882182000001041c1e80010700980307188054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 503302410 1250 503301160 503301163
    0x3040804031a190f0603080d0203040b100b07080a03090803090d1112180a0b0a020c030607030e0c0f06090d080d0b060301030b13030c0602030112022407080d0f020309 73
    0xa84401d403108020344a081e0310340c0992000c9207025610f58203002c882d043c000e0802200901c0351198052059964800020009180c400500f058081403d001601d1303203043d0070014883c003402002c0c003814000740e442c04d01c079013a00301e03055801c45500080c0301911014800001e80040807a40d00183c2508008010030110b0362001444072140c120b941d5400c8802c0a6440300c10f0b075240041c4032042c00e082414000d621070707a030315500c40350300400c00203050900884d07440101c0203d5900401c5c0070320040e0880c05543d40346090422609801c40014541000703002d11001280c2e4441c0d48032034500348201c012101e0044140d692100b540c1140034010980324461100e0b242041c0305512242030744204030b0800000e50700c9840e0500650303048a0b0409a000d01a0381c545010500c8441c0d003400490a00c1855445400840c11601c05107018004100c9440741c1d210450041100114141054600d84040100003140d110096019144190340c041e04450b1112409000b28007e0407145040e074100f80c0c40441000101c110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 503303660 1250 503302410 503302417
    0xe09150115020d080c0d1a0907021b0a150f230901032a0c050102071a22080a0e0f030a05072d050913140d091d010302060f0f030408 58
    0x40540846075411810103060ba03d501c0221170742c3c510f1803001d0202c0d0000c3d100e01e4124248030a0712400b008046d4220000182800780b0580d880001a40f149080400c0603c1102000e221601c088604200b103900c4c1c2008600a000d01d411280c040145040c603000015010305440401d03189110a0b402028524a22030b500c503400ca103a2041c002400e180c4c800410f07114a00b03442d441d10040441101c444040c034075003502c00504100301202e4030745d800c010303000106031000d006503d0429070012908090404041d03264034009600c0344202191600060702001850101c12144042c0f51400c040011082c42c100040c41003400c803506039014040c030181c0004000c80451305100b43d03020460301e481184038550701c100d40540c0c2c143c05070302c1107803e14078203114502e050107002d070340a0064500803500080c2990f03100810f001c80340329100140e11445c04500c145070400e070318001600d0041d800c003822051410b0701182c40b03001844007078011800064071104c0503111008440800072102c004640d6410545408010b6030b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 503304910 1250 503303660 503303699
    0x3091101050a201f02070f080f0d0f0212010501180512030705150a0c0903080904092a0510021605060f0c07170d0801081b04020903100b0f01020109020a0e091501 71
    0x40405200740340c4d101184280d0704240c0e080540c0c030703c18041c2da56640885074440b01c81e2040e08030f406d200c0701003c2c5256004e483c141c03140c88a000740e19810039401a1509090681015060004c0e0050402c918101032440c4d0003241d800300c441100029000d50414210320654502034554041e450b00030128004000e03483c0d001c3c03610b000080107005c00445080b180140c49000c010000001082100010301e0203412201204d40104644080c41c06c5404035480ca1000d01d00800300482d8018204210703510b001015204032074a14009401c101d500c481000500310300328010203104030800f00d84000c0e4481d61600392030040348980c0071030b1211038a030050591f41d8140e42d82c0d81c40e203500c55200404152403203070703068074104d0b840c00d4010500c4140e030348044c2d01400f403155441500a0760a00034600680c0d4100070b024030020f94890002125604c0001388a4401035156400341568100f011480042e142e41e15420200c6a0fa00d03400c00c01c68035617000c02401d045240c01c1a5080a4042c0c00104034184062640306600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 503306160 1250 503304910 503304943
    0x40e03040f060f020a0b09070b04062f2107060c0809060a02070308070809101b0908060408030f1305010603080c0f0105150420030f041203091101050a20 67
    0x450b981e181c00c4809041c1c804451006030000a070500000c1c09214005810800032402c0e500500d454060025050f045503101c80c0004080035241c12b000030541034148003403d02c0b1240e511184454686035690ba01030880541900e402d1251001140d40c1c025065880203a800714050018500701c0074018900c140a0f900042742d4000d160114044e42e049100700e9081c0340d410b440307542a42e581d102c0140d0300c0a00040180d0001d004071015508071010520400c00d00b03a820600c00318203280402d500074642440c46d00304003607130b0303001000348000f2603040002d4a81c804814070013914990b460054284c440203811000030300a40c00d2260101c01c100001c0040c1001541c0202102e507039420500140e82a2001580c03044d022000c002e22a01c03040c14181c1045030001d00c0d4507011000a144c1d50200384e041c0d4002c6a140080c0d8541d1014407040042d0512400203200c25440c013801105180c0e101c4810b00134020303d00905010000400940440c005c003100f00b400302d4600d044903a12101e0940941d200c078100141130490 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 503307410 1250 503306160 503306189
    0x9080d0c09080d170403170a02030a0b0a0812070c1a030a0e1b010806060c0615180103150f2c070602070b090405071e02070839040b040e0304 62
    0x5200002243c000704407540d5126140c0c4a203c1600d0a00600054015001c20803460064000c0e6800c450405006050070b40e00140e880c60400c688404507409001c5082c030440385d00008008403400015401c1e5403c401841465484002d840c05411030030303296104080d03490031010325503440c0c00300c100074510035440350105014007422541082e4680510080c4400146240005014254410041c0300d41c80791028040901d0f04202c002d0603454040129481c801c0000c4030480e40b1001d0900010b182d0400d65070211901e240d50441ea9114002d01c0c0c0440c42806644d070301d92420450000542040c1c02500d2440703020161035811540d0b40744c00080c5030645407481d1040200008440d0b2000844404940d000703c030450a25045500f00400303450003406400400000203a00c1c414909540f0792800380e0395590f0020f000c504d240c05140340c01d0124504410b81100120915154402e06410410740e20304034101a40019505400000d03004141c06010303070381c10501e8140300c01c0b8402030010040c01540c000700c0d41c42c0e41c0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 503308660 1250 503307410 503307419
    0x10050405120f0a0c030516140706020a0b07030e010f0203010306230c09010e03030d06080d12023a05070306030c090204030206120403090e0a0218042a0309080d0c09 72
    0xd105918107001d42c2e4008001c07210140e8410a00c115290740f0074a0a149017000c446801c4a24510300001070710408284889035901003001c000250050003e40007509600400d80c60351014100d0007440b4006045d2182500101c1035000c1d032202003c03000d004011500d9513103034180f000c02440e04085400388800c04072180140da0189070b4040d440303583e194043e1480d04c84d098004481141c0350460140c1c05100900500240d101c4a00a400290404000501c41082202070040502d4102c215140c4041c1c4104814410004210300c003070030310040300e1498003440385200d696000e241c03400e04148007207034604000d002003558960003a8080300d000e0300f200000d0989840340e540883c8158400207601003802c0058016250414424650003402270030051078050b82c80700155119401210a610116400110800c914010300000c6000c03100903982080b441d9400c920300c10b84a0b1900700c0d4660400e40e2440c150088038820b801c0440d641e03501000e056103c0040490800103010014010380c0803030104807001c1ba = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 503309910 1250 503308660 503308693
    0x70e070210060509011a0d0e032a06070509190e07110f0d0318060501031b140108010b130515120903073305090a02190b030a0c03060810050405 63
    0x95a0f0000d02d001600e074641118940e00490f421754100b1105014464547c00000c24495802d1440d811806940d6521299020003000d00c411b10f0f05100e48018903a103054402c000107030203a401446401c04039a907031a2000002d000000c1404c6109030a01ca200300070402251400900e8091400350710b07044821121120250b4544200100e032100a500a185210105200e0303000080d0700300409001c2c0b40540c00c09c3e01d030310080c1c41090b00169945400340161a40c80c0c232402c42c2c500001d03c070604c0c6041460350394000080502d20188159080d42d44d0109200e084000c0140005000f404000c0c4160150039039948608140e4100d080d4080000e040302c0000f405503480842240c8101d035100c0740c10400b183c1d201042c202d00d6071200c01024000c0804c2e4001d46240f0400d849054002c00b05040101000e60f070510403c0003240084c00a01d05005140d00c042240087e006c007601d801101d001c401041a07461000110010940f590084c50f9610401d1301d00a21501c0945c0700740d00403800381007a05c1c0c510b050f021010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 503311160 1250 503309910 503309921
    0x2010309210e030c2407020d05030301030605040b0a02030c0a12020405031501090509061003080703020118080c01151d0402120a0308070914010c060f091403120f040507060c0302030c070e070210 85
    0x14a090342070144103411760801040108041e51009000d5040c0d40c4081c3c0b20280345420980044980d5070b940c000740300512800d0850719034050200c010a525500d061031500d901400303546244020b12010b182424540112501a41d01611014003103486c4d04034400c40c46009000284034000d01315103001d0105083c6c16021074401d10481c0c0c01c46108482a207140c1d550704050340480025800c6541c0c40c08440400c030000070101c50013900804105440d044100c040d20300b141d1400144030b40d9099086000c0269203a00e144000100f03080d105410410303569400460f0007500102c8c11542c660050303404038000c140d0010701d400c0c0240010798810544980b104a41c1d4503107081c45914501150242044c00002842900140b100b000c95240204030202c00e5510b40c103241c80603000d814030030b0b0400714000c01c0c2501e800d0803595109600601100490809450340c0c0d8541e51f1500030003081298032000c04003031500030030860b45840884411290043e58808005180c06800e07101c001c01400780215842143d9a0741c000c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 503312410 1250 503311160 503311189
    0x90a03080f0708061c0501110c1c0206060402070f0c0b130e04050616050d0e030a0f020309091b0c0607080a0b060c1e010e0f010527060402010309210e030c 68
    0x300080c41d1141ca003049017021183c00d586007000e1041c92482c001810a026200401e0301603111140c5400800c02850305000c40c0700c40c3d400860075411540c1d4043c81d400107001303130400001e441c0180d07203d00900380b030500c0340d6040d00c0c00f801c100b2031a00300140d441511002003492100b108200148035441b840d4a14100e035007610054031b40e50040020450300324010800004041d4581013852401854560550507548a14403182140d080480c10002040c1c11011110600043c0d10103113280601000c001140300e1406480c0843d034031100000201039030041801c44d150b55503e401110060b140c108401071541c0c8084400072003503410f00b2144056030500d030080e2880c08401030080d00e083c1201c1e101d1202504100e080b010455900c55100c10301e041820300080300c1c5022440c0c00401c8905e00401d2541107510344800203801c4806540c01c062450101151054002e80d0910740411584031600b03119695040301108850421081c1c04801a41034000340c14455000058054030190f10402c001c000242181e1040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 503313660 1250 503312410 503312417
    0x10902090a08011a19180c0516030801080111310308031014220f11040f030b090a1a0705040e090a150506030309090903070b0f0708010f0303050f07021305090a03080f07 74
    0x314240386d2450f50041e00f200c039024600241048504110394190301018201138011407a000014031816002303005000016030300185980c0740011220403aa10001c0013101448004080d810320621401500700742d5001b0341c0c10070134a40e200c2c100502e901c009140036100780044ea041840c0241003030b08000c034901405840803030400422248140c401809030022580425807556103402501c00e107494500039101420110080002c007904510344019401c401801311320b07032640300141c404c000400b10f002e0300c604070b11106160a1180c941c81c6041d83e860007181c2041c82d1104a4004001d05504006440114a0b001703541003607405110480a2084802c140d4000703400d60010400c0100c00e041c610070640c0c2000c1560116840c000c42d6440c0c901030340000f65001500c0386014010b006a072948800801d014050340078015103520f01d15a03000e0020321511078180c4a0007070124182c0295912105141c60124800c5d10510041c5460b2b41155292415180211701103500749001c1103101d0b01e000c8110740304001d15103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 503314910 1250 503313660 503313689
    0x3060f05010503060a0b030112020310050919060204050603010612200405190b0d06030210052106011b0303020901020d11070501050f250215030f010902090a08011a19 73
    0xc0044030503500080c441500a40869000503000420070021402020784c0780d01d4041c5e1035160b104040c00c3c842e07030030f100d5100c46062900340b01d0700341c5001c07a00d26044140c59820032056201c40c9008400f82c0101c0d4003183d8009004000003951a412100040c203121103500c0c00c0090140c00300c03a1500c446452a115000c81c002404148420304100b81c209031991140078045a90a545541c18003c0740d02002072405800d0f180d01d4108210305005a409038480001c0c01c04034144001441820380d20100100d00070800c181c1c0b03e0101d0740e142d01403082d02e044035070135010048180040342070181c0a94030135195907005229013201626410b10440900740c0610b8804060802145003100450365a0802600b10751000d01c02c105211480341001d00440c0355102e0b00111a604d82c01c00d00402c0007020340042c1e1514640c40400070840d240001440c00703030565408150040e182c40405000c0755140328030703800c100050340ca000d00382c0d100c220f00d41580003c40321080703c80b030714050618188448a084140f241c2405951b642 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 503316160 1250 503314910 503314919
    0x105090706050904110d09050f060108060a094e120903031d0d09051c02010c1b0e060f0f0102030304031d091e06040204060219080d0c08090d03060f 65
    0x40c0003c05071001c0040000c40c070520700300c3c01410141e00091040b01c09039500c00c0d0107000c00c20140710b545401c00242c40030300019072400180e01d44031040181880100caa56820302c40411999142c1c0d514031040c0b441a100d607a403403c07000c048080003280302c440300c0349041c2e00036007005511024000001540c1644c03156040f40c001014200a40951142181419190900c0c0c50350030314403082075241f01030110010260701100d000c000e0a210480d80006004450b4141074444901da4948502007165082c0f1b0700c0144009941030501c407a0380035010040c0709a80007100003c9000d074101400b8002d5608032221259840440204004d8400070550b01e40507800c04d20020303000c01d000380809180034024007803621540c4811400195810421681310841e1141c07260402002c44146006a504c003009031011480c260030042d02a589505c807a20700c05a060000311484c003044101030a492070440404424868044184c01c050050394080310024080e1040d41189080359201e4003031001100c0e581d02000d140305050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 503317410 1250 503316160 503316167
    0x30504060e070b1e09030102070c060908120304121211041a16150204050a0e0712060b03190207050708071806030308130201171515030c030105091801050c040510020105090706 77
    0x5000c0e28040340c203811702440d201600d080c001030051074841c001a81c1d00307130b00300840a084d4902940010100394407040800c0001d90760302c1d003225003054229000e03545041c11a4802c9a03000f00d08200300400701d050000c2c040c0c5564000d07004d00300341c6440d052400c04585103280241002e00030030100c01c00305211b031480f07640807400514104d03904030300030391000d45015110740100e88035841c668030550311141240108a4001e45c8911070b85103103441c020080c84024034000e015405400060102204101e24023007040b503014071a1304503019154408103480185940b4880251030356000e01c1204428000c0c0c5a41c180c0400032440b5003c2525815211804103807039410340040d2000c0c2c0794000320b06011507007110302c1800c2c0c40150f4007803140c450110440c405600e210140301c0c004a50107481107a01600303100780441c102c1f004c420350b415200103490440003956402c0101c00080c40e51a802e074141e500c0d0000740044500b0b078900034804c0d6601074038010707007619a48200301d080350030403038030901241c0000c0307000c0c041c880c130 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 503318660 1250 503317410 503317447
    0x70c170c09060f0d03091208041d15060a0c062f120106030b0f06030f0601020d0314040b0c12040b1b071a0601020102040b0c010b120a0203101e020a030504060e070b 72
    0x30721b840e004484e210400f0300d9145180e8070080d212510b010508011070188a1150702d01c9048100600205003800e91104090444421f401da108881c0424954500391184460310181034100350284005070002007941c1041c18101c0303d440750001500e604102285040086807041c440c8881416000d0b840d0500c110010460243d045900c841e6042c2d0380c1d0526541c8802440c0208908030000c880d6041c02400a49403401480c554030915040c400210001d0040e006001d078080d4021142001030750b00d2441d0041544100f11503041d02d884010184420710040c1031001c1d1141d00b9120758161030400d00d14a8a4044c0036520340245000341501c0e5103a0240000004190890ba042c00094102a100d110f03501c02c81d0014951040b80b40c1d03540c55024218985a11500f441c20705102c042c00340f4000d40d40101e9214543c885207114115100d40d000481845c161741d103071100320295171045490b185241401000380506079001e440060504a4107168198045480c134100c41c21a02e2143c03034090114510242d101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 503319910 1250 503318660 503318663
    0x120109060e0f0c0708030c0909090d090b0d0e070b0315010e0d02040b0f060c0d12050103110d05030403080304030e1801060203031f030f0b0f0c0406050703030e03070c170c09060f0d 79
    0x2607080c086800000c04a0001e180642c40f01c489080d207882050040c2700c4004c1005001c0034040e803150545803402c5400c0103074041550029060a0b945a2001444030064507403110380043c10320500c500084c5c204c8601002c0c40c00303940142d641031500384203e00119410b50b041100154840440c880f0034005180c945e1001481181c054030616641e40140c00250454112042400d00c1d80c001d80081002d00f507000a1005010803194810401c95065854400e40c03980145030481c001d014070341031542880010000c1c1c40003140d012110720303901c1c40d09142c001c055200700025240a8081c00700c4864554402c800030724165681e60380154291b590303031071028980301a40d00200c003a440341c5100210218200703141c01c2c41c120f4004c02da443c0385030800c040354180c3c03d04010121002c0c858144000d020083d030140464803099098500881d811141203400340c150301c11804002c0c403d20300c1c10310005481654051a4440ca41c0d00300503518450b0041e4180030b06500e0880713269034000c40c84014801c0710b01d0100180d45031305 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 503321160 1250 503319910 503319931
    0x150702120c1e01020d1413030806150c15011205120a170108030915120f0a2702010906020309010e090a06030b04050c0a0f27150b120109060e0f 63
    0x402c40d040e90b0409507024101c0224050350000303040d6800c0c05850040800c5a01904080183c82c03400f14003a04078000340d104010100b020440c00314107907035a020907886c6c8104000907620394900d110351505941d007015500300350341540900300006020f04102204410103401801402c82c200c815926101e00380c1c41240d450090000d4404c0302d04040280c402000c2c003070f1000340000c56541c0000810006560000207181c0c014080c10040c141251540350115504000390030003010030340e01c400c1ba45201801c528991030101101400c0506890001d8810310142d050003a200e1652050302c2c0d01080ba101c2c4909907205d07000c51a880c0b01c44041c0e0030184841640306582401c00a440c81d101c0d526038400c035a0594042d5556031250110f1204c904d0304841c18402041d1030144414001d19100300500717500e1480d032540380b8820750210303039000341c10040c1c204400d48541104d030340d04099100e010039a02c030341100b8480300c03520140c41c00100d42800c06e44540c02c1507880400c083c0000750740d203203003c4204120007000448031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 503322410 1250 503321160 503321173
    0x13060f060911030a0b060309030a030b030c060a0810090509070501080a1d031308011806020304420203060d0f03050702060d0207060510180e150117150702120c 70
    0x4611640b1a0b031540741003400b0281d40d039007490a14041a62079522520384184810400c1c48604100002240c0400b42d2609000c1810a44000028281104034240c160030010001d07007011110350290201d88120741d02d00822030740c0c544a41e49a01192011100f86c1203d40c424142800350f503000b4943c20754041160b6901040c501045e070701620aa003080d04103c1d00551011800c0801c11602054903c043d241d464000c00038401c40b44c503581516011041d000d40107981c00030100f820b000340b0100104082004000c0c0b0000140e031f8000909100098488980d076103860460380e440c0820490080304d024aa0050903112604070b00d4403561504030803490102c090000c1008144016121a0064454101003900c0181c075001d55040030401e90b02c0042000c81c3d00b080c030038024810701620900032400c5c10800e420008403821600d411518003011815160744950400c000019841c0031110505880c248800940c3c42800105c0203092000300705840200140c0c008925061820311940d0191980b450f16000701e810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 503323660 1250 503322410 503322419
    0xb010f050907023403120206160c020a050d1103060708190912110a1505040309060512011a0412060b0a08061501030510151e0e090f180312070306060813060f06 70
    0x20346e10880102e00168025404100300000d00c0303021100f00d10200c0c00d001c022480d107580082c8001542d409101e210b400303650340c0703141403000110b03850300060009021588107051000e8050400c00003120384100c0a141850102c9190f0640d000b200360956000460176043e4149520070b44900701c04c609600b030144615903003103010848800d05030125200340000000c85042a0800801080c0260003050038088100242080380349282d91242c11140e49c880410540703a02d42c00400700d17601c2113030f01110a408030041d031013080c0031060380203540300c55045460454a81e83e40071050b44803c0c0845000100031510440803140e54000e400c00c3c1e500c961880900d00c0c0300341d1078404440e141d01c80d4210703403000a05019401e071511032480d044001c1541140c00c003c01c0007110803002442958000740100d00711651600840c006070b00b62a0591a052800000e49448046801110b202140b0803910940040d00740a8001a00d6009101e52802803040146225560059490300009004840b00c0007040320382c1d4038000107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 503324910 1250 503323660 503323673
    0x6080a030e04060927141005040308010f030b061002031c06140f090705090a0306060e040201030e160b07080c01140915010509070521010602010204060801051507021c0b010f050907023403 82
    0x40e0407c070000014050500f0308000b0074005058208035500601d1b0a000e0004c200303120080e661103541100c2d29051958208812405c50140c41c00e12010f14041b000361650f084034a03001030042d107075000e884201e0030000340c00304183c80c030f1161605600b02d030f20309000ca0003151264004280d41500600340000213a80e07680c1d40e000f00c880d103500440031000c060061108560f13242c010301d205480ea0034010081015040107140340000184903542ca49000051b2210812458800f0f07140c40f0407044000308001c1403400d50303504142c0021500407a040c010840c10f10103010038006101c0c142c640140804419030364400c0c0c2664943d1001002400700f264211100006034002c0d0013441c00381081e0750015807035902d0040702600880301a000303d0311031203400301c00d0400740c1c0e0740c0420f0f83d070000e0b011560400d20455414050140c1c0c000000091700000b0a44004035410500102d291300b22801598400c24650341c29004a0310360046100c10203d41a841e64080c1000841d5501880406103180e00780076001d44c2c1e644e452 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 503326160 1250 503324910 503324923
    0x50703200a082203050705010e01090f15020712050304030f0602160305190207050d02060703090b1602010e19032d050a0605181c0306080a030e0406092714 68
    0x7141c0601d00003070443c865210100d1000c0035680418806402e45007166229602c800e418010541048550302442c04147e2007070104c0001410400f04c0003003003130703119404805902e409212000240c81180c0c4001584030000e400c0340030440d0010050340c102420340d038502d4201100c4c000e064903883c4c0c0030f1084001640303c210810052074440e8956696940c41008007144103200c600300401075400c0041d04202076241c109018000541c105c41340e035528a50380c50160340707040040e0081c4103503110119040b800d41c44003280d0310074070710700036210b030b03100c1486850400070380e5003a15903211001d0942c03182c1040003c50f507841d01c040540b40461000381e401e140348034072004040440b9048d00d4542c0050500070074000b10388541600b1030000c808649200111224690340c1d940e510009074100c00c81c018030380302002e00c41c0c0e02400180900005a0700c202c482400e00030041406500400d200724074203440020408098070a00c41420a4070b00e100c0340d1129440710984064185900503500c0c014071001d44580c04006000c40c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 503327410 1250 503326160 503326163
    0x803120c04090222090902030a060c0512041103150705180a120c05041116080c0114130b09030408190f0f140c01020a020108011e082d030901050703200a 67
    0x40d402c143d00c40c4010304608440c1d8001d05170795180081090260314080b403020344254100c04045046840113000301d0300e51250380202c668064880052008009519400010113401101142c80c002c0c40d0700c07030000140c1403d941681c0400c10803c0021014508120f042025520041c448410707107503560340c0c01030b1214a18504a400c804410024440d51038030388114840c50b10640c540e5418030f016240000100070f02904094203a82c2d002c10300550744042500032400040111305911201d0401c0280070b000e00c40c0316281160884d40c1c40d400102c80b00400416036041b06c40e40402010031221139561504001c02c000c0c815a40707414854017007004110551f894480a602c265190b0980c5194040030904000201e80444d0454101c14003080150303a00848550560301c0c00049280c0307078424022010741e0b400e003681c13203c2d10f40c1c05840807907074050f103500042c40d01c514044008880704400600d40d00780c4900c140881c2e14085182400382c032001c030744602405102e11030416400b0000f0032001100301d1410f4042d420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 503328660 1250 503327410 503327437
    0x30605130303110408030a0c05010f0c0518091b180301020301060e13050403050306060f07050d1d0a03050304030b06061605010501090b0d0c0501050d1103040605010609050a0803120c040902 83
    0xc2604241d41445502400f4480c015610300785030030100340688030b1103129800350407c221100e001051100070740c40340114103082e20f010000c4062206004e06141c0020580000c40094180703d550306040902c0a544104a105c00150000c2c5200c0b40e1902180c0240c10f480305180e9940301c102c05141c03401d20045002e0900c94031503005a0350030340b080056001c0c0c01c0080d254014200014800040e0f0414140c070b42142c41105c1a170b80b110102240e500443c01244000b038000d10510010b03051943d040180d207411112500c00125a5607400814080c002c0c683d8070008046a0007003004001180840c0c0281d43c101000070481864400039828440e0780d4030002074242d07640c0e50769000412a000d0320784180c6480d0a01503d01024025003070701cae1810402001e2044505221000501d40b0135811585d00039480c440104118a85a08041c10100000c01d001d00480000c503040b10360100312450241c4000701141d1004c40210303c0c00b00b800001c405203030000f42043c3c2c07210006103c0410f0804060001c0c0c4040c44050301c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 503329910 1250 503328660 503328691
    0x13180b01031506081f09060e011a040c050a020a06090c05030709140703050402180405071211040518030301030326011e051c060504080403050d1e05090d030c030207030605 75
    0x1407450300f151810341c010900c0e41d115881c0c40c0710700d41c94055041500410000001801c0040b800d00340c02a000f840f502110651070300400b000d0800140c2d002c400c0c80c104c1507804102c44c1000d04400d803014803410039441b016900c25003007030340040d68941100410780d118800d01210300b5620000b01c1c2c0342c050240c200080d0310b511410062200750b801d1b1140d40d4894a10724080c4910300345500802e003045a000b003030002da81c1c601d500060a0150402130400108500a11943d50102e18103120510300c100e20072440c4502c1c1030401190300820015030307002601c2c030404081c510751b9203956016603104800a403661582c200c2e00d520560780514011036240209290740142020b082d5000031070030801030a82119109201c000092003110004840203003000303a010200080540325030500c0d03041801240e100070300c10f100c0e4121443d041940031744a0007840c2041c0300442ea400803007842c02c1d1101d000d011581a008a128110100800d102c1c2c800050264003a006580d80e154481e01c40400741c680886074945d0030054003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 503331160 1250 503329910 503329943
    0x302030d0b1c080309071503021c090309150201090f0b010503011407050307030e0a290c04051c02010c020315070e060f16150905010c090504050613180b0103 69
    0xc0c0070340144264211420050b840c040990049040c04070030001e0310001c030110019003400801c20012000c0c0c100040100000150204014061760010b1480c2d080740d00c0341444010340010038095103c0240d13040e2940740c0c00741c1c10048001c11000c0d140e101041191b480f5640c101c086811640440041c1c2d005e0300f40403880390304200c14182594035500c0001400c0a244003004821030384541a641c0010380d5182c041004062548070500c2c14528440c003500a0741d0060181e0102c00c92034071690380f9007028a903988416658032800042c1400307a4030486401140840303031a11307050710440b98580c41502c1414004e02024198012a1a05034460b40c1c80c0c04010301a401e0080e07441e0082c0d040351400303008a98807883c107405603034408118000c48841000c1016896818010000300b20202f48074400b007544100708007900340c10700e207002c1d141c459250000b1410404004c101ca0919001781031080070301030030b9a640025180d0545000f060302c00c68111407003003001c2c103030000550307400f491a0085000d1038071a1403840a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 503332410 1250 503331160 503331187
    0x50415030b0418030804020f01030e030d020318160506030628170307030207090902010c050d0509010e04140708100b0a110f01020304051e150c0a1724041503030203 72
    0x4441c0f10801003c3c0341c07031181d030000354489171480c2e01c140d0568804184425240040c0c018204a0310450f18600001c503000c3e51660040c0d02a5200e9080c914100f070b62042da518000e40c9030844040310443e02c141c1da040602c12420203d00440d08401d01034007541c00d80c04591070207004880d1020000300c0d4081d01d82c074204074030b421148400003400c00300b201541c9170420554010f0f40c0c0304110301c9042100340c0c40d140d00c2c9095a00403420180007070781040a0b10720700354a0403c0140740b540001c0c01d0318040f4400c40d14441d25810a40300e070148152400141c41e040f41c031a940141c90480005003001c08500103001c000c03039604800006003011043d1511690601c0c84c0c400c4d101400d003542090504503e070700c14820400481c00000300a0700842c0254035024060b0202d0f280a4244000c4403001100701c5903403010b02c0031450200004114981c09545ea07600310b41d4110000000400040e43d07914500000b450710260013a00144900c44840c40041c40000c0410142284950059040c0d00680150704040b90040394541c070b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 503333660 1250 503332410 503332421
    0x3050f27040b13050408121e090604081b2a0f0405040b071d0303190f020f0714060702040f05010303080108030405030d030203040515100503070602070b19050415030b04 74
    0x804803014064924441c022074083c40c852a02592880d40702e0700858240030ba00000c90f84440040f40e0000b48502c0d144003012045251041c1c1100021212800280940c4010070103d0140c0c0d0f010300018540401c1801a032840780041c407008005006440c10310529441a480c1d00044170720301d40a0310340090720401080020414081414090360524041000141d00d40e441c85500003c10304108032010604d28410080d00f4414001d96014400012260b0f500010340754407034512021a614040034207a0440100c0e00d0b41c910340d051407110742c4211000d011050001c0a10080d1000203882107080490b1900041c0030740d03100860741c9850136552001030050550001e8400e000d06041002540b520f071401c008030744c2d910906000c0504160f404804241004410300400c0c10032440550801c40d5410f00e80c941410b00b821a01c0303054460301c503043c4009489400451040220b0b11802001030410300b0520140030003031200490f140c2001000c01020880c1030b140a40c0d440c0800302e03642d000829141980a1004880 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 503334910 1250 503333660 503333737
    0x50d050c1c110d03061505131707030204110702030a1e0503120906011205030405190503010f0605040c2a061e020a020d09120201110f0f10060501080103030903080703050f 75
    0x142400c20910601d48130240f024070081c6c0e1880d0183e51140300c5044a80c9064050f0003403030741d074880401e003a8610b160004045090724000c450402c0b41c0c040d07a0f1352a0249104504009406410241110b004a40d017802c0004000d00c0200030000c184489070b031214110350160708131322000d0088005100c11b00808000c0d480c003424541310072280728540e5458171a52030089200741403040a5800700407404001c4140c000000f8035010300240000c144245070b074000303401da5008140c0211301e06044c0082ca28429541c0e10b00080c40355a00c00b10518107901c40808499489000b601c0140c0c58451618441c07800519200e04d480b8410001629082581c0000341442c20260003182080f00a41e820f00c000c81c801490300241c298242004101501d000088074200011300c0345849541c001c61045040101012420303695251011504001e19901e940055401502c203020143c00030b0345450050000507540d000401c1c210740242400f90400310100000541d0368030220130b083e4103c3e00100301c00a008600110440d41c0c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 503336160 1250 503334910 503334917
    0x4090f1d0c06041403031312060f020f0901080402060c16030b0a05010620120c0c011404030f0b0a0f05010b07050f01061410050d02040605120f04050d050c1c110d 71
    0x211507410009469000790300402d48000c001d07103e81c6001e503408000310340c800e0070680c14016029513076031565503110f140d0035020780300c407800d02c4040e242c18402ca00c200c80305510300408860070714072018011a52040d00500480c0c021502300080c003201c2000b0001c00400c800d455483c0d000301e6081d4900000201d5002e0001c10640d420013005201c0c00e60070030f02d44095503410542c48900c5070129500702c0d10342090743c24612450300300014804185803000c9010210501c084e00d610044c292a071000459512651102030441c0c10700f00000d2001561104a8540001c0ca00b6004918844462074208c211002a400b03418207103c005806420401f00380251200392030300302c0c000c000c0c846c03901a0850580705402a940d01c121540305003072003e64040c0090300c1c607807021004119201c0303403a20f4015100d98172900c80d2900c01160b481c00101c00c00e0855181501c40c95000c030203054007215001c4142d5a5421140c60140c0303d00504800c8817860340c003860211052803050b92803601c1d580d081501d007810002c02c4220071040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 503337410 1250 503336160 503336173
    0x5300414130c0c06090206120a02030a0b0f03030409020f040f0e150303070210051c060e071e0f0e0d02091609060201060302090112051e1015050f04050a0204090f1d 72
    0x380d030300240c006240c160091310108a410007440020001d1055404d8140520f550500b802010066039025500c81d070000c4404219001000042010b01101500d03070702d5155101304000e121180a035005045508851982c3d903081940f10000c174410b60030035401c01c0c0205c0710301c081084800403085a0a103141310058019600d482a2038001c40c01d0b480000000781c05002000401503040b20400c0c281e0b90081c81190b130100400c80c3c450355820030f1000107031480c000080c420b80c001404020810007000003805183c840341c0348885850801d80c0d007500c810305000d6010380f1032a8910056196200d64520a64001040b242483c41100c0050500301c80387e00094111381c5400b00520040c0c441030322407070640b245003c05408041d601c1c50300745d14180c401030a0704203c9007400644240b020000880100401000e0801e0040801c04258003c02c400c0303d20411b507101180c40c0c0c80301d095091941c09190000c0c4038a1026203042d49520b5103100741c0d010802007003c91540c80810001c4040d00d018101c0c1312118400c0546039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 503338660 1250 503337410 503337431
    0x9070801150c050c030109210f02030414060f0c101a0f060309070305160602150601080105060a031116020301050a06050303030c18030d05031f030530041413 69
    0x80d121070074a200e50510504004490501074204400010010000c00078000020070346806c40e406079500382c111b841d0300d1601c054002c0060081202142045071a40203504040c501007480310031410f601038141c1c201f8400c1000d603d0140c0600007c00140c4e03401c400418410290b900910111007035050111100d11851540090694400d100440b00120440b03009072039849051940d410441540d10007031140c849c20340030030060060180c806003164001d8090390311a4080000d50902800125491400980b034000103000781d103000405000c50110300e19000901d410144040150340e40003030300003100510500300c4102103290034010141d2000d13141c0c1051140f24a0440441c0d0b40e03000c0035000000c0351801060105601071100c41d400c81d01c100080498001c4c01c540304014150780d0040d0b4400881d861992040d2485034206140c036000c036075002004068812101c1d01400ca80280e0a1925200001034440c8460181800c00507201030300050003001d05425202c000c03c50190190302e00c15082e58203100c2080b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 503339910 1250 503338660 503338679
    0x1e0b0306011404020c01090f21090605030c22080705010c0f022103120402041a010e220504060e0c0315010308090d120201090b09030405061b0703080706090209070801 73
    0x50454107008101c000c44090a4000b502900640306070031740307941c41d00d074900b42481589800b540030640110030010403000452484ea030019008440000403420075a01040110703c03d4009660140101654034101500242511080c01010616210201c1070000501c42c1e510f040c07054a00900e1300342421503001d1241d075511849a03114220203423092144400001e4000050380c00503070381d10070800035241d5800803407a00102e4500150b07002d902075072070208040703000d10b00c080c0700c1c20110304140c68840b584140b440420110740210442c8404501c40410015007502e0303140603c90107548100c0e03021400006010203640303404031201496200703621690801c070440e16400082415070b40c01900c129034a040c0400461045114518000e00121009003285034265047d0f1105020381d1140c100390302d854852404840e92800b90303010b820b5102c101006410001c81c50341d0305e888044070000d02690149660b0781c4800143d03400c0600d054405940340d100d21320840c98086852075000c2c02c06e0070010309039418901e415 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 503341160 1250 503339910 503339923
    0x1718121e090f060c150609060f0f040f06180e0303190e0102040308071104050105120c09131a0a050c070807030f030b0a0803120a0902100c0c05090a1e0b03 68
    0xd101544000401185075110055a5400700314043c103400d59a079851032507240d54142c24082c00c44038403c40e0000c204240b9040410074000e0400601c1020000003850421220503a8401403962095589202c1e4203aa010b41c05100001c0c509400040006654034160200b6160888402c40304d580080042003040e00d5400000386070150700700800501c40380700c7d4450500a10035034001402c0c0840124441080281021a100f0001d8080d601840613036681e80c00d2040007207000260740720640000d045071030981082c01006505c4a0421000514021588c880022000c0d440041d280c00e442c18008001031305015010b41c075040300010a00b80d01d800440d072910340b628060403100900304030040103603014441c801d401070150800014091190540d5a41c2103039540d0380007040040391101410002500b50403a4414071040365006402d030010243c652101b00c2d910200c4490803200700f0355600b80401d40e0385404c0881d0b03100720415000007542900c903125180a019045004000c006d0410304074074629180441e80c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 503342410 1250 503341160 503341207
    0x160c2d03031707020f100507030f060806180703060f020903240a021c0c05090a0f0b190c050319081312120f18020913050a030e01171812 60
    0x82d003601c90078802c0382491403031142c0424600c12403564050194550307010f107000302c2da40d4034104902c550000384c1400b6140d6600ca0200030350001e8000551540740c1410407c4c1d0051060280c1c0c102e5500ca54484c02112400600200002c0d40440c0210b420708003009043c15000c002e0a95000d05000c0f403074000d103141030080203014843c0d00070a5100e0155244140b04011143d81c110610803031402c101c004069401001c441c0d441101d0402001803030000e07000d5408151415900a5880d011580d04d0300c081c0c60340140e04400420014540900c0030510030301c060020340e89403491b0383c554808111001050740c00003404008104840d4010500010315062501486814505040385400580c11180c001071842d080d0729280b40b4184460420219400407070303803102501c00ca5000310b598891030a4840d0980440d08001d009500c81120704010078040d1120b81d0350440140340405502a490000ca804614282c0c2c50380c515011208000b8a52a0144405410b122142290505000c1c000f0801e04600c400c0948 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 503343660 1250 503342410 503342447
    0x30c05010c0303060e090604030210110910020705060f1801090509180106180e01140405070e040809180603011a10260906010e061801030602160c2d0303 67
    0x10800c0c02c140c0603422050043c10107a80c05926403a041b100d880e2506000c6078200c0040c022031200900c502d034188182281e0041e6518098200706068040c0441801e003004411f01b503100364400019907945003002041001044e008168541940149000d1040700650045044c001450302c18400d03520703000b54140d44800d0703220340c0c181006400c105403401400e064000c1d1403180545200d40400c00210b412403080e15010074000c20081038400c81200c12071a090760000d056030010030007082803c0104264940040c0110016443c0c290b078507000540c0c0c00404140f60b00c4010807003081018030314082c450701d111150226548003030400c0490000e41c481d00f00280060502490001204000c40000c0000c0c0c00308a05190080e00c2e0300300aa035a0b83e85000c01d1082d44c4001c410000040d00b103003000312003c988110013101e6000c450342076070740d80d40280d000440c840c4aa84035105408000c5443c0c0703100c00300141048202c0c0950303821a03888400340d400c4101401e00307810f9101002040003e0b4030000b24651510502d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 503344910 1250 503343660 503343677
    0x19061b053a08060f19170f060f010609060f020106083901080a090c0302091305240a020c0a0f0c0f0b0414091306090c1401030c0905130b030f0a060e0601030c0501 71
    0x4520100300c031aa8201b01d80813030000d5842045c121000800d01c2180300c03070788102c1e00c441c0c0d2044041d0fa103a4009010707040026100741c10802c5000e010301c3e00242010301500001c1283c50303d60310841d00d0071441c6078081b0b03042c0c804041e01102c0707501c0366909680303815075014213681c850310002c00180146070701807d002040343d612002c08050040080700c1e1f0011f95070080002900c0e0400c030b00d51002041030000261002e000d00080c3e181e8038009040030300051030b01600700038499600c002405009400c084482e911502600c003072400041ca0200800c01d8062140400c0c201d51410b181030306481c00d001d40c02c40c102c0444204000e0201280e101c100c410440401c8641c2112330340e569401b9103501c2c049540c010035007800d0030244d80410101801000a03552441b82280c01c29501e500110141c07a030a01c140c80204150340e0b014085420712418858240c0c260f03410103c0d1038a884002b007460002141074016035600029a81c03010012580112221000301100a00280d419900c03402c82411040c4038050601c10b688 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 503346160 1250 503344910 503344939
    0x7020606101211030604050105100c060902041b080106020606030a0c090513020a0306020a0f030218010e0609190f0b09010503010b092106040219061b053a08060f 71
    0x4101c04050300d905144148071090540030503503e25001510761601c00d40c21f2000218150400c40c0500460300b8007a520214200400e4840c0d000410b42c0c81812307078000307403904846070086030142e4103020031050640e15111070b9851f140009061500181141d0712030342080552070089405034801c44240c984002c00042d0940b80c5090f4200201c2d66200e009400201c1342100100348034841d40507000210382521003140321a0900c208070102e10400d0107840e8200031100e0840307000d5110b0385181c0707285c01001d09043d00d009540c40000b44030145020304c0100540c000031081c00008404021640104581c0307500c6410904c012001074800e0005001d00502481c0124201c406560b96041d550701a5040d102044000040100c0c0b1a031544421103090340034580d1003106905c080b801103a520708072503160b60780300300b60b000c0607032140f4801c20000ea05480c2031040b4041c1d81052030032458606aa00c4400145025125207415620a2209003980d120144070800d01003004030313142c0d00b40b0345500725030440380e81c403144040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 503347410 1250 503346160 503346167
    0x30412031a220e030c060609070804060b0301060519082503080a020a02060f0904151a0901020f0f0721081207172409060a0603050601020f01090302100e060702060610 73
    0x15010390320b80c1a070520380b01000103007020004105807000d010559040d42c1c0d8242c10300164100581d110300014034214000790105401d603100742c42c0d14100400218601e503883c0005813030202100c0c00315604118099041000000c1000f581000c0008014041001141104000c940b4905480050001d0900089441585200f0f0000c01108c0d603000b01601c3c0c07901c165620508007034200c2c0ca4414007852a1203907281c02e0700400310507201110800714411384142c0401c240c80c0c000e504010b111605510580c1c0710750285540074818003d04445c0b890051035024a071520b503a800c1264110380203103141190100d10b0109a0700c03000c5501000e00c8210f217005a45540e0b000312034003202044601d095089840a01c0500107540b49080414504100501c0c0000b01003420401d400c1019102c0030340c803001000e0708020040c040e8000700c3d8001c105005540380111801c4a5909503040c204040700183c214805000c540712a07441400110f040c03000090003a854959001383d80c8070000341441d8803c1403041c12005040d8403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 503348660 1250 503347410 503347459
    0xf03030e0a05070f090b0d02030d0e0609041b09060810030b190f050f180312040807080a091503090201020d081b040e040c14011407081e030412031a 65
    0x1484000c480041d0703503500032111031320a280285080941014041032044c41c0102c00b00d5200f42d0000c0180040001086060794283c41d100d18442d040001403029040d41d82e120310500c04401c1c00d0206005074040600b400511401c61604450140b01001003849503615020700d01c1416241e1081288200b61035180800705003088107082c40c441c0e00d04103401c0e04e0092903580c204600403030048103000c10584070701043c02c20302074080c1c24501c0c46610610918035040095280b81c0c5d000340c080c840d4245048034949414645034403550721040811040c68080200250280021035000b205150801c180b1142e40e0000703440303e00c0b506007070007003182d00c80106040e41c40b062102101c00402c05c602e00c2d91180d581c55140202103040b1416a804030500900190076404000d104001aa05949a52203008141c6011000703401810082d036980702d007800041e40096850010390304055070a40115103038607082c5441c1180003050400802018245660016001105034a411022a00322a9802c8806070103450810199 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 503349910 1250 503348660 503348663
    0x50901210606091a030c090106021f020c1c0207050f0a03080315270108060108120c071508011809080a03020705100c050913020f0403080913060f0f0905040f03030e0a 73
    0x249000d000300070070130700260802404201502501c2e0907412000c100055400244220800350f0090243d095108040e50442180074207121b8005003070203040e403c0e181c500f00d90051a10481c5503820034610b08144c041141c070005140c2210b0407a83c6a0141012445010051000810841020000c00c901c40d9100151903c500c0001d40344203100020007618502600601482080510f9a00008541c07540c0c0130924505071001403004101c031900c1910b02421542c4001800d491038094003101140c0c684000d580488216003d681c0d00f00e20b941480050200c030b1402c55881d0b5075581c60300030010001110101940c0002d403080c10010b88401d1903043c01400d02c0000c10012460615118191040e160480050400981c0595009200c00c040503162012449030810783c8607907607014081040050b410f40010441c1c0384024000d6003440c102d2003440740540f50700b80c2060801c4d03159080d060280040c1103050000400c0307828000e21090903d9101e1305d09941c0304040c0a0109034949102c2e0032003a03000c00511500b103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 503351160 1250 503349910 503349929
    0x70302010f14010f05010216030f050f010e0625021506010903022106070207030f110406090216050d0906081f0f0306050406060504050f06090a11160c050901210606 72
    0x911040418030302c40c400c2405461050900d40e900401c065200045900b4041c7c0500c0031124103600350b480ea40805034440b80101d070325118543c043c820081d802c1c0035142e094000c8034014510703030402801400304410103028089043c0b82d501103041e82e0903800250850300b040c8150780360030603031259401240c025030580c002170741100d1b1040e140d048042c102903045070006440015103c0d2a04d55407401c90302e40c9500c0c400074029002030507880c800300305920312407040003000400c0000c05c2550f540d02c803030a0b1f8104004011000005246000a000003401030344007102c070b2840c0c03010156041c507401420b04680034001000c10044065403652981d00030040c00080c010326900c1411030b0b5034034a05000074240440d006c6841d5130510b00001014100790203800c0c000c0d000c12205d03051640e03416051013011203004140c81c0c0c502e034481c21444181c407118001041d2400d400f8070541e4014949090050903201950b000350700074103c001c0104181401d44008802c100c0c125a44920000d506060ae000902440e070003400f81d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 503352410 1250 503351160 503351171
    0x3020c010c050702090a05060d030e0102010b090a14010f081510080105100f09060b1c090b010602030d11030c0301120f080d0e0c090903030c16120906080a0917070302010f 75
    0x101a0040b0250881920032038081c0c50541d1680da094003a038600381c1e00941c2000155040c0d01c0024000c600d0030441c1c100c10b100016150134880c0c00564502c1c0142c03544481e843c0c0d5210808482028940181e024042603004842a1460403007810780e1070495030104454111400080390303034100541c1e0030320014040a00240000c0c109100b4a40c990a4070380308500c0d000344c12040015614030b50303004210071107440c038842504001405802c00c4262000005280d8103130b41d02d03080000000c01d41003c16000e800190300844d210340742c90714030000702c88142003050703503550701401007003410000242140e05580c3c183e40540403421451500006081c0408801400c010020807a400c00c40543e5100c041e007080e0b400f088940350041c1c0c4050007801c56042da401c40c0140c100308005000c00011400500380c10b4101d06080f03188545549624910004a071b110710006941450100000c80e80108000d07080105070100f00a10300035551481d11600c600d900c002240c0c140800c020061500030350040f42080382c0040180803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 503353660 1250 503352410 503352431
    0xf030a02030a0c0e013204140c030901110702030a03050906071203020702130b0f0f030f01110a0e1c06090309090f090506100e011824090c210c03020c01 67
    0x1d990b40303502420840d00d40c0000002038214224003005c20701c8994107920345000240c03c016a4200d030400f0405504036440320701c0000234050f4088402c0c880c02000e040c4686904000140314203480b02910301c40f980a82c18402c0c00056507010907130002c040d80c5824100c0c1e42e0004140441d11500a00d00090000c28002c100d420042390150010a0601c1c0300b210540c03107000b04000840300312002640d01076001b005080a034200f0341031041d02071145280050840e20201001040c85003910082d01099180c1200403030396820f515080495159484003c681c280308a04030381203d00180c505814000d00030b90345446410081c14051240040075024103081800b04c9141024007402074004150300f03c030780b485078000243c0c0c00980c00b401c41c02134940404010226901e002c03444c044800c1100e000d10300680e079a030f40d10300007c990203081c0043d10609552865095103000c80e1002101c8084aa50050010180e24252648009546588030400180000071410880003044000b40038180d00c103d6150b00c5c0c10300401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 503354910 1250 503353660 503353673
    0x20306070c111e01030507050903191104090209070c02040b0a0b07030801140f0111010b10110d020303010e07120605060c03070b1008071701110313030f18050f030a02030a 75
    0x1e90041c0960b142d4085181c8840520101200ca070496015409001180b00c05642c4681c0205402806a250041c1002d01e514006400c0541900d104060114640314103420040c012004040028040b01d040100c509142c001c2402c06000400e51020010320f1a840ca08558a43d0301041d1211405442d00c0c00e0317540c540c007141c1e219501ca440d00f98080398550740005070706614203030607824024003d4051003000c0145801034614007010f481d450203554030f603c0054800d407104800032440d42c12540e104680d10740d6600c60395084c08194550502150030410040c040412024092504031880380340080482c2c0c1954242001448180c0140d0b41c440d030005032070001f4078000009804024010b45030794200d0345546c0c81c07500919000d03129032070b5181c02c02102002020172503464103c0d0110048004100f407290340139901242d510448a034214003506406007418950b0110070340491000c281401b41506101094524850398148161446481583c0e40000180c03001d10000340015409030171a0843c010718035029 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 503356160 1250 503354910 503354927
    0x9010308030a2307110705031b0303040b0f09130e0309010c0206090307080c040b09040b04080703050f070501060614120c031e0c0c060709032a03020607061517031b0a02030607 77
    0x4d000040b1031307030400104d000d40821144101d0700018014034402178502d4020703202c076040c0840035505020a1000148107442d8900410a1040b10380040f543c0c1d01000c42082048030900d0320902080c2d1804c0e2009850103000030486490f4003090178016001810391000680c01e00c2100c5140b50580902040000e891343c0000e03405000759000c64040c842000c0f29810301801c203e04070b80c00b40c62088a14040740100701c42c40010507502c0d020340740c624607088103201a081c039a400b41c1001c9507241e65800c401c100c0070f80d000000c910442c8409070410326040703043c4201c085101002d03102c0c009001001000c84c185160310501f00710300031041d01e118420346c9045a0003510b0354102d45510f03482c5014034000104894880d11410040e80d50000e40584451a001805902500f1a40b51b07081609204038010000d6a9150068031095101c0c01e000315000010404020155810758042e03058485e920b804c070080c07030f1800700a0b95242202c5001d9129183c14180b032032443d0200f00c20019405000b44010300a1266100446c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 503357410 1250 503356160 503356171
    0x70b0601110a0c0e0907030b04080301050405340210060909050c060703120513020a080d120606140705190803041e0b070c03090302040515030c03070509010308030a23 73
    0x10610141d00da0340180382c0301e104540000b070001c514a4828480c1101074007199410404580031586d04a032650340320300310303010309072004d0703d5690000c0010042443c15010307a039400385c00001c07800801d00c448030b034400074003a903002440c0c0311088204402001500c200a8840d03402101c500500050b0b81c0c5d00000001024103803020b40380c0d030040031005007160520508882141d64113540d166403004291110703500a06003d00059014141004c051000d40e540151300e0003e4001c020107051501300026020b00300840101d1f8588215050150800c44640c0000500341a031003513600d06940e6640c503140c200c0c140103d0f070701c80300c03840b60342c503400d07001406210800f46110710701c038815129181c0c043c20394001e130701804d01e0401441100b5142c0010003440c03103250544100b40c2309041040644ac0c50b40e000801f552011030781d80c10703071300380d04001840da6280420441c1038045041c0c001c1e00300c0b18203110110301100014000600001d00c00404140d0030011a8003660701e034280d0b42c0e0100c020b80c55600070505010000d542 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 503358660 1250 503357410 503357417
    0x601090b150708090639060f061f02010605040603050d0f020105010b04181407080a231b0d2f030907140301020c2d070e01060810050303070b0601 64
    0x11444240381d90701240c01d400d030407281c02d504080c0f900f02007045550004080d41181110702c0c1c0e00c203210022203000c01091012407880d940c40c00404042891500301c00030b05e016081c4501200340b110503100d08031050440d02459140c040003444514041c0e001d0149984069002850610b00005000700420302d1154155141e40b40c02191030b907000100d00b40c403800e00546c1260001000b081100d0241074044100f003211900300031421100705144002d0042c0304950610100d000d02d010821040b100d0b100e05c912402c5440d030514610194450040b803a0300d0020028058032142c4000011403001d801e00384c9560000045c0c0520501d03c070900d80c802d6480c400380c00c800301500443c07038500025519405480c4610040c000070440580303482c504084598820015a0700741d582089487c0340c052040c4126040b107400d0028a51007103552490404d40d001009103000c00710303040010240002c00c84088010b0441e1143d1a100c03005459a6004003c801c034158041c03907051000140442c2000740c510145403003944240c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 503359910 1250 503358660 503358679
    0xa030c0503120415031a131d12030a020a14070804030c0e0606122d010819350a08060108070f0504030f06060506040e1b0a090e180601090b 61
    0x1a0680090145004801a01010400c40c4c1c90451091380000c900d80000c3e8510140030030283e001c9609001c1091104100395100e0280c44400d106110182c0b090b4000540101102206c2241e040700c0c50202500c99401c0719000240002058401e940090303104d02140c103482d80c0d8080750b1134034183c00e601c50f10085424000d840303000280e03804014903080c4581400b070072051034011a516600008070004125403000318000c030440400d4104034240b41200380b0b0f003503001c80b295410a45003c7c5043c0d035141040c802c03840c400c88040c0004014905801c100c2102888900007028524a50303d0152001411124075140c04038046120551005013640540030030380b600c0405489102d800c480340103001640b480480c508010400010340401800e00c0c8080c0a501c000600d00d03215000141d19034030981c0010507203803a14082c40408413407801d00002c034903000c540c4a032405500c10005802e440c0b03d40f0403c009107160200040300d28a00b51040c40c0444601ca0983d420f035078481942d407004024403081a4051103021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 503361160 1250 503359910 503359933
    0x10050301020f1308010c0807030207031808012721030e01050c071e02060a0f12090b040b1e0f09011e0c090e040809190f0308090f0405100e060604050a030c0503 70
    0x606c215052141c4c1c3c4d44c0c0c2d007240d65541402c180c010f507200c0b0340300707c0030010803070340c1170852480c114218030160200e40300100d000d003142c225040d14401030000b9008607403500b038100700c00944040d1249042c0d065190102900c1c1c040080107400500c202c58050407a5402c00d410000041c461100410444e0b00c00c070741c2c141142c00000c00215201c03140b850002d40200081051114850040d180c040d541e080c0c81c5000254401d5804020307041d5007003040101c40c1004000b040c07000f002a40c0d800c10398041d45072003c01c0c004800e0721a04510801000d403500c40b11843c0ba03004901a0b550a42100074881c10060f800b1034401100c00303d01004150038a50348002a914107008240c40021070700c054000e5030018800d0741400c10a0081040b50340d085c1402010303180c500c6c076002035403a10903014040158041c607412615064508203103d001144000c1d1244500d00c3c010400007103030200900441a03030703050700b500440c0b40e80c0c0d080802c1c402c0c40303035820030b65101d81400030000400401d98461401c0e140250b0070348403042d829 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 503362410 1250 503361160 503361163
    0x60c05070201120f09080d0c02010b030607020727090b0a0c0302070206070b070c0b0903031f0308070f0305040b0408011a03010203130f0807120c1a0105150310050301020f1308 77
    0x10100c0090010340c3d00040d10201d400a5004a040030007560380c0054641c05555810134075034414910024400c1e200d00c50300140036020f10070b600035260142e014100c00d240c0071100948800442c011102c08109000c2120142c02d13140d0040403411213144800c012400041c02c0c4100744003130448600d5611400e18240c102858400c2c020b440c52a5030141030745003020990b5680740d0890000a190303d040240401e243d1020400c1051010f00500a010207075560b8207160070b11196114030081203030552010450304000250b810003c441c04a44c01003400048843c2038607040341c1c0c902c80d550003031089100208000c5014001944032025400d006086010410340d4070041c1800c0c0d0200b290b00c8000e4500741001440403c004103c28500303144240c40700c1d840e10966550304003140340c0c01c00c00b000015807040d44604c10051a525030314440b48550f9420022903141500160500c034120a030140070090110124013545c1c901141c1d8005004001c00a42d00c41c4140c044c01495900704003080b0451848004000508850 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 503363660 1250 503362410 503362417
    0x10e07051603021930140f190f0e011b11030a14030405030c0406141c0c03210206010803030105060a0c0206031e1003030c0b131202100c0203090603041b0e04080304060c05 75
    0x1701d51582000304840350800315190b086410034513403c400c10400c9602e482420030040c12414140d443d8807030314200000c4000c140000104c0c0c8141072091401109d94407610300401d031062568402042400000500046403d040f881e9100905000c44c041c61000d650001001400968000b0b404403903c2c5107010007000150381345440b4010403070106440884583c1000003c9845401c022038040464007000e07a10b07107a0522440c3d20a4501000b4201c5500703d00000d0703040e2040000851000301000d504002400d500c9200600c1014885e003000070741160482e000300f5540300a550000c0c2101d4a07403410b000101090041008100214054440001d04e604403002000058a42581d03507442005980e0341c404800680151010001d104406680400205641c1000c005065070b580901064030500d00740c242550241106030040d500144000d55441d181c032015030307a219401c22181e41d540d1142c1401c0a040b5180c5030000c0344030850603404c00dc00e01c1001e10045006502c00d0004020f42031700440100c44600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 503364910 1250 503363660 503363753
    0x90a020c0d141806040b0d0c0f02030307021b030a0f05010b09060102150a09080d09060b010e0a0614030606040b040e090c0603010806070c050c0a0815010e070516030219 74
    0x6060048040d10a0480f011001507a005000b040c503250710740030104140d400a0000c42079903a12410783c02e144c90b60000740020008041d00055086003007014004c1d444009003280c240300c181d02e69000d6040fa540422001040075002142031610502506117140a0b0450b180708034003844081d400300341e155100040403004120303041b004101ca89c030313003020702009010311150a9420040500014840d1201842100c040c076120303000015401101c0300014140c004c03c132800b0761151f080c601c0104401608080da5500f040e030340c00c109039665545c646c0000c4030ba000700d4000f100546400b140202d80b003010302c42c0b05401414060220740c2a120780d1010821144800d0190805a810100104d19040c0c0580394802480c0d00c071300145c0e1244100380e40804c0d025101ca902c4044076134040060410066440300000d401742c61203d40c00c040c00e180c4644050500d01c282c41c81000050306600c2a4070a05109104031071050010603440407010400d07003000c2520403400d01c1d05009101034940441c0c0c245268044816081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 503366160 1250 503364910 503364947
    0x30c0f0c010c0b06031f0b011215030809040e15100906030c0e15030d02032101060c1410110406030c030b030d0c030e1305180307050604120e090a020c0d 67
    0x84581c1e40d108080c0346005011541c15102d4401100c46c403040810843e00107901480000034456030304000102210580541150034078034043d03882000a805850042c25a501700602c150307950b9000c008030b0000e06010040410500605801580c04c00d1501c0b06940642018012905003d485051030400c0b140107100091980711450300030040008100082580309291600d201c00301141900403a05040001038248016080011440505400c1480740303802990b40034604c01c1c03d503042001c0a4498920030001805803c0840300c401e1001c2c40070400d00c001070030011001d120f43e01d18410b81c02c41079049401001c011904140c2c844007110310a214112a484c401030090440d4035074800d0585205500c0d040c1039080100704100d6111903100c5500400140c107a40200040d0b625019660758918500c005044c0240d4000b081004040356001403200c0e00643c01002c0760040f02c0c20018191055002c004180c1d420a80741c004200c1e000c8059406801c0c07050680d0117441d04002c0d40e440445000c00310004c60400c0307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 503367410 1250 503366160 503366177
    0x4051e010b1003050619091d011a0f0607170306040b03010507020a020603060315191803050a080a0e010e010e100c02032d0309160b031e040221030c0f0c01 68
    0x3a11030f0700040e0304410045c2800c282d000003003808000d04075164000d41e41c1f50391111440c60b0007050080c1c2c0360890302045002002007400117076805020780740300c0a100e80308210f00040724401e90b40d00e5048418076035011034940ca8048080d02e00981c580c2040315141c1c4902c5c6450072041c501e05060103818460b21007503000e420701754051f03801c218480d0405080d0315050b224001150b000280409c1d1618003130309441e103001440c2900303030110f203068602e54550392030b01c0da40c0b642001e00066001000d55450305442d0905002643c0d0329035024004151840c031850b039544c03c1c02c00c00115140190301600e00b0403e00c0c0160b030005070744101c194040d5006660030000691040146900c0c5d0344440b00c00e040300121f071484164001404c542c0524040c3c200751001c00d8240c01410b260340c5100481c070b000200601c0e54039959800d44c5400c0c0e22601e410382d1115070f84041d0701526000202151398065406145040f2011a52040c001c80000c459490704000343d18a030602c40c8010f2903940e4103000880342e4002c2c00503516140b8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 503368660 1250 503367410 503367439
    0x30e0a0303110d02180a06020a170c0a0c060f080603340f030507060221070206090d05121b1b0d050c0604061d0906130908070b04051e010b 61
    0x10940e440300307600e04003002e02454400070f08030700080c80d4401c84802c484990020f40c030100300c10300e40d040d072203001598003520b02d00d030010351000001e012908092003032944640c030346c02c0014285000f44000a00d1701c400d441002c100c581d045684034452001584d1400001d5580d07a0030704d50b07140c0c40b100a02100250005100003494ed000c0c04000d5001c8407001c1d18509a50b40707441c2d0602d00301c05030b0821607c07500040010712a041e41000202c10015069401c08400d0380200c0d1094241d00c50324001a00440c0001b07644007003911554410000706612508503200343d000c00083c210583c0012089e50444030440b10001c0300054002812030312107034059000403210807500b0402c42101003040e000c81c0d03107015691032051103030396030710250009100d035840b51100100501e08184403000341c891640d1040d4224404c1c441e1070386651507030b400310204200000501c00c455003002e41d0b5a01031010014030402e1080100000c00802041004a00d581403056006a4100d100851700380c9010301c40081c3c1281650301c03242d6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 503369910 1250 503368660 503368667
    0x50a0b0a0519080a08040501020f01020306180405011b0f090e04110f2e03061d1618030c0306060e010608060d0c05030307050a02100e01020619020903030a09030b07030e0a03 76
    0x2500744021460704a401e0365540c8882c0c0c1403180e80c0400780c5d1310b608040303000c210650f01413000070320b012a890000c5103549466000900e810000301700704455245a400010708201e000d500801c03024031103094012082d04c1d0000010180385110350001e0008600010000b031001d5000640e41c042e581c012205c42d480c090b54818040c0c2c280100b400399500948001011030783d00341d03608800c00a800200c0030f140441c01d0b00ca20190a031202c541c0080100c2030b08240010070456a4140c0582000c0059079140060783d9003272003151406115404456240e05481000080044070b55450044a100b46001d004e0700d80d482a18510301d510034441c03840070819240c0001d20529009c0203810101c2e2140116211a644030404070780b842d081400c040f14140d01c489240d60952600c1d8216041e140d0180c90322400040c01800000d4071503201411091301e2045c4106200e40c1c41034550140d42c211000501265110701600b0300045c4500e040d844162030000f2406c0205080c00d11a02403403400301d07100310040c40c030207078190b5085 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 503371160 1250 503369910 503369929
    0x1020a1e020301020f0310050411040b09132403020301140106053103060b0405060306090307030513050909070303030b030c06121b0f0403020f1906082208030a050a0b0a05 75
    0x40b641035608100c00780f501d80d4103102960185000c3e40d041e80c0c440f0700b050140011242034076000110769600744410030900c001c0c08100c0f19002e800f51078407014203003190360000103000484080344480300502c4100c4460880c004018044070b000301c009010110100032801d00c520403e004400018404100c17050301d01c190031440701c42c0388030208001103039240f1400701021500c1a071303041110402d8031940c0c2c0c010786107860300400760002c208901030091400c01a85195607881303052801001d1060204108540107003404030040201400b801882c61403400c401c14540345d9a1a0004901181c5403400141c00ca0030300041c01090050094546858000240c044a1240000814a1b2480d110b4000b95000c0b00041e0000b5102a0f01e141c46c86130703240c50852041210196400365980d01800d660800301c0c4507640102c020608598807801c1c498400c1e2603c80f0060302c1c81c1e0511403604001144060305008001c0b065000314804c18a83d1400c00c000c0d11000304020a0301c07084902ca82e40030428420030b014030b15200640 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 503372410 1250 503371160 503371163
    0xe070c03020a060f1a090c0405220905060601110a0210210e1c050310350d0e120601090f090c0e07170c040b03070e091302010e01020a1e 60
    0x120b840c03820342e5540c0c5506642c0303a9030f5001000c5071155900c000c000c82c8140d50710382c0050f080354032200500c0c2130000702035240640d200b0b09105038070012a4804001c04004074050104104030244440032090805aaa80b10150346443c002048002824094000803407418000d6a0081c0303601c0c01e41041c0c40d400c45180c0030290700c214641c44000384c85070f2000c10303074450748540043c1c4001074024841c0b5001d0717410100e4000c0202c00e0900004208000f4505a500f80060595854004103801c06805001018103400301c0c0b040d10760a04403088a6500321800011003100100c2036641d03801b000c204070014418110103c030f0744100a0b5001000520210b82c00c0c1d0400c402502c684000010b002e151512840d0903c0c150f0fa2042007468604000e102030300758003804c00b00034580901c2c0403003c58203040f45802da992042c0e100340c00c0401001720100d800d040c0700d02c807103000d4000001d12212035420300d20f420181c000c000725803c90108210ba08000c41550011420308041c43d044010742d00c002104100c44080c85414250 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 503373660 1250 503372410 503372413
    0x304120206090d0b09010f020a08010902071110030204210308070e030f0a0818122e0e060a06170712170a05040806010803181e03070b120606040e070c0302 68
    0x201e4140d180c1201c3d1986650003060001194180401c42d07500f180e104240741250940104200c01ca50f075007114a0504450b882080183d98030304d5802c000300010301d400c0f140c5910150300079402e21565410f40113002521010482d00131900b0105c07001c9003040c0f89a010040118081d20300003552103019a031441c15940020302516241961310351001d09040018034100c41101004c01d21103025600c0a80a24114006072641c152009611014030b40d0f40c00380b0540e01154260728451400b03012410410121010105141404000c1c6030403d00380d1038400481d204140ca500d055030006049404040840c1d00e1103024001c0c003481e6040100c00c180040c2c61510642c0c0c40000907404980000902c030082c42c20262907903900e619141011030a0f4141001a4002150340d84180001d9080b020118804510440c0448041e03220054405034009045002c90034650700d40510180003840b004080002c3c00681c55480c0304c803c40da615407042021030302403070040c1003120f001200040c2250340039010001c404ea00a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 503374910 1250 503373660 503373667
    0xb0304140102220e010305070e09030d0507030c020c040504080316110d021c02030a052b060902041a0309070302121009050c1f0f0e0a0e01030b04030912050304120206 73
    0x40c05582607900204100c48000740000c0745407402e90202c402000902109400c024265241d0703240c040d91b450490040c003034250712703400100b90031110800c01c41d1044419084d040c0551f00d17140d00c3c040c0c000c3c035881051101500500d440c00d089850580301706071103543d101200c4c9085840c0d008014604603200d0701410305100000d03000c0e20f0402c0e42004440320041342075005142c2c010701c3c1c0503a1100306001060303003000d40d8014010f03ea0100c0e0402c0c01d0310543c024045c5825800d09412035800001a012a01c001c0000e10f004000300e900c200ba5002001602c2c1060414540020340c008400701d0703031004540b4a912900141014401072505403105078011030804121031503052035059440071500008030449141c0d1011062602504001c4441d0550240e5255041c08001858901074208c45111942c00e0410406050500a039034a100e0520064445581fa0701181e40e101e1a000f00044816141a400704d1800da80004001031035003c3d181c0301e1584600654185868407495012010000300200d82c81201070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 503376160 1250 503374910 503374943
    0x4050301090606170307080d02090409152a12050903091c020f01030203060904120513170606060405031c2a030f031b0507020303040f1e0603090c0b0304 67
    0x240510351007280541c03400a000c500e0414840700c10201604211500e4005018130070105080d4000c0d511b6000c03030300d0009a590440c401c0024002d160f0030900911800c0c1104500e0520500c99018280c41c004104c180011061500a12608144201f103641d0021b100f2401c0c0010a103119000175400100540450b400c011400c03000034660020001c590225a044104450540c5090410058883c01c2806c08510f14101800810400100108003030f02101d491140e25007660301c541c044812108051194030070312a00c505191440741990000d002c150720030300f000300e1b10a00d4500304950803a0341c000c00030000c0945401144411a0060318901c1c2800311640c805458080740175a1003540c0040013000a400c660240340c09800441c8564482c010103103040840304120f15100d950900e07150480c1040c1e610f07020305200191030340c0300300d0300070101c0c80400d0300d4001500c00d00e1595982c41040312041000669448403421011502031301009858488000c0003001982c8400008640044c0a40d00188205600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 503377410 1250 503376160 503376163
    0x20f100e2b020c010c150b010207050405090114010506030c0417030d15050907080405121e0a0f09091e050408070209011806050307082104080a080702010908011e020d02040503 77
    0x503103101d0004010a1200703140095041c0000f9041c00d10900b49060074480302d0720740300450040c080001285980d16516400b035a8020402e000040c0f100900c2444540707007444015002c3c2c4603132075a03c2105030000700003060750b260050035a4442c044404000d404c080c6851158540c05812818511450004021302615a20b550007060080d000c011b954080c4603241100340704840500038078840401c1188014000040d0001c01c96442840b244100191920819003000b0b80c0c0c54504c48a00c4c2c40c2040014201921a800040050300c108094990800390740e96040c3d55020f4851124800701c82408141208000f031456070701c6544c20038000c10f000c600706071140d80481e81c0c2480030707004008004000354035a01c2044040c002c0f00302610041d80500855032500d02107596039182048081900314854282144040801098400610012040f905215843d041c904009c2d48055001c0c2d0008400b0240480d50f0a01401130406080a840420b101c1c8810080100000c0d004403408443d40c640800001503039a40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 503378660 1250 503377410 503377453
    0x507090f03030c0311010903020a020f03070b03040c0e131220030a0306050f040b0619111905240f040203102901030905070311030a06090501050901050601020f100e 72
    0x800c2e16060300121442c2805032408020b03c1744026a60f040c801c0240003e80d0118411090541c184c821a01812503030000a0401d241340c0c11a82500c00c0110421091008079940c80045a14050810a40742c81d042d42008100103004405000c0a4240d003010058a1141c08403442c0741e001c81c00500c0400141800c0181117078090304003000020b484d803405002e6840c00d0304401150003c01c0f50104400707126800070424501030351704262403004091806140301406082068140c151481c1900e501c0b21840203407450200c000751065400d8480e04040e001640c0802821034031562a00c2e030218800d9861440490b4086002441260140989500304d04446a240503014280044040c004550700e4030504035400450f010030604c0c1014207250014000c100b010036280c00381c0707030000c50050700100650042880c0681c150402040366180c688000284141944000d01400d107034402440991110801241d9404816481c0581600584a40810103040c0d0384511402c1c0601400d0f00d0a01c07014908400200c81e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 503379910 1250 503378660 503378663
    0x1c060b060c1005160f080a0b030114010603050106031a10023306150306010f02010204030b0c0a030b09090c01030e0106050406060c0309090204080d11010213091d06040807060507090f03 81
    0x82c001100106801c007a80902540000002c0200d229803d14000042ca484070300b010328000e1150a0020841443d0203401140d84588094001d208030a2882811046441d0900c24240003d01e06800464558400e00503030521134000342030901019046410411582456103031031003581314002241c49100304072070305c120701200d22700e5950344900d601c03032011004050000c0410b88900c0e004810ba8466844000607603810800c02c1c41c0c2828070b9020084180e0091141d500040c00300b2000d0400c101030240c0c00b400402e6038100554092105141d2181030184600d1b0a44a1070703003d4020f001000c0c8254401d034007003000090b4490021422585e20404182215840c1e0003a00001d0303031580f081401e00d504a140c02d4010540000c04500d054640610541c48085044900d0100071204440800300a400d4058906c404c442c00e41082006035a060040000d0000d90a00c420010340101464029000807a140d40304513007100f040c1c3d03c2c080b0159101d000511004080e4024403119034804500c031a8400c079040c02a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 503381160 1250 503379910 503379913
    0xb0d2708030901061a0a030e070e090304051f141606180b0f01081b13050a051617010b0d0e15090c150702040908040b0c03091c021c060b060c 62
    0x1c0c20b1030246542582c003d034029900c5030f4407400000582c0c0010740b04441034010980340000c1d250450901071420298150300c0f5007900390107202440442d1001100500407100c08480000a00310000d000c1d1038554171024020f8085900d40c0c0b041403090044a0080280c603105184802c0103a285a540000f15128110326003140038100306a00100310f100c0303a03034035000f40308100040f400d0361401c6550b6640c0c00a41004040840c14014844040d4555800a0810401032001407209140424803000280b404480c1d01001440300b40b124044103024400001d0321000c510000e164580c2000e500f80c1c01c3d5440704402c520216503808221200da0018484c040e080700c4c805000b036505060120b00300e4134090440103104e110b91142c40e600c50b13041c0e187d242100c102540c16940491840c04904084145024951010f098944005890a06e04801000a051410084503005160740c1048840030f040c00b10902e00a41100c40100025820058050040c614030701c6004042240d005600215151750050300f0f0302d4007107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 503382410 1250 503381160 503381167
    0xa0b0d0b0109060b0708030106030906150e06010e0402040b0a030e07050315070e09070f0e0111070f03150c1b0c05041d0c180c2d03010e0a060b0d2708 66
    0x844119000d00001003003581d44c2d5500b80516510780140902c810302c80c85041c107959441d03000030400d141d003062515500d141c83d800e00041d512500a40142c0e400c8400c140003528811040e00303a4036003842510107950f6401d07031485c01c06442c00c0040c1c00030314030b2070070502e21403040c160700048503070741000b0f07010207000b41440c040554181a400036007000c807520f0001d446900000c04001030f09034050300f0031400300c40a01e02120b40034a15001030390340402841054445004100012454029840c04d0408881c801c0080540d40e07204104180d084070780e4020000006500b4400c6040b4101c4201c5034058420b000da180886840d032344200203411a00052004444001e80e400c070410102c0c0305000e6850001f50550300e541c1c400c0c03811420356007840d20040581c141ca00c4042480170100c030408a107488159241c1c04d149801300c0760b400c0ea5440c0d540003446071404160008000520000785400359608681015004030300784450300070a1000f911071701d180401c4141010a00100c07441d410f040c5100054002c0c4c61060342c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 503383660 1250 503382410 503382419
    0x50d0f121d070f0f080f0309010f0e09040b060f0607111020010b10020105090c01030e120f0304050c0a0803090108180316060f0209060d0b0402070f14240f0a0b0d0b01 73
    0x30442d45a900c031061070b0304a189806d441c0c09020085440e08442441e1894002d240d0100c00c0e108004405140c1d50440040b00400041103c2c10420300d01444003140c18090782c5c12000c1c204000391086040040240f104400c84040d182043c901d141420b40c82401c1164010b01080c0c003049902a6080e50701213944e4403401480c407142010070710703100d08012a10081c081c924000444983e41e88203450903034101a503510200352035030410b010410201c50b001100030f582780d280c03a14130801a00113032421b860500802c8428441450300000c40c0341119034a001860821050400545001e54014141043c2840c01200c00d441c504082c001046084402e85840591304c1e11401c01d407084517030104081c100c543c41000034248682e50b060640708440000140480c0d50b88112000c680a8010140700816020723040001700700300310b140d03484c1380305070070782c01c1c0450710808007030200e80704148110440000409480d1780400d2030a000c40412907448011000c001c102200e803072000c18101400c00030103480d41c2c1c00190042c00f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 503384910 1250 503383660 503383679
    0x28020c120604150e0d0806060d0603050313090207020d0b0a061214060106020c0f21060705120c0a0e01031503051006061701031e050c130207050d0f121d070f 69
    0x10002c400d00d441c20044104501311240c0d50300c0744081c0090500c43c1c80341c002403007aaa10b03411503042c4d800300307201400020f07507034a000c0d60741c0d810509240e0f2008402d1040030030000700a10945171003d400500700d00482c180c1d501e412014a0014040750340300c644031032001c81c8854400050b185060312030344d118100e01c03548400082c100503041c1c102c0011500140300403c4141e60780c42c44000d060034211540f08580340400450400300a01080c242c29501030401000425a00403002d4a2060444044650140d03262001480b4604c0742e866101c0c0840d0f0080511101c651281d032000017000141c1d1150002d654403500c990346819600b1641032030441d26420140701850380031002c41d120301c2c80c5e926116159415503994240c00752010031451301c921503219440c02840420040c00c1880d1002800c41075131512001c1411004e5480380e501610300388503420300e003140c0d0b900c6124044051820f907a10824102900400030015000c120802015485180003c659188041c00280300a00c000070000c50780030f19160072003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 503386160 1250 503384910 503384933
    0x804030219050901170f060703050103030f050705060c221512050408040b0a051902070e090a020a030212010e19061104120303050613020705160b28020c120604 70
    0x1c9802040d82a04018030f0321480c02c62410341d80081c46140e000900c0d01c483c14501854450700a445100b80c0302400903003078043d4002c5040c1c1c3d0103940c841100d16082141610300e840350800091690744030340001503054607084042d220381e8405200c1032508500e0050211a181007982020135413003c15101404590303042641d5544400e0b0442c018403451601c1e40380ca443d68040d612982d80600070000381d00700741503c00c0b0101d800ba00e2590300404401000302200a40d100c40318080c20710304500900100b08404000a051025554000d0046074101d04543c240b0014480d0381241d94040c0d0740b510b06040c607141082c8100315140e14001d429034203014140c01c0c02001c0e40e4600101030300d020b10402c014000301944520704400c2c81d1301401c011540d9115040400c400080080ca148407080c8081141010090045118501722100500040045848a540c02c5031445102e80354503e250350300030070720300c40c042d410940410807901e4016a00004400000324148043e0219403401a80149003000100007034844035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 503387410 1250 503386160 503386189
    0x607030806091b071b0f0602060403091706060409171b100216081e04090510050108010b071104061d0702010e0d08040b06030705030d11010509190b0a0f060308040302 73
    0x103501c4580e010000e000121320500c00003520b080502c41d002a00c0000d03000004009040320080c1160191b51514000d48414081c0c900b2400900d40501c0003802d52502c40807084000a040d020b080391b5160b0703004110040039110703c1180c0f0004190b145568070302c201c10240141e12400d421155491301c40d41002401d080b0444480d41182e44140000d6100f0040090007500107640020407036529400030028200c0c1c010b50b40e0080c03110040000c0d02181d0404940c01c164050a0325900c1d107031640d0b464000540d0140c5090203a018000c80038008072000c01c010700a19211350710064400145162650019404400a802116130100e504400d0000165092142c0b0206809031001340820384c0702124020062000548040e190704801c202060281d6400d108110080c4401811a11070b000384104c0a400442c2c00e8400411551030880000d0801d007000c50107207c8154020250000b6134101d80d1392221122011740328a42007590761410480c4910b0310f20541000d0b40c0500001915141755204003c080a43c5021 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 503388660 1250 503387410 503387431
    0xa0f18060803031302060711150a020c030705061c0b1002011b090f0b0a050c06073c03111303030e040507030b030a030f0c1a010f08071a18060703080609 67
    0x410900544d4512000103241c2d04884c110b60321401410640901c40800003100d502251450800440380d04100040154003069000d03140c40b008080304154035200c0300d101d1243c002808001c000019080081c1030342d0030380f1400b10300013807011103d40841c065281c84110000903030340d034500d80403041d02d0904049001607981e10303081c984607040002c080d8001d4464454200c0405c00420842c07001402203089d80c0d10301200c802201c9582c903000c1c0b4018000c600d802c40081000404001c6245201100416000c50b550003070703c9807084600440040300140342c2d140d229201170f4014050301c03220142829402c0f00550207641d549600410b204108030840304c01600d4441450714102d80d071103860701d002c02c170040072582604104441e00002d03030341a038540e5205500181942000580150166800042d0301c1c162521820484521030300c401d00c5641c0d6400c14060034080301703010205000419204001000c079496625000302c00c2c0312001000c00d03a2074010010403800315001200300521801d000510075400030b001c42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 503389910 1250 503388660 503388667
    0x3030f18030703030917070f15140c0703020c0a0e071b050a02040c03060902210c21070203120c0a180f0303120b030303100914040b010506090a0f18060803 68
    0x54003140e59128942c1d00505040e1522040b2050005110002d10050b001d259160f95989080c0b4202d58401c804050444105031400c0a00302000c2d060301c50030407045494032001180c1d850355200c4200580105030200c003140316100c208000c680783c1d42e1002c0e00510f88000598124246144041d218003825240001e45111001021002c41e0000070756022107901a1fa000a480c00d0b0010106c010f003030301c3d401c03c401440c00000c0400b6140c0801c0114804015649040348254441c024150610301c6030701081c18040381c803204a41c81c1800c06400b169009065401143d28201608460100c2d00340d0031220072034070900c0415440805900910b43c2003403010600e2012000e02c0c108418407404076081e0001408000000c480d20000008c140e0265000714801401c9a48034a007070414103000d84032a00400e00c0e03490a240b0f03420300402000c5011030060754003c4901850741c2c00c2c1030030321100d03030400c20013940d01002e041c200107803085101c9107080c05400960448104034000d0320003c0300762000790380711046650040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 503391160 1250 503389910 503389951
    0x1005030a1a0934050a030e150c0a09090504030924050d020f040803161e0510050702030d06080106061403010f05010f0903081c1a09160201060801050903030f 69
    0x15400207501c041050403050303449040f01d2202c19500e00440030311010a803680401d04185810002030104020507590920901c090b00540e41d0300c0e010301d1000301c001a14424007041c0640403403800b80909445903d032003145141e59000c00d0342619815141640420100700090003042c00003040da416004001c451083c1840c0c40d228010010300c40c0250608007182d0203c3d4010910b1600310440300180b556608132521070000800740c402e24907144200300d48100c440c082c144a016501c2000d00420f607040740c054203100480550040c06001c000b420001180400c10000522040381d101e9200981203900001800d02d040c020007514440102c100c10800c00b50a1004000c0804d00402041c103640d420320b010120755690f10001e6450040c60742000302440000300351010041c1400c46140003d0545070320a000c01c0050252006540c0e110020756500044880c00103205448000110045180710b44000a005580d03045220708403070040d50401c40071740002060100a21a01540a41243c0c0540c820f0344030f02d010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 503392410 1250 503391160 503391169
    0xa150212070c031e11040b011107170f0d090e040f020d06060e0702012c031e0c01060b07080315011e0206010311010314070f1e0201020910090f060c0602091005030a1a 73
    0x1035031211b1007030345c80d440c10009591003011081d1a1641078011a0801034a0b002c4c45050108080d945001500c02c0110041c140c00c000500c142201c0550780301c9510340c134206110f184105c900148143c8540c80d40300c1c1d440c401a120b144911600c9802280001520b6003803521420791440058004001c5a051401c1e0042d03110b18100709003541090802d0544504040700e04407415402000801d43d41004800160301034aa10940203041164058000700f098a41311401070a4a00902001500a000030300000e045201c0a030106144800141400c486a0b64000a60040301001c624128016005640100300700301500d5a81d050541090034140803c3d1402d50300714290b00301c0140a2401c001c500d04110007114041c134400d82c00d80c002400700d44601c240000c0302034083e43c0070543c250f0061350103a102c41c14292040c0403034800d807041807040d54041498000b0849040425200594500d9420000b0141d82d0f0345401c0802c0c00c950658070317140e4507480c009140c98121790b940c02c04803907005003404104129648 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 503393660 1250 503392410 503392433
    0x80a06060f14120a02061207080702060412032d0207060b040e2112040609030206090d0807051308060f0f1308072306090304090c0e0a150212070c031e 66
    0x82c140c400540d0407484810880c6044000c11019420440000d00c0d60084640f12010038030403071460301e50041ca9222a5030480e619141120061b180020b140c029000c150b110390084d1030311910401070209034014420010901303005058442907403550010703000e802c102840c016100b07c9070302100c0c20040e440f2981d4115481d100f0200c1c070641c2d00c05160040310790840c170321410f03175501004024415140c0d2806140c260024132100b0310550151003100e00245a03010000344d40420000306603909038803034540f0307007003515150031440c4c01d0120840e00542c08901100d00f0007070180f00718030344418030440303040640c1c407404000c001400c450107890898251801154581c01103480043d44038190310340c01304c80b688649484440c051510741450042c2400c5c01000c0c0c6000005c1c00c2510708511041000e0341c0209019109000d2640ba81a04000400c0d0b040007601038600d0101485503031170050700c4100100400182c01a44040011680503010b41c0080c0b090210309034a10741113400383e4000710811212078807401c01e50003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 503394910 1250 503393660 503393699
    0x4092f0a0f030f05150a05060a1202101803020303070b0f090703030804110f060a080106110a1e06060806090d0906090602031b070902070b04120906051e1201080a06060f 74
    0x15403016440f41040703001c00800607041140c148096250902008180c0502401d0315000e10810b194032010410004007001106403e40c024542059981604010f984054401c0b4031f01e07400714142071340040940c40610040140707521034000303450107140c003106072034017030401404041230303070740546400d00020360440759a9400c01d4011070a08170406170200061030f5001090031290300a400401c1170400103801a4505040e07800c20303180c10b0000b800e90001d00d40e4404100c600504071807540a01d100700303610010302205c1c40c50302550000c200c00351100891860100184d540501c0c4c0e60107a080c151310503a10034004c1001d001c6070301d8080da51741d01d81440213550b8000c5111030003483c0c0151580c806002c2c3c0400c0303258000c00f907128065403100058148071014007801c0702d054848403401401d00904500c5015a0300c20348603180c0300c2c241000308200c400d48040088120040800d4001c00808490410100c1007034020800c0e13500a00701c070909407411f0015295554820410040000c4041c440704a1902c2443c4035003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 503396160 1250 503394910 503394923
    0x60804080c0c0409030302030601080a0b060a2d0c1106040b030138040e0f0c0412050c0a12062406050d0f050708010806011205190204092f0a0f03 64
    0x8414981400d03080180090110f5485843c2155010030075030150007443c4150400d03250140f40c1e64810200d0b0054400c0c03200c090364080400c100010703c55008071041509910303200100e08103900c0c3c036900714010000c0d1103031800c08100e04003140020002642104c00b415081503c000b420319261604418039800180150700e0301c0e0b03031504e00405d480c4859415513034000350f606a007002004070760070b2200002e074001c1c000c0300a120f083c0340c00120309100c511010740c052044900300d2440c017840c00f000115a1342c4603040c1200c0034010f030110500743d9075924400310068032201541c084a48054a0031204840040480f60444081c4980c0c0340c080b0200181e4480895001c0d052050b9180d204815203001004c0700a18082d4462400e0140184a0340c402e810605a4041004407803035030742c9414844000ba00b0f240e1004096070b001c02402d40c03c104c2d411144021244c4040c0010a114500342c1d034a42c14400d00c4060f502c000025840f40c0a4400055108070a2070b040903036190103544d0904c00c0c0c0c100502031070701015248 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 503397410 1250 503396160 503396167
    0x20a051b030a05010c231306080c040b03040b150306040b0403050a02070f09020d0b09090604080906040302130e06011401020c040e030c0604080a020d0306060509151b0105060a080706080408 83
    0x20394400344440300550754014020800f80c50810406000c0704440351501c001140008180500049054100d43c000032422150b01c0c3c100780b81007004c44d0a484010b00c1807820401c14400090708500d140c0c00740d40503521a0000d80c811786030030002d0340e6680385204104d0340700b0fa01031400e00000c50301c454000d50700180c061900540d2420b8141d002d07440c0c400d0300c0c0d0140310020020000040c04003203507409807500e0070541d00d0031302c16140c900c1d08011407020107660445958110f078000c01d0014040100811125901070107150401d0303600d80020303010740035403290308001a49900005412001c24020310340503100c1c28010403608918200001e50b034190541000c0c2c000d0b582c0b107442c10003c1408109480c9049821000c03112a40fa0a01c2c002085401100003000580314298465601900900604040e82c6141c0d0350030f800c1c210301004001b0b180201514203049800104140540c000307840300071500d00d003603d400100301e0303040100038407079500d40c598030003029074100a00a0003a41d42c8980500e400c1a0002003240c3c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 503398660 1250 503397410 503397463
    0x316020f011d240a030608150403090902090d06050702060f0916140a0f240801050f19030206030c130f060e0d060e03030106210b03100f0207060204030803010e07020a05 74
    0x24400018404120f0704004503065400c25807541040c0c040c2c6011000f5107100c4145548490f0282e03200f9180107000c20402e0506201c20050f586c003620710b01500804110700b00d0310300d4a030181207902c26110040140c01907020000b00c100d450224580005220b001044804640305410856190328001c00c0c085e1071201e004240306560703000c2590050206801c0340341c2d50564030440d89500904041c900c27a455190822140045070141c0c4400341281c102030112501190070408028091550600803841080d0f03c0c0c07404800360302d820340958803a41d920f020450369a00301640071650501c3c541d11413062506102002c3c407402d60711440d07c541a040a480329214a811882c09001070310942d15182040e1001100014540b0741c41040210803030032055884003040f103190441c1013501c0940c42e200390994403c14004650012551141702e072007044072001402c00381c450b580d28080e40c1c00740e4415035902c84e01100510130001c410f840d45420440500040007000215236900da1100c18100241c4c91104d594600c3ea070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 503399910 1250 503398660 503398699
    0x6091a131718060406030615020c030c011407140102030711011a12071508041e1101051308070902090432060a0914160f02071e080316020f011d 63
    0x201d00b0400140016200e40e00e490700100102020300c5101510741301c40307024850440c00443d8940000001501a148100c0360600540e4552200200620b851750100401d00c0803545803030600107943e80d0000090780c2c03400c050100501c200114031000700325900d4111420000410000c04207041a000d0f14801b0b40440181200c41c02c3c034409a000001001d0749004a40380f669110007450b02c05d0707105500e0303803082d40040c80e00d0082c0c01c94401c0c0002c140303000064914000d503001c2c00c040c0c15158200c4141a24803615250b070142004075641c032504d1800c1e004541e6400c0c51400380151f64032449070032800103500040102c01071900b201c000340f8060b21210b0a0200b05c070768a441d0201000f82c8801031050040505912001d644044101d60080402500c00c005440451141d290702000031115401880c4003030800010314680c0c0d808046003001d00c444000006921281030024003214100d038041e60400c000c441c0140012004006000d50401c83d50703481000c01d60705c0159000d0240c6034151405040016180e9001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 503401160 1250 503399910 503399947
    0xf140a050336010f060e0c09010e060d110418050c0307030b01031808090406091b080a0605091006120c0504120201030902090910230105010f0c06091a1317 68
    0x80c1c040c44466002c12482501508040400001100308220081e170780c83d18074000d1170080c2c40800105070100f1031000c0c07030361003284d801c2c460806c0144200e18203d0b0740300b110812a8101404c01c0c8402002003420441000400e0910701c40f14143c0400380182d01c2d0002201e2158440205820141507603501401e8442e4480c0c0d0000c4c22907000181c3c1c2c441c681c9424144100300c0c1e001200864461822721102144110307031409404510034107081c100584a4000c2e109640c2004020510800d85545400018540c2d950004d03542c0030725101211800070500b030035001400902c2568140c40c45a040403107e00742c1d507900604a4040f40e0b29100c3c40803200406200481c09440380680c0a076002641c038051154580c000708034060702e0950b5610802108900d00440103200321000c0501200c02c13500c1c0010441d80d4080c0d07424003201027075837405c80b0f40d15002da07030307044200c1d5148001a00e145044054201001e20860051034008101e04200c5021440b40d54500f1700b842400086820001408901007420348540c401d007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 503402410 1250 503401160 503401231
    0xa0203040902030c03042102030f07020f0301020d0905160b0304060203041401090c0503011808030402091003060c0c0309140d11010504180b0312030108060f1302040c0f140a0503 78
    0x40d956070030641452075485d001920103840403001e103000c8021790a40301d00b548900781381c2600078505010340c203502840c41d504030035426a04500d03240313062005580c0c01c0c8020b104514044900280b441403e0504038540850040c803004007802101060000134a0075003941d91142e40280c01580da65a145450b11840031034800250896090003000e01c10400004d41080a84100350020420031801c2e02d04950b0a403020400582000c20401c003140c058100354031403c0d4000881800c1440e2283c2c1c84e6503030001c44ac1c10464400004807010003000406a103c0741300002000d5040c0008040d140d402c00158580c803d103800200a000c84030184601c41e4019019030b8014a040950003408503a403060350700c0549800c910142c0f0070f000d0401c60300c101810b010182c9069460000c010001076946d0400756290000c0034103554200380c2d05036a04c40041e03840b8000c00c146010141e6032580e00322102c0e1805081502c010407440e03060702040c001800200d902c5019250b02c4050324220669034885102e001e425001075208 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 503403660 1250 503402410 503402429
    0x7050109030e1e130c09050a030b06030606010c05060601271d0a061a0f0714010b01080a0e0c01200d172202040f0f053103090b0a020304 60
    0x20800506401c141845980c0070241c886030500b4101403640c07a07081c030411443e140d215071060248698907a5543c040456042c842c146496110f80311000510615059070003203e440039600c0c208115030030b080c03100a400c85e40030308010341d514001d5039409071944001002039040010007e00d088140c1454100303d0302c035800c1048611030140d00c41500340010590303800249040440300c804510000c0c1e440c401c10302103521400c4c1c0c0b080030112403409030f94036500510070420009814807444001c18824580074105042c01000080c00003034040014080160080c040f1446038a810200c0c4200303a4082901c01340c0340400d20300048400c0700d2403542030b40550208600403a9100755048880071a80048a1040c20410582d01311015911070b4008030f0202188084c02080c8401050100010304040c1c1110350b01d41d42242d00444d00642200c0c0e600b00f01c61b011030708142e4002c06124040c401200782c6003405a400555500d07003074800001d1300c002d055006075100e0980744a00000362414814424020b46000c1e101424 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 503404910 1250 503403660 503403671
    0x90b070507091d0c03060601080601050d06050316060f030908041403030717030709120203030d0b03010902031c17010b09091b07030201090c08150c090a0302030708011401050d0804090c05070501 85
    0x100400c1030f010240c08064810310985502c12458a0000b030344502c1840142e40364001c540e83c40004403290303006110b000c0c54081d11900e0208103580c007845104c80c280504070003460100d2502000504008854429105041c42d107001c400128040c2000c503025940022800c400508140b00481d00c2d611403003101400301138960b00841700741c8009000442c010001d9030350340c0c46480d869100c50480810000d50081d4103620030005840c0000341500030aa00344030040001a1f281550340101c0d0914051000290130385207181d2400481c01d40011410b40c0001032030b400c0d01035640c141880c5010501c81c2e0440544902810400501c6c00c01209070045110012034030350700d803100941e107801380c040e14089070210342512100300d0103e114540000c54548800b020b045c134400c5500c0320380107041d09901060040d45c110309810000300240e1000c001260081c42d01200004010344500c40c3c0d82c85012042c0c100034030441d40d1400c0c1d4000b14074540103503070071344800c60400244034282c0682501d5030700c0703900c0000f4815401c09 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 503406160 1250 503404910 503404931
    0xe0c090411040c1e180e040303051006090b070b04050316050601180c0c020d0510020a0519020a0506040308060d0b040812091603111302041707080304030201090b07050709 75
    0x400d051507000000d540610058101010507110180a41004076025042e400000c1e51240f02e1181200c6510540d62034002c0c01da26030003224000d1004540c1640407a80307440070300c41107110700d0300540c00034822840c0c20080c45007001660202c51103042c0001d4407540908004c5810702906000311844503050060141601d81c851425507180d001c240314911103501030800e850948000350048448240d0141c2d074585d042481c0c1e500300020046510000e40740d900c0f031111000c00314507044c401080150560340303600f92102d0320700c828410b0140c3c410800b0310464004143c0000040c0c00001d150b50003e078141000a410f5960801103070141c1e444100c0582101032001c240700c244541c40000b042e04080101001015648078603142d550341d80d950448401a00c8408010000b1907410140070900d0b0030300511a0081d1f0103a80c01c450182e80094100d510380380d6854912400e040000c001c00b0004109020180d41001d14540018041d081c01d48540729650400250600c1003110074441140a0806103d08001c901c40b41c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 503407410 1250 503406160 503406173
    0xc141e0a03090503010b060702040203040311100f0605030f0a03050a120f1b17010506160209040321050408040e060102100e0c130e0601050609010912050607030c080709090e0c0904 79
    0x344005801103006180081481c0c1010300070400940300241030345207840415400e01000754002002601040321200210502e0b14041c400402c0e0340c120701d40041064801138042138115445540850700c250b01c40303220347e00d0710b007000300b400e41c24650141041600d805c06000b00707072040350303403104541c000519122882c0c110409603030180148445580309021081c40030321096914413011400300101d94040b0707004220500e04440101214080500420841c0200b90701051b01594156800c60118041140290f50182c0410410300d11b04040801407245041c10389621005100c2e0307000d54401e045103080050a145d00030083c00c5003ea4a1f024204a040c400c40c5d0010307103c000c10125648207814400c85513800b1100e50045021247e084000303000d0591a04e8200001a400549842e05005030f05800040c000101d401e031980440c001e0b40644140c2c548108010100e0b000000c0907018024014140002243c1c0041510140d0303550440c00200c4140180350103282003650000c065000c1d14040400c003c0205 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 503408660 1250 503407410 503407423
    0x70602030301031202010b150c0703081306140a0806040c0509030f060610020a0308061c02060c0d0f0f0c1112030c01091703062b080304050102130602010c0c141e 71
    0x584911340103c084840881c203035410090303284e901a060620f01501c50b607103007005007aa494034004540059039a9590b02d9400c0d00b04c2480c500c00d440030700e0700030041a0340250245245d240e01c42c0401f4901400c080e0040c0189002821036400b95a4841c84424400d00540450742c540d58014100c031410b1007405880740c3d81d00f40413100c007401854105c8000b82c0c0075000007014026280e15850742d2100390750b09014080d481082c050407501c0d8100045500025031241002020480040c1001e0100b528001034050f0000a0503005001001603888441d50703141c3d4440355543c00c2c0345e40310550b000d54074500d01c000fa104d01c4101003201d8280c003000032046c0c080b00055020074102842004070701202c009440c1d600786580000c4618582182e002d0307501c1030306000d4190750741d808921807241040d00421151a00f801d1034001703c8049440e41e40c0017030302c2c501054009074020000c01140c03000b0712002c151040300078001407103d80000e003480108410070030b40810a0010202c54120310f11002c62214585190503603c80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 503409910 1250 503408660 503408663
    0x1401020703031a0d0809060708190f0e0a050402030702011104140f0a0f062a0b0a0b1002100c020c03060f060a1d04031110060b031501080411040b0d0507060203030103 73
    0x3d103401140c20b66080002d09010801c03900a1880d00500d44503281e684096001e11107555200000304080000610140043e0195442d80d080003a01c0e010b160101400805094203140140083d101007442c4585d90304010704140c0788281c42c0544c032078440c3c080c00d90260011900c00c202108012070040b80e01215182d00043e6440e04072000e4410403000d10600c001215140142071001d22800001d1102e980140b060120880170700c007801d00003d483c1ca00909408000d601d00310360706100c06087c480d140341107000300c2212100c200d507c11001d44034400b020355100b9200d100c40f0f03580f54850082045041c004e0100d20074066002d0b0035690245040d02840010900803150144980c00320307040400e001441080039048050b41c400411030a4a45450a0f50045080b0030008213500c00c0d400c440d0740c0398006000700001000301c0c441281c0c807800d000e00380a42180103401801d0420180e0b40030400421302414107568000e5007900e0020300d05005e0b20202d606491500b4000d081c130310a0b2070000a000e1f500000031412039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 503411160 1250 503409910 503409917
    0xc0b0913052412100903020304030f060b210703030e04020705010204030602030f070507051506040204080d0201060302040c2c04090503032d01060507020909011e0609060b031b161401020703 83
    0x40b055008000c2d8401c07010400300c1440d480b5032615060b5030004d50280c0d410301d009004030b030f080c295641d680c0044440c25000440c1d5250719080c46d02920700303103010741001c4e90b083d01c0a07001d500141010880e5a8007100c0c40f014040024005000c0b030944c0315a03044582d5290008025035035107481c0d00b17100000e50310548180e00380760314840000d048030303120f6010340c0c0219a00c0b6014011107401c2c0c020800074004058110740e407080d0b00f08000034032150300304901c90010156400120f9442c0c40c0d40100401c80320405140360034440b060034046c1880210041c4080000b03138414045000c910424003180003000201c9004002d44400000c1c40207403d100c024400550f095041482d4843c1181c2010000402c020301c1460082081031040e00c1c01841d08560290b4001040b80001170321181e52041916001036240001c1546a81c5010034403444490740142e00142041c05100d42c590f003070000c41f40040e851300b1909030b0110003002c98144c07012505400c844890b9034000d80c0301c11100500c601118001e520404013100031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 503412410 1250 503411160 503411221
    0x8040308152817070b0304020f09040303091218050d08040b0301030f0c0807050603040206031305120a03140c031914011805090d0807181503061a03040c0b091305 71
    0x200c0c03c040c1102c03c6448080010704500c504d0420041100c0d080034200301d03400154001140708649600c0b6402c0c0c0305034001e03500401c90004a0074614201d601414200041001658a03500301038610145501100c80c140e600101506007820080d0040c020340e008200b900c40000300020030703c82c03404112a081c03400344000c0d2501541d03d0102d99520b100c00d100b07141c0c0001040c00058013519004004e1540300405c2000035104201541d2110b05062041c48807010510340442d4602c5000e03454411481e1301c1e01c080184050702e0407c60840c500c1408001d0400981c07400c3c40000b01041400c1d900300a41c0300e4a01c0254040c02c1d41c6801c5044c0008114130a810744c85841e1400061014200240d1422034014075140c049650b225110120385d41240f00d03200d0f40030384080c59000101c010388540070311390307485090380c4c0000c0050030841d0214201c0c03500e00c200c2021040c14024000032610425580d02183e04400380d45541c0d01d09480452a030f140c40191050000b860729040005d4811071044c11011401200d83c071182 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 503413660 1250 503412410 503412419
    0x70602040311130216021005090a0b040812040f03141501090603060b0301150603050c040e09030304030801080601060206010b071106070609021c0b040f06110703050406030c0807080403081528 84
    0x4c80c080c007440b82104140800013000503060020b2131002d041e005140c03041c43c0100c0308012403144a51070303126484d110800901003240740000d1080302d0716462643c00320b0303241600e40318401400c26258080584203080500318901200403c1106020f4105040b0b01e811403503941d0b0a100c001404076120940d0f41c01c0c148502224503250603c108848102d00c0d007901e402c11411300408400600000301504c030300c0c2c1c00070000425601240d1040c148500c1e5024002c640c1c078034051600402c681d006910003e4298001c1d00140306998000c522036054607440141c2c0c07a29812181007204c508010040380e540c00241c00a00c03041800215004000002d0080d654480c2401089228003410501102c018200010180100c1c00082c1501201400d650065001064003501c0000551030380d84408000c80114000040810070039405004000003049181000c0b00c00380351200c00074000080091008042055800c00600c1d524031442400340c030600040d01c0b854181200c40383c0c07010a84244843d004c0b82030100000003a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 503414910 1250 503413660 503413699
    0x606110c1005070f11031207120e0f1216050a0b040603050601030b0918010c020f030703180905010605120f0115111c020703030e03210319021809062b0305070602040311 74
    0x100c0c2c40b54021a4484030600c00c0270100d4040c8201c3c03001da540004909261074050780d13002e40054040c1c000101412040c404055a4a00071160f5400315019801c6500100a0800110140c0e07049070300c80d0801107a15640c5a004070018029202030b030750b2011843e0180700d2080b44140400e000c2c1210240200102141004180e0b60383d10388000c0306030203034030800985001074880c1720280703003c00074403d036550361540310042d800540e4001d820044c0000d00100d0300450400c09080c1440d080b4480e51000c0c40c481d41802a60400549100c080b4000d125040031410660081001000d0090068694044403282d9001000b51919001e100583c00143c03001e05a0050f46000315402c0703160a0820a801c130301380180080a000c5400003881083c940070f04071520724407503003d40014151050710910700c00d5400e04a4040040750403014001718020302881c120346081c0c035034051003550b40d540140d9204451600c6403400b281e42c2c0c824414010140c50001c90000104554484442c968100403500c0c4580703a1213900d01807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 503416160 1250 503414910 503414917
    0x90e010c080105101b05070b09031b030307171e09010207050306060a0501081f031b14010c170c1203040b06240a03021b0609010606110c1005070f110312 67
    0x1079019107816102c10b40d131401004a250000300702c4038581d104010a0300c1e4103080030040d600c0701c1000d81000401048070f10341444044005444101001450350011020030ba0700c1c0541c28000309501d00d092050422650754005444540084da01c180541c0c43c0c62054207030443d00040b016601612032a1000705440c0b0b401302c1c000384070b90750160008038414503040044800c04c002802200d00c04828150030385082c0800304004001d14040d104003440081000070050001c07066a1000c01b0390548042d60761846c3c0c0c0e020382d142140b0f81d00a006d00228500403014510381d0721610001450320700c0340008010904610f00e000c3d5104901821401d103072a550b0310b0500c990054034028045601421a002442c100c0d00d1134080d00c04007480c1d240050420140c00001380400501040c035404580c4810200541c280007406064043c088515118550342d402c0000f603a903600400650501c2030403003800003102180702c0c1059594030b42d0400192400b554860410f025103070140201c85011307001e201140d02a49000000300c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 503417266 1106 503416160 503416169
    0x906160b190c080a0e07090f06030203100204050d06090c0b21070201020906040504050a0f090f0b0703090c0611071a0909060d08120c0405030106090e010c0801 70
    0x4003005550840e4203884128248007000d90483d0f84050001c3e0070080c03041e00032812890b1200345174204449070704154204d13481c060002286000c6d980280088900a40669007603809900e03000e4260302c13440c060039802072056600c0c6170000d5070a034001e4000303a0280c0005516580c80315044a82c691080401200340ca46020429a5440c001c07004181c1103006c90000714604004200403902d14080c038420035100b0780d516000602e109425411035264010051f80c104008182e62030402d210550880c000e03101040d6603800201c0d445d0092044076266500704d41c0b600b025a24001c02126219450010405640100d00d0002014051002c0c165031100c8110300781c036206d0b28014140400504010070040c03050000b0031001c1c0200e8181e400302d48980c15031b29140c3d9482d90f40e001c10b1000c580b15a500854056180110005021040398482142d0140700c2c070003405105c03034054040303600613001e005 = true := by decide +kernel

theorem cover : BRFrame.Cov 503237410 503417266 := by
  have h0 := BRFrame.cov_init 503237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 503237410 ≤ n) (h2 : n < 503417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
