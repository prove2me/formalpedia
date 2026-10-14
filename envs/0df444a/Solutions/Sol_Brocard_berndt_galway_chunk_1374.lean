-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1374
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:38:51.139178+00:00
-- url     : https://prove2.me/submissions/181fdbf7-8a76-411b-875d-61777f2c2269

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 246942446 ≤ n < 247122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 246943696 1250 246942446 246942461
    0x90c0b0a180321180311180c19020f0606010305040c210204050124032d0f060506030709050d030c050d08040308092410080f0102040501140403051f 65
    0x121004114a4807441c1c0503a00f90002040c10f661400b40e1110016000c1c00b81c029503160307004681031207a00529543c0d408086201c400c04041e00042566241c18292000303441450007030040391070068680080b40d0450f038160188407034000c00c40d8001d14500c403800d100410001e810840031301c1c0100711035466050040514a041d0302a40015019890450030300141d4600422011310884043c0040d0741d07a00101681200c1900d036a0305100c403901540b1090601941c0001090300c1e480304130350444210071b001e0003500c0c018118408241038490342440d0541205120b40c0024000c21900749055041040000b4054045406818040c4e40c00c400280c0030706025190b940e80c8658440204e0f96120080030009001040070307102180401c0703c2c0e00201d9004003001c501e0040180b0034109400000341d100100e0301804001906015054501c4a00803072081c10a0010026007900e11001682d04e034a4074000420322034081c0c1001c0c4648905000500c00550003280d84042103000da2801c0ca8045100700c1d000e4010b1154 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 246944946 1250 246943696 246943727
    0x80703050102070c0b040b0a0f12090506010305210307050d021207050d151a0322030f12091a280b03010b040207020603010312020a06020a0302120a090c0b0a 69
    0x4504000081120540061103554490800045515620040620a07020b5070003070300840c00303007070001035a0203110340c169240a0585180c14100c4400c0d022801c0c0899041d00e106030742541000d0014014000c0c200806070720304034000c00c0e4042002554600c3d1400b8000544040708000000401c149020440d80545078541000c0c030080b001800c00080182c40e503840312924002841c1044005009101c080c16030784221041c008141c0700300d14900c4610003403540001c00032148541c412045a003451100b00c05441c1c418400d440d0035a02e030121480261000c50001843c413000c9090400450000c0d05041038146610910400c011007a255256a01407175019520000404081e81c0c039410318043c02d1340c0210304190804c1c0c000300080ca004d02d0501090b44501075000c2c3d00080101b0041000407502c89101915840d288140c0f4011140d44d50b6072810b90744400c0c541d81c0029004951851250102040e0036000303103104400704100445982c405484540c0e0b84906402c4920228540180c64002c410360a0b04081 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 246946196 1250 246944946 246944953
    0xd0b07050c0607030b12070b0a031812020c12060603031903140403020d030e0307110603100b03190b0306090a081c020c0a060522060b01050d050702011a10120c030608 73
    0x510800090041a49468241c406ca0324030241c00c10b01e41002c030329a000d642c68104071900c1e004510b05c0c243c1c00f400d5034034000c840482100c011100442c04500206110710b503143d014000d490340070700402c82c00304541e10407213006400ca0000c2c026995000400c44030b14025142d01e03000c0d0760240f4182980100300600c41c07107003000000020007003007650118021070034880b9502e0070001810300001c000d55a000d1844000d00c44007104612900d10700e0007402443c2d000020842039020705489405911540d0815603c4108040450860504652240c02aa2914441503005040318989040643d9461100c800060841000010307420b00c1ea90712500d10401c0c0000c002000d55403003000028980c0e442d40e01c0c04060f01c0d01813810740458210b1480c003c90040450035103000f482510150786581c00100300810740c140c18044104802480c050b628015180700c2c45040d000082d21031140042c0c80b15070040001c8941c45400c1c00740001081c10b070400402114280d00b02d41c00210504404000c2d0014030b52904203103020711 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 246947446 1250 246946196 246946201
    0x6030204090b0a0501090605010905131e0e0606010c0b15190e04140606060a050a02010204090504210e0d110d02121e0106050d02040b0d060e0304030b150d0b07050c06 73
    0x10b400d14665000d419503420401081c1e0361280424200d0b4202c0c09141c3c00210040c40c01c1065203054248040b80b2403600e04002100c024070942800c00000c0c071074041020680b18010100502410f1002d507612040c20f00304121604141d44c1d6640c2d1014000384105081c5071140e901c000203803182441d40b03641d8505000788580e0301c3c2c1c84035100d1504d04002c42e000c8030010b07903080c1c48147e25032020071500e02036100a040c241c02d0030f00a0005942c0d90f003200035032008641d800e120014503c0c01500500d4025809400700c0d0140740610074245070707940000f0515109010b1040d4010300661603541d80600c1d00c43c3c20150200d0984101c000150175525280006580b081802d0290010f8031004200ca22800410034940140e005103800c4c59801c3e100540310380365008074402584809428603400008080390000d012525820b004da6400e4111044e845510b161079001060500c108030050741d0040e0002e0300c4501c041c0701c4507417210010320202c411f00002401c050100004c90740d43e601030301c25500940c41c003005440035031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 246948696 1250 246947446 246947453
    0x10c060b0319050610030804030212010e0a030f03050604050420030309100e090702070303080106030e0a020a03080901094e060c0801050405090c190e010803131509030f060603020409 80
    0x494158800355202c0c01001c02003000741000000c1d07017044035405410703207080c18516000c00c03000c4001941d01c1103080d502e0b01c0700290000c1051000c00001442601e4400c0c43d40030341d6900604540e8010311030b03805186800c003031001040da0f5028050300703840111f2480340c41c1c07181200440d00714017070f00600b2a040843e59a44402c6a48c10800070803901c0401d0b07607404d40d40e641c1c214080340c0d00e050034030014020683e49001846660300c660045080e00b041c000483c0c020703400076030106044c1c00144e801550408801304240d002e0350381c0801240d0060030b03402801103415a0400c1e1004a0315584a04514200201e42145025401000000c5a00407040388507400d00b05145c24800d02038419090054000b9403194008985490030b4031809015081030f100905203201c2c480148189140c46883c012540442442d0000f00c894103000000d0191407000c016544556000c071045450b240c40c0d03041502a030040100d071030407055202942c1d004403500300210300240546030510000500f415040039401c1f07403c212280701030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 246949946 1250 246948696 246948733
    0x20313170c0a03080d09060b12060a0606180e0907050d050a060f1b0e150408010b030d030c020a030f0504090c0309050d081005090903040e1003030e1c02010c060b03 72
    0x5140400382900d410580810811080c0d00b6140002080c0304400c0c0008480580264003100850b44117501c0020b4030440341e00000e40d8481d0b54800308a150b4440800c00088000d240a031400524140c144003560703621010200c203100445004003c04404900c00180000c0402c0164400500002e02f6040083c1814102140c845c0868003003500d07614101542d0b42210007892092103003800300c180c001c8103003c500e903004036506000b140b0f5031342d8440042d584000c45003000ca001800100ba02c0b00002411500420034107042c0340e699804001450303d000400701c42c1e183c0203d020055a0380c545044660724040140543e000c0c0900c1e0001c5c03940e5841c3c4111443d04942503881440050f004000712025042254000c4480020448480302c1e00c044000c000c000e2800c0840c016070b040341e110800d40b4105a21503a0080348001d00b21038400d0080354850b020030506800c1100d0a48024050b00c00c0c2c0384117036024148000081a42a0003410068050307210b13000e20501d035200038001c40c401020303100980641d03a0701001c2c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 246951196 1250 246949946 246949979
    0x4060b12070906092738060703050d020319110c0f03040e012603040e041e0503180d060e0c10020604030912060e01090809041d060402090709030b040c0e07020102030603120901020313 80
    0x139070040e20700c4040b13600c0c005048d111040d6061703849130728046940c1601006500054a000702450b03410030902c41c0e0f0081da000706e440c4802044202900d501318112101d00d03044040d03412054a0704104001d0102c030126103846815590071561101400f4400422400000d81ea60400b1115000200e4041480b420262030140264095903d01410703914030781c504901d42c0300c200e80c02409a8420420401504a840e24000500c80c000f0f16034100446192641c5065a804600c10740107500101d0b41c012705e500d401d4604941e41c4615100910440c40e055501030f21203411400340070902c0050703440141c10031986400102c092038144000307020855044c60460000d401a40c8214856410031a240702080750141c0c508012500050040c407042c0c0b615000c0c400c40030005005070041004400d4048080b5410007101c5008070702c00c8203908005454114061002540500004110b9004101b8081190b60014103d20520609490b0640c3d480007d80140c3c0b070342c82a51180e81030f000c030004c800a0500c660282d01d84 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 246952446 1250 246951196 246951281
    0x3060f09062412010608100e0c160b090f0d0f180306020a09080607031e05041b030503070b0c0301080c150d060603061401050c031804060b120709060927 67
    0x9139813620025501034130119070f070750703c4009049001c0107a0b5125442c03564102c20441c4501d850f04007100d801c840c01080341042614250406400e020045108100b21a40003140601a0003e0300c200100106503041003030008040040103486540c0c94502a0640b0740110751003581155100003003070002e0302c0b04095108282d2103000d52400511458041d01500200080c034458600110000f641280010400608156400c2c1900c400c9240020010b40545014500400c01152543c80d145003545450310000e121407041d403428401000041000079102000c801c08549507010981c159003080b01c00c0c0110024603400a0411300001105070b050703400340c429900418000003050316600d00541e058811004001a6648100810a0700b103401034005054a02d00900209a696860b01e08460726004580715849225107101800f6095400c46211070083c40f80d800c120740840d24101c41c4505440580c1c005110040911503034044c000100c0d4081c0c0002030807200c114500c0d491a00c2c482c0303001e904140200303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 246953696 1250 246952446 246952477
    0xe16030605030f250302190911090f01030b0103090510060810060b0328111b0706120c0c020306010f080706020f030304110f041a031203060f090624 65
    0x101c0e10b41004a041c46441c2c0038803009002e1410314281001c4034643c00c00701e80702d8030342c001c440c080016510301d00c940d6242603090b5032039a407203410110350900301d80c01d0410814a060b801c005103801c0b030320380f55886285a5401d0030b0014080300d0850058010300220480144240100840349004c4103081d840f030b40585581e8021107201c1014040314000b25280c0780100c0c1c0d000d444c148005054100c1041d800d28003c00340050702c0c3e040b482c02d038405a06440c1000e00320800303c075011400104c00c0442044645103100900008c01c0a145400e00c0a0040321021a96290007525a440c03103030300b1030080d50301040c62076001d02205d200b90b82d646591151611603000d1304d82940140702d000a4814400a10328030044d10300805103285407a180c1c3c031440722a5003441240d411200f604800c00096641d0301c114085c01d48800010b40c022545c0100b01414003520b00c100502d0a0b9052040c410719403038001c0c04014000040e00c003030025441c0c4000041c1c00190341d0390a83c81105200800d80094043c10015200c00c084c0c80d03025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 246954946 1250 246953696 246953699
    0x3090c0103110d09020319051506040b0a092d02040611060108070501081b0c0606010306090905060a050a020915131a0306130e0d0207181e02070206040e160306 70
    0x1101601d50b04074036812440ca080c0b02040d079030152513000c0d0310100c0c0b0007012244030004c0c0045444100c01030b48410350342508070313024034000743d1111008154082412a8100403039801c1c1000a40043c005004203001d003540d07820900e41c40c02c0e0240315951000119450004250348031b9807440003a501a0045030005041c41c168000a88400a87c0d541681c000700082d003c15401e00004551000004040000302c82c24941e84181030f150300c5004101200245014041c1441c2c01000502558102d03441030380c00c586008040d40c0442c60200d21203030006090200400e071500d4034005000a8010101c0b83e60348582008070903a118a02140107280040240007001340d8195140c030001c000c429844003202c1c141c50100001941c13403406115100b150680c0b2030002424046912a440c42d140e2040703410b40159001c00d8050080b0741d210f120340406410315070014410403a0000301c20000d4044901c02c00520f0703030041103440456036980103880240920743c0500150f0314011444998400c0b080044002003807a0a50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 246956196 1250 246954946 246954949
    0x80d030509070e070212040603090512031009090813080604060e010c0c03050c0f1b030601080d0905060f07050604062901021917041512020c0715200303090c 69
    0x600d4851003449000d84400d80c5071032804070850100070140411402000803460300c09403400003402c003911555a0001d09908140707005032902c46a00c418407051a000d104201002108a009006940224001140c0e110840c42c3c11001030055404400b1001e104d51404200302c5400141d003841540504801c0c0091085100c00317a00301c034101c0c1131030710000f04405528000300b40070700002d000111008046400003015000342c1410304501064003d50030740710805118807407404108141c00f405424010306030740840b001c0042d052040700e1080380c0c0980d00110320728040d0136207102911003103900081036421500d014940f031401440828a101d4540c8443c500c51a02401d00075100c1c0656801030300204a80c0b074030180f0300711102400d0602111107020615020301403c420b880548000c11404040710b041c8104000e001d40180d407162000307a0b20301c1c4140301e5000405400104401224030707441162005800940040750a44032100c280c0382c00e03da601c41c940419000c000010f62080c0c0140c0d040c0d42d000c5c00e0200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 246957446 1250 246956196 246956201
    0x6070215010b16110609090a0f0b011d0f011806020703030306060503070c0b0a110c010f060e1b0a03060504050907090f0b0a0e061804050f011d061618030c080d03 71
    0x300c1c0c44030f541c1c11540640001496280b0701c80074960014006800d00c5980c0f07000800951048688046c031507100c80f21002060b0b114000c1c1018080309007840c4a580f0704035480d0480030001d20581c240f0070019030507407aa6990180300118000f120b03182c8564052a11888040e595243c0c40c4400c400280c81e09030700107003a43c4104141c3c0d0180030741d65904030b0340784080d40b1000140180a401844401ea4a802001040c44010020a0180029400441c42c50f8554005138121409544100003110200301040b80b042c4810000215600301c07400000d84840425000714010300c5540c2145401618040500c402e0180c00070700507040b2001e20105010300820148114241d50b01070002ea500710904e400305000550100d07035520750016000d8243c5c502c404000c040341d484620182d409440507000120080490403080c02005d407844120140d030401c084014001540d9003c0c0100b00209400c0c0180c40b0100d82d03441742507500001e6003044202203406803241010405c80002e445450035501c40c4081a05401c2e0190 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 246958696 1250 246957446 246957457
    0x8120402131b080c0f0c01060513050106050301030b07020c0a03030e09010902040506070204020c12040e09070b041d06010e0303030c0a030b0d0201021903030b0904150b0910120305040806070215010b 87
    0x418100c0341d540441000d80303098001404c0a5040c0d1014081d05c6801c401c0b110103000030201c41c100101d41e0515101c184011240c0900103081c3c3c1a040c400148003d50700b100032070f41105c1e400510722072070307540704e0108905110000380d14540c07000210380c000003030507842802c011180300c1c11620807601e45d03a0f680b881000c92085105068002c0e0b02444064094503055000d800b01c6c030000703810358071000d091070030202990f407040c1c1140040042040901880030303010440e43c00604103034000103107401c1c1000d000603007001c9040b40c0a610070191100069041c1d00c102071946910700d016003104e40700d0502004800142e00700342c091000007481c05c0c8404849107840b40035140442e8061300541300c050140c83d801c0540c0c00314803000b502407540394240c0f0201902c945404520840c002d0741400810600502080305031402200100d100b02500818006090040500402101c0b403030701c1d0045400c503c500e000d6985000316446a48140550820400c8464020480200420488030014400d0783c071015000360398002c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 246959946 1250 246958696 246958721
    0x4090e06060907020d14070c060302281b0510050103050309031b0f30010603170703140d09060e0705030d02030403200d0210030b03100603020d0209130812040213 71
    0x154503a1410900a064081b084005601c40318642009500d03610808d0105074450790002c2d40c005165600c102400c40c140380300c0803100d80011003440e403002004004854681c1603000c44039601d0340c1003041081c10000c0841d24015a441840150b071b5074201035890f5004000c019010b80906404107195410548141c2d00c0c020004114180f80700d07030700e0203000c0a0781007a910040e1007610b04207070710100c00302540420503403c01d807400400d20504500c3c20501c40d0380344c604480e80f44402888685c00281d0403458000d0f4030003824080303584901e04516140d0180450440140440c1d262901c0c4080010000c59401d083d54015170480381003280b400000c82e0782e44903030301c400f030100c0713090400d00100100d0252480581c0c00009010f22542c40091300007840e008443e014510100760f6442c4e00c24038609090100d0303800d4508000301002461f207560045900500d8040000f44181c00f0407001400181221604c544000d82005080ea1207401d01c00407845148000e5400364410711241d00c0c0c40c0845000c601510406518 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 246961196 1250 246959946 246959953
    0xc0e0d02060d020d02041a0a031401050906120c060708040302150c1903020703080309030a080105040c050d050a060b1c05060402070218090703020613090509211e04090e0606090702 79
    0x40d00c1e020001c0d04000d02c85518117408100006208486c142205142101c0c0b0015139a51504054003402716420b00da4550422034155004101d16600d18078041d43c0184150341d5203c0059608488500b842d0042081c203900c6240484c1c0e4800b23000c14000a00305991013a29030340402143c40410042c00d004031211000240d000001c0b2042eaa43d040045000789440780c011603940588030785c2c0310f0940b43c00845450b19240c2c03010a84004080d4041c00707880c01481c0640e800c0040a007840b0000303186207c0d826008142c1d1703840348049030394484103130300c5203005101c0403000700d84a890709110000c100700c01c90000016941050041011071409100311a03000340e0003003523502c5520340c8824a8048000007480c0040c5030003038450000260319050028044045414200b040c8541845140350888102410484050b403140306222015810007040c0c03410340b00001483c40d220082040c0003209100c103400b5000c01c3c503001140c00280144180c100490221541c001d8030180ea850409100c04003108071060750043c3e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 246962446 1250 246961196 246961207
    0x40206090d080d06061e1106010501141b0c031005190f09020315061008041a1306020a02010507030507050c0607050a0c06090f050c06030915130f060c0e0d0206 70
    0x6024408411802d00c1030600c241043c0c280d0040008a6000d64400b01c04541c1d20701034090500300359005d0400241440c204032855040b881c215542c6c41d001401202e040c0811030106040c250b04440a66175406402c4140b4500c6041203d0601c1d12110000700f0705001e4891440c81c2004800d0500520b44681c2108441c01c00a1003004000d50160500c000184096642c40f1200d0b0b016072000e10a50f43c0b108443e203695013071824480d045c0900f605100d81c10604101c081c1050000040d11160200c0c03287d429040c070380d042c540390030203882c1426403043c02c001d1203140b0005441e00ca00f40c040d04614401c10b05505c040020340c0e03803420191440e10903041c7c40ca0703082d0084800240480c4c0644050134545c115854132010102c041e982d803d0442d440d5182c03e60344640d0081206007003000c10019080030913000e480c01d60031410729680c0d0030703614503c07010502d00d401e0304040002d040154805d0581001600410509681030380344c1000702c020801c4500800000c3d02c03a00031102d80e400e0101540c00065070243c60a890300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 246963696 1250 246962446 246962449
    0x4050c04201603050c0d03090b090a0203120a3513030e120309040e06040b0106020309090a0c050d1a0a0b0f040608130f030807120c0804030c0507081b01020c030604020609 75
    0x3501103450807414850140501c0c5c40f4850200498980d01b103107503c00141d00b20035410103070100c50303000f0114049503201161481c01a100400e440385894a01c211081d10344901207002c2e2840f46610901c52050710505498104203014060794000d0341c82080042d09490315130045c0c0c0c181c0c041c111080030740460341e001c0160103603040c2000d43d02d83c21030144050381d080111030b47c0040d090f540b52400c2c0c10b01c2c0794000b00500007070041150303c1078010b2011340021854502e20710013180c1c0e00c8030003c0104130120750701d50381101c66a010360b040b9072440004100030400080ca0410800d03411044004043c01038088480c0403e822900204448044104205050030708d440c00004030b80c180d00040082c550029050342400010b440c0450200000e40300b601e41c91290320300944003e101081030522501840e040c404508491a0441006e90b00b2541515220783c00c2d4020782880c51030401c240c4d1040d0218070a48003814940504045002c0c8a46401da094a0580d102901056520201650040e42c8881d080080312580d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 246964946 1250 246963696 246963727
    0xc0b0912040e07090906140102070f06090e0411041107030216030203061602010609060b030415020412020d05011e061a04030b010501081801090b01031109040b0c09030c040504050c0420 81
    0x800051310784407200d503031244100c0050340d2283d4014003107401c6440313095a03d90f80522a0402421527030180300328243ca041002000a041481000c40c0002c2d040040f40c2440644081c0702c003992006041440071448010083c0f1981c1d2004000354014050303406507501c00c40c0d102d024041169002002002140c8134150302c042d105803043d072101c041d5944c40100040343c1d01135001b4a4010b01000802d10f440f80303006c2c1044910384403e0b0070780300d4190b4410001446040303007000300d9200640d01034407605804415880c041e401403040507520109101400420380e465012600100b094888800c0c45c80e0200004907180b240f140900d0000511080c40c4400601095100f080069440790030901e1604d1482034503481c441c21150000720a131001c11090b8014005e000698540281525050750b502040d8035083d00d03084041000030300000760350318000a403445556810844240740901c0103200b00140d050074a403040e43c5201d44000c80e4025400d1400c0303841500301650305440300c607250340101403902412444030003a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 246966196 1250 246964946 246964951
    0x20703171503120c010506150414040617010614030c09180313060509010905010c1a0606040810060905060a03020a0e0702070b0d0c140a0c031b0f030c0b0912040e 71
    0x4040582081c080070a690030800e101201d6140c0d8100741da40c54100c0746036030075140010301c40e83c001c6030980c00c1e90101c00000c500329011100201c52030654440c4d40310026014011a07400190740e1980111341e2000413006600c44001c40704502085882c081108040c161034081c1c4545152740040c924000a41001111041e1080d407400c10702070328076003120421040c030f4601064100d2000220041108145542c000c810720010345400d00b03144001e001e00750307219440120500141488400014086440c83c4c6400302510040c1401c0310540e1a001442c00c00f01d4000c02091088811445c18600440c006040c07160003c416a50050710301480da40c00c2260a010442024090408522420800099406400021b043d10400d01070000c1100e034001c0344000c000c0000c901c038009000c00c08000c00105aa04082c0f801d000c598541000c941d102c21404070300c405c0d00c1022034086c141700424000482050391204251030003610606682049891305a14940da4a548000c40148000c1c100018040762408051890303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 246967446 1250 246966196 246966211
    0x1141204020f030d0908070605040e010314010e071203090515090d1406040b0603160612110c0304030b0718030b060108060402090d03050d11031909021311030609090102070317 77
    0x11502e00803900800d140c0040742c1a100c000480e101418000c843d001d1015400a000d946801c42c28541002c42c0840c0c0c2c1d4406200003401c2204181d840b81030508290040b43c4080d80172400e881023141d507007440c909000500c45040340000c514920100c0c840c0b4000c0b861980704240580070074103144500c2e0038080a81020803055902c05070081d40c1030401e503002c001c01131241d40700c0c40c1d10903140d08150091502d00307040401444c80780b4807841c805015981e480f06146a5808132000003103040e85c12408001f4a92161400d402424080010040b05018000d04294001c520703d03a941801d094418520140c680c01500000b44500c03034010100c1c0596100f202400c4c0c2084004100510b003003404800500c02c1d004c004811004500040b455540d80c6200b07119605e1048840c07640c1914518040410500301c40c4141a050f030b889940c1c900040664490b80b858007000c0341a28001c1144850241105034503400407541c5500c11481c1400207195500107000b6201c40691645800000d00d0044c1903580c2510002001032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 246968696 1250 246967446 246967459
    0x60516110315090309420706021201051f0503190f021801020c01020114180703080412120302070b07110f010f02030a05060a050d061e1b020c0114120402 67
    0x24064400e58826680280390003c002c550307414000050150541c0d6540040d0a402c0120f54200c1c4000e02d20300030342920301005860502010b008050502050003144005000d60b8400b00f00000c2d0125007400c0241a15004c858a203000910940385860584100150070009082800412149000720241a0090341c1244021600310f8071020500c080780c125051040c1544d030a6a6501c4155805220749841c1d41400e2000303104141030004401c241181c0500b100345401c008152410304288184241009154400e00041c5e0f81e03503071600c501801c40601d0a0584903200c2609204102900074400c603041d0b250700040309000c030341c0e5212059641c002c010100c1d520074000c1d0f502203000f200081c410a0503034030180304010380300d0529039907420032100004c0030b55001c1d10342038200303025a550b00301045681036402440131030a94801800a80720307007070041d06004c8180c2414100d1200c1c05485030b08000751070180d421240c00b0b0f090a4011100d41402000300c041c034180410480e1680801ca15019501c0b0340043d000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 246969946 1250 246968696 246968713
    0x80306030f07032a21020a090515090c090a0807140102071a0d09080c0a0b010801020f09150705190218070503011802071a011e03021f1b0501020a03060605161103 71
    0x45d414650141c0d96071030260003140412085242100012014101c525800c0160b0f20b852160608080f4246910303031301c1011090001074000b081c480407121002d0740944004c0d0800e5580318995510030440c0a00809c0b139010f92600a0b103940700143c802d048401054000100801c1c0c484802c03d03651040e20310119640e112003000011582000c004e0001c01410001090a05118102880c07480410f03000f0340c0003a40108108500c2014002c141c03041c141c0215400c14629040040050741403041c0b5100901034019a00c10011480c0041070000445000303072607000364046003202c0000e00d5181125244017103541880113011454801c100810a0300141200521300030f06501c96207030545c1042c0d502080b440c40c0c48014080c002000b001c1840006500d000046031600b5940000d801c1503c10215014908003481d1010070350740301d40d0a8070306000c99007000403159810b0341800e501079844011a0b8011900f024400034003d4851012142c091103100d03404d905a40280d510380b00b03c080942d5910380c1c1403084004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 246971196 1250 246969946 246969959
    0x3080627070908030c03031501180909120f140c071e0503070e071202030a1407031a010207030f0f060b0a0f0501080c0301061b030318080306030f07032a 67
    0x4030154020310905000180d8a80000001c011140303540291010307400c00d000c0700340c0103a00001540c1d00500c964001142c54502c02c00102c0c1e0700780c0d4250007030858858440c2c0c000303181d003a40e50044d0035407030142c0469480307030b280d800c0c0c203813541180b400000001503a0882007001e40e03240c0d0000b90440c40d90700310948840c0355640d0b240203400c41c8a8043e03200d00e075200f103108100603c1d040204e00d000300011020820702b49407001c0007801074240300d65a90030640d000000502101c64030b07401031502d840707070340c030501000d00708108001d0060011115030740d030010320072000901c03a6000103901403c4940c841c200d50403100c6250754400703010701e0908040359215111440088182e40303000d2440060722a500e40c080c80d075403822000424844000c0c0c820f503104d007802c000601c095940081d28404100c0101c0081000c203020b0325040700201001c10011200c0c00d20240a10100101107005601600088040321251081c3e04145600c80c5014440140000c0c0d0701806003410001d80419a0000d521500c842c0d500307650340e0032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 246972446 1250 246971196 246971239
    0x6040219020c030613050616090506040e060429041d060103030c1a072a0804060e0f09070219050708100f050f19150515070302060f070c030806 63
    0xe1058050b0b0880018001c1d20b0808200726644485190000203040c043c035211552280c030040c20140f0305090509042040500401080e0000d08000d4092555039aa44a01806e41401600c00714405d0741018510344041e60b6000f030680e421080e1041020310981d8000800c4002d0090030505112851040310401c03c821051142034000c2d8003d0b1503010800ba5545042d0380d0414040f4074640007a001c820038040101c0d4010300804400c00d862806c90383c250030200a042d40091108401086103c002a000c9210359001c1000c0e064004240c843d074071030345188000c00480710402c0b0b82140059101c0a09451130802c500b504c0c82c6c0040c00341d020303100499280d10b5002d09003089000a4a006501c620100999040602c24070383d014241108100c41820f00c0039030060440d00c2c40d150074415984032000c540051501100035401801c0003455000c0c07140800c244180076420002040e0054000d20300010165103009017007a0ac9040c0310740d00c241e40e0842a54050f1040d5034040d002940000003201420800445c18 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 246973696 1250 246972446 246972487
    0x70f020d03050301170d1706060d1a1003110904020f040306050109090b0618070815060304200a03150f020c0a03020105091e070e070309080a0c0b0703090b0f060402 72
    0x2036580b41e41c2d941c10b0000801030707071010041520150740004c2901c00b0081e845421103401c02d0040b562022292126000142c450264860031007980780380c6210a01c07001ea1008040c15003074800c3d22400340803000740005508807000700700c1e002c8599004101c45011898180d0041042d1412210a1414140c0340d4550408403042604410981a510031000302801084000140e000c002180d4501035101ca00d0420b000b07001004d40104280608180480e18401d6a110710244500c0064016916840c1500700311001e1002c604248070000c03003c80841103582031005d0700f4025650030000d80740480c106c0032801c000500312284294102c0c0e0b4244100044214140300d01788841d4000d0340007180034104410001e080c00c000c84000e440080c0b50f044840030250022031410200c403c1c1000c3c0350781e80c0c1c0e91000168007a140500004150b204000759105071690030009640c1e0f0f180c05500403076060341d0391500075811190400d801501404406000400e03403001a41425805003000e40094201a0303440791848410004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 246974946 1250 246973696 246973703
    0x3050d030f0b06030103110d02030708010e060103020a0803040807030807020402040b0a17060103020405030d08040204090b040b100e04170706060308210a09020607020d051f0506012c06070f020d 85
    0x295905030814603802d000d10303407808100f154014910b515560360259646d80c240d15482c01035095030a914190742d001d001c600020041d44d40213002500424420700c2d00c3e1402400205d114140441000c03030380b44000000d880680d00141d000700641c50840c0c8401d451174010040480c6e00070b03004c20000c20340c0d4000c00c0141038001d0707440c2c40c0e0100c086121700391202841c1d00101158109441880100190b43d00061505080c3c11181043c120546039400400c0c06000e0520001d40003079090002d002c104203610562034852498060300303221840d254120010840c4060314060442d82d00c001080742d604000c0401000e00c280700b8000011040c0e500c0d42c9035a801d41011a42d001e100c48840c85407401da05142c003005078080c00c02d9100700403503060b17a40050464091010003a0080d041480301000b00b08041180740504800b01750b051000060780100c0034042d003000c0741c26500042d0381040034582092030140300c81e580700c007407600e00550001c403e0500909410410040d00c44003442d80340400580c99400101011900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 246976196 1250 246974946 246974951
    0x7050a061103060f12060105040b0402070501020f03090f010507050403121107081e1f0b060c010e0319020d02120f070f0f060c080c0a0503060d14071a0a05160501020403050d03 77
    0x1400c9003008610f004c5021003c0c011560320b07122211056010405a06440f0700305e90000710b000030b00c0c000c90300038090448000c0140d0b10008034240003100c400c01440c030581c80441114070000010380308070300385d83e401d032035880102e0400d12040c00000e201103140c81094410385400c4111f0070340c917406a40791a49a80c4051496000303005001c2e05a1040000d00c0046000c2000500e0710103801c818a8106032400703400316141036510407040c01181c1d9034504a84240c10480000e01252030b00c883c28a481e5405561444403043d5040d001c640c2c424008500c90038246055005813a50421000512460fa4400c03980f4030042881009501c00003007421040a00c2c060183c4030440c0d01007550b260030310450b41e04c80c68507000d01c1004402c0120b01e40d90b0008549244100d8904103443c2d4032685c5c00316083c449070101c01041c41045201c1c060310300000040440841c0c0143e40b540054008035070400a03984220410107000540400c0300b0281e24000c1d600011700548100001450705d81d80c2e8842c68140130520349803c0c0040d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 246977446 1250 246976196 246976201
    0x11508010608030a12020901030b0613080115180507020f03041205060601050f04060507020f120c040c0509033a02030c3313120203120f1b07050a061103 67
    0x18000d21412016080c008015450200710301d0001c0e00c035100d11042180050b03000030f2007000e164466001400c0801c8080c100d00d13200e001c0d484050f0f09a000310301038030a40c0d6181400307413543c4c40c0da07940b00b030401c446544040f040c0d0302403603000320005040020000000c1d44100c4201a88030b103030401c0200b0041262298040c04100c03207140c940c1c1008006400c00e410407000303000e001500c481030b9048a003102c1890400550f540300340d1001c00c45900b010303131043d070380584928107004158601181005038018101da00300580c50b01103806841c1802840001501070b40801d40c00e0302072601380e400801c03009101030114540045203210707012082520114400050704082602c1c2e40d460780030400070746c441c141c42e0304d40803a0405c25442c0c032004c10401c881c1c114011801c90045200c1d080310384508196240c000800e02555240190042e6030b0303621001070400701d20b82c03413400542d407001ca030701034140a0501c800341040850243c5103042ca503a0402402920140548190700c00025082e20804030028100b269443d12072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 246978696 1250 246977446 246977459
    0x20909010b0a08010c0e12460b061309050a03030621150f09052e05010509040f230c010e0d030818030d090803040b1308040506030a0e0115 61
    0x3000301da488810942e04000d4000d5005c4e401901c1403034510019200c420304001c144d088546042040a90118035400c0c000f400c280006400440ca54580c540c1e0081101820b032a5400100201c0007103006084030b0503100c0403c1c102c0c40c001100c1904171035204400304444c00c0e0303074450600784210250220082591950304001050292101e000d041082443c00f43e400c0c0d096480310840140072075440c03041c5640c0c40700c10900c0e071105603000c3e610080d0040101c480707018444040e41d86c1d900400f07804e10540c00440815142c100e00724045c2c541642c0d4060840c514540f07a0f50390b082104d0351030350b20440d694101c0c0500c08001505400341d0000d0001c01400034159000004009401c01070900609401070025411034004a0f0700b000645800c03180c1880044408540c0d10103107030860041c80e244601c3d00e401d0031b81100034401000003a500071341c0980074560f03403515407034240c44640310140c1005003140c01c00d0000700114503000c4040c540c002510b03c00824912409000c00c2c1c00c48440b900d180510103281d10043c0440c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 246979946 1250 246978696 246978709
    0x306090203010b031015050d090f05060a090507050d0f02040c0e06070b0a2712181701050c120103080a0e0603090105071d150c01230403020f06010b160f020909010b 72
    0x10301d196102a4001089484000d00b22310a05101e020b1036629054410100b00412030b82c220587d4205064071480d04100902030050300180d1004d8400380b08900c4003060510302140c41010007540048210703400e9100707501b840f0107019501001002d0000708045940640c0720400117109091040d0f402d003000b450310707070059402c4422280c458500e81e0201c8140c0943c034207900c90b00c001e0700d641040d01e20411020710f02c01100d6000e15907425034007981300c5100c0001c08808855000340307944241c10007441581da850510b11041d0040d010300c0e8542042141c010030204000d00c00804261040b403070030110341d22004020a0b4640d009444c0b11a590f95031b0010420b00641c095010000c200d0100080b9046640b03100000e40c0c60f51941581e84210740b4000f03000c40042900354040115813080c40300c0e50a8800000d1110080c3c0c40301100c0c15005401450b6a51210080102d802c5050b182d04140c194100000203a45030000441003004440302c03088202140c0c0541c0ea0b51145612030702401002044030510907080c807e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 246981196 1250 246979946 246979949
    0xc060f0204081e19030923040e030a0201050609060306190906022704140109020a0c0614040b07030203071704020d1a27070b071e03020303010603050705090306010303030b010306090203010b0310 85
    0x60644d1108460000c0d43c082c8400701121440130720071565143d4a040c0400d00d603040744550b540710b850214109641171010010b0702282001d60001c102c0740c1d070361800344200000100c2d0101d80c16040715000070261494203070908240c4c0820301d4006455900c80d0b0701d00b02249d21540c2240340000440c0083ca1400c1d50240701d000e13030200283c8c0c1c28000c6540c1a1716154031404e06020b46c4e000b040d00400c580700c84c94407034422100070580141003407000006081182c001e03a031081c1d03000c0d214408000d0000d20741d240603008683c09040c080c0c0d942112400c1c0c03032506030941c40000c0d1080342c4c0414140c8011001c5501e030848600113040d103180d00e10306420101c5013991480380080b1207680880940400406061010403204102d800f9080d44990341e101c2450310b10000c150140b80d06a0f1a120b815442c024164008041e5058404507241045203444583c02031303826004001ca05c5a040c0e004800600029100790040c400b0094103040204602e078551402c0c0040c3d81090300700003403005001c0108100c0300e07000c140110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 246982446 1250 246981196 246981223
    0x12070606060f020a02040519091505011203050409201c05010f030f02100536040b0915040f0c020c0411030723040e01030b040209060306070c060f0204081e 68
    0x1e0641e8500801079101c0b4400040a1b00c1590f0b510b00003440c04a550104041c0384a50320703c204800981b601c1c05e028061441a1408034007840e01002003000440030740410f070803d4060310351a08091070540b04030064006a40158503800c8183d46e15200c21000d28094580c401e043d1200070030080202e40c0910488034142d004042e42c2100d21803c0001c217480b0500c4030b20711030b0140d514000c646024001500d0902c6013041c036011030050b200e2030034151210b181c120300c59091010011180861003104110541d101c680c00694815003240c040750451840844804c01424050004540d08401c0031210381103881e00154040560000341001589250911030180c1245098401c3d0703040d0304100b42d009092000c0031110030b02010190301c0010040f02541c0554004202c0d0092506941d070b103a07e032500360721034141c07805c90054411102080140c038010030440c1c42030f001544e80035a201081d46803100901004000210000d5080102180381102400041e07059a01c0b1428113840385407082500b0310b00000e10340c40e50b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 246983696 1250 246982446 246982457
    0xb0f070204181704050105220f03030512060429040b030f010905100504120f0201020903073b13030c140a050601060503150d03031506110f070803030708181207060606 73
    0x140406ea07000f405a0b078152180454810400350f41d04401440c100c66a0040c0c3d00c0300520150020801d54070400401000c0704650f44030085880702c1040c0400e46030400c0d06030000003604142c003034100500c00aa5805404001c00101d0164011400729003803110002c3e2601c0143d46078812141401410080e84001e4a03000c6003c0129183c01d849100d0701b406c0b4800c048003080050500c542c00b451003501502c814003801010b5940241d656043c1d03080921aa21f96400924001030f031403880741d901010601020f1410190141d215542e4450750301442c4c0590408600f400346040b021000705600c40c81d00f8000210000040410b00d559040c42031a0540503840303d001c0020400402c540c0300314250211349220010f0302c1c01c0141600d40d1405034050301003040d40302160754101c0000500d440d400300200c5000f0181c041034a0318140d20510031a29800c0c1e50150762416403081002c00c1541e4070a0142d01e9000140e603003203200c0b0500c44566503040200003044488a501d010801005000840c4291401070000c2d0619 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 246984946 1250 246983696 246983699
    0x10b01080c0702010f27170318091902030c0702041515050307050c010e06220305030c0919030302010b030d0c0b070c0318031424010b0f070204181704 66
    0x2058207880342d144020f0410400c03a1030292020300a018600d154980c2c910301c00240e108090100e6040c602e244514000058800c5403000b41e120301100f128605000c0c0c20010212a0200c070a00c440300700041e10900d0100520301c64400100b0062001d54020001c000c0031070364400d00c41c010441070710a5200c10510f00e039508103040101c250768070b8030a50902c0050a25039165580c140040d58a4000c400c02c0c1580341d400d01c400c0c2c0c507a049000c1207580c462800b699a8000071452030000e1400503104440c02400f0a10800c0818a41d10040d000303002107507001806c085841000c0d448000d007407425640210003507074403449002e03a240b400780311409000740c051800c1d540040d000d854020911201401850500c0301d00c0703001c10141403040b10700c0b40940001142c2000b00d80c0e80c80ca03107134169503080e40c200c8a10340202500320510305420300d44044401c4480b441800c040e420105001c102c2d07808400900d440020801c40c050068450380500c0d540e29885142d103541c1c80c030071405c100c4441100417a0100031a64100070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 246986196 1250 246984946 246984961
    0x20a1217070809010b090103120f110c130f1103100e0601120c0924080907080303040213091205120603010b1003020c120705010c1404050a1232010b0108 67
    0x300654401802d1625502c16211007003628018030301c0e07015003504294060004000e22000d5001c0e10b104c2c041c9583c0380b003240c680c505000c0341c98070458440108240c114004c0540c813032616031802041000c1a01c0d00003603807803541031174034100d80180780e4402c2503032030210422040e5039441054100802858007000c0d0103140c400c000800c0e041040f0029210b20b565401205802441800200094400208c01e004040348000382e80508603101c000706400a002440000c030072400100b00c0b04101c0d00c45000642c01c6071929030030010b0300034000482102007aa40d0002c1004504071b044410b40700c0b01c3d07685881e45c5d02c40e4609002030380164001c0605010368100342452605841d80c0403c2c1d00012090324005031144065620142442c403a840e2000c289140401c2001c03e0240652200c05010465291b02c920b035040401440018000d91040f950300001d040306c104044125800a003040d00d1085040304825002c0c0d40030755003428020240721091482c44401130014100134451895016003d080c0700d6524130b0800c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 246987446 1250 246986196 246986237
    0x601080d021902011d0a060818010e06040b0712060e1503010e07062006150f0118180204090c0e090c0702061803011808120705030c120711030a020a12 66
    0x2000341003140c0341352608514503d60a1714030072000001c0c40070542558402005010200c15920b60441002c207180d118038038601441010700040340030010f409241ea4a4554000c920750041c0072105008100d208030134400304a1040c04058038031503540750901c2c144100e69075280c01c40180a0745c06070b854a202a200300c0c1d4001220000c0320b0080c80c003d03605d8500d0500a481a80700700020030704500c82c00051110104a0084c2c01d24aa2000c0c2c40e1050314490303160044440405180c1ca003000018160818000c1c040c1085400030810351074400589000c1d959503c29080f07518004520340024600109244e461030082c510b2034015006441260510742ca80c3c002882c90301c550849a400d41050740f00240e01c81e2400c0d0040151001213088601c071200850410034029409488612101c02c0e060000a8500d405802600d0280030983c200718244001150070030488031b4043d024400b4446c41e4a600b415000703080005012849190307016012200f00c920f489220005507510300420701448000c0340c0404141034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 246988696 1250 246987446 246987493
    0xe030316020d2a03090b0a08042a0605070f0b01060c0203060c090307090b040608070e0a060803070f020d0201020a0213090605060409021c0305091e010e10050d09080c0a03020601080d02 81
    0x2000301d040014200d03e810317110280c0c2c81e40003c29542c000f0503d48070041d005100c580c4264000c01800060754013125842d04000501c0c42d48089180003d0000d202461080020308181403041446501c2c80b142d40c0c80d200c400c104242c0c420300c00903e8180080c81181028010983c100f621020300710306085040c0000703900c407050b40c02500b4400f0340e690f070000100c1c0c0d1b458001d90024400401a107603043d80310b0004803204001219600c000341e0400c04001241d103000011154100d800a418610940c2e0300c1e0b08100030406040d20503811803051060640159a5103900780705000103958000680e8911407410034103481c1e00428845c41980350030301040141c0c079a415050007039409035092104071007a07482c0549842c003850b452103030000a001441160791444d501da981c03c0d500241c86001d0f1b00702054003000405d45d009280c42000031002d11003d00e9107001034000701c854034071640362142002030109003586032418041e03080c0c006902c503000410802e101801984284185840070300b404803040820000c10b102407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 246989946 1250 246988696 246988757
    0x13021c0c050f130f061d060603180109061103090106060305010b09060708040e09070e06030a03120b01050409290d030f1206090f050a061d13060e030316020d 69
    0x210302c0d0501030f607840f40d07075030108000401030030440c040201050710002c000500643d034041d01081400d02c0005034101005114420040c00e1a00d565180480c03c268221032180c00f04466403607030f44110000d10140103100140b130002c60480d4807440c10071403d500303403403082d44003030141440c0200500982c0301100407542e01c1c04095900a40d18200c80c03a00c012984901d038050300c06400080d05001c2c90756004580c00003110001104000f840c1c540d0020540c031000250402404201550482c0794941010340001142990505102e41001d0340c1d00c1d940c00070b8686002480d0010398641c11303105100905020141d803074013000e5420070b004103600d0782d02400300e011445c0080309100e48165100c2e240e28080c3c0014002c5c00420720284004014a29100301034003003138418045c60740c242a40400d0707018401d003030120700804402d0b20b221144c4a0020f0001b004c06540070942d00940c8030280e004501000b00b00a60080305801300c0148a5103a044000b0f09080c07601104004111108000c0c21031014410102d0656202 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 246991196 1250 246989946 246989959
    0x2011407030519051b0a061d030d09020f22051b0d02130b070501050f01051002070509060a090203010f030b0105061204022e02070509010801090203060106050a090e13021c0c05 77
    0x30400d100703842c84d010b409240f9201342c030311703c070006803515001c640030744100d00c02c0105000008046c3d03d0014004055060b85005501c14030029031402e030241c120b81007643c00640210b00040481002c00ea84610342400c02201440c102494070b068401c03449029488008028440800d8045200c9440309124a504404416801040b0313680000141107035600203000e010040381d69031170b891600d00d0190000b26514061100c42030700000305070500710044060100d90768060140749046c003042112204001e402e0b207411082c1135002046d02c4070319100560191404140003890b040c55403420a424000c140c02c062b000d4801400794100006044012941003a4100d070310080012000f605010f404440c9042d00c402180b002c8842000d0341c1d0085980b00c1603940a0710741c5030640ea00c0785101403c0c0d800009000790523901802c01000100d00c6000944040081d5151450280d5030792190f540c1d0b070030300079525101d10708640268601185025020120040100c2410404001c01038540e42e803170220b00d01c1054020345 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 246992446 1250 246991196 246991237
    0x512040308040e0c040e042103050f2e17240c0901110d030c030e0613030f020f070915140906150d060306051033050d0207030309020114070305 63
    0x804c50710070340d400340c0b0407448041014030346410210801c041da100444210f0541d140b5010106101c0e014052184061318110203840c0c4079041c1124500c0301840703142c090508001c00054140300c00d908000028804660409080092403507510700f0040980100c01e42581c030781c080000458003000c2c5480d4040d29240a150f103414080300141e0b00040720f561403201c2c9000d841d140e600c0035a0140d01c003074412216590100003032042c4000c04d5039148415600044005204080200040e120388a2580c00504600c1612000001101340e589000287d801012059031500c41c55808002c03201458001020744048032600800c16002154003040f002d0a000d0040e03a0340000700c0c084407011021034032140c10040741040055507038109000201410785000e145603101c0e190025580d000c80090b4030f1070400c04031070009040307840c2000c0d111a070440428602400707030a01c05000c21403580c0c400351600c01c0c004d0b02c01083c4104503100050490f48128400c10b024201030103405c02013540b0809941c168040750300e40c540350a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 246993696 1250 246992446 246992461
    0x601151e0309020d0b090f1207150b0a091e02030402010f081017060f0c090616020a120602030a0605010216090b06190c1407050d030f0c0605070504030512040308040e 73
    0x28601c0e00c00c084c1d005841c192803141040080c100140c4520340400a8440345010b5001d13580c1c940030303089441c112017007080c044040800c020b10012160040c443c1c0000524040740c4011a410030000d900c110a44bd543d0230062494440340b1012123030b908003041d4114034620341540081c3c403481400c01020100120480000c01001e01c0009800140c0071261900701c01d00b4040c03101c03980d90368048aa107244000301c3c50204e03804241714420b459808a000f84094140700721041c084001120071301050b41e010100d110000b070546a9140c0e41c51101d0b009078405070340c0b80b404081900c280c507459844281107602c01c04a440006942071901000d0720b84074a40400e98034102c400040080c00b5030080380504201003d0840b00e51a04420725854640c442e600c548405c40c64510b106444000d03034803850350049511201c0304002403060b02c0404603a115420000c0d036148070303038850800f22041200c19201056000a06005121003003010000c0003d25142584c5818203503034800e44180540c1c4200c5845003070803004202d16 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 246994946 1250 246993696 246993701
    0x30905010b030106080c011701061707020712120206090a05030d1e0c0302130b0909070e01031508010506180c12250309020411090d020f0d020a08030c0601151e03 71
    0x55030010004e11549444061060f1560082c0349001d022540c4900300c844010701401005040394140e0700da0040e6110001092000300c10020121011805084c2d004600288904880c11400f40260643c1039014480c500c080c1c81c1610141c600540c592092840000180001007203c030b0030300001d800130405090380190403e401c0e00e89414042682d04100302c0d200c50035490741c05003041344810071028916a40c3d810503c0d007684500303048660041001000030701030500072004481481410b14002031004142500d00001c0318591b0007410059440380c0030f000e024a041040102d20000200390340d10b85080040303144c2840d02ca402d92000c03091074810b00081100301c0070112502d1a103004030180c03003d0003002030000e0007898018012481140361900c0d901e4901c004000791010790b80041e14840340d11600d50200103a203090f4600e441d5001e4803c8140304016114114858024a0560010354640310b60180c020708201c01600000560002030b180480c8090b400350000d4528912a040c203c080e85500c03404402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 246996196 1250 246994946 246994961
    0x130311040504050a11012f0606060304050c04091719030b0f010206041209050a06020706020712150b060d09031d0d020102070e060a09181403040f03030311120f07082503090501 77
    0x7c24184100814100380c0302507004040140d10300c007652240c0d85e40e0810840e1902065401800701d901910811855003013035845000020300403005602100711003055010302d03038007035000ca1001031500122845801d03007501800401807021036080102070f00d1710380001e50b152030040c0003414008402c000810802d01840010340500009004241500c2d1100701c040d55804092142000622820740c0c005075210307040b26164005903000b074031101d8150203c00120040e00341b44a602d903003e00c0c2000b06030440380b1140724101d0303450310a4403006c2c0c4040384110b601c400c441802d075000b03010301e503407000c1000141e9000c54902e0a80325500c030200b200e521050301140307442c04d00ea013050603035510740450454042110300c24205182d01c140300c1e0096818500c410580c0328011171041d04000c5111074000d000190290300301880c801d440350800d5040143c042c413010798690041e500105940e0188060010f515030002c5602d80c041010010f040586500d50b624008000090344140c0405076984028030800400307420009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 246997446 1250 246996196 246996227
    0x60f010b1204060608010221090a0f03050d0f1d16050d02060a0e0604061e0908060c0d110f090a0801020a08070f0e030a050309010f110a061104030503130311040504050a1101 76
    0x1502d03141281c1c0e04c03440752301d101100c82d1681002100003801c40540083c490501719030102c80003030a81c00301c0d9000d80d01504a60401d056481d141d81890f0100e01545c0318041198140095518035410f0500a1a0404144101d44c1d64210a803030014020740c0c4a078850500c1d83caa050b40c81d42c0e80d40c216090200d4090000d0f00f200341c0d00c0304000400241c0d40d5480704006903003402c1c001000300c19031202c040607070309a0803034400c2561a801500c0011178660007440500020903542001248070300f101c072680f00366179003e2210f62000480102d20604182031441c0700c80042d14140c4000c600d0a2034400001d40b07003440003040c0404014003842010039282c80303141030000e4484040d08071a00300c9500d10f85a52207402191503240080c801e140308d00c044520410501c070401c1d419501800310b01d0041e4031020041c3c4030759070748440420010403000000800c10401051030348004d00b00e07000c0150070741c80d0000c000b1044494541c400d900b072034140030103c1c1000c9500d000c29944a050000041e00301780c0143c5601e4050151030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 246998696 1250 246997446 246997451
    0x9031209010c110619110903100608011503030801090b0f030d030c18030f17070c1502010c1706040510090c180503010606140703020106090c030905060f010b120406060801 75
    0x400e440805400856003500281c031038486100500b01450354900048030003032005950542d40f486045041d0b0b02c002504011046014940307070b000400300346480c03600005c1c5c415403135441d00d0800000c0420300c14a18080ca02001c903d60300c030710b9900c0060040006004000280741c2d1801034071213036a42c249048040b0480a425a115100b4072000a0024118459240081018683c00d03519040400040d882501c1c1d208004a88815444e1110402800d8042e40d404c00d9445c10440d0801207415044072a0080074041000742002c500140000e00792004540614140583d5088245039191000b1810354000c2c401e40700000d00c2d43d106c8040d50094a10350307004000030b0303140400c00c0d00240da10060b03005029040c030042000841d514024103080700d280d449400001941243e2094540f82c2d5400200b5509000740700201d4069103602c0301d4801c135010b64100001180e51080030400308001031001d10741c00f030340d0304003401c005600d0150340038a14421400f4845860318050005010803165a2242029041e658000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 246999946 1250 246998696 246998701
    0x302130603020a0e0609130b131503030908011a06091807030204050a1d07080a0b0a0e090d03110a0e010912060e160501050a030911090708100b04031703090312 70
    0x60000e52000c2c2d07801c0005843e540c4d01d83c0840c1041c00403030b000170f140034050241010b1100700c03d030010860858190b600c0f5502180081d0342c0100c5020700820b00714003c4240480500d18a8040c00c01e450300e0b482580715904150035114003113485600c1240c0342c0c6050700c100c0c1d40c0390190740c00608442d00210080312040300410600010326810781c090001da500541c4e05126070b94541d800c54000900f6500003504040020000400c1148070304411034124150081c0031035080c0d01e03200080c0e0300c241035800c0b031040d81c65068200710220004000c2d001c40b8141608041100d01c0c99220705000034410a400d260a218901114094136445241098000c1c11032958542c0306076420314007c2c001d480c01c215441000c3c0300d0504510300307070602c250390704045610503164940b406040c90002c6d009800821400e41c0c1380180346030350204a4680e591441d100b4600d81d1f8900c41146003980002d130002c01250440840d00700c0c00d000600000b00c11b070100c030810300404031116403650349248006146d44a40c40381d03605240e420310705 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 247001196 1250 246999946 246999959
    0x911010813061401081e06060d140d02060a270209090f01061403120a0806240d050403030c1103041205010e0d020304050405010501030216060903031d0c09011205060412030213 77
    0x100f0740d0503511920152850706940c1c2c4446c00000e840a01c0d01c0c002a00240040340c901c0c60407160b243c4250340300c0c1120b82814100404c0407400c01920380a200c0c05a02315908111540500b4131030f40105c900003030342c0504002d000e10004030154070700c0b1500900689400f40454010501000502d000e003070900024070030141c40d030326401c61311800ea96003240a0300c129025000310721080c02c00c4d100202c0b003540d5442055540c0b00100521101c3c00c1d80e08114000c18100c011015031f1150340201604101e2020115071030a181c600281114403840e403490801860f08010304040d43c0220484007262a10170a0300101680d07820410b0040031501c0c1400044d10440548201883d000f0000c1c100b1920100c600300907070b030b980c1c4005509a109031401c607402c403a03140005100041c2113501c0010401d009281c0082e1801c54400004500361940310895802d5116141000759417800303601c1e0074003402e034511080452026664410381c0d65440038200500d42c0031a61402400c0038460703410340340131007192211900c03016500c42 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 247002446 1250 247001196 247001231
    0x10213080f0d0804050d0f1b0b0f0c0406050904020f040807080708061b041e0f06050c010f0e150901151d0601110319021005041b060201091101081306 66
    0x140041c0c01d00503509000811802810311030300c200c1d00580508550395420340304031210f12400c3e06030320901580303c01030132120b02d040000a95152003584150440e05215002c071415410040601241250410007800007590001c25603060850075039000d0780301c0950308613040d0b59000b02d03005000a440382c45030000e008403001032503100b280e2014061702ca4a880c0c3e1031185d86c04034201e4041610310901004100201c0280d070b94400c42d07001020404442464803819103410003031039603022070000341d070110b60441c0c550400c0c4110440300840e920208424004c00705050313155510221441408182c000029034050000e400c02e146411004540301071040d20b9003d0f59041c0101c2003c4500810546c000041c0d03d540104030914400050000842c1400c00441c100c0014200901c10001140681e401c1c4500350202d60040a0140e481401491001d090a04a2550700506035000004581c100110080440e12800c0c220000308070a00c4c200c445551a80c1102e04e080742e4a604c02000f0314a801031083c0b5085804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 247003696 1250 247002446 247002463
    0xe07031e0c17030405130e07050d0302010f050a06060e0402090d02010e06070501090b0a0501060314040602030901150f03060b03030f160c1203030902090c090109140f060f090f0d12030e01021308 85
    0x1c852581ba0500600450812a040d60007401d1182d440f80d44140300c1031130b01c6143c03501224407034030000c29418120b40418040d15800d407039004880343c60396018450240c1102001812405c103542c114100188000081e000d01c40e05840681408500c4210b0300b0240c441d8400c540302e0070b8110000784801c090318a02202013102c1140c0d8904910301e04000419603d1180c01500f20554000d4a0350034580c41d180c4801d402903002074808261596191500b0f08803000803014807006040b195038221044d0301e5030600200380c4080c1c10f4458031070341041010302000034845080c1c41d2160944021000720300c0040c68644105441038014010502d50504544100355050700a1000382d80300b070350503001c191540070740c41c44035004200420307010231216041448054805201d103050040010700c00040c85c0c0b03a030b00102c4c02d9070f4807802d5100c010920010303011310380d81050010b041440d0416907414000840a80300d050003a44140c00711001c140d120401d0080b541c809405544811a541021803085a80c6c1c500440d030310b40c5030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 247004946 1250 247003696 247003699
    0xc051201060f08100b2205040e03030103020414010e070c26031e090307020613030c0602100e0a210309020402042304050907050909030d1b030e07031e0c17030405 71
    0x30001d6a00c1c00090030100440300b91111a034100b0b000b05200000c86c0c21010311981d80c0d00c0200e40006100c0e901c5028020940e42128080c569039410341c0144800c0d80c88540d000d4a9040180c4010400004102c072903a45c04071041c40c024018100c2890700f05444000c00d2049500a00030380c528581c01c1e44072900440c014456444907084011f000c081078038003104129011485900180040005400e040c0b00a1000b0310126151a10180d12a9504641010031f034110788016400107400540300b51040c07282d10960441d0a0090000030115510086071007050364031000c10b042c080c528141294003c0d00301e101100c0c1e0040c410740d100ca86482804814490240140b2103049405900c00381c1400c2508c510360045583d1000341c5005400c00050140d40789000d00000c40341d05c41000030840e2111301e40b0030700c51342c2c02da000e400c030f0320f48940380c6030080640b420a41d9813007268200c404100001131038400442c9000307000900c2000b45407002e0516124800142d8030012140903c3c00c2d518041220110050064600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 247006196 1250 247004946 247004957
    0x1030311030d1e0b0a050109170309060c0a0506100f090c120e1006230f060f0d05150616030e010e0d05060a11070c05150f18010f03020c0606040c051201060f 69
    0x30140100701729000c1c980309581c0460300001c0309000c01450410b12400d060103101c01c90f0315007180c2d41c002c680151300404580006401480c0c1540403c40248005500440c0840084103402d0502400006510613841465180350f0380f0302c8107a4100340500c002010014940e0300803c06491581585600c50b0300a0070120130282c80c00c0d0000c50482130b100c401c8101c4102c6c2c10420000c6110175028082001408142903900c25001d00140c0c0701c40048000400301100e9046001c03c181c205080082c0c1c240444e607210f00e11525003404030900440d072083c0008201038140c9803400301c46001000680354040a07040b4250408800320240051060008029000d0b1030401c00800088035209803903145406062001401c110b1415000c0110703150201d0071568100c0d16040f5903240044180c44030403280d010000f5928450781a941c00398483d038001400c41910b11395800c09500e401c0352102076a8582100620881c459030784d505d80380c41003a04c9030054072902100c981480010b540c66410140000c000c5100c460b00040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 247007446 1250 247006196 247006211
    0x4150501092304090804230901060c08030a0f0b0312071509120c0809041a010f0305060a03030c050a02041d0c01050910030b0d02030303010f051503090601030311030d1e 74
    0x710322004414110501d02d0030b200303500308008100006000806000d84062105010218a480c2c5a8581203003d0b00810846007041c1d1300b00040c050200e205a010ba414403048602c500702040500088036440f01d440310000508200d082c032100028145903d035140c2501c1440c03068145c01d02114001c118540c020822241000d007800f402109660131240000e040003021a0004080c1d802030350118035403446a0440740c01c01c5e00e400045000c80c1e180c1c9540b00d0301c0c1c0302d088000c10f6a07075030031481c890794403407140c58180001d143c0300f40403a2044503e480006c0c02c0040b55000581801018420302d08810742c01003091245c0300c0d0301c103401d11001884181d58982405589622400d030340c001c80c12200d000ea4080c00c038050340c000c5c68205030003d0548a500c142c0041745ca004d2400141d8091000310302034414029802100c82c282824400084400c016074000a001002070101903000040c0c00340c1180c6d4541b82c030784215106102c072241540030f81c0c0813544100d4140115090140092041c1d0809990340100400100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 247008696 1250 247007446 247007459
    0x14010b01120c1e090b21060901060801050d060e2401060503060904151b03020c070f05181306020301030b06010e091b0f090306090a0c0b180d030e0415050109 69
    0x19031800c0214004104101003040f0f0310a5210100b110b1001c250820010a139a07402c4003002a42c004502d002c1400c6104444403c41024400d5841e000f000130b46480109604148010b820b9002c103000300c0c1c0c85a2407510710758080060a800081700030031250160b07501d1030002c0051180c103828051161808846040c00400d82521400c182c0c0d104089c02420810507440c0d90b1600c0401c0f0402c002c24540c61600d4495030084e03100046080723071041b41140d400690720491040b404d414001d464100c0a0003040b41c0382d0801456441c5440b500184030303002d003100150780300c544241401c1c109942d001403d0a00100000061000c0481c040d8460322081c0c8504181c104924104000c0f0310007210002e001c41a0748030050011041c2c08040e00c503a8041c0c0300c03007620b45680c03500041d20b4600c7c1159443c07180d03070140981800300700c440c101240003402c2c541460740c01c140da0011402c01045041604a000f015000d030ba1000b4180320f8400340f502220b01401c208080009003801c00c040d42e010380a0715010651702c0c42c000036007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 247009946 1250 247008696 247008701
    0xf01031407050d060e0c1206040f0c0b19110c010c2a0b0702040b010c031b050c030102040306050907090c1d1507210207150e060d06080f010b0916080a060314010b0112 73
    0x107d000038000e03040c1980c590f5218480703070741106800d0b50760140b001c90118203142e01100405035085043c605041200c010f80002f00003a1400c4e01c150340c1608501c150742900d98020040f8002640d0202c500068400c3d03521489210881d5034913116140800c49500045140e051001403103071a001b03880503c00303402624015150042a901c0041c0000c40724a1000e148101000210013154412401d03544c00d84480d000003803d81e00a03400c241c0d0f40507590424414100d104004002c002c21182c0810711580c4191030001e80181001d203201d2000303c0c60620001201e0351480902c1c0d10910060000b030741c8a00003804c00d180451540d02c4070a030701c91000c150b4901c180d0f0000521a0071181002400012001c640800f100d0421040d04259080310060082c48100d000d24010728028141c94030041071008106c00045094660120015008411100c28065a1035102c0151034070070107241000c19840d104c10000e580245103561001d00240c5100c0a00e44000307006400c0f40780c50b000241e0340c0002c8441505c0380e0604 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 247011196 1250 247009946 247009969
    0x801060e01140915030616090f06080c0d150e0703200306040903020109060c020607120606080a0e030c0a050309011d0a05090408070b040804030b0f0f01031407050d060e0c 75
    0x80150052201c001d45003d4060304c1d480b142101006245098042c0800d190620641d000b06401641101018070036521944420040030b00e41401d101e40307854050050541d000113000c07144a000c0006080b001100d40b0303001900707101c141440d0001c1c190b1780c890340a409403005407614000a418820040354581d40c0c41100340b40e443d0b030701403164a10740f500d8080000600134198110250b548030807802c4c1c0400c08030f00c00d0b81e1031400c280d006003241d454207410003072410702c00104822105140400610613280d20040c000d5100145030000038050100e18034035441d50191500020700343c0f04820f03820b4100030340880600b178042d40a1322104400103044054055a83c0c910680d5508902e02107810410341c98102c034000d801174088ca0310715140100725142c9040703414045030b09440c45980041d00f081082170102600d035000a10100e01095800e00100e2128404010b21029014041c00400c50941c0c09080c0140d60080400034010410142d90749800c5015215400c510090303030188060504150130900c06482 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 247012446 1250 247011196 247011209
    0xe0c130501110703061410052707050d020a030b010e0d05060406090f020307030c15030902010827030a0e0307080a020105161104020a0206060a060315030f1401050403090801060e01 79
    0x1101a041600442c0d01802d84000c00506100b141000004203000e849074800c1041c901c440d080071840d010700d425500601a511050050030200e1043e860740307403400007030718a244450b42c050800c0e48446004480718042d8031401ca103114030001d5407403151038041e88100f1a005007a00c9080d04612548204456403c400c8405806500074000140021703030b49030b21600344c16226120104404055401080c42c01d40301d600125050207980d501404407403141a082210f03d0001d20b014040c0b900c2aa000a100e4500504082c2c1003000d42c0c1105146440c001c4d1f1240c2c40d00c51007400b00c944995104100800ca10031113440349000e4040c801011600303007404a040c9801c85d4040c1c403a03e10301900305085551440c00e0702001c3d14900d1905218400700da030f90380000d00a442c0a98007c020070b0400c0c031b0801c215040d241c0c0c8940140751901d004000030310740e902c41c40c1e0300302d03900003030201da024a42e428910855419500007181c6035203400108420141c0001c91101503a0200008200503a00c840d0702c074090b88420b00407074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 247013696 1250 247012446 247012477
    0x513050106141806060403080a0804050c090c27040527010203041205030c04090911090f0603211b0708070e01050a0b1b0d1d0307180b180901060e0c 65
    0x103076880c82c2441d070f10713070300b01c000604520300d0165a03403208040381d004480580001004030052100380722080250302540308048414030000d0400c0742e5028114481c845035400c0502102c0030703008446800049002659101401c01d00451900602050825816502418001d100c590034001360100510030789101e20f60001e0f07a049651501181a03902c0e41005141040c0240c04210200700c107141409000e07161489500113040680543c01000326814008058804200c502410480c06a8001070000780261040c80f140c01c480303020b142e01440307034400e80078441c10142c10311000811003030000900404551916055654954550f00680d03c0c4010038410151312455400081c400d442c010f80043c183c900c02005442403081d0080e500c0c81c2443c0010341810003180c1d03000c00c14038248120009010501c0e10417006000c5442c2420840c06041c51001c1841d40030594030b41c1c81844035100c030300b080303608406842d4248680d8680b1b2141240a401d0500130a64030361381080200b8254440001a200b1000004119 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 247014946 1250 247013696 247013719
    0x1080610080c13240602030306010e060a0e011404030507030c03050f06160e04021b0c0a0b0a0203042d0e04060c031112070509060c010b120705090a05040510051305010614 75
    0x610016108420315003141013410591268520100c4003290300802454000d591a440d1440001d000000d8003403900340207560400c009407600e40d204a18020002013402c0240c1c0c0250702d414000f10f14000ea8000800611607680b0200512051081c00d10481f03210b402120400c040f01141d064840c41c3c25940500b0b00b440010141200760b0040d40c20082c0c00c2c002070f0006042069110820220816134600e0b0175890b048810034248600740004424041e1202e00c080030314102000000950341e02c66441380b140d03603015507048603051442c044480301c64020f400b640029031544520340100d10441c26241250200d00c0d00c0004100d6602902502c0c074045540e0a9150400c103c012603d031030150001c100c4e000f00007003000403080c0b40d074815000d0181440d520300005444401c0754140140e603203101b03101d027103181d01600c01003086507118010300d6032100e02c1c40c4020442c0d888600d841071820310500e004440349400c00082003500900412410f0015008000034821580d4628010840003081000310340c102012038035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 247016196 1250 247014946 247014979
    0xb0a0207030e0a0905070e1909050a0f05010b030a0501050f01090605030601021606090e0a06050d080a02030c0303041103150411040b0f10050415020705010c020d1a01080610080c 78
    0x688203450003414140c0d040b02840001034140c04154110408a555a40900c001c480d0b100c42c41002d031450a1301d00e05111042402d500800f002e45200b001406600eaa0000b82075000a801000c036900310440140400e58555040d91000e4108442c6215221311f844000549450860030101d01c500381a1180f05609040038021034480e400140030030f05610400e5001c0c142c104004000100400c82960344580e0681402c840e0f170440c80020f0000c140e03060402d1000d01039555026059004150b220f04482d0f655000324000380d082d80286107803c0c405000220410050015010901c41c02440440c2981c512096110744034491f440c3c10790740030301a5040d2003001c80181c1000d43c8025241a40200902c0001d0100000039995541c8864058006600428100420300d000750301000010424000f5021481c01c0400081c0100d94408000e403103050074045090600140c210303003584082c15103001030030560b1161400d907030300e41082d111142811410f030b100044441020a4580c03500000414450f110f46141c04c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 247017446 1250 247016196 247016201
    0x20d020a110108041a07020106090b0a150e03120a0306170d0206240402030a090b060a08030703030203070516030c02010f0e091305010b0d110102010b0a030201052208031b0105010b070b0a 82
    0x140704840a140c0c3c1c030500001400032000080c400c86c1d6642c0040341103414605e80d841070b6055403505900405018400317000c980c41184201c1e031410703c1072902c80d04405905001928000d4011020300d03007039200050305c0301090b526402c44401c2d10440800060740011031300c2c1065541c100030341198010380050b00400c04600c070718200141401016901d810007e0710550010f01284e10541e00409003907034623400002000035a0400c940d01403401c0f11124401880d20704440d0304c03442101c2c40201055400800204128020000d544410340103c0101c1220301c1d242ca0040d03d0722140050503800705001500d003000207031140409112201002e031040300191900c114400c0b850b004840c00b20f80e1952100176044098441e140c1401c0a01d003d6002038039840040e40004e400c4804554038140200c00c128014400360741c00004448220014010030000050840310303201046020fa003100c240d0303010000e80c02e9401500f44c3e18090446040740c00030032059a840d00c030540346100d4060020a0000b501d4002603602c1c1e07032507 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 247018696 1250 247017446 247017451
    0x1b053318010b0612060f030d05041e0f080a051c1b060f02160b0c0403080306060a0905090108030d0f020c0718020405190305011b050316020304120c0501020d020a110108 74
    0x10001003101c8001c00001034007600000360004034505844100034462410f00255030030300c10141c01501d0300c003032308900c010124490341c0110070011581c0502c244800400000c5080204121f0450001080c0c9800501d80c40700305040c401d841510403210040c890071440810440750030700548481c04003c002c94030f0004025032041040c1d80042c0c0d650b010b40e014200c1c81c0020034480320a1160080100035602d401045090040c0c0340901c244070510051000030a14130441703410035000ca41950f02c1c2c0680e1081101e4051960708600e400c240054000500c144001000d005c0d2021041424040307400c0f03214141040b4000c005582455500c240300400130180040f40300b0f1101a84004090703c0e02d51038a003c240d903820313146080c0c14203650036170703040007400390a2050319103240c10908940f1144540780c0b0024001e00002d0100d5482503d4000c480807100e000308100d170010061540310503641c54541c00c0ca43c00c040800d205140c094010b165100c0d003c20302c003150040405620603003259800011100444030070100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 247019946 1250 247018696 247018741
    0xc1603082d070c080c030a0f09091b03051810020a0210050408070305070503040b07080a1d0109050405061206102c010608060a05130510050103020405060d0c1b0533 72
    0xc005d05005103101344010103805866844034140d81043d00b4000b400028140e1000d11003a00d040c00c0c80b620124030600c845513695440c034000c035080d1624601c0e00140340c100c5030711419612400e400b1070600a0a500508002c40454094a80b44800640d241c4140d03013046a00402c000420810000000d003d1000f80c4903070386c00390b4102c1c1d04003619003103d00019809104195403044001c940a01003e81c458461403818840600322022008d801d000038003004005d0150600c82c50315880060701725205e064002200c2079081d42101c07901c1c2401d80d0211000000d0340180ca1250640030503844265400c40124602ea098007410200140c1c0381c09400c80d00107501812042d40f006011030006090781e171b00710104510041031000000c590034003c4540f030302080c50b41c1c0442c1c1458014001001b02d0317aa004152062501c0b0303035001040c000c2d40e0003001c4400782c0305080c220500c500800c59403003e0000000b03009c0c800150140c00880003550074280c142c54003030f81e00c10b030032a80203401000500d905030040b0680c0c075a0b40c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 247021196 1250 247019946 247019963
    0x1020c0c15071e02100302090609100e0301110d060b0f0315010201090b0403030c030617070302040e01200307080c19030b0111071508060d0c05090c1603082d070c 71
    0xa40c3d42d024001c41c4040402110121820011001e601d080ca68104804049090452500c2c4243d0042000c2c0d0203007980785c0c0d2207240c0094410100b503018011706000d060004000b0801806991180c000035002582101141c1d403074200701040340100f10303003200e0450301f900e862a801e5075030b8410b501c0f1648107060080c5046548508024001508501e4524021480f03510007043c50b485101005007111321a034054644101c40c51052781007036401050a800740d035015200404c2c9004008802400f6000c200440f01c012124080411f121403a441c0140d0702502d8036036616140341c0c94192500100e03004142041c0080814001e0800d14036010340d203c0e021450041c104580c0884d09000001d0406001d80c0c006810102082604e11500c0c2e03000740d04a6010508a070f071040703c9801e0381c0341c0c040340c13174554004e840c052501203000ca00d03080c001500740c658101503050140c1c40d210444c5001003142006031100941180d103074000000030403454000e4050500b80384250016035541e684200c0340b49007451420350f1880b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 247022446 1250 247021196 247021207
    0x170303010b031906090b040f050103020f010f17010306021e040614160f03091415041509091107060c262806030b130c0510030212070c110301020c0c15 66
    0x8143d40148001000010b0001400445c00350601c0152503600b090b002c2c20510b00001403006a0700c4d01050043c1c1c01007032800200c880c80c07030b041c252410410180e400500c00040c40000040080b25001000c144500041d5032025904190700b0314180d000c0c6018000c0415448018140134040200c0a0403411403400144071201b40f190301c0762140315074072120560008003071900a01071040341082c14402041c0543c0c6000950140d6090200c16000b180204c1065526050700b00303c0051107030320010040d1482990401001c59130034005036182d841824129407603070410461100042c000d00d200000341d4200300c81c080c12080000c0c4820100c0100400c035904009100ea0141026a040e044150642c0b0406000281042c01c50620314000e841c000c2010b001c003008000c4420004600061110498034196203400414803070031001c0d0060300404204035103082000040011140d4400203005400740140b0000c039100d22030784241800e0748580f40b1111003035401001c0c0502241001c040b003d90340c0d080c51500f01c0c00c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 247023696 1250 247022446 247022491
    0xe0d081302061c0b04050c0906192106090605090c0d0903050d090b060310050408161104090605060103061a040612090f1202060f01030b04020f0102010e0f0115170303010b03 76
    0x3e82c0802200d411999a90314003840f4100b5200d801e0700f0000b5003208600780b50045001682c00e00c9031082c070311448403100780240865401505000701034038244001d500c001c1142c000307500041c030340c034440c01e46218100f87c000074650900004150044505000c950303e020b046460712006042081000c8082102c01c1140c404089a81d200362018548031703007400e4580342404000c0500c0c1042a000140bc0640b81409000c005403624040f603002d440c217960f00d165200b074503080c141048141c00c200550440c0c00c00007000d00300301c056803100c2d2055600340c8081103481d407514a0031700c40c40b400050f809800b40c4200400e2000038040c2c07540f000c400301c01040108008403e59a041d00d83c440c40b0350121101c0541141c624582c54041c0407240e8440d0349030000d100710750301d1500c0d000e070074810190000c1d005030f0b582d4008a1169100307400081101050300b0071100c00607510100b0758028645461409041c00a0b00e00108140801141d09110005032000a50441c3d081a61214140c1d00151800d00750703110000f95020003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 247024946 1250 247023696 247023727
    0x30f111e010c09050303040e1803040308030708040219150302161b0302030d050f07060e0a050a110a0b070b0a0e032101050103052a0d0b0405010e06040e0d08130206 72
    0xd012240046104051000b0103802c00d1040e4100620030740084c042401900b41d10341380280d00c036032503060405040e440340a9890440c401c682000d806c0305000401c020302c45411031052805940700b506c00b82c4800010002021024010f030080c1d1000c21500302550b2a82c070311a401030146003100c0c003a43e0b00c1001c8140d55071418885441c116480d22020488204258a414844c1112046442c00d200d81340841c07a8000b02e20034881c1c0744004110baaa1400b03100d1120a080244140c501da2000848403000d41505043c040320b4650026640f0403401c072072000c2454100c000586010a034000d40300342c2c0c1602c80015001c00382c068203240c4009484140032200600c00c030400d1008103d00306295400303030765040000041c01d170380009100c18a00442810800da0a07488840381201440c0700700741d95900e070031913600254040c103440d421803584035080078000b082d001640004103024040c1214108429011a0790f01600e030141c03006204d02040581c0009068039038546a401102e83c4010246031800304c0400d00da03102c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 247026196 1250 247024946 247024993
    0x7080601121503150c08040f020108070504050607110a12050a02100c021302270603150a17060a1b020d050708040e090a110102060603030a1b08042301080103030f11 72
    0x100b0b244024201c0c1c05400c828440c03401c01100c5446c05400c1454161110010390120a000904001d0034400052005100703000343d038040d0800820707040c0c0e00c1142c0e0074403d00d080d04181c0402d00c00c03103c440c800202c2c0d5502c0d13103100c000c082e40040904540b50030782d0200450422181051004d2002d8102000010780d2840e0f6104251a124400147c80d482c800c1c8800310307000e01d0068041c0200400400c0030390144d03128800d9aa000011401c0b828000096002080410b05143d00c002545030b4000d5480391701840c0811840d101d0f50f00c0c2d00d806c01c4580c844141044142d110000d0100140e00400c4295007076070310900c0100010f90250340c000c3e10b070a0303845040664031082203401d01c5d9150807940700c03001007117007c210b500d1121000348001c01080c10030100180e268482d200d800c0c018802840c0c15000c41c2204558440291074020440c2500c869885012070552100d4490860102d0400c11160382c0d20340c002c0000c981a01d403d55190403829484440c103075015440c000c03140c1d009100703400c0341a0340e8900007001d10a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 247027446 1250 247026196 247026203
    0xb03030a02031305010c0b0103080319061701051308040509041b03060912020a170c0703061b080a05040b07050327030c1204080c011809050a14010501030507080601121503 75
    0x181e5820322894800100c40b004e4012504001e0850440c20100b0010b801c0e160549030001c201e5540c90310b903440b88060748209070713050020403400c01d84005152440e101c1070000e0110390f04001e00c03490751610002198103004000c000d141009c00c4c402130256040054441c3d5001c2d01c42d01150800800d086c80311809c2c0b202c3c1e64000c4a81680f0303481c0302c6007000004151100c550180780014a800d1030b00e9a41c11400303150907101d0400070440401c403003551010400191005680200c82000100c0000702d45143d82d460103607003407001c00c80483c0421103c1240e8851248150380000682c1b401ba117809408595aa001400040c074a954000211204500811030001c070031040c180207582e9200b003421181d00b408000c08083d03441190a02007000f04000c04a520075803520f09203400150142544c07400c2501c0f000c40e800c82e07000b5518110401c007042090b648a5400c0940d0301d25201c0782c580e81c40b0011030507107904a62010000300c2d0000401d4240d4000c018010b01090041e1002c1810b1740c81c0440c00261030314962054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 247028696 1250 247027446 247027453
    0x2010504120506060f060c06010501031503210e010f0516030c2001180302030a1101050c030a0e0f0a050d150209062a0609150c0d0f020a090e061c02040b03030a02 71
    0x304841c901101c000c0c17000c9005448240c141500b84042944907801441164140b40d00c80c2418203102c149d80c1c1911001c0e550190a00410911702c050b07400c034280b2854519004201c03d070403c050550700a10841daa1010303d5601d03e850201040f5a00c220101c9160007201440300301500c070b1000841149291541138540c5c2c1200da88103100c00001001401d600100320003910141c002880561000f0a0900d10a80c2080c5240360049070080100c480b4420352151461038080407440000d01c0d540402010340c00e220880c0c0203000e42d40204104550300d0b405100b45580448007040d07100001d19000e0448030700041544c40141401034003000b00c2c3c60f0354001040c058200410b440c8082c00101240301d20312126030804003c3c245d51505415455076101042c0912580391503503c000b81d8644800c0080f00c5580507120402e110400f01074503010040c1d0004050709011400070740300412000c803400c810352301c1071200802c400c04003040d1a00362003000d51041c03c140d81003901c41c00d0180a030303201040189141d50030342d03006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 247029946 1250 247028696 247028701
    0x1b070f0503070203160506070f05030f030906090705092203030b061c0f050106020c011803051905011a2d04020301030b01260c0103240e070207050f060f0702010504120506 75
    0x401d800c1003030a030f280e100c0084040c1e0080c0701540342c1f00240ea5006074090103a401e01d04041c240a40b0f035004a6546903200c140c00410800040c2c00070509a00880315101216222f81e01c400070400c80b03000854010400042e5140130416003149209441447d07402410001860420540030a03001e5004041d03c140782c446103074800b405d003101e5105048803030140741e800300065414030400a4441c142a914141000200500d524420101c619564011903002e011235100c80d00380359005004507101c0d01c3c00ea402d07518002c1046900c20301d051114003040c4000b4030400d08a440e02200c0350a95480c1c03d15407480040604100000c3c0e10f9900c002c0d400703907005d40e115103041c2d03162034480c042c2c0c1262514042c4003150f0360209220111000507110803220001d00300415240c948a03940181904402510f440301d0768034610001d04050b100201500444959080e20301d065254000d00594a0200b12032641256040104290401400014001c40e41c4149403051600d50388180d5854451030a00302035400d500b21206 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 247031196 1250 247029946 247029949
    0x4050403050d1a10050c03090405100b0d061406120f0a090501050a02031b0406050d0203040212030a03091e080d024906050f1e100302041505121b070f05030702 70
    0x303010310340e0840340745c014a012407420000c0c2e00c030b024110443e4092602c690102e8900e02d0384130401d0014002c2081c425407605408003815010780168800c00c1b14500d091104048581040d404548000001c00d40c0524152a66500d5006040c401800010b0b001da42d0b070420300c00100280035035070060b180c4480140c0c5030f04100d401042c94a541c0c004224907410100010428150407000399000303071b40034040040c0c40b6a501c1c00032039000c0c00e0300030840e2464000022034040240e050340c001d00a0600400c0c1d8000ca80d0801640822a000701c1403010b4041074050040341495155900200209800b5203501c1d000d064096001d02201c01c400345442c03c0c0c0007269001034001e104d07200c84490340044150340500100d0314160204480450700d4181c58000d01920640c0a00028000c0340c0304002030015001605074425408018003d400c180118240a03a000c11040d09951007041504c0d0300c0450407141ca009501e0700042000354901640484900540903c00304006c0303035441e40c044280038040c03405035503502003e20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 247032446 1250 247031196 247031209
    0x10090e010605070512030703020f040308030411030c010203070f050f1203090609070f1e0312111b1809120403060c080906090d050c03120406090308010909050a0204050403050d1a 78
    0x2044841040410300883d008580006196000d280c6403091503a607030f0f1030740d9004901911500400b20380d00e0b48000f40000c00c02c20460700940c890742c050300c96680c8410301d000c20551a03414180c04a401603200b0700c0f0300c0f0041000480d451a105201d842200c455240004401c1e0a04884080540c082e110100800108442c2031107050740c0400d0460103004204d0030b007003420b40010f61a0040c00760303122641c01c03070a0a2060584920021f103410061000c1c00708480304000340350030121500311001d1b001d14100a100308880420101c40c07600300a001e0280303c0c4281107159038442008100010383d201c6c0100e0100050503000040c400355000300d401055011469002400081001d810f02100d0b6101d5030400c005000c0106480c800d08001d071605681e10547c02d090180b8501070390300b0350720300e03405454188420007155034050444a031290b21002c03800d070b030b9590850040300c3e0141c6010b007441d004800d010005150031351000d540a407003418480e00301010070800c038049030502070f1852079620041000b9001880d000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 247033696 1250 247032446 247032449
    0x307020f0a051203060118090b01200d05070f0b0405060f010608060a0b0d1d070504270206130b07031106010b040303090b03070c02060c030405010e0405060f09090c10090e01 76
    0x200d00400091070a980c4035540d0b20b08440c038112014102201180311a0b10070044403240f4125002240322054944103554000d010044005001c2241d81c52041a101d03001030302a0649000203000d46100b2521070816502c503402054221001c022000040e400102401c2c03005000702d0281004105500d41110400c01c182e01c103800200a100c00d07002002030583d105004078083d01c100790041601d64007500048005024041355804242c00035008903134070741800268203000c03120202c8042c482c040c00d00703600c10000e07003a640d09800c0039245600300d000581403980c0200649076200b024407034480d40d180b02c8580340340c10185080300051800340c03d61000307030f0040040b140505981d4404618103072460f03602600c120203921072a4403282c00070000901c45400366116249564000e81040d03940c4259000240e103039407250117824007186844080320858101132151a20500340070f080d5400402e0108108492904010a803690303d12421081c0b41c041c2e107640c00c05800e018890f4072140c2d41035041c05108100700105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 247034946 1250 247033696 247033723
    0xf0c090609061706130507080d0509100302040b0708071b090e060f060d0b1305030a110105100518090a080c15010504020a0207060c110d030f0e0307030c05040b06040905010902030702 80
    0x707540804200f0f580105040c0e070070920802031108031003640d1170700900344a10307940144032038058000907070f4065801030020500002c040311048900003c491080c0c0c00c0307000d80c7c000e00c0700d80001401800001200040188a224003031003000080c00c0598103c031a01c00115001440c2d002c1d194204c4560107282003090743d070006540d540c40c1890f46420070220f994116400805007128a004000c030302081851582c44a10039080829070703648000780301c00540390522829044032150b10f02400a5907840f114010002a03031001010301d1500d21407078120496806010741a42c0c0310703020f141115400669850000c0001010701d02c05803a0140c40c0200301c4540c4c44050b40500c2c013403070041101800300c40d0301103140b0041e684a410003c02610031820402d11950310a141d0581000c0c0c00c2a4000905422580022044030340e91b641114550384201810b8403203180b07104c010403609451205000902d41174201d800305081c081c00b41814030390744454400564800b07a00c014403207a0f00009005549e030303040c40780146a200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 247036196 1250 247034946 247034969
    0x20601060e0607061b020f07080c0102060c0a02030c060a0b01030e0705091f08010203102d090e03090402071a0601180302010c060912020d12140109090f0c09060906 72
    0x2511a01511030300c0d559141d94403404000841104002c5103a0007003131140d00800b1381c4d40c0c081403a100040c0d590742c0202c0c3c224815100c1c208000514180000b0000b2003080180d01820302da0321a10060001e503040199400150b0000303024103403040b01c1c20048076104082115000c0b450401e250300140441c1c0c1e403150503466a810040083c01244c0b035250400307802441040020020034007100d002e00e50102690020506540008280f180c0d145000251b0001e80b94251292542c100048000481c00c03482c100d030400340e8544520341004a01c0440c0d100644403440d00040e00d107484e22140008080b03074407040e400c84102520600c02000c0b241520078240c3e0100080c281214014140da18500f058100e03848001d040114164001d42000000d80042c02000d501a01d00c0f080c2e18200b1002039243c400360000c3d200040d01508100500408501510442403041604154241d00340b4a42d40041d11059800b6102c1204c0d4941c140c0010710300240075070061100c008000380003410828503a040e585998080401c191 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 247037446 1250 247036196 247036199
    0x90a050a0201211407030c17012916110a0315051b0d09110901060203250c0b07050d0f0507020f0d0209010602061006031a01050901031d150618010e04031205180d020601 74
    0xc8004809054851515140c0b603980172b00102c810011110070125040590003243c0c000200d5a8034003101040d500c1880c442d00401001010b04c964100d00d480041c00c03084800413510f880742d545034402500803001480e95030488480118200c2c80b0350003040308101d8143c0e60950f05007440390040841844c9541110000d41075494504000d50700d000b03100c03040c1050b600c48000c4401d079015008900b914207a02029010314903555021906494015020030745150085a00d45249a481082103200481d041c0e01c41c02d090520030340034050252045460981c10980e106440c0001da52560445802000c07e1360080c00d50b440c1c80f005400000313515620800c145401c054000480040d40c0c004107400300d01c20b01e009601d981300071004038090300c0081e14504e403040360103c107260750030008100c02803d145000c1d1000e200d91140f90500c03030586054034654040c1e1850000502c800d815005440d0b40190181c5091310071111710341d440d40203d600903600c0304403000364440c908110300424004111110304500107002c1c2903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 247038696 1250 247037446 247037477
    0x230703020903070801060b070203010b19260d0f02061302091902070b0a0c0f0905061806090d0b0106030b0d1203110712020601031401090b01060302220803090405090a050a0201211407030c 82
    0x2071082c01404ec00c4041c603521039004414502580c196501004111200086070020140c0402c14240d031800040c0039007000208402240714854000c150f01a040d0512581d812030b4000c2c015004840042810f902040920f0100c1d2903070b80c0e40ca02404000e4400102101c0e14107000e41400681d110b070009001c04202c0401c07050343c40b03106840070300984544645440c010f540008106101ea00d8207603900c00341c00d58181c018009140c003030034180c03010342c2c404104400c2148100045070560b000d000740307001c1803a01d0059005119800018407002551182ca06012503603881e10b00144482c04d01c000180d0000b40100180b040321070360070945003100002080300e14441c1e2590901c031601400b45030141a00000e170b40440780340c8401240518160742e032401d04085e488501180c0c41c2d6006850031441181010007090401c000802d403581d501d60301c60018664481c0300d40c01958010100b561a02043d4400f0303c2d00388070001c240c0200e00000d0810280c5030150710b405200a0115a000060031007000304014158502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 247039946 1250 247038696 247038739
    0x110a050423181b04110a090f0f03020a0b0c24070e09040308130203250e060414130303020702090a020a120b0f0d02040603081903230703020903070801060b070203010b 73
    0x621102c3c91495a54601103002c98050084d00302403030103644000031440f035119032010040042c1c17090201481b58595494046082420540c000079520542d0041c08016022409004040f02072100e429200d88202c0424094010018420640030b80d401c0c0c10200044c240d0302c0340045070500f4080700d000800f402c1940700105500c10051200024000c10200bd0382036540400a280c0201d0780320740300c1e41c41c9a2105083c0750b013203d120710400604035900300108005107024000d28040c0c00c0d02c01e01c0c0791810342c1c6141d10520110082c107000d8060503400c1110300056140d45031140c0c07142007614405a0344803141c0718010545580d0304040038100c2e18110641d101951800b00480c040030086804020541060002034024a140d50000309401000100b24070645039011150351400c0d21a01c00b000088105030311100850710403001d18190384120383c00600d01c64000da02030410002c003e0201d58400d0b45500403503084030341076001040416000f244038030071890300b4003480310410b4043d181200108200c0000041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 247041196 1250 247039946 247039963
    0x6200403020405190c030b03061006022806090f051b030319021203041209080d0e06030712090305180402070206070209131a160302030f04110a05042318 67
    0x20503612540400c80b8101d508455078201054004100040c194480d0086c009000f9003001d54000d01030b1b600000c14134500001003400700c80702034010300036490084c03e03403c5580354090a02d0880845c0082e81e075000c0b54081c41480c40c02440b4011040303151080b41043c83c0340c2100c042c9030480b021140c0446c0140d60f01c0101c1a079070006030b034480036200560a59000c0c0e061005074142e0101210001c801c101c24030101003486a90000345449003c64241c44181d500d440382100800348021807040c610300000c0b4140b2100540d0f002c0214a41a000c1194040d009001e83c0c6025070b0131780028002007188403102110342410188480210390442c0381aa01d0707408070384a8028646c0c007901c2101080001078821030b1a9001180d030300e0384a10001c0c2c078096585c09004045c00c050b81c1c0c0804981d194041c3c1c10416000e882203901800c80700c03009024a40d500e595403c100720042c09900d0b0441801d02c4009120b0f20740340562050b02c0720034400d0390032410391020501c0c0e884000a00f0b030902d0500d021403032252001e0124a501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 247042446 1250 247041196 247041199
    0x317060d02010e030705130b0a0509092109060309010b0103060b070312150b030103081e0301140d05030c030c060103060c0c03140304081314040e16050d050111040f030620040302 78
    0x1480243c960000b80c1090f02e540d10298124003446103480d041c40c0749034445042e81100300d0703c04044548900c18005c1c020340c111001c3c0c0f156440041d075401c2c00f541c0c005000c1440400e80300303110324018414021602c603400a80f01490140c1d115050f8041560701809442c0c060702c44000703c9410801d00d920000c0141c4100039040020030b5030b404040e0001500d0449510141c40350b01c900350780d2075a483c60404820360010400c070030101d0043c40e216441c2d44c80308003264102c41400301c1211401c101101008203801400c0be0886607480200300d031481207a01800a009160090409445c031585503007410700a0b40c850400c1d610401c010000a00d000a811507114240484680603042c0c40e941e9900e071100f90380c41040c58584d0440e80b81840040d414001156099014106803410f0015980d401c01c0b42d079503603a403540389055103610840c0c14011410400c1c1550390f814011400443c801c45d00d0304203a441d0b584140c00451001c3d500300000c0c400d0184900641d112403206001c100510b0b2b003580c00340700240c02a400001d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 247043696 1250 247042446 247042457
    0x50307140c1e03070605060a120204241e080a0b190605150720030d050c03040e0906010f0f08060a0b060d24090915050402030f0d020102070317060d0201 67
    0x4a03070101c410059160000241101a90091a2a400a40c2c1d940042c2404c56943c1c3c200000130b0040c5c2010500c900464006000e5400c0d4104039908000140017010101540c513079115018000203000c03d10014000d14200c103d040c102042442105201e00f4203800c000c100d0f900c000e0700c1c180000c603203401d40f0380c2c4411b070140b01d0000103c001d0688005444154081540f00706003134501e44002440c8002080c0c80c0c0e12032030b81c2c01c1b102d80e440e404111201480940c0c0c0f03a8076400070011040042e004900601065015109072032400307848904d0100111002c0d05e601c035244d803200d00107000365204c4000305400303000c0b00c4410280280c07030300b42c5035941c40c10010804000e030b549035404a240354854000fa00d510071502c82e4103000f014200b106108000c120a01040c1e1100d5041b075000800070580e104000c0c21316002601100c02040402100000e03220141003240c00d40315260101030100d00901040418105650000d6529512410000c1c00c001e14590282d0034000e080003801036590380c8901c40144141c1c2800d22 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 247044946 1250 247043696 247043707
    0xb03060f0f1801060803030a05071121040905040f11010801143109060c050901120b031207031d0901080307060504080409020406020102090a14010c080711130e01060605030714 77
    0x400a144203200b94900d6003402d6021a0f20711012000d18443d913841c8400f0402070707541400c00c44801c21036892040e040d0b040110700f48090b8424040d40403514190030b241500d05561140b000044800440701601d5030010305603140b04000d180c400c4850001030900e0000c1c15541032003050b452038028031200510900030b0028604000d4003540a0510030440e1075461001d08111040030350280c04050011200d10f442e0107014100e0714041e0041e2412100182d5440302e2550f528504440200079500c045589441401a0307510b14202d010000c000e514484c0e9075101c000e415446004000c401e50301441c0b88150340141c014000308a000041d91681500060f0100340c540340d0b800c09958902c5a504410f101ca07000280225119805400500a1140c1034a0a94031141d03a08018851000b011205500040d124a441408200d113040070303007403040c000c241c80d02c0341d81223080000707680c0032004081000d00c6480b0403004400700001c1c46890000c1c402030070f04903d0f528081400403c144020b006080d0070603400305070f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 247046196 1250 247044946 247044961
    0x30506071e03091712040218010b090402031003020a0f06030f060b030a0203100509011d01140d1412030a0f0509062203031104030b10120f03110114040b0105040b03060f0f 75
    0x500038a0b001e12100701c19517418100c000700a100c24100c1d41640958085102c458105414403c914100ca02c0720200340c0c1042903032010003010f5440075001d05a1210060b9020000da070310b43c070540004081e12041c8030045450b240300901136a840c828036803011460304508201880340107049940c40780d17551030010703560b6a954100f00910b180c2604100d400c06480b40007c41c0754a0090302d001c05003090030348804850f03a61508246d600c040d000c80103981003040540c4a4002414244c14800405244c009445001c02e00b9030100216800440308601420b4940c025581c446000c0e200c0c194020300200041c00580ca0880d64254030b0514606006a03026a510706031418076200c0d82c003e25030401042c04150381c1d95a20305088c800c01d002a100d00c010b0300b00e845000100491040c03540c0c0300031984000030104944454600765100360544042103c19500d6000b10503442c085035071000d110340d11a51580840d54106401e0008903198040e0031030080c2d20403024031080c050441d085035400080740d0781c5101290356085 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 247047446 1250 247046196 247046213
    0x12070318060809010e06041124030a090c060f02070b031803040b07050f0a030e0402182e09030f120c050a06090201260a0f02040b13030506071e0309 65
    0xc5080c112400e00800105086074000109030140c54030384000d204006a003905952140303000c0e82d00604c003241d41d0b001c0c2c0385a81020b520750440f041c100c06002c86032a101401d100f8007644200c032512009980c1d04e085108003c0c06108020140c03c0c0c918050180b0001035901a503200014001c0318091755021000400d038550b26018200c95401801c2966151651500720403100d402604e07007180c4901800d810301040e01c60008800f241da5405a03551941102c6500a010080d0f200580d000c24401d6072101c4040e903a1500c21440700e000034084540900b601d400c0c0c1300008415403c50154041141ca04010400b003000405504240c58216001c0c64922100c0102540c4080803000000c0c101d000320b91010302072280e00c3c2e0000400354005c0e22026000301c1c2c50716000c902c180e49084145ea151440b0008240c0b606001ea008540c00e0360300c48401441c041e1110802c03122074204844450311a090301c4c0050040005c20300c41d00d6045034484c2014014082c144100440201c1805c1d214402c266603408050103100081 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 247048696 1250 247047446 247047467
    0x100f081b0f06070501092a03140712030c020a0b0307050702061606110c100c1403060406030804081e1c0807051e1803060c0d110408010609050603060a02040305120703 73
    0x28245035803181c0301e20704503000c1d0591080c00d954442c3c900450346c40580b45104402c10942650304042003141c20340d60f440c0b1203910364540350020762054507000710b43c10be01c8194101d44240a9207408648540d03d204110080c00640c1020900c2082170061100b1203410034107444010b9412130f549515940b0a41894046483c4a80060403440c10001c421101c0b940e9100140b560034206000d80e90a0040360714120180c0c0d500b2a16500040c88810307091011000c41c0f0080e5420103070040011400955980700c1d40000e400c19000101c9a41000c001c1c82000340c09017400c1d02036030340e040d030190100301c1d51045680d6a0201041e50201400b0f05031000800480c4a101100c0d410021301010810840d41250240c4640d080810704900c2c0580041c1222082c0c40c0004265106051009031280f8010420030000040d20b0038912000f034448041c000415000307070a0003024086c041807a4000b4551414004151414201030600c0480034410881400403580218100340f6032540151a143e81e4405d9203400c8500504e00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 247049946 1250 247048696 247048699
    0x30905060f01030c080312151f0503150103060b0703080c0415021006092901140c0c100513030b10081603050c01110c0d0302031908100f081b0f 63
    0x5210810040c040d20703864141c181c80c05821414400e5481d007074002d40d42e200c0c00284164030001900040c941c1015803d06c0e040d003620103414843c002403514a4895201040500030740890000701c10000b102c5001258902090002d10f801e2004c58074044020f42680300314000503042250f02c00004111b005020302320313401061321094040d002d140c05180251030b64031040c606c2c4080790901c00c00103000d400d68000c020301010b40302581c442e04113504007022241800e2400385414410344006041000d8501c0003d809541c2c081c1004c0c01d041d101d054100720502c0700d5800c241c010b0000038840c00101102a0307000c281a69031041d920300454a0740d001e8010a405242d00c046803d100e030030410302c0140c501240082c01c4074400c4088030f031540c0b00301d0300544c2c6034001c500a080b000e038400c041e00c0403e0318007100380183c0300f40680150384c90030400c0b0890411980400e007540c0d01103a500001e00c191140d42c2c15500000301941c500b180c0035207013030070403032600c0380300d80c541c10351024045d000001c50315a103080940014040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 247051196 1250 247049946 247049953
    0xd08060f091923040c0e06130e0106080a14070f0312110a0c0b070605060f0d15020904020408071802070b0f10090c09060201060f0302010c0f03050d02030a14060a060915030905 77
    0x80c190302805800100e41c221680d017003d80c0c0000d44194030103441c0e401140000d02d900c1204442d28010402424074842c20305840d07499031400600d2a4041c01702100e214002d03c580b041d2107130300070f0f043c510704006980720f596240e2003010104007042c06c5c44c5c84192b01d820103140003605003c2c3d02e00c46504d01041c0440c043c01844803004001a1f2415030b0f0010401036110314414010365443d003080000c0071081c98070301500580c030780c070015000078480c1e00e17504d2000f810182c005003800f5940c2c0c080f900302c3c1c0054114400c950300c8664144241071060f4440c046494042100394174080c01c40d651045404005061500b0701c0c501180880c00c59000c403011740020306202e242c1044a680315250081200140707102c0d100240d40307007030404180c043c43c1c4c1c206402500e0b0103031680704659415560300c921146065400340c00f00f01c014055075a0702d24513400154007840e10814082811051145d0340c6560700c1024111174030400300c1c3c3c10208200c5811820207422580c15020310683c1802000042c0c3c05094141d500500c01d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 247052446 1250 247051196 247051241
    0x101709070b030c090f010807091214120a1202070f02060901020102070512030105040c1b120504030c0306060905130b0f090307060f0911030307050303010504020a11010c020d08060f0919 81
    0x21411005031605141c200d1742c6001000400d0b00550b0040c0d8195154400208414014448071140c44c0b003402c00d003482840411510701d4109034150411115135140d80c060702d4006142b20304240d004281b400d6070302a8203030031883c080099036600d250f030501840c001c0c010304012071502c0c640d038000e5040c1d5622a4002003a108003000e5080b5840159209000c2e0910840c54401c406a0982c03060003d0411040c051210a207541850388502c40480d80740c4074130310104182000040001004c031030380d8000171480784502003842400e2010f0303035080d01c0c001419161a1050120b9101c0400c480003001d07500290b981440348242d8643c645100d04602c079440b409800340b402d10541a000724400d5101026260085008906115454041548900c224000500150302c00c2c00184094030301a40203003040e0f80607041110340c0d4860315169500b969140c001003009600201c01000380d054201c1c0e24280c2c0501d0071282c20042018000c00280c4184014106803c41001611048032401d540d90200803410039200000c007045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 247053696 1250 247052446 247052461
    0x1506010e0a0504180b10260c130c0e06030c0910050904020c07050a140d060b0310060602010c030f020c1203040c0e0108070303030b06030411010804030212040f050f101709070b03 78
    0x131484a81c04541c0440c00c100025826904501d13114140c1e5100d018428040e070040042e909200c800116161303a81c0101010000590b0741c00c89140c483c0500040003040400035100040c00e1820040300490017180f0130000c00800003e50380803a41f506030215203a9484628000c0c00b1a81405101270241c0c0051000415101218000640700c00303c0c0c5085641040c101d40712100e6800707241801403601c0e00b004244075401c0019065410151840401508680e0402c0040d0b08100035200c130350344200c0151359644c0040440720f9141c001c2d40f0401d64103200940c6400d02d0004804e546a02c1000c481c440050040046000c20889a200e40004c1c6940b41c040780302940c54002e6907032602c00c0740c8800c030003280ca0541c0d410310b0f07410008152445140c0203082d07003041c0c59035540103440c991002403007181140514450011100100400350000d0084da41440a84a080c0b00921984508031802c01c0d1007030460654460040f035016612049206203001c2007101e80d1a002d140b6850078a03d5004107000e1078000c0308000c0e40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 247054946 1250 247053696 247053731
    0x23030a090203250b0a02010b040903121404020a0605090d0c14094c380d0908070506010305060604110903060a020a1709030a09081506010e0a0504 64
    0xd2500031800e032200120b041e900c070418000600c0208003800c0c0086800c01c03401404401800e42a6070600000c640c2054070000641128070b4080c00301c001c00c072000300b0b554840790b55100b5111002c42815050185080c5a000943c1d010b0301c0c1e1040a081000001780d441030360b269101c01412041c1d00209155005490340006602c03071514600c5640111441400142044900c00c1c9418840010010044031061214800280c4001c00c0555410b981210985540c0c0c07070840c0160b0700020024031500701c040b10407807480c00e0350350303104d18101080c00809550590b0100f012402150007000541d080000c0d100c4c09898024024001d40c20041c06c2402903000000c2401404111203200314004c840c1080701ca00c044042c40694000c4640090705503000d00700140300001c2d144e00134081aa054241765070724907040368420062110444001c000c0d900007061a0703c1d80d40d0841986405061241c01800a0400741265400da03410004c110340c1c100090007050306200d4540004003400741201030710600000c42c01c0741400c640e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 247056196 1250 247054946 247054961
    0xc0f0c080d050a050f0310180e0105092d0c0d030e09010f0b03040f02012c030c0a06021209011e020f0c060307020a02190504090b040507090c08060123030a 68
    0x105405144849541c031489401101c0340001c0544036242014003407260300d0f5007500000c01d01e0804140303004001c0384945060140301c1003401481c0c0d01240788030500c0516030950f10007500c40c01c0247d0044c0340d9004540d508404118001c00b00c21250b20f060f40b03809001900c2e0040c100d6043e9008000040d18038185030740700c005050400780036101d00b6501d036600d00d00c00d000082d143c415001e07041d00030700c040b80c00144401000b0014900500d89150811060b6003441040c884c482c0101d03448008031000313442107040a000f18070010a0480305480b5007880c1810194403101c00c500c40340000c1d00000369442d0a6070248100b024803100481402d114907041e020065550040b91800b110507200350b0011803490310b0490200d9120303212941c09000003c00360f0313007801540c41141c1030b40d04418800030400304468540d40b045a0b80d0502802e000d11641c00d05090490400e54140c00030f484503420411074030b01a541064595400080078a0485085400d19221400380d0f4800020307400c80c07407000030030300a45ca00903410059 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 247057446 1250 247056196 247056209
    0x206010602010b030d050708090d02040e160e28020c0106300804060e04020c0f01090b130c05010f020c0904030e010f020c033d0f14040506040209070c0f0c 68
    0x200d100a10f004151303480540500c20750028408003d03020025a5800280c4281d100c050005480d01040da8000750607510342044101d00c030b900448459140e102e080c00c40b8402003e400d40e0080807800c218000300800030301001c000c140d001880801411484140c2d046410030341a681c0200442c585074001c14145078400d040d4181d920200500c4003030440175a44070303201c5d6254018040c0b4034141c5040d10544400f07a420b910a5030065090188850184040c000d414060140c64000a142400c43c984512100c2000d1321403c6040150440d040c00281048101030544200b420120006406070108914101c11490004e40004030503041c04109a045442c130780440030242c0343c00f1043c02031352800701d0350341010740c08507a41540460742d200301c04000c0b070004142003119007072a88010320a0720426541140c060200403a080c1d0b0314041109040c5140c400c400010744c600034840c2050605894003a0740340c0010380041c0c801c510f43c81c081030446001c0c40c6009a0241d01c03041c5990a500701d810100714800c2d0328425003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 247058696 1250 247057446 247057451
    0x1032102031201091d060408040e0907080d0e0a0b1b0c01050a020717010905060c1903060303020d082206050a05070c020603040b041a0a02070c051014030406020403060507020601060201 81
    0x50201a00210070b44481003105010b04455a29140c050b502601c080b0f1480340d1602c240400c3e003108202c0c1070216511907801005082d41e84c42c544000f0850264004042c1c00850700190b034103100745800441c0704401c042c403034545016860380000000d82d1019040c4d00c1031506820014800c560a0002400c04140113244402c0d1201c1c00f00c00d030019078040c441c10400000517004100c003030001035003001005a295080c8800040c1c4a0910354496107040b80907240c6284080303000c40d0484050326540c1594a59804601e0103120303040c07541e5400707035450030112050400d000c0b0441c00074540740c01c9a10342e03518039400c05181e600740780100d00f0804001c080a07250318112074100400120380c039016001d84410554090665072650784c0e5034036074010528003c4c20403621005240b40131241a2581131000303005c0c241100c00180c3e00c00840ca4000c0d848040d95000501072032202c0c00f2050455000a40800e6030082031082503600e90315441c0500c003d1103180c00c02000c0a15080a2040403030380040c840d4141d503801e8008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 247059946 1250 247058696 247058753
    0x1050a0b040519020c0f0a0c030c060207032001021c1805030307020a0b0703110a0c0503060a051005010309060e0304030308040224030429010b0309010b010c02060d050903120103 78
    0x5100664000f1160740c060720081c860030052004456006140140c0c2c20800d8403220444248941d007000845541641d20008001f0203105000c0b003071f2206030003045c0900003000310350b280d40da581d0305160180d840340f4480c4403611100001a4000e0140a40000400f460741d954103094401c05050b0244c1c2013040c521115007841c02040d203040000c100c40c4041e8009110450851030021102c0e00c641c4540002c0701000074011103a20345c0d030420011002c0c89803056043c400f030f07241044141440c2600061600106d64100302c140301902031141000f8003545c1080c60040340d50a01410690003510200e0720156162000181c00810301d6400303103526005920844200782c0e501e806954421961303c940944480035041000428002a04003103c4032021035080420507001205031101da4014202340c1c024410603000104010000d5803c0c1b00c1d848446009007440e21141c1503c0c0c0204d202c5004800d50800d0756a507400108681d054200240c1710705480007600034080750303100c1c039010204200d04050f00c241c105230f0104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 247061196 1250 247059946 247059949
    0x2031e040f0e071101051501080c071205031803030a1b0801030822080d03051812070b07030b03030310030c120b13030306080f150105010f020334030201050a0b 70
    0x4a40c1107403889000802001c0c1421440180280064038881c180f203030080198914500138000e580c41810318200d40d203034221110002402400c0018442281d412042052000041910075540c0c15400980b5007141c0300d60351501d140c120359112441c0b0052600c0084100801c00b446600046400c0180014034806c2103602402910031010a000041c04210144400310080743d03403641e901098503241d8114010340356100310f52803e106403101d0b0040020340710f20401001b542411221030b1100c20328001801ca103c0825021612070090740801010f218912000c00c1100d0f210b900301016034030008064903a039080030040d0303105120103403004590100200303a001601d000e660040c07001054022103608400da403071808020703503070421190441c2815914080072503032034020802c12008015090041103d40045002090b01c401c0581c01f880c100028000304075290380d1b000c02550892188808000001101c9100140786841c084880e14880c0307001900900074554150055401128440d00400c11100f0850 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 247062446 1250 247061196 247061257
    0x6140f040606080a0b0a0e01060201020a08090304180b04090b091e070f0504330546080d092108091c02040504120f080f04110f030d0203 60
    0x1094101150243e0000f4440d91002e0f00a001910030041c010044552100854460400203800440050f0350102780805001e07017100c002e540150264008500349490f042240201c3c0ca6a248142d01e80340d12200c04a0b019162608140d00307590303000110840301c0c646101841e599a852001002040d03000c0f400100c00c4c603102041050a4a00304032021440310300303010034040501000c4e030f82044040c101c10100c202c1c40003007804405017400000e1106400525240c10050b0310050041c080c1c0741d28040407803511044041c4070300c00700701240810710820b0590501c0500703041002309500420940c051060075007480c5034040311000c2919210404001a405403c800019942c8110001428888100708103040b42c40c0c8400c016450642c4154220780300c181307941c003240940380107407800c8401d080d0710403594403c41d03044a1f401074044100c1c501500da40ca4030400707044c080000a00b0241c0260440a1600e2068480c1108000b900001030100e450304290940c00941d603502a07001002d05505c40c070b003000810700014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 247063696 1250 247062446 247062449
    0xf03020301051027060809070b092809050408071e020109060815030304030809030105130f08070f0615091a180702010b030a03080403180b07030309080d06140f0406 72
    0x240108a400c880d003442659900703240405000004a503505070700c2080944c01107900985100c0c1e490170b0440c14020050382c60801c050308080310340030b010320449550b500c408a01c04100101d5842d034042440b0714640310a0083c007150008040c00f801e0034200010b1025403c000c00ca0144202241519207010052100c40c07004010701c02400948521404c100b603504c2101120740001c80b02040207800044600001e00d56800f035441120441030116400200b80340a20441d1b5005d5221000c007060404182c0d07c13031011510144000b8000342c0c01007030ba182440101d20290301303d1603204208001961580100d161151000e100d0351036801d00b0301741d6010360a065541c8145610102a21103400039255a00a05030745200800d500210b40d41e0f481e035001d190394100b001c480c4540c000d449410190405040083c076850052070740c200554600c0300104070080644088444542c2c25290020300700107070746440d0302503115045040704171608050700458600301c51448034109213411900e81c58203c800201340400c1d038029 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 247064946 1250 247063696 247063699
    0x5010e0d030c1d040b0a12210206130213090f23120a03090c030b19061503020d090209040c1d0c0d020702030a080417150717090c030a080406260c0d0905100b010f0302030105 76
    0x40404030380a848070b5214412f80d40d100805110058800394101c904603290400309030303440c201603a0003005211107680740e4880700c0d1f00c00150031480e0b01118130290fa6496a5040762041010002e02c1c004010320a5001502055010300d5101590f40d90f4200041c40660698124030010006074000004132000d116800c115040403070004841e002144041d402034000c40042d1440c141c49200e02e200694411840d148903903c15198000c0c03003410210110314a100384c410841040c00c01c9000e00881900039400d5070790340e612840026984600c64030200342411110780c0300a01d1507202180108110840000c0e201c1407074500030454800f400c2c40042c4070f42d40141a502d5802082d8405824402c0e2145500c0302c0d036110079010704480b01242403c02003403802000c00c50a948281011405002582e4858250600021841704c001100b14080400110100c1c0182040c03554480005070b41c01103610071b4004c100c0881d00b1105541401880b07045141c05009041030701400644c2012669040600034070a90307069070300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 247066196 1250 247064946 247064953
    0xf0e07050d08070204110712080717041a0114030c0102030f03010302060a050f0f03220203060c03072006010504050c0f120c07060905010e0d030c1d040b0a122102 71
    0x103000103006200781c106a05561103401045600f001d81c540e4064400b4140128010554a445505092144440007d0694104543e0700203000d03c0d0342d44403800380500c102d84070f400035064607245862180a407515600c4400410008000184038403004c04000ca18841038081c0d6032185140c07401261a88502c06012040d54002d000610150900c80050308440c14941082c61805400300e00d00c00c402d8210580159a200c07000081080140c0d6607034185144c020f03540031040e01c2036456030000c1d466140042039107101500102c0046d80c03992144880c0511164801040102104100b0030ba54a80741c090180d039010b10309210100e802c1019500458a0584451124a041640a00d010005200c000d425086032600900c00c00c00460b2081c81a01a068171400c000504509500e69090400100766a01c5050516062003c80b505802400074120780c8a140c981030802c20070500000c0c01011880c0c0850b811550418005c110751075100203680c031060007051690800c40e03040e01400203082d181c0007003000580 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 247067446 1250 247066196 247066199
    0x60518030412030306080a0602090406051f2706080a0e0604020303040b030403050d05180c0102120d09050f07061d0d03090918050d0201020a080c19051b030a0906030f0e07 75
    0x410400034007030503c01d140200701c0f41d98480049142c003c0d07171507094503800d60014100d011072809114100081409a82c41003507108064480c905c1c00340380c42d06413000d2180413441110141c1e208903c500141005103400ca1440791100e00c01000042c04407003016040345400d100000282d00040c21b030f841668000e004620782410540e400201d90000b80c012018003006000c291180d2003140030341071042e990b0904181c02000da2250300e40c50481d40020150564028400041000b07003040704a07242c8000180d00031850401a203041850a800c09030043c0e103a005080d004220075502804101c404500a269590500218010441c0c11000c00b1001004903140c0d4200b00011400e41e040311100b0b250010600f4207885041d140d2600340341d601d550313810045c0d60004004a41e543c00c41c40c6160026040d2643c4e038103100080310856402d4090801704418400c0102d0340a24488281d140c2d00380000303420341682d48070b542010000d4490300340c9000d0100481d0030b1010301440100ac500c62854181e0030300c0000d19400d13 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 247068696 1250 247067446 247067459
    0x170a0206070c091a040c0e1c1401180201091d0708070203130e01050a0603050903070609050f03070c0e010509040302121b0102120f180604060c1101090f0605180304 72
    0x7584061000c54000451401c00034050f81644280034a41008401400382203418804010481d01e40380161814004004041c09498403140d4807080d0581c18869403810714225414241580003031103078044c0217982024102e4144513148010b0801581c403c0e00d1380c00c0c040c1c0c3c07104910400b00d44202c0e12029a40b42000000e0070592042d480181c2044460041d64a8104030311044000755490341c010b10604801e1400401007800c002c00c518006180e1490104040d08184100e161644503851010388840d0701c3d0b12852060010a002080031050301c4e8044907a2100b0a00d08000c40014500c500c000e00003401000098506141401901c1203515030f000d0001c41400740d0014510b13800c21010fa8101c064030200c911010f81003440240040ca1600c20140d426207064010919006402040a8032111100d6103c0d080ca80000a905030019400f0001103a10410700c40101c499a035501c03804481c41d0b090103050f805106000c4c0e490340159004000c240150795034000c0303440c1030307403040320310b88656500422041220 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 247069946 1250 247068696 247068709
    0x406080c0d060302061215060711061305120604050624010c050c04020c030301080c01030905060411011e0e0306070908070605031008030309100b0a03020607020108060d080a110601170a02 82
    0x6a0500710010b00907440350041103081e000f01c04211a08a0020240b0800c03005200c0844464801169a00d20b0009143d59404519203442d8009024240c049000030a0100400c1040c02410300502000c00d0900c1c20508255585426141542d142c020314011030714180c0c4648141101c40a50020b0304142e18140d001166880c4202200b030716640940c90410f0038560701c81c00200b082d900300344003d5481e541070804241c02c042070103401905140c5000001c0c0001500450602d038029000b001c40f114014a00d00182c0c1c240c1500714451600240402c5000d8055400140051814400340d00301c661603a2050829280310b86540944242035204410421026204400440c0d10801e01c0124100d075903078818109241d50000d940251142e0004034070200b840307010344141d0440307a104856000c40c9070304d1034000c11014130649134040c0c108240c642c0000c1c0715071106081c0d011883c1d0308c8900c1c5541d880310124014440741c49001140c0c0180100400007500c03141d08860f4001c1c01c00380710081d0423003580b641e081169 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 247071196 1250 247069946 247069957
    0xa0801080d0c0209040c1802040e1003020a1509050a030807051608031905130303170906190504021801030605150301020306130222080c010f080907170c0306010902070c0b0406080c 79
    0x31080344420000c10f07581c1c10761040e9801c1409a103005a03c270b0341070121040e8800c070000c0c0361040000441c00c080015035a411140c004032070201d800c0f1580c03001c0308081143c6e00c2c011a0440340d005043c90318000100030705d0400600b400c9028901b030f500324040180903550022190f101c2c0003081d50040c04401d0354800c907064020307403403d46400d00314a850041030190204410702d030310a030041031400700b2100b100c00d408454160b102d049400544054a00340002c4c19090b22a03098105056558000050864881081e03d2036031000d03d603c2d0340313080c1d80d4914042010b0300c0c04403900500c068207140042c81508050003035a0045900a002e2001f102d96080403000a410401c5211000e4a001620b0807140c0440440349000c2c1c192540904920f0f1001c0001401d5010b00100722070030402444100540c0d61303808100e40c8207480c00c0481d40c02d003d10350400a14501032038803041c03a9041c00703818000603282031240e00800f40d1b0382c4926101c2e42100e40e61110100f59002d94851407020801060000b0000307800c2c18000d14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 247072446 1250 247071196 247071203
    0x130303030b0a05090f0f160c1b3203011a100309020a0807150e03150c0d1113080f0d030e1908030604050109060501020c0d08120c0a0801080d0c020904 66
    0x1080d40d0754410004c0c0d0949419950320a4640450090100e40708160243c41c2e030100c0302c600000c2102c50203910081c810050320502500100b40810026000c034400c640348070080000401c08510001c00c150100c0070312025400ca0b8940b40d918141001d007a040c10700070050000c8525812900210f4074600380501d15521200d40000c16a64400c290016503c48060340301a080403002050401e041c0700c2c078000d446c40d01070007940c1440030f10710030207080307550006000c02000d50b801500f0b411a103640190450b6800f4440030418202d052040c490031101c1e580c13000d4083c4055000031080d9840e9201c0c515605e0b00c2c04820405031682000d512941c1490098004203030800501c02254482c0440320030408004020440455030b82000000b0700200b480e150240d5405044101c1c000c0001515020001c1c1d501c0840c200d0040c0114811064a024040c6180c292946050040039000c00381c41c0c050760a0501e50b004900ca400490104c03000402d07402c000041080c181845a1a02c035213a01c81c50b020403c4014004008a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 247073696 1250 247072446 247072459
    0x9030610180b270f0f0121110a06020c090c0a08130c030605011412010e0d030b03010f05040507050910080303070509033a0e0f0f01090e0103030c0c0506130303030b 72
    0xb80d0031400e450400b00c8078110380f00c1d807088642000d003c40210b0f0340c030290409401021210040c00350201a5110b101c1c41d81104e01e000104c0702c01c0340340c4440080146010a0760140300110002440703900402c9000c020801111544641d07540d24904504a008518a8600140020b0b00080d2080d01c0c0c04414070201d8050b0810307426040d500e03900e03801550401d8114a2041c0501c0001501c00d040c441c001200315080c40c0002c0c050043c1032100340b07035201d01d40b181c140105500e0b0058282e081d1420350140601d85148003040c89545801c2c1055680c0c2d010903c500ca020700b81003000034250301030108030324040e0745280d0041c526680340e1250843c0c0d030741c124800c0d190313242c02041e80001d08180c04c0c000380502021403e140c00300c10500499002607170030b10340b92900c3c240840c6042d84641c42d80c4054450f55007000480c0c420f00b81ca96500012502c05045410400000c0d54010012050503040078241c00c0a030700c10240209847d403201d040c842c250161004644000c00d41e10010300009010b900b0007250714901400c0da = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 247074946 1250 247073696 247073719
    0x100b1204020120010509210c15100504110a260f10150306060e0f010507080c0309030a060f0c110d0c0611040906090c0c030c060c1e030209030610180b 66
    0x18203003100c1c0c091b40c40480d5640b0026400400f46c84030611041d030a102c65502c1d501f0500c05210054850400d00411311841d500440002c880c020410400310180c50040c0040180301109101a01c0503804040c1110118425850a002c14000304070b0700ca0081c034103140b500d0703180d0302d91503a4410f060300d01a1400340c26040074007001c920240010701010940d4040c0c0c0d070203e00b180c0b41000c06852030556101850003002d4250500c10305076004000c80fa84240c0c0407124903a80c40c000400360303041d0f02a05406942c107000b00407400e0140581600154200e1b0310402c0c040000c0c4111010503912005e1861300381a554100d4032070344a1803801200c0c2c84840303a0240d440030403450151081190f043c0e1260b0080c40126944030701c00d1101036030700e200301c43c4424828100074416003400d44000d1b200784044140100000c0e04c0e20328414405100c0e00b4021340003180c1c0340300c800384c4029800c40903001e900b003840d000d402445041c0000c1e41c42200144103008a80301c0281440d1100e5900c0401405000d4121500b508441240030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 247076196 1250 247074946 247075007
    0x30209031203090c13060807140604030503130f08010b101b020a0b0c06010b0a08011509030b0a020304060b18070c031701030503190e150a0318050105100b12040201 72
    0xc0d40702e400c0e0f040240520814203000c01c840404112240310100f8034200c02800410720018401c002e8500002c00e4602d03050110000642520030394000070b002d80408212450100300d45c000071000e070b482c0a1401a800c5840e4032a85088986407126954400c20345014140e0700303409051449020207001014815108942d00814402c00c0942d0141507600000a0625401a003c0c44224050030864482c146024000300000785000c0041c09107814918506036800e401a015045520095922001a0502d454081e10343c2c80250811501562001d052a400c54000c1c64004042c400c00c01102d000a0001e840b5040111003140e403102c42207042c803108900f444032040d01c01410f41d0003140300300000d541d5404006074009001c414034031030342c060118801182e4182d07510600c3c907038000300440c1c0700940c44108000c42100600100c40410b0041c91107038441d40203003c0107402c1141700b500080d104108031655110f55640c90b2081c4200110030846a90110300158882c141c0380c0b11302c04000320101c904c4442c040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 247077446 1250 247076196 247076233
    0x102121c09050f0115081b06070b07030b1206240a03200102010b011103030103060203280e060c040b0405040203090109021009140a061e120c020102091c080a03020903 73
    0x1141990076a004140000c4120b0f024003a0911380d0381c0c0002d4044c0710601c0e1a8402c0c0c0d5594042584824030001c2055813502c503110081500d5401c0c4d040440c4209a0521000280090840c1e04d41e0074003c0418a24080301c40d000068101d014400c40c03d101c1c410f800b03168218040b415101c1504691004485500001160741c0051000300e615652078005001c8090100280c2103a010344401350501c110003c400191100203c29681160740114015a0f2a91002c000c00084129140c440040d800029410300e881040e980c4a40c2801400b441110040c1e140c04c41c68403554003c074891154010000c0005201030f0030b00f50061078101d81101c0001c10b4507482540000c02076000f14104000082e46031900304541028410b2035140c1c50000c5d1a0b032503c8604216004040103400040300c60280e050500c83c40d42c00d40304d20a420003142030440708100c500306480009010750f1120307000503c2035074a46a0301400030f5014800c4000071764820b0007240740c924414002c0c0c001e5008444001e5060207141c0c0342640013001d01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 247078696 1250 247077446 247077461
    0x2060c010603150f050118090302070914070810140d05010204050d15270f050c0a06030c0306053003070c0f0312140a0c0c08010212160c020102121c 65
    0x10007640c441c0d5502e043c4090110b034040301142055505007030040060520604045580107603031100031480c601941804d0f0300d400349540c48141e010f850700680c4003404c03540700044c50084029985210a0b41c41c0c03400034864010081c0140a00500070321880e030007a1514036001399420303100d1000541401d42c0c1c2c0c00001c03104035000d641612003550940300541c2c41881440b60143c2d0700144150200019200ba00c600d0044248003402020700105034058001d1000810203010651001404002c0080d11004001c020b0b1885010220104c0d00b400c001050a1511003116100f442090308046c0780700440d4001641d200c820381e440015280800c01c1040c010854941e0640013820405540928191079440c0140328030949132495402c0050b03501d100f101580c541400c682d450a194504581d001080c1d003420f00c1d00700403551040ea140d42c070002d4900300311255000c4503449640401641c40320441e00c0c010507a190b011200e0020f00581194501a09906508000d072059140b50100c2d10f0154019090150445590 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 247079946 1250 247078696 247078703
    0x150d080c030406090e091b030f010f2304150c11030a02030940061715010b0f07120507050f012c03090603040318121203020408060f0402060c010603 65
    0x241c18000c464210109900030b0068001c140c2c01742c90002c01094541c40c1e0745003100b6540c40030642003803d5903010403c0c0207284540034001c0010848003802c1320001c10300c40050b5200142c0300c0c4039003c40085081103440c030841e005000b41023100c0a21030010020a00d2a4100050000711030350300c0c6650408001811504214ae002165510300c04d00400c1201c032107000c0c02c41c941e00424001c03031405656a44494581c0c4408404031000301e03000070107140c06800030350400d482c4941261448003600e000040e80200c3e9200401c50035841da62190092400d605c81c0440000c2c080b00c0130020f80c400a806054409a45000c0b841d2243c01c265040d0b84050030841e121700320014582d10782d100d00641601040c20f144036180081000c00c440c0f400c482c074250f1240921400e1a104401c0440001c05040c0182c1c440040c40c3e41e00d4080e520990f84500d0351204104c14402c048d100c403060f600c05000060b000c0c1c0b00b103400342c03000c0d0f6000344056a94040f1051000b80000d2007260455403e1001040ca264240110000b6511 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 247081196 1250 247079946 247079953
    0x408060f0108070e070509010e0312070c140604051c0611030106020d03050f070e19090204030507060906050333130608060a0b060a050d18030c060e0106050108150d080c 74
    0x140254203031070314005070004c01e5659060b10a0111040d00325007100c0301c8400a0038002a507145d05d000081c20002d500288540d80b410000702030301040240d45101c0143e5804062003c41d028982c01405980d000310302806800c9060244600310254500a42c0121103126080200700d035980341e00c84881030340007a4032140150384803929000045070580035107a482995180501000c0c42d0001c0c004040400400c4860300507401c00c0c840411050b0102014005000240000c0d03503184c0e542d250456907080148203d2000417101040407031a04d2142c41102d000e03800c400c5c51803105482d480d1201290729008400d035041c0703059400c5503c644d40c548850720f4003080c85078100050110700d080c2c096410840000c195001700c030b182c881c0c5d0300050b03540c2c4810b03202c182086261139238680007044d00d450700a0141182d0703c1044070789030601d8410140e00165100d001403180006219109030402c0c8107013669228025240890300c0d02e40094410898980b403182035031030080a40c0220895a214034001ba880034a00900642 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 247082446 1250 247081196 247081199
    0x8041e080a0e010c0b0a09080c070311090903030624091210140c03070f1b060507090e060a06030b0d0602031806060102070806130606051801030b0105041514010201020408060f01 78
    0x10b400080d031070140107003800c050140d201a540c0314a803012006205068080d07595481100340203c1500f41c846960080c42220381c0281c5071304200c0142c007081e25034503100d00f80f0300b030000d8140000441a04d014410240c03a00d4000c0da010304141500880103401213003005002d1050032150381c3c8010261f2000f0b06000f0140c0071185881050780c0590341b00c0744503541111352000910540841c000308070380d40300c80a0720b4051804c80b4407043c111303880f031241039100440c030950950a02c01d020f61544941d0241401d5102e1200517581c032040b0f00c11040c401c5513a81e610240c0c1d060304110f524080c0d0012841c0f004001c00c16107042d01d0680c0d841c8200c2c1c00684001c0d201c041120540b81540408001d0341c1d40100c000d000074041d00707180c54102c2e0358420000703102801d050000004a010440107810001c0502002400a401f41d0660303031401c0c001000920066078012102c01c000211410070303104855403c0e1582140c10700f80e03400c1c015401d242c105200c81c507a04540d42003000048007070003444101c0c043c1002d00d000303280320b5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 247083696 1250 247082446 247082467
    0x90f02191101060b041d100f03030206090c0f0d030309020a09060909050d0c0206190c06020301090b03010609020a090e041401060305030d0e01150e070c0605010924031208041e08 78
    0x180c0242c4c12690140904100a000d450010b044150301d0000c8102000e10941d20350b0207001c0d800f83e00f64010300d224080030314040200b54004c1500361150a00004882e010341e60701c0c2c10068126007007400c0319088449143e050010a00c00d4200342030f1940064441d04c030300d96488109030121540b9a000303505080d6030700c4900082000038000414512114a0304a0204026400190f45442101940960f00c201c0c0301c06620100c1c0210300401d81950004011909c03503a6070b20a00c0301034103242140c01d01c25480e1480c0811012707070508c01c1e1035810183d039440c01c03200d60424800c04e000840240054610001d950320b03564098109000d4030000c4c510800c0615201c45034401031074156984e41c00803400507418000c1c0d0790070424050444030308030ba0365440094040d48454038141e91480d001e07100605041e041500104483ca20b64104c1c911550840311000d02c580c04d000c00d030410000b4513010007000c1035580460a070140d480b44a0058115026804603848010110206450072034442412510614046107981d0722 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 247084946 1250 247083696 247083701
    0x60a0e0105090105040201080105060a03061208120f1015050c071e0e060f040207030309140c0a0b071101050306130213090608150c0c0a0c0b1e13090f02191101 70
    0x4542202c000340034500302540040c0514105009581c001c03a000720f1040a100c2c800e0304460700815070300240f8001504582002002903005002c50f04111065101107050400108269817080032481d03039801c80d041c18420f54448401700d850000341040410300c120302c420704041c03101c1d030001c120b1840341c040d1001051710701c50716265966006a00d520390030800c01c02180c4130301715000d5000000300e0b40180e80b042c0e01e103016001024a094050000c6000c002d140c07403021300001d01e4a030207070000c80700080d01a03075035808a030051040083c014001c081202d500103080d4025005590021801040010884250075a8408136000034500c244401c407070100400c103190851191402802c03000020303194210005000300071503003014040f1205100001a0348295840c144044016145d002101c84c1079203580e2011000c5a800c0181c074035200810608000c42c9622000e000c03a203080c017503240f1a030380705490159881d000b0429442c410002c50707001c01c61110700035540c5e20891408803142d103a101108040303c2c0104e08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 247086196 1250 247084946 247084951
    0x1e0c0201060503060124121401030605010b0901020a061d030c01060f061407020f04020c0f03070614160c020307170105090d140702091302060a170a061a0a02010b03060a0e0105 77
    0x75000038005001c00c9030f1000032803000380c1c0300799860340d40341078400300c101c1f04103c0c0d602c2c4410010b031400c1d00120045009018550403680141820b01c010390f214a410f00d201d1090741840c5025900c0b281c416000181135402104e240105c9402460409018600d00c0d4155840000301c48039076550382c10b00707004181000f80c0d24000342c40d031403400b20440c42d41c0e0105c1012601c10008083d1084048071802c801c0c5230342d16011070304500501010b0398a134141c820707041c60396500000d81c222407603800c0001c2c1401030183c88070345a00c1030000781c00241580310704002c151210700801809036050b002c1c413100828103c421b200c3c1205211456800060145402d100080c200035044280c6400c015213824071584118032a0b080d00d0100e5011036545c2c0242d02c540158091081d40e00c0c80c000e4124201042607004144c00101003203191006240203c09961010181411540359018007103490402d905600248100880074091104850000141611017180000d16102c411a151b030120b03a00c1d0030380004258400e00800740c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 247087446 1250 247086196 247086199
    0x9040b07031a10050c0718020a0917060c0a030e0601060e01021009080d0f0605030a050a0b100608010e0c070b04051f06050901030807020a0306060b300a050a1e0c02010605 75
    0x400e00b01c2107500260f403c01c20f03024000304200b00820000714128091150100404148204c5403140e201042400080c0d0401c1d0901c1022480310304001503401440107500159a85000181ca415619803078610100d401c100c01c07020030141d84d035184158842c02004028060409501c90301000e21030180020301d00001c0c9c400b0500103a003448d0500c000228804c0907240030120300480402c2c086102006000180002d6218135814401c00446a0500c400401d5000056005004200c2d00342d86e1039800a5140100b84030324000186001c3c0104031515030942100d0f0001e124600e0b1910306941611414440d0100340d80503140c4c0d0300032841034070b8a100c0000000030740c0c1111720b100740003039458840000c01d0590b051202074801240042c281d000c560320018000b010f994001c0c000c200c856155684407403240c00c944040c10940c403201c484600d00103e5040328107400003080c062944299070b0903055a0240401418512401e5251983c91b010240c0e01940b40c6414503e0a0380040c0b5807010040007400c0d50019800b06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 247088696 1250 247087446 247087481
    0x306020711030d091a09060d0b042d09060b090f24010c020d0204110c07091d100e0c1005090a09050f0106050a051603120606093209040b0703 62
    0x403140c0750041400400c40d882d00c03001c00c5e62880344208420f01031007030380600c40c0d21800010301680001907030390200054103429a001c0000000d00c0701c0d2040781036590845000124680100c1000b60f08090b01b124100758421400071518072a004085900750f131040e03800006440c0c41c2c4040040400d0703846941c101003e24558000b200c55005c00c00030704800031a601c06801440310400c50019901c864200956a850b5140150b9a0707a204038405138894070540107248099040080400500a5284501ca003165810020b000c4a410007441c900c0100079000c1c141ca01c0740210342d949140c4c0d82c0d1302503441a0400c000d850315542c4041c190b0801080c1111034010200c0d0741c0c680400e000c0c80c6101d0029141c1521a142840c03540d8500885c5d05945c907005e80d03111103620002c054620003c0507440b0650205094110354140100c80d102c83c810343c0e9039480b42c0181e02100043c4c0e8503528801205420b1102050300500040d240300c202000851404001220b040d26100300c07000600840d80c2c0c0c0b520035600300a0280d00203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 247089946 1250 247088696 247088713
    0xf1406010302030c0405130b091810051005010c0c050402040602030a081006020a030507110405010311040e010c270b03010906030c120302030909071b120f03050603100e0307060501030602071103 85
    0x100d04c44c016409001e010f13200c46586030207240c1c499403180d010b040c00240b04150710702d001d4807800c00700c406035075078010a03000c1c204000e0310f04440e0b404ac0c1805082c540d0b0100c0722190810300115240c20b060f800540e42007880d01d9002880303445510061001e00503a030702550b41d510042d04050a070b20400b0384010b801c0d041581c2c04008490380494a11280d603403516040c4c0d951800d03820201030440b220b088096016107040300000400030700002c50041d40f0f42c01e550038407a4030010000d0500300c83c581c41c1400081102800949080d140b9581c0301c450740300070f41c11b0b03c02086881e45074094481e04241c01103521030fa0744c1e0502380184803905266000811503e04500b8444032540d500a48900504c000c8600801889000c40c410500401000056400d41c500203440075906003804c400b07088413240c030000411244c607911308111f40b203030260500c81e01300035006001e080c03120724019008180f03480c420000ca00042c803a0782d00041060146600030340c0110000750b01c0d00100d003400040c81440c80000f07441b07640030703010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 247091196 1250 247089946 247089961
    0x507051507080702150c0d0509100e150915130302031606050f0913050406140a060605090d031704060e070e0609041106090303212212030b040f140601030203 69
    0x3203031110360781917a03a642101c0711005041d429010b00b05040350707a4054914039001780c5a00401400c0b034100300f1643c00071002d82007081980e030111095240c941042c0f40606502c80740803000300034681080c0c0501100d82c00e03005801c04c01995080b0003459180001c05d10010425480d08010300d0002c5100c03804062003061400c40f010344948102c800c95a409a008181e2048903a40c0140d0742070148040b034000e1005240a140c54002050f0801e038020500c0b4481d000b0501100c2e5034462101910b41c036865040c98050705a00708100000700601c01c07002c02200c500d0f00344c410030480e480c103405180b20380000700d180300b0340c02c042d1800d240340c42e00000440034101c4100b20036585c8917001540c0254100f605034100303401200206400d0320440f9840c83d0184400290101d45454611011401949100168090352112002d40b1000c0020f01c1c29940064410342030080400c1c0b030340509500840c054240020050030020124059840d019440040d540c0e0715080c91a82e40c2d00c0744c01c5103034468824681140b440c580200d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 247092446 1250 247091196 247091213
    0xd0b0f0d06090c0611030d05070e090a020a031506050d0905010905070e0f0a0b06070f050a06020a111902010c0b15030a0605090f071503111e0307021212061e0406030507051507 77
    0x4050082d51f90f03c0c0d80210705028042d94000304454006041030205240070a843d2001e5400226030b280000d14000750380044034621412402aa9030596490b480c1444800c50310020f4400360401341c0307541d5600d0a865000840800501006000e610791071811803a121032112801840141f20011540c00c04000e4025a0b48140450742000d0b404011182d00994602f0100e03c0e090000000801a0340300040f8140c0003900000c001134400d042c2001c03a28030050300700d0509440782034550b0013400325148000030400184459011035200800481185810f03407078000107843c1c050b0380d81041d60700c169640d0a00101580602401050900e01001085c0d014a45180380c08441a41c2415404141d59400e912441c0e00e14a0f0440d9015801006a400045034038140c501c12980140d03008400f40c400c0c1c00b00205114000004c0c0d80100b01c0e80c41503104660340c0d8030309008003043c151003520300303250b20400d41c0c51041e40c441c8946400b5501901c01040130354144414403040c420754204c6d1000b40d010612440d000100c420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 247093696 1250 247092446 247092457
    0x20f03210403021005071805180a24030303091103010903080c1e040b0408010605030601060c080d11031608070e06030126030f03090714060d0b0f0d06090c061103 71
    0x6a4a440050751581412404e10030a0b07640065164200b40038450f013158040c0541040200d4500800c00091b40c1b001000030401d461011281a8401c0c034000504d8000b040e1301070103c1250010342441059007000b0101c51403851138000700c0219503100d4003403082c0300030000c400d526044103070001c128800d1030340c502030040000242542d6800358005800541c0000c401400540302904281040c0c4403030700d0b40d00740303111504039010300d512961038820300246a141c0003407201d048640f40d8640909000f80d9480d01c080551048100a02e015140d00107003810801c000b00642c420389641c03070b41c10300c5000c0f941c4004100070401380900d000c100b1000380700c10842e0740d00e404880c11039516034000036005100050404084c10301c4a101415030102049803002d50007010011031162811a080d030320500e03282d04100022215801c0035940000c0c0c14000070000301e844d54409542c410000701100810f842c1c0c14002401282c0c3c070107084079450703141d41e074041c200145c0400d02d8004e44020b0906c001c4414240481990302d0166 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 247094946 1250 247093696 247093747
    0x30b15060306191707080d0f050a0507020d0b0403050c1c12150b07031e030c0c030513090f1a180f04080702030109060519090c12030e03030d0606020f03 67
    0x445030f480c03c07070100d602c000d200208a004030205880041d410b010b615030b09035200e5280d140c090190840d1110b846038460000e800b07001c0e1105030034440d41e80e1049030f580d0000c0c5402c0340c21a007a05045c1000c00c0301102c6c1300b4441d5100b0f60f20301d84c0e2424551112030410060003925960000d65a0750701e403090740c10107140c013070300590000005800c03104c50700c488240071207580c05280c0d800800240c0c4c000341a4070180da00f4100c001d03010000c4940861020840848280d84c4e4504009902141140c0010388648002c140105240501036046a2510740030380031194120030040e80e040e07941d003000034a0300a15280c1991494100c6001811890540340ca00c1009030080203000044442000241041801c3c0e090750358550300600200580c00d850b203060340c024002036528100f5407003c05243c00242c075042c0102c00c00c0d254007519482c10a440c080748400d088240740c1c012820b000a101d05980540c404001410f50300707080e82c030003161a62910902031304041000c0c0c00c07a9856001045680d280801070403508aa4540c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 247096196 1250 247094946 247094959
    0xd05270c0d050111031509010e01031718040c020d0207090203061f05040312030b01030b0d02011211070816020415150509060c010203041202060c0a12230709030b15060306 75
    0x18a01a03004202d0300b510b2007040724000c406d00404c0065900e660407541420b895541c02640c8403000c40f90030600901c80242000d100342050395106088001074a14400040365118072070500340001002c0d510207a030034500580c0401020958107a0411205005004081c411882c5042400100f1003280a5509044081c3d4030380d100070311118818002c4a0046400003c2000b42600c443d0004015003d00b106050000c1e017809500c500c0707854050010844241d050311101d20840750441c5c103d01400501501d855403010070f1181e0004920004010200c011540d0b4100d24503c1682c410401150242e1080c10a440c80161091103200030140b110f28030903156080484d00d4200307180001d0814403485420011650000c0184070801c95011400d08440800c0c3c1c00341c4140f035440c0d07410401c990141204403c00189a22004c1050954542c1700020300704031000c1a0421a1440200c0d04004c0340688201c00064146603040044c042c070b00032015003103201814220711006107840003501c2800090501d078400c21 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 247097446 1250 247096196 247096219
    0x170109140408070218180717030a0c0302010b030d110d02070522021303060507120b06040608100306050106080a110901080f060a03020415090e01020a021f0e030d05270c 74
    0x161054000c030494583c25142c046030f071800c401320303886e0480c076080145101c1c03003044404a03485a2005e2820a1040a100110304103c10780c40101c0351a1407150058007035560782d0701d0107081030b1020321150307210044d940c0f03c02c03200d5a1890f4402c1d1401d2108090001190000442801a0b5444904407007080c880e05500c01c40400c010314441c0028401c20400751682040818000100011a008030b80304106580718034a101907502c188605403440104103c2d4403c400704404d110550141c1c80481d0405d0740d10458030070031502c90b9643d20441d4400e8105a011031820000c1040700305440c0540b114018580506508000c03c820000c3c0003110003400c0d4840b6404840000341e500d85036401001d00035900100f062110b0303030a070303100b50440354490b01a00305010306106640c0140c00741402203510701500d85d4000d00c0910940f414030240400f12007004c074400c50700c0d41c4042070a560200090b1021800c001d9002449080400c0040b80c2c242c90b0441808080030112451a8802400303e41e50415100542d82c10b41c0d040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 247098696 1250 247097446 247097449
    0xa29030901020904050103230604020a09020a050f0a02061b0406080c0313020a031101030b04020702090402010c0203101b0906170c0a02011e0504020f1e01031107050d1701091404080702 81
    0x24010300d00703c10f03002441c1c400000240104080c26a1007442d50314218a000c24044008940b00d28003110b011b500203000749410032114030154001c000c2c1069501c0c2280c20480b0003400d44482e030740300f00e40300001a03021a080c0003520558101c00c00c5151032518045241624004c80070340801c0f0000c180200d050b03000700c00988000603c50068000950040000d1490b68991401e2a046801843d000d170000789080040304c00d07801c29200301d6460383e400401500040d5110385c011912020044012038160043d0483c00e41d1403090f030302900210b82c1e4000c54003040c5c032207002d01c020406496035010008102c900c03e0074500ca0f0720fa588030a50841c0e89280b5442d030302e0b0300f006c50036405000564068201c516090042d0000d188403a40224001c920072502e031440c00398010704202c0303000480c1400420000e01e02d0782004040d03000758030500d0b45e4421200c08078204840341d25aa030500300c0b25401c140c041208903090702c03a0410094440ca0140c49000740820110201c1601101e000078014002405c000f070010b10b51040d07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 247099946 1250 247098696 247098701
    0x10050a080a150b010c080d05010915030c031502040308072d020d030c03050912030c010509010e1f06052106061e010509060705120a021203130b06040605060309010b0a29030901 77
    0x590012a50391f82c42100482c8100184424070075040410300d003110041540d030304c03540060b08894100f103501010034110345031801c3c4081a0502032041c3c039070800c000000a4401001f03480028010b5640841ea06100610180018101500304c040003801c0030084006079602062200c100e50113107001c107415926490150740d81d01c901462943c2c000c0c0840920520310000000400c0341c4449500240030b141c0b281d10449098444d55022044160481e50100d03041c2800c13069200c180941d05100403460039603480109220030291003032041025000c50340458111400c010203a009001a201c2c54040464803a10005980502405074100000010405180c0d520a400c1d030b0f130442d0b0400140c4460300a052200038041c1e102400c81c43c058085c0c4103208c1c2041c2c400384156403013490851803219800600e40d66100a03068000d00459009545940c0400d082d102c0401842c441c078140400003d0320a914001c000048c0c250380d003c4400758030407003055428100d0503203034804404100d4107195202e44411201c02d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 247101196 1250 247099946 247099967
    0xf15030905010e0106030c0506040b07150902100305011e0f2607090504050607140913021b010b04150f171005040308040b0f090c0f030304080610050a080a150b01 71
    0x10341d82880ca803c424241c0651103c0c040700c1c071510b1070400c0d80707540707100b440404c0c0160f10070000d41640a10408e00425040c41c42c498100b82412400100404140d000a00500d60040440c000940c0c078030040c02982d8103915180d0304c8c000e403c6030341409245481c20780351840c580b50244180503894001c44801d164a0080c001d408458800c2c21b4405068681c003c1c1c200606040380e00740d540b80314140100742040d00501c030380d82411491880f440d2409074a0b4080c4010303880540000c5900c02c1c0c1c200501d5944500014040b8400030b603000000c14252180c1d42000709076511422070305420459400308208030b0b10b481050300101d455071450f00720007041540b0400e0820019400c0c03a126941000304000401da4000302843c440c9101c2d49035031129482d04030074480245ea080300d041a0340d5002482e210a285001c04403080b0158009048901d001d4a4176012401c0060030780d045401310380114400d00031480d01940000240c40d20000415003000540ca4414940740800541904107550307508210541c1d01c509100c12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 247102446 1250 247101196 247101203
    0x10216180204180903020c060a080103030e060d1505031b09010909030302073302040608041b33110304090b041506080402120706140c2508060a060f150309 68
    0x1090011003039a00f00613100b000c904600502070410110294a0840140c401070b40f056614840140e0039940e080d184154900c0180d0790100c028001000794000a00941d8580035900d615150750302d1514042c507142c032010240c50001044040c103801159100c0c800003a0446020b40c60100d0542400d05055000307106008019100c0e2202c2081d520b441310b01c0580c3c201c0f08802030000100c1d00c04031088010101d0081e80580e200043c154400b20300840d00d6540021a0002007a0041214a03591260700d12128582c3c0c982040310b4107074003140000501e603103908180f20001800d02d9140c0d00b40140340c003522807007140a090352066403412201000d0321103600c0f00001e02016810501e410740c907808054050030086404038421403116108984007000410210100e50068440d96115000d403024001d643e0410460300c400c078030504014820000c800480b648165600c00e8000b48858200b42c4198202031000302541011402d08208000315400d1200c200116038010708500046a079114040b0064400c451004c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 247103696 1250 247102446 247102469
    0x12090f10151a0712030204030804091a030f1609020f03070c0c08012306030a020a050d080c1606120203070f0c1a04060510060201140a02030603150a1a010216180204 72
    0x2141c0e44019004100c880e0041600c0f440c0100d1040f012070680c81140230040901400f840100003440c12900304d1025040c0301822034813176544150200e4a0500000288010340e4403074500500c0c1c40f001807841d5006042502c0d0254a4144038044a080501c00035100500708040038075502c0c1401000514080501541030007480812140e02c9035003900c4204a600012800c00000490030305d140000b440e03151030350b010309000302003484c0c5070800c06241420b85007a1404041003128905210052040c81c0517524004031540703110303082c448020f103503007000068916410f2041080c02005a00700d03110400d844014a441000e400c210314240c03100440c40c3c0c0c1d00c0328016501030217000420040e90090751044900b0107590070700c1695410100d090302c08211441440301010008900005481e400071507202c2c90140454503400301d075101819680600703c40711500c11380d40d40c094120f84155084030b00c44c0c12000b403004014a5040700c0c82c1c080c1c20b022610034a01440901124006c1e51101a01941e0040c044d10001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 247104946 1250 247103696 247103729
    0x3060204030302010c1b03120f0b03030705060109050f0106080f040311030307021f0213170c13022802030d2403050a110105040e130503041203020312090f1015 70
    0x31380a01141032422000c101140150b455100e01100100c070103540660300d180d802d01d9440c002400034140041d2103a20f6503100e02c0510902d403020070082c10400d00c41c000034030040d031500c0c00141c2200d2001d05542010b00b500c10040017099400320065400145207a18040300b0f0301c452070140d4010130705682d413200c140400710410400c2c54000c2070304500d000711400607213015804240c1c120101d1103401400c0d845903030401000c2c415043c00c01820b0000c505044201c401c82c00c0c40c4e80010b01d4158803d0810b0300c01d190001000c40480102401d0700d80f6800d403404110420714000e0401030744034015a29042c80c42c0d42d44449814940741034a040e003803e03003038400e1041c4400d0b813a400c0851302c40580c440c0c2664141c07602409210303203510440c211012200702c03a45041054407680c1c0c1055480e04401c1c02035075a480300b80008a001450f84008a0443e440303600110395861007030a105001c0003005201c50700c580c000c071040b50312100740881d0f00c1c004402c0b00d00000800300e074080030070010811141c12141024061848 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 247106196 1250 247104946 247104953
    0x50903060c0313061802030c010503091906020d0501030c0303110c1008151002030705011103060a03140f0d0504030605060904030e1c0b1611011a0904050114090105011403011b0e03070306020403 85
    0x580c0003401c0c0c029000d86840d4001c0c600152b545100507103041910750b2040015024500d1850200500c0500c18074003d0328016811f10824185c0b8000e03001a6003000c1d42c07100800400d500001d01c41d5414428202800c1c0013a802000a00c0f404043c01f2000f05001404000580461401c5030b90a50750100811003c5a800c002c10020b6882d000204100d807290b217801001d20110709c0d601f06a03445100020031500259041d581c07104401240342c02c0d1ba5100344100401b0301000502405040122100c540c1e6a40d159480d50504100ba00d002034001d6010792040000c0c4000710340c1c040901c11000000782e8602042c131649a211a908a0180d40003030220540b020a1007404029076203418141491940d8100c11840d1440285c5c1c00c03a0400c40041112a9192500da581400e002d840aa0b01078010800001c181c1074403202402041c2c0c0803034600d04242d66039030051200c075004141034108030303005800800000c0e0000303628002d44200e60500c01c06010340601320710070702c0c0c0c0c00704004006035a100d00c0954445039a441e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 247107446 1250 247106196 247106231
    0x216020d030f140306090c0a021612111905010e0a05040219020105160c0b0a0204051c030207140f04090f0f11090609070c0605180d0207080706050903060c031306 71
    0x30050400600703610f080340810b4100c2070036240542c600816144003034540d41c1800f100365105840d04420350141000c209400152513013108000d2150300c0a00c003088156182c0843c0d1a100040e01c0340c070900140c980011011403842010040e14404e00304044006110b01c0003e100b210580e20913548140005107a05840b500c200288404464a130006d0001303440d4a02014108640000c42130005211134000e10041402103c2103508070000c01c0c401485c0c140c403100070a90740c00d401002c10040060601039a003c040c0d04001c00300c0141941a05082c10303a480d1800206d001228204261040d5101e02c00c800c28000e6041c07200740515481001044201124070703003c01c003956522f284501c500071280004030b07141061900c052003444140e451006212041c0e41e03110041c100a4502004914803550815403118100000c40c0b8050f1590002d00c030b120310f484400303031410405030009020001c0920101c40203440018042e0340000000c0300c0e00d500d82e681d0b030440507034003038040d00042e120504108105c00d0510070070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 247108696 1250 247107446 247107467
    0x603241f09140a0303141c090f050d020606060f0d0b360f0c030a11030705040f080109020f10140403060c020f152e0e0105030f0a020a06030216020d03 66
    0x450380240200b000e00c10030041c0d03520b610010b80030443c208565064142c3c00d1004010907079191142582403040302010300d0458010580c01c0b00c4190881c0303510020700004224144620749a480107019030310f44040400c0440c050318541d20401400403035203803002007540c0c011251002004d842d01310490030b220030005040418200818806000131007400300d0000c4440403911a291030040c0029645039a0810304143d80000d0440c5000c5649240c0b0070014401e5400444c0034102c01ea4640741c036141001100c0c6000c100550020003a0f0385000114801071719201c4900d10407000403a110300200040c40c8044d1a0302100304c1d18013140c0440007902004000190b401142c12040c95800c070750b010f500a005960395400c0c42c10203042c0300640c101c00104407040080f405804100e4406140229019051002c0000126608056043c1c03682e14014032450400b004200748071a103920047c20f148a0b60340209601550702e0181508141d000502464456048042580c510b0b501500485014005050040209200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 247109946 1250 247108696 247108709
    0x140f010914030a0b250201020c120c0307020a0b0c0114010513020703050c060901022104111201020d0f1a0a0e0403050906040302060a080a0f06260c0904110f0603241f09 74
    0x81c89140d45c60901c14402d0703900e226400c0380100368000701803900d0750007600f1a00b06107580d84030800c02c0100580b40c168080380107041c0703c03002e252600d01c01140700c0d095a810804041c20300100d00d004211540d03404503503441c99894400c0c01a92842d41e07080807680d6100d42e000c001c000344180c400b404600d250543c02040c90403030102c0c0209900c960611516090801550050800000344240c01c0f07a6242c142d482c20420441ca03000107182890ba030320404160760300b41c0c0503003952664175185187d0401200c81503244000046030410700311400e00000300349028018002504000010031540402d407965400c880207140c0007801d40e40c0b00d0018020050010707200706c0e2000c0b0072504240c00c000c6902498000c140c01d5810305804020500c0d900c107422104c2440230f2030408024440c410003030309a40c407070300c4840340110b0154030307291340240c500424070240c2030000f61680e0050404004210b80307280302e88000c000d402c00c801a00c00c0c18000f0b981c0018081c030301c0042c601080c1008a480c2d448096007210340380c4111040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 247111196 1250 247109946 247110001
    0x110a0308160305070e040f0e15010e010e0f0a0207030201090209010e0703060803040b04051513080307030809060601080a090203070b0a050c300706090c0609140f010914030a0b 77
    0xd0014049098442c1130740d484001c610010a442c1c0f091803d608550503004c103030000003440016580e045803800f1a0381ca00c03092090001d500501c0307110b2903444001d003d8a0140106425405d01d00f000f224121001045001400c5d40440c9050070035200f90020409590001c100c00c505584410201403403050070703180715012901d48940080e5141d008401d0350215201118940d0406160400740501d1001c100038982c2c0d0601c0422001818440a214210180101200850b2070744034034036028008240152620350654800001c00144d40e030f1056030303168010456440820700103c03901c04203103001d4464001804000c804140c103201c1582c080041c03c0b0040301c60040303810b43c0150500c0d40c903484824030750901080d0007410400316040515002489030600c504000900c80e04180c640703200c1250150029400601980c0d410002c020081103d0b1503082d030103c03052a2418030000010f41402c81d184140c807011100740114070341540e0107004280b142c5400903500390301d901d03048484424003a00e102180301040c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 247112446 1250 247111196 247111231
    0xb071e030801050d140a20040b0a060c06060e0a06030302060112020607080c03070b0403050a090f030c0e0907030c081c17010e0c070503040312090605030702060c03101d100504090809040903110a0308 87
    0x1500d0702075a40340300008ac00a850f85d80c201541102d44031341c2c03008162501610342e8030016420703100d510f1039032250001190001c0c115056160007410000103a2081e5401001040790030007598502007120f02d00740c4e0160200b03540301c103044201402c500803400080e007c0d1405408008c14540c00c1402007000040a0385e80000c65a202c0d40a9414a003141c00080d004e0792009205100c0c400f101d035101900106024103c03180ea130340d680d841c148040002e0304040b806412010401400c0c03001b4040032008440c0c241051510410040a0300034980380502c194003210150b01c02040c51600300308212045660494140c80c1d41e5a224200b04400012025403000007a0f8030720300000b81c99205209a030f019104550107001d0680f20382c2d00e60303205d9420141040d80c030004145000100400e2009012124651904a0390007610b40403200700c21241271079000b5405541425441c800041c1200708641128100700d5000901c84068102103801c143c2c0d050710545148114002641030682188070648130b4080500340340b1101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 247113696 1250 247112446 247112449
    0x130b0603030c03030c03100308030a0c020d0e0609310603021003020313110102150103201e012304030506041b0317070203160b071e030801050d140a20 66
    0x284140328a080241d0420700108030080085c070010740d000700ca1051040d000c25100c3c1c60344042c41d403040d01c050301c2c0940e40b98240381490340c052004503091100c80c24014a141065004149648034495659101d10b000f5031124104e1100b25188140303840c07800e0a40352400c40e0301071501000301458001a4814034044000410141c441d0084074440e9840001650403052550782c0d0510b415068840c00f419401510389801d019001d210f81240203500500c1c00310600403100d03910207841c0d60013080090142c80042c2d4411b0030120700c10044801c100082c81e000a40b03982c0a500307070b800004c001101880c000d200040c00000d103d40015210300079409401c0c0920501d0700d1600d006071826251000178801000e442000e03008640340c101400410f80090305450b00001c040c2d440000c140d19175045202c040700b01040d510706009000b0000b0320501c000c19207404055105880107806200140b050364070441c44201d00c84100150411982c80e07e10310003040340d5102c209440c207040126a001c07080c0020100d11464034003d03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 247114946 1250 247113696 247113703
    0x150f061005031e0a20070206090d03090302060d0203010611070e0c0d020702040e06040510090f030f05070f051c08041713030501060b040e13020a170a050a15110408030301180b09130b0603 82
    0x10359004020300d02d030031240300a10540e0000ac4c04140c0a01c81d118800001507103c1d0001001c141c503840100580e0381d818a00041c003182d1405100341640d5100110900841071006049034010a40b4045280c81381d4000807040080c1c403844c00300940081c20440c104411a000099150165101e8005d171030002e9114035003a81110490840604482211030a100100380104c6402803040c100e49809403621a4036226000460780e010700484007a440381d0001002c080c00804080152030082c03074003c41c0b50805444182c030080341700003d038014041c002141c20310205507841c03000007940c1c0040240230281c0e4400c01203116402502c210340a103500d40c2c00141d80070b000500d1000f42158010a001c541908000c2a03541540d5030047c800e105110b8007129401152041111010742441440c0003854010716010f20340960395010f19809183c132061005000d040008401d8905550901c04070100302a80d0140717482c05003400447c2150802d100e48180030340d880c0110050301909000e2841001c42e42c40b0401411f0b034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 247116196 1250 247114946 247114957
    0x406030f1208010e091c17090c0f011b140304031211060711100b011103040b09030c030601030c03110d060f05060f0603010b0711120708150f061005031e0a20 69
    0x40386c209000943c07032541d10360b14050200d04a40b411403c000d2426070001c0008409481c40055035000308080981803902c1e608401c0911000e00e00101951503403506480551513a4000504800c2c2c0c8132548905604100140c40040d03402181811203000500e20150401b0009500c45280c0d00074600040c00142c0034055094100700040b00409540141d00940702c01000f08000c0f203030402580c00ba00c02c0c10f060082025101401c1c01d151201d503141030940c10903140040c0405268000d40011004001241000502004480e004030300700824000b4100080c582c00e00864006200615100c0002d41002c120381c406840303054107940d02418100502c2c01c10050340424400c00f841024100f000b04000b82c2140e914080c1c5600280002e0001e4016494aa0400c051034000201a40c00044040b074040c0c1c042201d00d4000c902e05140e00b483e402c0c010301050002800303c03502c10900c44000041809600214200100001c0788503440c01d444c10010a41d0010b840308505010f0b04880c1805070084807085c03541240d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 247117446 1250 247116196 247116211
    0x1060f05060a230c010618141801020909010f080c010216051c0605130209180307030c0201110a0c061106060306061c05030d06181a0f0406030f1208010e 67
    0x181080041c01086503200c448001503c441c044031403400e0568403095002e0403001050704000724582d030900300314510002060800c5000700d0b040059800300901042c2c80b154000b1031403034124003c42081ca170380501920502101030303004805503000050452010117504180c070b0318001035031107848100e0012a82c40301010714071000307514009010403103031800b1007130000c50515003000440764074020380700e903022034604890350200244404100300861401e100095030100c00c1010094042d28160341d0141d50340110743c8001d0512078940b4451096a010b02c085048080784075044445003035041c031f04100180c50a00c100f0f4040780d117000c0c21051050000c1001da01c80c42c40078004062664507041004040019007150001c07404200340f84001061090000b0024400240008075501d45030140013401e40321012040c0e52010315240c00ea002c175004185080144900c04c54083c40781510b0100040c0040220b94801000003401001c400304204e00010230380c42d14406916550642d0703907140c1d01044100c3c811210403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 247118696 1250 247117446 247117459
    0x1090c050f030a0b09060604150303050f0a030b030d110d020a020102060c0714060124050405010e090a020d1a0a06090b160503090616061109130f020c03120901060f05 73
    0x38456828407040c0114064001800c9400410f034a4895900a99054604a03800c2e0040401c000d1141050f000e0703020080c0e0328503002921540f564400600e1401a4000381140d0708002480e4034486200790070030000000d00909840c900414507002518005540c55079000c14000c02818507070750f038000300d0f1481940d501a00501025610b082110400ea032094004070396400004160b041030440c2003120601800808114401c0c0345a42440b0707c281680a03c42e0504210b0f003000107022a9034040e4030180e03d002d0075078a02c402e5850343d900180190260325200d04c401707443c20548088003c20b0115660300b044c02030b20000c0b099515018202c6091a09015800c00071008205072040224030300ca25071212801072042d2800c040b21100001c420354440e2440a040001003800b0700c0500100307200350115880803511030780c6440425408a2030481200c0315034800b140e41c2d525450039015003501182e80e00c9002c030040c1c9a45503880030024080c5003083c0c80a8045600e0100c4c0819283e0341c40505105680f00101403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 247119946 1250 247118696 247118699
    0x3080a0612020d0f0602040303021b06040303121802100507060b1927050708070201050a0b0a09020f0c010603031106090a0206180f10051903050402060d050c16060501051201090c 78
    0x3e00011440c030f0f0b002112110402d05026000c10420306c043c10140d03109030f01a0181d00b017885451180241544149845900200b00800c0002d0b0440e40d0404c00e881045030100b840d10000510f00700c40c030103c1c100a500032021540d1000786940c0640100505880754004001c142c1d0094244a08200f1a9a2201d10009071010a00c104501500900745000c000c070115044020707500070500546000340e0781c54011803114014020159028000c0742d6000302e40c5101003000141d01c900044100b01940b0600d4211a0300040b45c0302c9d01c0c800042102c008600a030001d00055940741350080074180c818207140c4050040c0d4010400145000c00c0d0f2910040e0006c2101d8108651000902809841c40d000c80794042c001140f803404039107841041c0412640551102a19100662890b15155006480030010940780c0010003006035140c8081e94035480309000001400d5403090001241c5215078003520b240044180000380800c070094008505a44080d5140440603100c0c910a5007a01d562071070007460b03034102150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 247121196 1250 247119946 247119949
    0xf1501030b04080f0703170a0b0a0612060905091c02070b030a0510051003151d04350409063c090c030603020a0608160809030d0c050703080a061202 65
    0x103020790802e0090200790300e0710200c0c8144c01003e50043d5401c90109101410140d000702003104410780c0a0450481409030104040019040400e03600a50b01404021050040c52207000d5002c44044c15a1070000c000030304015030519a100d4150a07464134070a0301d00f45150408d4404036200e8201e882c2d250b10681980c03540e0b410030000c1d01000313040d504035007404500007039281d8034242e05e04020b500316100020701e04160b403a0110301802503000032900c04c1540c1d907060020113203409403541c4145c01c4041105104610b10f0402050160b91a02c0c030040c6405024010030a0036a100030003c0f85c0a407482004616030f599680504e0142c041c40f0b03201000c0704802d4182207401010141d00c24035035500c0d4000c0c203858944078547c0440d036451308100d00003540c0c0c41c018021410300c03000100150685003400326031482d00300c142094070440c0d00b030700c04100070038800441c221003030800035a0140c401c0104207101224840d100207000d5040403400380c00140e203142c0402c03c4080d40344583c00c03e4a0491503400c20101c035540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 247122302 1106 247121196 247121213
    0x4181b0b090d0308040f0c06051c0c051c090506010b0706060504020405100516170c060a050c1902030403060510051e030c0f0f09180f150103 62
    0x303058050b5202d00121007015403510349854980c1c3c8a21748442c4103654841e0060402d0000c04000c01d045401401a04802c00c511031650011030542040d5003e5070301114494000c10b004004015840060584200b40504840307000706025141d659500c2c54120309030300005c6501d0000c43c0903c200100d9000c0e036001003804940c190b0900c1d040c44001250000c80150001c107201000030820004050343c42c50fa0031958100f102c1ca500941c80c40c80d10f8090f584012585031031405000001820103071103201d554000d4000c42e0f1768908140e44c004595610301400c4c510002135100c10b0100000050481c0280ca00c62201d0541d0b0010140c0380005100072481c2c5800405404807038100d0148241d05c00007204c2001781d00032100c5000c1100178001244130900041c3c581500b200f40745040100c5003a40765070000c4414119004c80f4440d10381c1030100398981c224803050344503100c45800100040b49802 = true := by decide +kernel

theorem cover : BRFrame.Cov 246942446 247122302 := by
  have h0 := BRFrame.cov_init 246942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 246942446 ≤ n) (h2 : n < 247122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
