-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4175
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:47:20.087438+00:00
-- url     : https://prove2.me/submissions/69e39189-671c-4f7d-8339-69033ca190d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 750719424 ≤ n < 750899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 750720674 1250 750719424 750719429
    0x31413021c020d050303040c0f03200a180e010b0409020a05010c050a2001111b0607020d0606090204030c0b0301180b1f02100623271317091f020106 65
    0xc41e5680d0241c4044c420040300440c00346010f85202c1e84004d4035018214038001c00740c03000030520040f01d240300c150700750002c401040c0307210020305400160b659038040c8003800704c800c1e4000b0303001666a11140040e000920420340c5801c4c0645040c060f000c0690005410b060452282c00d05109202070448104201803105203516584590142003201c0340c0100405141403840c441408100c0d44d02c681c88504200140491625140651401500481c103050244503003101000701d030002c07890301380400050000e003e90300103400754080060b00c8510303505201600030a00d5120842c8454204014003124200c02c041d803403201d428040125000141c400031825050301090480428000448a2900140d01090f8061098080c20050090301e41742c003004408242800c4924903000c0e8903090000311030416092070030084000d401480300d150034160034418042ca085500d0408170140b08118410007011020141281511050f181c0c10218460040703000c0201d4040d61b151041c40405035160180c2c03003500301801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 750721924 1250 750720674 750720679
    0x70b0408130f050108090f340b12161d06120a0c08220b07020a080a020604051501060c02040b0a1205060603060a1808030705040b041401031413021c02 66
    0x11001d540d24075840e82c11420340241d60000d821400403480400c40001c2400a040240c40a003480f0340011503c07080300102440041c0000d820b125011005070000c400040003801031104903603a441103a1000120180010150700c030420f07101e04a0603007568000c200d12207032910700c0000f0034440d0918000944a010f003040d051514582c00d401c00200c00000c4d0004c10701d40c1d010740c07510700745600c56551828850013a81413030798103c80780c100300c44003007111394031056040300f40703801614580425529030101c9a8006a180b2000d40d00c4082400100034082044404101d1040c3c1d4001a43d4103004004140c00c014402c0a032055448000d210f602d40c4c3c48181d540c000300403582d00d40c10083c03074a191081e211101201d01e540f103070040c40001600e0705154000c25220078020112600604107540d1102c909410161011080082c14030011400d4004200100007901184030321130743c4000ba800004003a102007103412401240600705000300c00440d69842560305504503600004010040c400d4003141e00380d40d90180d03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 750723174 1250 750721924 750721957
    0x40c270e0c1f080601050f070305030a0b0303210108160b0c07350a05030301060c0606150908010c020d090b09060d0c050306031605010c0602090301200a03140606070b0408 75
    0x10b101c1115032030345080041c58079000032070369503503005642038025080c1e00003102d10200580c5000078482d800a40d4041c0a040d00000c8d5100c11070003003861600420b03048800031408620000c215130100c02d140d801041d212000f051200c6108660140ca20b0051086225455011844805400e410701900024142c484d181103201e540200d9140350794035000070624000c40c01c208011a05810110b85240780c980c010000b1072a5074a0300c04200c40c550510391007075400603510000845c0446114031003490380f518540c0c940012034203050740a801c4401440c0f008081d0752210074a15911904240b000086543d50b0f5402921001010041020f6201e100e074169005403a003203405010381d030000082c6002385c01c140d00700c42c2c08944c105110098100b00d4001c4c10301080d80340303000000040360f50b0012700c0d0800010700081040185d03054081e03030074240e1045031708451001194640003079501d0f200c0c408000701e208500d810582440404a1024440c00d90041c00c400c03080400075042c091100708941c481c01ea000100c0c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 750724424 1250 750723174 750723199
    0x19051504080a0f090b03040b041707060c0e0102060f060f190909120507080d05270a060e0d080f070e030f071d0f132603040c270e0c 58
    0x160010752240c1c10b4500840d1400da03000e0001442641c0c42401d603000c140c0903d1071342c0c489440d604c1720420010012510242904c49002c5010706841c0949801e074801c42c004074030000c00180c0130705076004212801d8119030049040003c143d15a000c0316402c0902503814003840728024021a0025014000c00e04801404180024443c64a0b6200d01d10550051140d290348200410003120701d48580600a05200828484400240710b160b110581004415098034400c107400b412160280300c140c400142c02d500903207070b550240b01d1623005a5204079001409007030020000603000e0328421002e420041006601c1002402090181c80005410900101141c241141e06928503644000070300a094001501050210051441d41045c50083c5810b40417406a542c1e40c410020007203800711002da900a024050418844103031251444c1010040b034180c56807403030b083c2080e010700c2031186d0020700c5120034440c241e0b90005642081e0205800703820340c0819800814108140761a6098070b920794000d01c3c45020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 750725674 1250 750724424 750724433
    0x1120221100f2d03060507080109062306090901030803041703160e19120209090a0201170a110a030204031a060109060f02010609020d14010b0a0219051504 68
    0x20854115422020500c5507140030544401c980ca0340718507075450041000a2100000c440c0072602802142c0440d00d00700c0300c40d0510b072408441658403d80750f0311382c0c4a007032000655000000038003501c0214801c0c400381d03203080c0c0341c520302d070f16034021601e9451120403601075650340300400c58a41c83c50040c00c0d1802075841e42000e1700c1c958800d030740c201d07180b0070b01c101903800e21032060080d40c3c8100c09030442c2008230016810151104902cae800301070ba10002d05944002034240e1a685000500010b500c80d20303814030716205100002d040070b40503440c26480380c404030300182c0e400301080c0310004410700d0121190b15000041d401500000d02190003070400401c540444a43c1640604220780c0140c1401003504502540c00d0070104068803c240011001441800340304d015100c400c1034030340f180c03000151855803072181208a13045401c0c2d0300001919520461161420b0342603050240500f01c003140d151600050019585580040818086010060399241800800d00080350395a652140210303040c03030305280c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 750726924 1250 750725674 750725707
    0x30506011509050a06080f070804050a0b09030c010c120e060906060f0303040e160e010e030703060c020312040507240801030b04031101021207090b0c0703060b040e0706080114220902011202 83
    0x1814032040c2c1f4000e0004180c44c0c441c0100900603a004806004840c0072030300e9420010754010550300280c0720800000c81d03001000d00c605a4181c0c0555920300c823905400940e407081d038212a5416149503c000d003400400703540403540c541c0000084540703105180c01140406c0c1940103903400941e4081a503401c01c80c104001d01100340000c2556500d080c01058000015902500d1a500c15074140c1e010b00d6040c80081d40c560b01c40201054079004490420310f188035103064180e82150110703401d0304440c400304181d8001e0703800f80c2c442c103204004419550407001c6004003044414413020301001c0e60000400c1c00c2c1402000000141c11116000395076900c80091032030b600c00340c20b071040310001d03121220014441c0706060a0310860f90020000d40641d40c9162101e04c0904204804141d00903503170f0304200c1c0d10301800c1141c10020105a00d60721484d600d0000181d5842e20144202ca01035402043c1d007400d031605040d5400083d1030090000940743c2d0050004071150900b9044084a0307a200094880c0c81c52030b20784 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 750728174 1250 750726924 750726931
    0x602010204140406030305030f04050c0a06021501060305160c113105131b0503030c06150301050105060405120c04110414030d050901080c090603040b060910030506011509050a0608 79
    0xb1007039041081d40ea0922003122000d1001500250081c4041001a81050011500580511b04840b540fa50078400201b0700740066104030090f9209002d00780c1440401d0707600b00c0c0104a40d0404011500d0255912808003102e610b0000800c803114001e4410003040314000c560b141e901801c888810030059074540e100c4080e03105010034031384080d041d100740b0b0141d50086c24440c00c01101c0c00460401142e03100d01d0710401c0158070f5000440c41e0640031445071410409805401a040001c206500340100c41145aa900b241440d000340d042c4801408152240c070b04540440c0c60903511040380780551120b8074100300304540110703481810040070349034002c20300d0058004c1c1d500d200e48000c4100000c2007011741e10803240134001d0214509200c150070960150003015030016404000a1034104240d00095141e030048a04480390324090042c48160700b8040c031004e90203240c07224144e1301c060035034130f540740d0304d05c4144a00110503031a421190401c5100d00c0340c0f030004082c094003080e0038540380c0002401c00705089 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 750729424 1250 750728174 750728189
    0x90504050f0a150902030309040e0105041406060d03052b0b0a121a060a0e040b0a0c020f060406021c1e18080a0e010302120906040510060b0d02071b0602010204 70
    0x201d090307510804030301e25000aa00640308500d0514003a11440036009082050740c0c90b000034000c1844584850080d902031245417000000c2034580752424071300c0c2c0e400050300c0d419541e110404002e50758039402151411301d03415003499a00c414414400701c071a40505070148580c1060304101c2d0722010800c0e0442d80c1840d004030f600580f80c5803180c1c505042e80b5103130300014006081c0b007a407140c0c08000d1030b03200540188001e08800030017034072411a45148402510201c940500180401c991041d15214a00d10030074540b0280c614002080050390303032100041d00207000c0c0d41d400603440301603129681407602800203060f13003889142c10201c038800c4202034a496a504050602c1012110014898044402c541c3e00141c910308107442500201c070103110341001c032814503508111044101088506140c8070301103202c000d001c0b52805d0318003c0d081c40400d6030920501814084144031880e0f10304160340c180f60000e0380c01600c454141c20005001116006086101c0c4034028002c110a41d040d0001d00549080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 750730674 1250 750729424 750729433
    0x30b0d0f1a1e01050f040902100810061106040209100513060312180e060a03060f0c1403090d030e0703082205030c18060a08160e0c03150603040503040f09050405 71
    0x448890002c02940c03103100d8224180950010b00c003500c0d2081d400541954003820000f0300380c44540c00301e011b180382c10240c10f0200c1c43c1d040c100310031801d42881400251042c0d00c4e04014040700b010045a41d8a0090002881515010000f8009400f030201d4171006240040003901c010282180040041c5818003040d19040e62441c81e00e086036001d26030040100348078202c1d0f6159070786000c0440c01b040d02c002d840541d12400e208000404629075000c0d010800e8030304900003506101c80040074140348018210822866028001c009040e5408146013032008031908010501e40e50203071815003488a07039000240701d0b02021420601d100030800c00b0301c52096050030000c407074645410405036106602103800d86c0c40711b00340006000d0303003118401c25900641c010f032031841080d4071210f40754100035820300701c6c3c00300b145001010000440c40c0e14201e03400c02c12904800d0b156080100610010300200100940598400000300b002c0100c100210b6006103c000c01ca496035035200c0390f40d034004d003a05440c142c032140316 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 750731924 1250 750730674 750730681
    0x2a1305221a0a141c050c0406180b09100b0d090218070206011415090f030d080a1a06070f1514060f1008070807030603020402070b0a0501080616030b0d0f1a 68
    0x103c0c030741c41c8821030001498801c0c40ea0b1030001190001c0015130003182c1c5401666114074207919540a000081e0042c0000c103000d490643e02d00100300c0f452030803481d210f0030000b018403820715800174204050703408403040030380c1d680610341c1c000e0040c22400d107000750808202c000c01710150300400c80d80d5008814690989181e0b90380c1e2001e4036440c0000d080c80070f0384a15641c05400450b240c0c04000c106074000035102c0003003014040006401c11980e010b458011071115000c10848044600c52605070080282c02c1d07400d0000300c8804600f281c01f4510340205680401c44820003405aa00c004060100088038107011140c0c1703080c000215280141d032418000c42c0d0030303880820180b0b8461445c005908107540c07440115a205141210072420181241007851b5440e600440540c90707500042880718090103810b03000c0d0524002d03410071140140d20000c1d6035080b100c180724440d00c4c079044219804015280c08144560b0410000e400c0e031440030402004200c40390408810401c0c2a841103062040714240e81d049680c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 750733174 1250 750731924 750731939
    0x70c0e06030f0d05250c06020601050303070c12080f0408030405042007030f050405041118060a051204021f02060a1505180c0f032a1305221a0a 63
    0x403140d19004900d81122940c6800580700d5005091700c41340c03440d50342e44108145d510084d603844400c02e080d0754000b910340c0b0601209404007c6540180701c10f4000714a09111511354103140c000c0ea025850070400907021010a0000010585603060040f1101d01c3d0f69660b40d108142e03032030348203104480c001c40c24001c410403983c07480c2c0842c902809900890794509492a5000c54100e0b000c0400d540901000344808941502c9902ca88180000030041650350344008a80c007a00401102e101507120700310802603503240310703484401c1e6210030618803c1400143ca9910000300c0041e014000b00b84850841242a0042580020600e000302981c80d402c00103080c0b0b1860214105001c0e0141d550449000d000041c15050360104456100b220020480e0500c071003518107040300c0e4010b1350141105a8502e03140380304038050940300c2d104900c0010109240c04c004c14000700980d0400d20420f841070220103083c083c081c03000720b0354060700082800704010480c4529030180e410b01c2c003407145c41d0040705020008100103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 750734424 1250 750733174 750733183
    0x7050c0105180f12010216140601080304181e0507080f06090622020310030b09030421020f280506031e25090612290f06070c0e0603 58
    0x2d1030030070401480c0c001030b4061001d0f4442c500903454101420081401c401003007031010313050b5101810744014541c0c2c1c240c20070103c400540f8030b842e54141c21100040000540c0001220129a5400949480c41c0102d0300940010030004145424105411022514907041c0b03500203449280c4644070710340c25803903500c0c210360301c0841212440d42009a103008200d042c0b81c5051050280065480717545580264500f07987c040c1c1e0020340300700e0000b1340c0a0380140104803080341c0da594441e101c140114205850114400000b03104250341c642c03520b04601034a419510b071100e0394080c121000d080d2008109000b2420700c6031801d0310140201038a81244c000c2402d1401000302d038002e20700f01085440206515039459241d041c09414500300802400c491201920402d031843c00a00040d01c49a5041d0300c3c0090203440410701e0404110418a002013284601e03082c201020048644903141c6000c0f48034000120362074165420301c40e0790007240420540204140007004205840048411120b5601c58405140e9503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 750735674 1250 750734424 750734437
    0x90a0c080a1a100f090204030308091603030c0c0e0906160905030a021e0a0605090102100504031d011214040c0b030106050d02160204020412020f19050d17040b07050c0105 75
    0x32500005030b1819042c2000c010541002041030820398440d9140c42d48040f002c8103038015500181c000c501002815040382d883c940c000c00709400703030210130f2904019501d402e819004c02010b1014203070642c02800482e054100c0076180d00040e8980500708241c5040c1d41c2c580450300c001c612228500804c042d64850158501124005002007400566079420030a000c0600b5010f50410304400300c070602d044e980e001014000f40b00e80c2c1c0311590f0340c10240000a0528494001d00b142d0a810316080c803002960140319000f01032882e0410b030020018190040f030350561800b403440f030760500704401c80c0c20f4101c52009240c003a0b8854024400d002d50b554070b00180c1e41c00244108404103a0611010124042d960020041540b41c8a1304e045c5465284d4001002c98000c0d404c6050650300c201c80010441c01e0400381d55018035000c4441c92140f00800d491401101c034580289070040410a400e0001c001d04c03000c03e840b02013944c126845d02d554449031810156017104200751070364403036400600100d5001303000702c135038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 750736924 1250 750735674 750735683
    0x6020f03070303110d0204030b091605180402030c030609070f23090a09050109030f0e0a14010509010c020d030503062b03030e0a05060403030e0c0906060d2003090a0c080a 75
    0x800707240e0b48083e002400100e0602c4c0094908010150400342c0d03a200820203580f15580c030003814100100160324010641032100c0d0344418503202807015544174062540703a0610060320741c9560382e451012030f0520089582c0c0503058459981400b6030020301103803240030b60302140d1070b2103c6156124014000c3c10013003640101404c0d00c0b80548411400d11000d0b0b1603100f0b0b0508004600014203594141c219a010329094001900001d640002541c1c00703002e4006151080fa43d420b04c09080240c0315910310a0103000c54140900040c16524a90003100e0080e149900107200386c0315100710341000340041c4d000300d40e2a0711454081014080d02c0c8042c401c080b9a0b40758100c0c1250004060303660590007408880c2031203035544a01d8810344001401045014400d511903900400c0d06c1c140f02d4440c62a0035028000d0a205240100402000e41c072160181d410100d001940403640102c0a40d0b04480106034509520303500c5400800c01207000b10010300d00c1c0324039103e100c3d260020360356803001c00d4580214420050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 750738174 1250 750736924 750736927
    0x316020115050d050a12020616230a1103040b04060e120a120c05010c030615030c121808030a15090e100e0304080304090f11040501080c070c050d060504020a06020f03 73
    0x900300b01d4450143c0900c96400c88100c04d589403102030a051181c120400183e2115003000710b4420b8420ba01c0612038124144080d024100003103200070096882011010140041890b0404621501a00152800d0b03070060305d6880703446a43c403403807581c840e00460002c9603421440d20310a0400e0781000c0c4600070841c0186c40c40c15110b03070302c2400c0d500d05400c0350000c0044c000003135400b2500a11400280c444551030000d1880e10301700300c9030754405600203032200b0f26290642002e5003d4010701391519003a5440400a640032441902c051603441d103d0015014110200030000c0200082d48200c9440d419050781070b82c5c00b651041c6210698600702502415504222081c09801146401080d000780e40d000c2031701d087c10740351442d40f4030b10b4226500a01ca01034682030107442170596031203100e85a95003080b07a00c3c9031034106000a080e02e0800b034001e1400e42800560501404002c9407140c0107004000e08030720200000d03042041c0948401e4a05a00c111019480064018000214511802002707009103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 750739424 1250 750738174 750738179
    0x203030a081e01240207060f0503060411030f010303180b09010c0323070b010b19051605030a030e011805061f080f0f0f0c0607120c020405010306020316020115 70
    0x100d0340004081c2c403400c40070b1a0464241a280358190300c0a020705148442a8019420422889800b4080000701c10542d003219000384070459022540307501841e0b03903003001076590300d0f000080b40050110015812854001000340701100410403c1e0074122030081c1c1e140c5000c03205c540d900c41c02c5c0c20910300c81d503000108104401d40c1e0795402914002c2095000e42002d10340301a103500c031030041090f084424170b005400003884004200c04d50b01940d015081300c98455040c846075800384d1003504441c080304001d22801056241030f46240d150000101a4001c0c207a0351214041c1e0350150103015880550302d16942082101d103420384062003504d0500d038111004040580300d14001c4801501c611141d0094000c0020002c1640c00c402c001c0e452030000c2c1200182841c580c803031100c500300040015249101e402c002c1a543d2566079040641c0c1d41c00e600280c02c4985c0081140007a83c0068002c0300082d007080c1131600020600005601035889200e03001c441c00c0c500c0c030448004908072000711141c181c02a1400106 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 750740674 1250 750739424 750739427
    0x90306072c0105070b0a06150c05060105060318120a030621021504050411030402031903090e190e010c0206090d0519020a0f12030c050307022a0d0b04060c08040203030a 74
    0x640700410b050041c41d1680b940c403491540c2c10b0456403000c00710348070302e4100a500107101d03200c0c3c00b400040c035200101c0c42440c0e035520389464061145a105041c04004500b00c211a4490200c0d20040720049421440320440100c10235000320403d507001c0b0740f81000004811075800400880026030801190403070407568200b00401909035012420340b101804040b075151540e1052040e40003111100715240d20780751041614206000410845000c82c4146950000e600101024162061951200c0c801d686008000c041e5018502e415103025041031001c0d2074448040d0300560710317100e1a5080d161595141d81c40340d40e540b5603846030000007440c2042001254246403088c41d1049082c3c0c416103000b40d0190f21000c001d50452a42079520071408d549924050360503102c1c0c100840d045060403401e42c0303402240a5110441c1c40350340d0ec03445d92038210004101401c1649d90310f242da00244002072040c0340d4188140071780d500f16800c448017071520307603a80300c41c07070003404123034403482e4010000d40c9403c1103101c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 750741924 1250 750740674 750740747
    0x613061e051e220c0f03080310080c0a090e030706061518080d0311120f01090605090c030c0901110304060201020a03060909020d030c1104090f031b0228030c08010209030607 76
    0x3070540341c3c00c1401c080402e81410b4840070100840c020349040e5100d040c2901c00365001c509e00e83c42005907034006110320510b5200e1880343e10441d0702d40940041c43c40ba003481030f5030039803044d080000c254610b00745010030907219110007a0108045652411020041c1103c1015a00c1d42801460110362201c403000c0c50580c03082d041085401d800040c0981058541c5407010103108066402d054240c640c40d0040c412040305100d00741c010b0201f11242d01d9039080407503940b00700d807001904c402c882d081c002490884690082150032050b41e8000100c0b59965a03a4100a00075002a001c0c0000030b410034900107030140d020b0185041b0b4a800a108081c03904580c0c0c0d050b203004020a108032228800a1400301c2c85540e588204450140942d07441e0054025038075000349580326000303200310345c0c0c115075a103840540c440c2c40d020080546001e00300940ca04004284041e0360902d940020b10080020401242160040d0054800d01c1c20981c201c60b880d403a00102610401d0749100000c0a004070b180000822403815903 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 750743174 1250 750741924 750741991
    0x30f090519020d1401063312090c0902130807050f041d0d020a030e040504110f0d021507170316210c02060907170613061e051e 56
    0x100200c8403903d075595410002c0d13900c60001001c0da590703040204820610b4a0076028841030707841b40d012003a08104200718072602c0b01e8601c901001641c000503910b803140b175880148140d400c010030300d504543e1207440700701030740c490306880c0f80102e805640010303003100005101041d2140141500307201002035003444010a05441c44018003102090020a000d60512407541030074181d50281494804904000d0500c0c8404071b00390380260305d82420031000c0f030345403500000305440840b1403500380c103180000580181c1c010305010390f0106151000901e0080da940040242c07501c103071138808043c01206034401c4917000803690400c3d0b055000d484940105c0c03084094907a10a00040c4242c5d008000114850072140c100c8603034400341c0c0c000c1c400e00815440c20084500100206164518402e1403001004e0305e13220082d1012020001c106480300800c00903810075034550701071241d2200030203243d00b04400a00300603529212064406403555190084a400644c030a8060020070007400e0f0040c0e218100c0b0b0710288 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 750744424 1250 750743174 750743179
    0x170309030412030e0324130501061508090d080c030c2203080a11010c090e092503030305060f0f0d03020a12050a0e0402071a041b0e07030f09051902 65
    0x420002c82d414021000c0161554000d507640c040c10407440007854908001e1403030960f44101600c44100740d40c0e801d000d54662100e070075a42005440d08929150380900520340103140454605100410225441540c040c45642c110044550788000c501095032400000c0d203600310000c10402c0041d4480e11290000c00512084c42c041c548041300b1094401200010b40d002142ea10800003a0803181680c003050780e0b100c42900b00e00030424110000005003680440380308906801c0c140c180020700c2201c041c0320b40c1000d550024044040200120640303080c258007400100e020900d000c0108040f41880c20035030401c1b0303801600c2d440101e0180b50030410f149101e04800c50862249110002c0081c0b82605180c07800c100340c1d11042d880b111090005041d804003819050700035481440060003164000ca4200c44a41907c1244607194a4034141031000345c0700c0d0200552505803c00c070004607200c012071154803c0069903000c0040004040014040d42c8045101501c95440440a017100704034960300e04e0300707a40c0300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 750745674 1250 750744424 750744427
    0x3021e130204060e13020a050301290f18040b03071503060b0406030b010207060503040309210f0b010501090e06030607200312011d100302100507051504120f02060a0504030c0206030f100b0717030903 87
    0x407040c0b07513094ce510540588890003030107d00200c01402428500c0c0d20713000c00703d070180030028404011036511f41162141c0c5c83e40b81000c00d5580300c803030b00030b90040703025185561030b070f541d11512210090046c20103030321043d00606c100040024518400c0c4156801140c0c155100280286000307401012080a0100c0880c40c041c120048400a42d141c01502c02d16842204951150361400c0000342c40321199a210f4217014004404010341c5550115005034480700d141408480042088140803001086505942981c400000d080c040489400805812683c01c10140c8610794400f0404102005007520203080120b00c1180c00d1005240c004c1c0040c650768076618100d410000a915505c2c9042000c40140c031407105048213010920216040d01246254281044000741020302c1c0b009649480040074a030041c1ea81e000410101446401d4000074590000c003032a40b01c0c18a04041d10010710141c40e4041c0041480700c0000d032441556003513544241e0428000360a20340c00f490082c406900c001d0807407219000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 750746924 1250 750745674 750745739
    0x709150e040f05010801060b0a0e120c030708010e0d0e0319050c21010e0a02060a1803060504240c0c1b0b070305030405060a050103021e130204060e13020a050301 71
    0x29140b158038031000c1120404541949404641405c54065400030850500100214002213400c01045c0c20040d0095a0030301004800780c400301e04080340d19001a503d80554040081d03407420540204004a184206407200418032202c10f80e1207007416101c884d0150080b10050070720b0840e2441060040d4000c41c29142c1101584c4001481d100302c400c070301d00004c1c0000e450015031020034403034103003100505002004030144a80002d0502d0040c0941c18003005000300c000c1c01c0641002d41440015544950705220341d09003440e02c0701902403040c1c60706003600c440e601040d800640a0040000d8682581c5401d00107517101d456200800d1003880d0f46080e1103a00c905c00151082000e4010032100740a50b8135180c0342d00b0146001400e010b4013822891505050400503c09641e99407241c4000300003410503548000644000304120031001c01b10110241d102003800640c07036401100d61700039104101c512407810300b50503160500700d004500c0c8034000990240018040700c004001000c00c61118240403400054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 750748174 1250 750746924 750746929
    0x170702010b0312180f06090d0606120303061509061211071b030b0c0c0d03050a0b090a0b030f010203150103050405070803160201032a1d27010b030709150e 68
    0x5401180c4004441001a521078552010000010810811901d4484179940200081e410b4040c0801082c07181e420019608100700e02c66020390020800d20007032040130f184900740500284003502c5031aa50030014540001414400c40c1c3c0a4242c402c0303a100c03441d4940480c4c40ca100100300c0c404840300b803403804000d40c4012030499140c00c842281c00800310fa419500310300e40007a00f540c0c0542407075200729081c4582403d0140104114181044074a40000c4a643e0500c2c0c2001801203601a690030180f031405103e003801050b000042170010640489949010703042085080b84022105801001d1049021103000d61113501311702d030424003e00440c1d060719116840d15003958441543e01904000e00501c01c1c0455070540614038145205820f05e4400008456500752a26403541400c0c0c1048860b07400d0039140481d078001080c8034080a001808424100d200b2940003141c800107241150005030f00009007007001c001200e1080311140d580f4124246041c0d420654800d03080a003c05106006440340d02a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 750749424 1250 750748174 750748183
    0x51807050c19230d0504060c110405150306130f0f0804051e0a060302070b0601031509060611060a0e0a0f030306170d0e01020c0604050f030c090106080f0702010c170702010b03 77
    0x14060590403400c1d003403500d0362148060888480c003100313811402400c0d41d001d401c04161401c8591a041c24084c8080d039142002200c04a401c02940c07061800d4184140b0001d0030b0804102c0001c150100c07602030700c42c000c505c8101c20801c0b8009110b502110080000103401c00d5004416901c030385082820a40c4500004901c1c10b191403160122800c140d203503484501c0c0803002c0f41c0080a007410214a0840da0362100701840c40010207942c18592641d0b1040c0b4011803100845008003070f010f2082001c9030301d507070740105000b5403585003080c03c0c4500301c08584607a07258410000c3c3c04510344000c003806440381d80d800f0000e41900f0000e8060581c0d80200050a0700e0070004020281001800b500c102e24032850040c00304840480b00700d04661040c25542d10a459210458052f6002100c0440180c55148002440d10524024040e0814408800040c495801c2103c2c1c13030080050502c00d03411070752000b01c100d08960429030004c2c0011000b9904001300e14421441e9504801079100100c1c0350004080442d140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 750750674 1250 750749424 750749473
    0xe01020c061510050703030c0c0204060b07060b090c03010e0c0c0a0632070c0501110a0e1c0c03030305070507050d050301150924050712050d0501051807050c 69
    0x20741065080204502101c1502485404100c900210b441c44004008102c0e00903058018103040d692400d0300c03034281c09403e0303280305503074018400e10501d5180d030811122908907200445d410b60505010106c1031800c010124401e0a4442c400c0d406c60b8a4001c0c00f954001c1d0141071011070302410021a04c01500500c141c1628600402000c940303034104888483d0100c00c0c0b040c640414010a08940c01c44240b489182a001601450459843d0100d03080c124014810460005404900007440c5005550019040d0846a5080390980b04440c56015680d10b24070099200030f103030a6540400340300090281e40280d0700800c65182140c00c0030b981c0e42d601d500d400c5150901c400450404401000a444e00100e10702507400e0910b001002d40d40750114410248040f54905d8082c02542040001d0f11442202500c8072580c110041c0950410303140800340c21a4045d003c6601c55900f000c3c00424517052154140d0841d1101c881c0620056890540868068100034003804140c002c101d51140c140f064550403500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 750751924 1250 750750674 750750697
    0x70303150314070f090905070e06060d020705010f06051e0405130503030406060302190e041202120d0603031d030a0209090705060406180510020d05030a0f1a120c0f12010e0102 77
    0x3c89030401d1160302c05090b5a40c403120899040400500c00540701107403000031a0022a2526032a899001c00540a8010003a030911000c0c8042003900501ca4150890b16034a01030038020020140c030741c01401840701400c41d07441c0c4004491556404103040a52105611155402410120500c140d5800d411130744140c8007926100c3e2a03542c244103514100c009916070030b050856602413146420800d803800b5070300a10190031000110509224240244280b01108180c03140496850400602681c0240703114041a400601b4003424805100040e6000b9a0f03001801401403c1c0c2016a40c00c00c40171381d5000b4401c401600511000107084d0300c45502070300240050b0340303038036580c04010035003490007428940c4014403a5500311100d401c0e068020a15101c110710f6464825071703070750342c07074002e94094480c03146800b0b05585007140c550202861030000c02656181140c2c1000d9405a84030035540d240b41140c4002d904c00451a002c00491510302d03a500c1054146000114480d80761401060898109040914 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 750753174 1250 750751924 750751933
    0x7080c0105010b130513140f010f0e24040609230a020304020a030f030c05062701060b0307030c0210410604090204150f06120204050303070303150314 66
    0x214201020700959014155104074942080b0415a031500b6100c11441141d0241c031001c4100d0144d84c8440d000340180c003428109144003406c22083c0081340310b400348911100c01007230390b00208943c1c0b2001080b0b4000c5d01c400d040b0844090f0b50080302441c0e4280604466070041e0381d4000050440006d010300041d00c9042d09645201c0a10352121210394100204014105441002000010f0395441c0b0341d001640d82114000400b81c45030301c8c003a82d182103071400142c0786201c1c0000704010845504082050f1501c4003d02d080d004e5a00704100c0d00f0b8440c580184148860284005440c01e1310030f6000d600100414411903075592401002c035802c940104182804615009040c00071840c0450031840c41000c58020706000d07480321a105510b0b9041c050701c40d0340700310348540d800400e560307071074005010300074058400c82c055650301e4400f402680d459100d408045040e141030900111801c1c800c1d40c04650000d00514503101c15590102c0003040c00c0c884600c200810f400300480416041d80741040071b00b403881c0040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 750754424 1250 750753174 750753187
    0x24030b01150905090c07260702011214040b060103061a0315010f0c1b0314060402090702070602060c0c030f0a020c010815130c02011e020306240f09150708 68
    0x1200045081400a018010415020810f0f40c94003400c80340e004242603c95070f01c0e151280b80241c402581d030303030224901c00808000d440ca00c2490400400030726100341c035130000f01d07403000044005446e2a004040b40031184400080c3c0814420790329543c1c001c40c14500000c1d01c07601c8072280707840d0b405000c12000040402104101c1c61400009041c040e800e42402c0100703400c078242c0704c014040e8800324002410700c0407100f12090805c003480d22900140d03522164042d940b29400845943c3c881089801340d21610480c00801c4200d40085000d07010340f441c42d400b600383c0e542c548a00ea03c0e1079000034403c140e5031104000803000c41480030301034502e41946030f018080d00b40d202c100062503500090025141c013a00100c080e41070b982d594048070481498140b01044500b2140002c1c0e00400c1d1910641100344241d42c40c0504100442c0d00452189004859503c04202d2880b0301130280c00f4082149903402408010f030516000c50f0902412a848000b007580011380e900100800d2150081c1e80e04580501020070034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 750755674 1250 750754424 750754439
    0x60a0c02060c100917120c0c011d030a0e0909071214060708010e0702010b09130302070b04060302040305010510060f0513030203070f090f09021003020901051213120509010c020424030b01 82
    0x400301703000040074a007414503605441e01c41a00c100906911890840020001e4507020290000e203a4100407148446501400780740f99910fa82c8495000030020728280c1c00a21a4074003452414092910301e801041e0391810140649000c0417a0741080d911321840d103240685642c82005141d2082840766128002c9502d4518a9244007001502d06415039040154007551622100c2c2e105512400e003581c00d040e80c4645003000c0e130820300c0d160001a0182d10000d4041040d6815070002c3c02141e100d00020000d075035403400c0804a1072102d0154034001450140f0f1014030794890b001601a608000c0780b10300d5102d56030340c00a403801e504c90b4000003c01040744410002600244906507064040c100c0601c0515142d0703000440d00184104200281a40032503800354036441041a58030b140160070012900782044144000700318104142141c074050b1048042e0341c51407050303042d100c203240107854205411503298208000381c02500c00009003003c198010810800c0b001d04560021400b43c01c0e0070100354140b82c00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 750756924 1250 750755674 750755693
    0x5123601200607050a1e0201020c150105090f091005010e0f1501080609220807050f03040b03130206091c03023c070b18011d060a0c02060c1009 63
    0x20000201d0100003080510400881d081c1d40c4505140740450340c0320780c0f9a406503401c40c141154041d811140d14146420036405500038940302214508580441c084088048183d8509000b1540c10000c2e00021818035051103200c07940003508042a2449001a03480c000100c5200740d00c2480e406d0039000910100c0060421466080a003000080b0007412404001820b5000003404c51030054583c8800070301480c069104100102080c06041c0720142c0d91820062460342100a05a400e401440c080301e0300744100108036801c5800c030382d0403141965540600d4410004040300281e800090400100d845956440c1c1c42400c119038070102c1c1031402c0c0042c10002d02d0724500307006403070f401103e03051103103000021458801c440418950b0302ca0f01b941d0585c0240340c10041182e02031041540c0100700b00c0e60703200b1005524810390000381e8541c1111001d0a002c000381c520210b4419170415001c118100c1c642d80318425514005002500b800e1610050040d45481c0c20070011b505080c00741da4440800c100003102d107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 750758174 1250 750756924 750756947
    0x309050d0e040b0a230406090e0f07140112020a0203071a0411030c060904180f050d02010f0507090e070e0a09020c0118020901062a030f021905123601 66
    0x224420300e80d50800042c40f80c200c000c501e881c04002d149100c85c25241e540d41d00003002a00080381c05000d00c40c0c0060106543d00c1480d05904160b005202010031160603180c0350100900059603044e402d04038060001d0000c0d03200041c4881140000c0007043c012136004841441c034941d070202d01d000107280c107050001c002003003400410b01c2030300452a401078998402051b00c0360303500c0481d000181890104552030008009000040150810004d05814403001041c040314210031030300240140322010ba030a400301d4004440700c401040c0c0c0d201044c84a00e1050700c1c02c83c0c0c8031000381400701003880490005036418404c2c0e41700c2c00c601ca40000311401c01003001e0080d201c0c0b44840350380141091460381c0c00034501030b0b41401194104007910702660054022405030200070006483c0e018161140c42c100106118041d080c04030141c4110ba01116030000c800c105c042001c0d8100020341a45107441e0f07001d0020b81e111161b244c80d00455030521011411403801001c400b000021300d020b551016200015000070b0040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 750759424 1250 750758174 750758179
    0xe070f140405011406090a08071e061707030e100509030c250509040c1d060a05060715021606020408070303080f010b04120201170f010821190309050d0e040b 69
    0x104184c0703076007514480240e002181c42541354510080803465071405680024141d03c200c0f0000280300c280c3c40714105084c4104800074480765100c080c162441c0c0c1010700d10064228100d000a400640300354040f0402c04003040030740e82a41d526201940075100e099a44680700d400001d52091045020041e00a0132415040d01c600c040794465181100400c9911840d030045402d50001000c2080c0409808080c00540c5485529014544105107030721804540d41401205802c50110355407803c4000e48036110750090010010502d41190071000c0d4004840c1140040c066240c0c4800250701400a00040c041a80c0141407851650070002e00d02c2c03501501700f106105500d00103200300c981d94401c03070381511015114248000e0780c920040780d01c6040c110140c654054120300f4010807040811580d4101c590500445021031000030340d0040301c510258210744400410030100070944580c2801000c0058182400110000961985810150080340e124002440c03050300ca070306031401e48202c407000c00c0107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 750760674 1250 750759424 750759431
    0x9060207150903060f1103180d170a0902040e0d02011b080c07240906020a1d0a230a031202060a020418050a0b120c21071502010e070f1404 61
    0x5058020303040400c607000250456844101d560031a030705c541c1000400308220040e040d0380c1d00d44035021040600081001c240301d0700071442ca00072094407485198444140c603028007401074690000560040402da801280c0103600c480403608881414000c100d540b141c25000854982a210801540780d0050000c4c02c081c00f400d00b040c004a10070700420399500030f0b48848a40c0e1001041c00030000b401406a0610410328244515071080240c03d80162040c1c04103600c0e4040100311081084c5440303035140a5498101040391002c01042c8403990711040184c19588840e1603680c8010003290701207400341c01c00d032400c50394020201c01e50355040149580c003583c0440304504003420b000b01103402c40011205581c5035601d4101158010350307203030f1002c00f080d81d0040c246420040102c0b82a525101600715051150805007103010100c4041101e1000a04540303014000381400c081840750701c09240c0f01c0f684219075950001185205c01000100041c0c151400b144040d0f9280c03100a500811170031032414000d070704 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 750761924 1250 750760674 750760709
    0x17060415050d2f01080604050c0f07110d0501150803091f0513151b1518050706020c210d03020a1209150b060c07090203060402160309060207 62
    0x403030800304003580d008481e414155070103810041070f05658844000078034080780204482d142d0b141e8031501c02c0300038280c03540c22072070f600e001c1040212002103c801d21865001c000780c1c44034485c40c070002c1c01b001d0320403840c100c44c051115010070080c003050f200c11203d60303650308100c20303c03129140311407001440c04a00461404005401184407010350814030309041e110090101e0506004405407210031891441c501d06c0c0ea40e481c050480d849400da603000d004600c150741c00116500610300c0c1030080c2500402410007001410307000c42d000740035100d50307070018004200c00180000c10a0008500038040e0350b0090040040460400000c1d10440d142d8070418241c415100f2030f000c0001c5511950900c660500517202c6808000a0342d04140e00e80070781030781c0c07440c16809004011800d0741c038000010403800100318581c900001e205c7e05d403103440d04000140c0e00100040000b9040c40d0011640000090070142c00d000b04580c045034040f400c10007c401050056400b881711540c1084068010241c071040c004aa50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 750763174 1250 750761924 750761951
    0x19180506030118120c170c0a060f0c1b020604050a0915060809101d0d320316170c0307030b011b030c050f070b07060e0c01050a0302071110170604 64
    0x814901340c80c418091a20100020300c07105400c0603582e900d180320500d9681407d448007940700c074001c10045a09500c0e182070861084c509100d007a0490a09845203e800c2d0311038645a1007032180704c0800c81c0c0c00071003080045090b8868007001802401802408903403510b5040030f040034034440780c020508000749001000307045c01000481d014a40d1980d0000210405c2c000c40002004480000b400241d11441c400c82c51707082d41c0f01c40d031581007080f03800d081d056004603602140080400040c00202142084c404220213200c00190240044187e04000140d07200c44c80728001c485101301e8810103051408020230007501d0301070103000c2c414142464a000d000c1c158000308110070700b400c82c015007084901c1003013004005c400c003e172480700c142403402c4030745080d50b0706490005d590058000704d482c10300300100b50448040000d004841d258050712804d05103003424508800075080801e09460154641c1c0d00c55a40340c9803c94000b1044003142d40f80a242c01c4440c0c0e4a00e110007001d407550b400b8924015940c084503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 750764424 1250 750763174 750763193
    0x212100608070e091b0f040b0405070507030305060a0608070f031803030606020606010e1e06070f140d05131a1209071a0f03010506031024030c1701030219180506030118 74
    0x42c004171021781c4030710246c4001c20000c02c040144036070064070b07020a00074981d0b000405440343e03c0c403a98083c081c2c0da441d24113006140c5c0c003500c201c1021514030004140c1039400341702102c51011142c50001520009048103015514112405402085d5075013801e000c06a41030243c90351044007800c00c41012084880410421110458034a6100d4003c9912400c1640c0310800c542e00150000380f1070300b901d0010b0070403108000211b0b24030140c6108040f907800c607090040055901c117003400100f0001040c07074030000901d10101d0b4a03070800b43c3d640401c40881002c1700c008209004400c80c1d0b000f40107207410415001202011300d405002c91600600c41100c01d10303010030449041d6902664038540301c0c2c503405448940d04643d83c0240509200d0341c1da100d000c181d8920391582c1070407035940c2d0510603100c2401060720641d294a0032084250180030041c005800c14112500d43c000071a001c240702d481e0f880b0038910440490340c107841c2c1c6e040d446005009192409020300480c0d6001c201c0d101207464815030f541030303c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 750765674 1250 750764424 750764473
    0x706060506090d080a02071205011a01110c0d02010c080d0605040513200a0e04050a020427020f15040e01030c15050414040b06160201030c0216030212100608070e09 72
    0x80d11000a41703800c0c5034400e01000d4014401c400203121800071710305d030041c00303010302c425a502c002c0c3e5400a007020301d42c4540b0702c1d0464007100720042e200072032100301481040b8100010030b0341844030308040d000000d18844001c0104038003c213000078006d801e1604100c150390010b0003650002945200c41000306000d01c0c080804906008060003c0715070030b0010070b0146a170b42c2c0c006910703000c081d0104810702601040f000e608501c02c5030100300407002c2002003200b90300c1100742c00c0c101c0d44010b0520b10060a2144124001c400001d041200145102c25412a2548103030000300410707894000401c100420301ca5907001511404140000344041854000d0140c010780c4591514580c15100284150726103074401101010040c1045a440781c481c01c6228030050b600030101d000a10309a030a103001d9101044808010079078a0049030002d103075800300002404c1016401525003e03421110741d50f00c6540c4100b20041c031802d0054101980b600d5281140710000034000045a00120098418000014800c145 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 750766924 1250 750765674 750765683
    0x80f1e060d0203010c050c010f0219030c0e0613061701060512070e03030d0203040308090d09180204080f0706091a0703120933090b040f1a0403050706060506090d 71
    0x469665480000703081181101d00a0b406518002c3c204207901c0c0e00c0001800c00d005440300070b002d58150a9140412846002d1403030421620080c80000032a121f5000130004d40038900e000c606180e07007180022160341c082d8011500840011400700509504004030046072414060310199641c90054060618441c00104d900503020240018103440c0c090204181e107200080c0481c0e84401c45c5200e0880254800d41c1d0540101c2c41711000509103280011740c03030210340301d42d950340850b041c030f002c0956800c41c0614080c440400e0f000d1101049501c1c0070407010b000607a903d40201046403424502510400081d08100070150549121054040c09007017100e42456040c54a20a80b00105100100410341164010419443c0e80013038045809154884010503500801c4034034020104d81a0104581100701c004201ca20940c0024020031900305e40301c40001d0103004d001000c400908241701010004441c101c02060000c80c0000910000e0300c181c01c06024265402890540c02c0c40020300c1c0285480d10052 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 750768174 1250 750766924 750766981
    0x30a0e0306040c03030806010504030c03050d0e03010b0112020f09150702010f110601140d140715022e02070503070b0f010603111b0c040e1509060103021c02011709060403080f 77
    0xc4423a480b0311308441c0116040b083c880307072751038030307890b0807601e5038064080b1600040d00f11017024443c0c41e061103008050724050315182814081c4420b104040d4000e04000d00307891000744090078007922001c01301603c09280d030003195a40d0690344005850203959400100400180c9072020303d03504400550a81500d52820040e01342c010840002620b803400c030034008102100204004400e00b000040040540300e10082088480d070303d94500300c0c0c0e01d0748400d01c540031482801c84800c08881c0c0300c103018081c2d034020352405417400e82507447e42c500c0c5502c8070b403049444220346c000b0000c082d07140401003805003c00d80f50900c5144210f402e80e0040703000d164685105407800390f10414001c07004201c000d14140014105008117a12001c0c11a26030700c0907039140207204042e000182107000d020826905070795000b0070321032013000100300a44c44101d103200124140100c110409030800e0b10901c045103d00a00e0004081a2030706140040c01e40c00054010032242d040b01c014041050b28a42d1340070014503a01c0d2451 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 750769424 1250 750768174 750768181
    0x504090f140a0e0a0f030c0203061b0d09051219080603030702090103142a090108030f27030106091d070819030212040e090f0d0f03020d0207060e030a0e0306040c030308 74
    0x440c204804004c00404500c0301140c00c108140d0056081c0070614021002d9888982d15807400802d500d5112600c200081001c00c4980c090440076880404510b028008981c1c0c10000c120300c500d0298000c10300100c4801c1c1c18510302041540c071100d190740c00002074010314103205450f4007154200740180001800c4210f4903001401c4180100040704040402c25040003100b4039007450340c40300743c1c009280e45014502c440b0003c80c00e800c0002c1101c40511078004041d180903c5005518546c2600407280c03621403134610314101a580d424007415000d40101c2d100010410f102402041e000c617035484024a454002400401070f803440805c03003004040d406018503651990600c0c1c12402c00b2003a40d81600014400b040104040300756401d0301d40b141d0209022a01200d1003d0b00e1103a54136002480000042c4809500e5540d05110790054400d814040b08054200101035565100760b801105003443d2551002c182d00c13405c0c0c2d41c0003030388030700c00300090740500114141364581041c513843c140006018055440080b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 750770674 1250 750769424 750769451
    0x12020d12030e0a140d0e09011a1308100e0a170d09080f0307020106050306010803070201121103090109020406060e0a090e0a050d0c05071502151009020a0504090f140a 73
    0x200c0850042d50107441941041d803400318080203070404d00d4a51442220300b00c8164900030012515189801031a60b0f015a19040b43e1101a10758070740301941c0701109105c000c4030280e0b2800701c10060a0310801a1070100000100c0c20111a00541080329991023130344000045105c140c140e1494031072104071643d0310b441400240024040c0c40d90020094940018880c0002030410065802050f00e41d00030300540c0d50b540302700741da2843c0038005d404054004224a030010341c0152208169115408008201d48110a010102c82d8008440c00007003030351141216001c41c6040c3c0301c0e00c00a000a4204400110390140c00b2907043d5003035010f0014010b40c0c0f180c007082d5004003001b4400019038008106d40000000900081614040000c21a102c2c89090404110501050040c0c54540020303030040002480c400c111081410002e498951080040d002c0800c4d02a0103000038800c14440e511036540c1c5902d030414220458610380c0c841805949021038944901550b6012940c00c440703003000c086a60707451082e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 750771924 1250 750770674 750770681
    0x1501060e09041b23060301060207090504021f020a140d02070303120b060f0d050105010507203609010e031c060509011404051806180a08040602070f12020d1203 70
    0x803c20503400640001048950b0451042160b400707038020b03070f420300003030400d0120a02007030140c0b030056003102e04288103030042940144ea2080c002007000e11841100b20700d034040c0c0d80c0d5901d20b00340181c000b0f10421f4240440d001c2103410504800004080c90360b00c0b07082c000c1d01e51486010081c100300d804100406410925001810507600013403080b070307a0302501c00d1035505a510a00050003114100800040e00d9030080b020340b02c0d000d800c81030107640e1038216140c20725602014411150300003000c0000750301c034109103443d02c880c4408414034030704010700100700064020702c010000e901d80c0e814280100b00810001c019512543c01c103000707241650300f80415002c00b504941c1c000d19041f4111034000034400400d0f4003041c0038100300f5202000f841d01e40c80240d0054040351441d9010580c00300303002c900134a030700c000c0c00340e10400c07a8401d640c503100181c1d403000f40320392090340a180164031010060200140089400d001450b004564440c201910380c0854440c91100c4006494001c02140c03004210340070740c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 750773174 1250 750771924 750771953
    0x11d0604150e1c0b01030204090510060303050a020f060c040e10080d0c060c0507031707090503010219020d11210c01292d010c0f0f051501060e0904 65
    0x99410640c003441d84401000304031000340543c4500708005014004038614404a0704031a0843c05180d002e0f0709680a000180c400d4407070846075403103a41c449403c118094466800a5440380e5070301541c2d52000d20009141c00b401900940305a0045000d01181500b490101c5044410400c2c220b10140d80e140c00c0702c2c46198455010002c0b41c080d030b4403602c4069511500c4050164071a178800c003d0030345408000c481501441c24002c002c11101200070090f065031420560f800809403408241070f035103c03804242aa00500b103002032494030800c0d4850320035010700c000d00750f80250340b41508036800d6251901c2d03074401150b00120b0341d5804012030840c2045180382198150307101302c0c00a04c8858510300411920234500c00d074524140040c00e01d054254505000300b035110503141502201c4c64510304248414000820401078180310465980400051a2140d048422401010718161040907420007a080078041440381c00d0641090006014040e003000402104030000d07904451180d03940d1400300b0b900346000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 750774424 1250 750773174 750773189
    0x90f0d140f060f07080621070801021209010605040e060a0c0915020d0e241c0e07030302010e0c0105160c230a1e06050703030b09010e180705011d0604 66
    0x1007000c041d5040001102c5000f2401000c0c0c12249544054044456801c00c0d180391f0791003c0301819012902c402e07040d605c00d2107a420010b40c3d0384590745045007822640007985851260300701a040010b094428460880104810b45081c002e401841503800d444502c01482085a80c0c3d6610b00d030710700786200b20040b10150903070a520000340c101000307000c1d54540711a2030b600009000c500100f0050f060541403421000014a29080346201100303144040360032240d604403046014040e07656507600039020f06c3d40a02c8a0300050807110307065060080c25510b0400d6000c0c401e41c04030840c0c1a40d41d07030000403101420329001c041d82c1c2c0101c051a01d0413440702147e00c60016006810344010010365819110007031104100c41280c071641d41ea140d0050301e042c0d1440780c846070760070a900c1000901d02030300c000c043c168424940050070000040c009030400e01c00785c100f040441408070800c0424a0440e5450554900a000a1000034035000008000040206102079094420f030300d0b080b0140c44030800e480241104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 750775674 1250 750774424 750774433
    0x60714070605010e041511160305091905030607090b040b09030a0b16230a0305100f030602030f0705070507060e2d090f04150c1103070f02090a02090f0d14 68
    0x43e4800c0414018082c5d9082d2035a20310080283c50f082135a1040e0103015940b1007980b82802c110010b0940540c000d94801d40c10300508110000041c2d988a240e180c0440e0b04175480b50801d4208424036181000c020701d030900b8041d04107018414282c420098500721003150008945da01d4517400428100807500740001c142c404414140602d82c054070221403c80d0229030380744040603104040c031401a288010032415076003400c020108455129422250748080d441c0481e4002603a2541994601038017a802a1246a07001c0705000c880940700c13012540201c00c620b040e5003450b0490321010f40724011032103a0300600000840848003502d8080040d1055058810034480c86407954149458903907540b21150300c11240000051312503010f4143c41030180340c001012520000350004480300030321801d44a1414030070091201c2100100030001411054030510154500911520511030b820b10003078244000c440c010700c000d00068507422502038000701c04440400301444103040c8504e2410300000041242e019 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 750776924 1250 750775674 750775679
    0x60f010e4609060b030307020d020d02040e0d02060702100e0c1009050a0915091509090813080c01111902010305040204090b1003030f050a1407060f020a0e0117010806071407060501 79
    0x2403030380c04610b400340108814002c0130200b100b09512482902c80c001d502002c0b160b81000507091440468041620107800000d0000808840503c4c11009603460801640710300204076090b5414010324884007080d2501344016000044865150103064514a01508085200404240c80384154200400002c0c10f20000c0c107440d5800720000c0d0816941040c001d09680304005036140c3e25111300600b030b44550f001d9807082424121580003130440d40c2c5003a00c1c188010302210b103c2c001011059001410520010310041d10f006d4000751221044140e070051503001245490510b144062001f04007560900c0d000803540ea5502c001401007206440c0544004c040804014103114103d8901c4240c1e030284d01d4184504074000b2085500c0e1040c0303007442c0c00180c0c00d8a5400945030100b000b5086d9140314240c0880c40300e4005030030f44201c1c1c0210400c1d600090043d2136104465030496600500301c00f1604034136580358140a1843c0e0b499030043d140e40e0810010310b00c41e0614180c0d40301680c4c841e0b94030080510076075a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 750778174 1250 750776924 750777061
    0x1e01051f031103330604030b040311030307030b03061602030406110109051507180b0403061802030a05160e040b28020a0801050f09070804240e060f010e 67
    0x121355004401c00b04150388840c401310104140c422504000500d41441d1605541d50036100000c0a8412414407007881002740030b6160a00c080c61091129039000a40e00d00380504052610390060100c08214032040803041c0c50940c040700b12002c1e07410900701302c050024100c910f180100b20010001c0d203079004010514000354855030038203005844540da480800802021203c20303c6804d4420028883c030208010000200c00d50003002c180b40300340d407601c1344d41162900420b0400c1c90102044407560404441c04a101300c080f24160064105282d0600492170550340343c0d201044094107080424404540b050080d070032600e2019003888549105545401030248040c107101d500f8050180310701e101e501386403420700b081c0d20b1407441b50f4020b51702c007005501e480e2101380c1082d42e82e20820068135890414a06208000d0040c0084400c04070300400003440c040b000b1f2060454182c01400c0d400d064601403101d81a01550a0b201d1501c0c0e0382280c54505c0000c40c2a150388466031020b00d4540c035038044131907a110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 750779424 1250 750778174 750778201
    0x120c010f23040e060a120308060d1a01061d0616050c12010c0207050103020a05180a05040903050d11071a091608010506030111090a06080a060b0f031e01051f031103 72
    0x1903a0780702d00f00b88582c0340d000030001c44015a000c0c490100308501d0115001c284282c4049421000c00703864400000100d449260900d40c00b035201021542c090740041001640c845c1403001c5520300b01d801c03003441c09001e0340020090700c1604000140c9007908048103041c08001c2c8001440c900004059507101604c501c10340e4043c165021400c000b60040420004655020380220b65070700c0c51541c3d0346440e0000740036941c02141d00148810f5004010301101203442d844510540a805000c0d48801c0c2d11520010249400c3c7c42c4043e031000700000c0103012240014080300e5152001c450075072402000b81e034a0001a42c41c1007403c1c00c46072441d06089200084091040d0b001a02481c130a4009004400c4440c161960510075003c80c01d801c082c0030401009081e1251881c65045008018045400c0f50764042444868200d03800c07907442804000b082c01a500300c42c030756a20409500108180d40c1d50300d00000581d0086240c40c0384c402c85c68404c2c0c07507610058480c0c0e014100100882906980b242420320884003034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 750780674 1250 750779424 750779429
    0x80d140f1209070f06050a1e02070b041815050307050d050a020d0f0213050c09040908090a0602031308060f0f091903021006081b0d0305070609030309020906120c010f2304 75
    0x1d2042920010510a215800321800020203803141c1d0f206402d600c4008852340d000f00c00a10441c05901e5001c102035180c40010700c001c00d0328065809003449441002c0c0111010203003002e403481e502d600e041046490100f282030171104200d5490716800c095051050506141d540025480a1035003400c10412103074250802c20180240c0d50581816001c03100841214010345181000707007018085200f80c1d1070190844408940710741d10300c170b042101b03080c00301c1c040322070030b0704070b880545c0000c1021a404080814000001c0441070020300761030401e420901000c4002502c038441d0000742800084e4200400c004402024110100c86100c003001400d0003520342a02c1d1103440b0205003000c100280031a40040c1414440882c260014014183c050420618607180e920460034490140130002c0440e0f014031440c00780741e0094402148101c40303841041a00c0c5c130002d0000344140d114103050003000d07200142107a01c006081c24416030038140748c502500c038040d20f852407800307860340c0691244170b80c06540c01902c00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 750781924 1250 750780674 750780689
    0x90c0303080112020d1121030309010c1704021003020702030d021f0c02061306380409082217010f150b0a050f12160801080d140f120907 60
    0x14aa40c0718201220f05241c0100c010358803000480c000d20220f00320451200d035014008010010310600343c0100c032000ca6070544440d03460b40010080004100c020300400a102c42545441da500100c3c00350340600d5200c002c2c00281c02400115a00008140294110b52070f46400034100e540c40036002d48000e543d03c603080b46034500070008041020400c441b5014440c2144496000303480c0720303540c1d440b403ea01d40140980a0b120f42e516044503910b080c1c1301041c8192078036004080e07081d568035407904011424803510303160344c0a03509e4031050b2000304003908190340f80c03900414040c81044d6180e005033107443c00c85400c418a06800005c0451041005600000318261001c4d0b09220b01c0810f80c0b160b201c412098800c02c001d0090800104441a00c40c10042c141798800d1441103043c203d003808803002400003120120a000b40100f14104055002000380f40180043c8004002758525020000c160240d1002940d02c0042e000c1817510004072004183d4160f41c2c45d0b843c240f4810714100e4100b40d03490409104a04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 750783174 1250 750781924 750781937
    0x5041a04060f08031b010209120a03020616140a020109050601061706060915031321030e21072120070b12150909030319150e090709090c0303 62
    0x28000494a282e18219800400a1828040d4200c1d070600d2124002c0100600c40d54200326450301555110001080c1105c502e0050a0240203481c002c0e140000c0a0130b0450150b0800d000305800c5c0e07901841c020400414005610b481e0b5164406c11fa000d4000b2000060a5020b24400132410503030250980c0036451083c0040611503c400c03090000070b1043d0380d00300341c00c000098a15000f1341d202d4001103420001005a4501c0c40215440340150140030300c1c410054000e00c0c1403880d80d6640e1501510340990301030320142070741180f480d5100c00802d585402a03404554081406001e000d00e41700708031f41c0c40c81a107100ca00c1c1041104402004404a00310207100c2803c605080f0105203000a20710050300c13502d100081c03400707603400c440302c5108400801d00c00c031a410010b182c044a8a50801d00760040041000460300e03130802c105403010800c3c40640c4030681c41e19001100d03065194119011046619140900380340ea1581c10b10f15003000000d42201c50350600303040c3c248040065844940048900940d41c0c42c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 750784424 1250 750783174 750783179
    0x3053a020702061e070f06020a1229011725020609030301090b040b060c0a02090112022d0613150e010c150b0d050c2103120603010605041a0406 63
    0x800890150307440c060b421003000e1000104800103040d04880b99030880c240b542c05c0244941c0c0c0d00810a286a00440d03000d9008140c4800890300404403940d9400c01110610400ca00b204440f0070240e03580b0202c0c461341084d01c00b80c0c2d4090b40a0500080b42000106111030340e4503190003201040c0803980711002040112040c03500e140b6101007101801640c1600146207141d03e0301d00c0c0c1c100035056642005030302c00d55903200504140d4a68000304040710241c00a0320b48401c1d54010400e44001c1640910346009006158030016503a904240b030186402604d0105230181240c0350046e014000d000003504564001105207076a8a02c21039003003241e540600900b50440625803c51b0141f0400c00d070741d0302040305c10268500103640c00e052100820b03a40c03100010800701d1000050980c44511109039541d0f0418205d095160901c0081141442c3c400c601660360340704001141681c80c481c07400041c09241e16030b000b15030241c7d800e420810041800030024031540010803c502100ca03d103014041c0710381d28100b0300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 750785674 1250 750784424 750784537
    0x4170721050703081503031605010c080a0b0a030b0405070f0f03062f09030c030727020306060a110115170c0301050403050f090402160f200a09090305 66
    0xc40b11200ea00d80c2e00c4200e01d403107800c445140194600909680b5010900c000003208034440000c0d00c1c8180124004550313219040006000b00c000076001030710140c2400203920407031b1101000101280c0d4404000c6c0b15039900c5040131800c0a29540080808140241000440031042041d5405803402820b08200f62540c884c15a40c0c1c07980d0b04001c9220280b030300d4040381c100040b88005015020300c050309540e004000078000900341803194221142c1a00118400d1410344030540f0014007441c44181c0441c5035061803030001d806409880e980004100414000300030408007908a81410300c00c0d003030305240c8580c640b040450a90560b0f44040182d00c145141d00f02189814050741d40600c0d01501ea007441c244000703140303101c182e11008003941c00c00d070204540480003203140100003100b0b00030502ba000b41916841c0c242840720701c08611080700101e184140703d1503501c840314901200d201c042c000800c0b004a1600341e8545c09801c580c24a184030701072207041201c0881001c0c524070f00b0309041e0410380400381c4d1700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 750786924 1250 750785674 750785677
    0xb040512131206020d140901060512070302060915070303050609160c02060307021509030d05131509060b0607110a150512151f02060c071a0417072105 66
    0x9400307503070044281088240005052400c150307002d071002504d4036443c0244182514030303010250001c0584901000110f010a1243e080a000d00311140e8401e000501149643d85080d408003070b11030140000c804040c0d07a034001d01014212807114003103441d0030060a0207002840201c0700c490084a080001a19540305584401010760b600d44490544042c0d039000c0c0160b45c0c0004203403200794420413400714503003507034400d0f618400c0c00e180e401580e95001400d0088259003018281c3c18408241c0141c020024840b80080024a0030190001401c171200381000c5020300b041007184c80d0411000100c0314144602c10610841c2d100382a04c0350b40e951941c88070300c65044484882850001582480b0781800600c0c0048125007104000401400203074403c0300144131350842204120b000c07003484540c0041190140662580310840401c014100560b50311109407400200804003100104900002c040250801595294100c548585500c0700858644654a00400c00e0b00004040e00c682c180007a080c407840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 750788174 1250 750786924 750786937
    0x60605090f190204120f291305010b090c131410110a1403040906060f0903020d030c29010839030d0e01120b0105220e040b040512 57
    0x1d160101c02e564203515450100e0005005a014035020000015514002030340c8041190203488041b441c1034862810040700041d080348031204401a0343c0039002c46506860342580424002000a18030726503107840c42c01422110903841e48418083c0501103891460380c00380404200f03a1086045140e2156014003c0c01c602c465010341c0982d1402c000c403021440303000d440c03030086144000c41d03424030000c1c2d6900540001c09ea034410210760022134100b0035400310340200001000203041821040044120041064860740006402401d040f61808105403041c048c1c40b10b2150442c2c6a40c0c0000003541008203443c01e4500400706184a24002040308280030ad40f2120514080c1446281003030501d015907200c250804001c06c03003120790702d00c580e820740b4244501141d60300e041d5110304042040e0300c0050040708200d4115000c9619194000c0101d981110880d040f691081403117141041c4118400742003d2469040348004281c414244410802e60105141c01248140251090215100e034010041d00400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 750789424 1250 750788174 750788191
    0x417011b03090503091017010f060207060f120504110a052e11100203270607031107050304080d141201030b060f031c0e121b0612090a06060509 63
    0x100080d441502a41c003120a261259084d01d0404500400045600c071003850b960300440d94820404201c582e000154a0150404088640a00f410704000a6440100d405402d060018220783c2103440c9001d001e0192070510100c0042c03150346010718100c00841005180360f80180034000e80410349140015110003002c3c40c40c140211000310540e110750403004a8442c0340180104c402c40c03507004920a0001280ca48550b000c0581c0e281443e8907101404905910110f001c40d05840c1c1e0b02c52400b1021802036000040e43c507001c21032800e08800b44600d4420800c0c0140749206c005000a80c066010039000701c550340580307800000e0540ca08811340244111031001e4000420400140001000c0310501c9030481405001c044010000c003021926128254611000110001c122040040d6012690b0021100c3c182d0b041d040e030125000c50036584103140b40b40000e1445080030b45801d0741c2c552100795100054010300012150420b42c8401da2903074000041502c11500b09000481d00381460710f0201c0c01081071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 750790674 1250 750789424 750789461
    0x106050d060c0507020a06090315020702010509040c270905090c0a090504060209120c040605030c01020a0303052203082d040602072303090118080a0f03050706060b041701 75
    0x56540c0001000d802c0ca9101c140003042c4010740c0541c40d140c0361a0301604107a00c0d204003550940c2800d0400522541141c2c1c001c900401450300140d0b4020b081d0354080382c056074003080c65001c00c3d1060780c0102041e030300481901080c42118070f101d05242d0054048422101003000284c540d101080d454851200070355400104c60b2004100c0d803411070344a190f2207401641e0060400c0903140004c0c1008218070161180d40d480013818500c02d01d4148180c10040c8001c40c010181c82c8411700000c2d4031400d01c0d602c05400d150341c0d00005141d40e485a28a01c8000603440c82c20810b002ca070f4500030b0300303c2009440c0722100075058031141c80d200340307101d900f0003003c074040c4164480340d511591250040d62020382d040315108400ca51a003e080244821a41081d00c0c0c00c0c091030b240e14501c400181100302070100b4000740e8410440030014818046000903020390005a0220305401d241420348a611a054000b4085c5151442c001091034180c40900141d44410760384203160140002c1c0107090301c501640c00080c0004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 750791924 1250 750790674 750790699
    0x5013b0d080c0714031b150f0105100c020d030f1403090604080d0e070b03010519031101030c0c08041e05040507080609100302040203040507030318030515131b17010605 74
    0x68141c042c00e0b80380d2003a03012544d00034020407410700b1504941180c004401c1174554990034120248144030807000e0b207050380d2001d0b103407010311410901d1040c414280180d020036100d175020740c82080c041c81e480d500542215100c1c04589030003414000300c00003980008900f051080700890398002100c2c0540ea2160050004d074a0b039407219440d561106101308020b9544401810340007105000c2140289000309000b9181c0d0715100c14000201d01007003032050003250f00c203824000203145694501d1100d40a00e800944040181c8098410940000001d044540c001c540003ca0040c20440d400e80c192035070000701005075a4409010549009486040201d611180000c1203802e000107510390050385100002d02c451340c1c03a0040b40c1268002d07503096500b40c101c580d043c428560411001050865141122459289184c0780c280d11020303284403090b10908003501003459020000400c0724196004a8500d146244050300d407071710f01006104800c90101d102c000190400810f10070b580803a040988211403541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 750793174 1250 750791924 750791941
    0x1a12031908070c020d03081503030403031b231c0509130c2106170f0a060f0b060f07120306080705060d0204152706170405013b0d08 58
    0x108000c1c0b140341002101c4034050301580c0c800811000710b034042e4540c0141c3e401d095804210302c00909a15a01940c4200010000a0b50154209644003448050640c160415241030510780064582080c801c100390520490001804120001003054918180c8110803010f0402c0c0c66500810300b441b58400d8038842861100300319500400100d0350b030351900080180801030000d03048082d50001d0710881e0340e18001840000076076565001e141e803c03140106026442d0010003640d4001d4540001d20241c0ca919029035814117503003110514180083c9055141c5042400d03100d40c0740c0205e1020b503400410b00d56521070b0b0f18041e2140d4025174200b00050203d0a08103002d04ca4103a02c21a0f000d48035560030040080c4a2a40c14580355404d1415030718040b04c00c4074843c02e00007001c03044821002d0409080001c015440d08000241c0080150080790701b016699401c04074010300c500c041aa2072481c3c4003980310300d4024160400c4070403a8403038903850924481c0040740e40d40c82c211680f020300400c0300c0c40d0100d24100e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 750794424 1250 750793174 750793187
    0x604120809160909051002030702010e0115080703080a140403060f0f2009030c090a050f0f010807060f0201180c05040608030405030a02091801090809010306080102160204020c010905011a120319 85
    0x11360203101160f010203050400780c17080364400c07204500146d40d945208100c15500b0b00600309600c42c2e03203048515950a04146a4a6201600c0014000c40d03000440e06146806401e030701212100c1c5040040e1213581c1ea0510320080c00c0421441c400d02450012018001c95075449a0789290800c10110110034140460301a0982d2040307002c95454494400c1c514a16030b128000d07148156110200485d150030030310051003494001900c00c1a80c41500e400610100200181c0754040701e02c14580b580180b001450280c0c010300390850300d0545102c1d40e914000502c55294881c031704503201950204543e42d50380404035228021303401102c1c0c0c50b030402d400100162a081640071380218400c6461a00c0b441c5100d182d0b0f003140c468030b10840d001600070a074031442e0342e050301c624170060041038029803410740e04a001e140d44c5040c80600912565000c10b0300200a1402d500134407403182d00000812840c41d03c08820404000c8028540c1c0c40345807040e80741d0101079030220070750340c00c124010303c4090035084484064442 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 750795674 1250 750794424 750794441
    0xf030a1815020421052e02040909060506010512061903150626030306090c19020a03120911010f05041d01030204180c0b0f12131b060906030f02040806041208091609 72
    0x182501003803485c503111b166200500c01041c0f441d2300080e105540e0325000064480081289061150610100d50b446a503d11010b0303201404403050f44616601419907d00180c0580020300b000c8080541c0c1000c01d030050b400304082e80c00d48110b185045a48000920050410050788985c50304140081012424903071201500451000c7c10780c0d05102e800c2c1c0560007020020403103007005a001d507240310705058001c01d001c4420000c0c441d080c0801720494403040c5030001114191030403c01d0700f990a240540c81b80003568082c0c02d110396988001042c44002c1c01e5041000c1c04282c0c811071420800c240d400f90006650801294070002e60b140b140c0c0b034440d80d02190341051985801c0c002c820020703044948584009c250ac035500340441c0c0d1200c0d0b425400c0071a280e40f14400200380c00406201c052003003d130855845003c50341b2900d80840d140c6514400d40b0080e0080e0f50160b4018800c020030301c801c1014202c07280200b0043e640d5950402c0d40c0303848106a41c0d81300c14070200540036100005000d1004180c102491 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 750796924 1250 750795674 750795733
    0x51e0406150512010605071e020d0506090703021203070c1205010906021c0f0902030606040b03010f0504032706090603020d09170408120f030a181502042105 69
    0x50640c1d545106511100034925508002803000031000c1d0356160320b085542c0904124900030b07040106c80d568044a1901c0d00412107000c001d140404d0046680c1da010910714558420242e030103900302100a65561001804101d10600342101c0c01c1c1d0084e8000026100340d03a800264440c00149050015102e048907404241d07039654844100b00c0100b000390004100858021816643d8100814000c0c41103820966419447d40d08001c0075901581e800a0b10f260021170446001038045e28810001780100558103035241c00030704250401c4107250b00000076210319103060ba000200501e1404d440030680400f1300402d0045507800c2c006007c640c2c030950181070f000c0c2303003150001006030f040d4413100c0d244007041d201c148183c00c1c00201405018018001d000700c071211208180d00300240c405d00b071251400b00501c03004180f40c2d10b0440c014108407003000c030402c003904014904010340c1d002020074013079403160240004031481c0380030011a00da110f0706480c5030b10fa04000540b00c03c0012034520441488044003c06 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 750798174 1250 750796924 750796931
    0x5010c020d06020c0d090501031406040c110604051b19031509050303160e0303070b01031e1a0f060d050c150c0106170706020303010e0a0506060f07030203090102060c04051e04 77
    0x400151540c0f000300310100d030b410000d002400101c0401407158150303030001410103040862800428958410311900031100301c078081901e000008044401c0d0074805008081c0b0301c13941e018441440790201d00c51041070f03580300000315224100410b0160841500c002e00c007142c0f000719402c1001c541c070705010b0f1440f4403070114049600f1010741c80711440c40d00103440382100c003c111462084519044215a69441c02c19800f6500701009901c90f0803070202c05100203446140e040a01d0004150900d2420144641c085150044050b00c2101c2204000e030072204011221101008a01342d4508288001001e81d841402441d038003420209210b00c0d1460002c0c89014a68140958242040e00f03000710006801d9403007840402c102800c3c442460408143d004a0954004000502500e8050381007540d0242d01d501011420392a5440850860310a540450511190104040c0e08042d400310040800c00c000364215026506c45200c20202d603c6036128880d40030041c0b00b2041c82c03e2501d0000000c000ac401070002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 750799424 1250 750798174 750798199
    0x6020304051c0809060f0c04170a170d0b0f09060d0201030f06141306060206011a090319020301470604092901051821010218010c0c05010c02 62
    0x4100615402c2e0310310300854480801c00c407094500b04100780d481503903444c100d0385905241056401034400c83c02100340c042d1500701400c000a070100300d403018a0340c5c8000da030520302d04a4651964a90400d05024000509002d03040c0e02c0c5282500001c4080803000b0505041a281c1104004900c11031a008a060680342d1607190b10940e0f803071260000401d034a0f140f0198400f03e403c204010703201c06000c68207080b403902c40140117040c0c0c00030341035055400b5559540a42407044d0b842c5020780c01100b141c0c079410b201d001510480c2001c180c1c05800070904c00c0e00288240c062149024491004280481058526000407648402001086812f0008050102c07000402102004c1111a0701942156400356280c404101d0454000b1540300380290301811901d00314414800000c0580c0701e020708090a000d03241440300c200b503650316113100c15909012040c0080c01441d0745414041e40081c2c9803c4c001340821105100c46501603000d0b07100c2681d10105180900d170070040107680e0114420b0050f0382240c0303d0310b030380c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 750800674 1250 750799424 750799453
    0x1303031401030c05031203010e04030806030307060e0d09050442080c0f09040b06010503040c05060a02070509060f092a0d020705061501080f09010f0c0e090703180602030405 76
    0xc0d14069400b070380314443c03541d06000c1490318150501c840701c41120010001003040901c1c2075a02c5810550624200ca0b80340c4541001070324500458030083c20f51407900440a40445000078400b80b0b80e034a6460f8255401d590f202040f0440b003007a007400b00300500c00300401110002101c9280c203816424110b0035002034030b011607582164940c2d0402182ca40c40244032090078903005001c4800e54204980c1d60005140a50303462605210141c005414010044045400c00c03a10b00f04000203814040c1c1019200c0e071114500942e036060034400c032400f5204010111350035041c850144c010268002d050840a03454080488101c1b070102044200351241910450b40381242c8503000b001c28910f5103a026840b4806420121304045000c0c04418071000c10040e42200780e40c2154103541d0040b1411941c0c900c50303503401c8000e80076009c1200c0b088422840c0a007483c00280d004150301070041d03400d881c6201c40d070f55a6142942221f00c4d4038901d41000c1750242150000408a40065a01c248a40c058134180c41c043c914 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 750801924 1250 750800674 750800711
    0xf22090e0304030b0f0405100c0302041203020a0b0912070807320f0606010c0b0403020f060a1a04150b13090f0e06160f0c1110020d0206150306130303 66
    0x300802a00002420010300c04411031054003c5152100240542010f690390f9666a540c2000700c29080e894a248220386406a4150340080c541504210180c920f180f4000752581062001202c40301000004204510000500c0c182e17400e0072050b08918000d51926101c026410241084404940201150505206849513902c81d05a0b6198500c001801e40443e142400d200541444c1ca40d8001c0701000901ea0b0b205005424040d04160500801d8495040032030805c1d40d150641240c038070407601441000c02995100c0900001c03c1044900c3e280b9020302088280c42c03050070030710080790082a084c411000810010400740200418040260f0364a107800c40954080e003440d6510507549001c840e032000e50600c242603100a44540c2d80e20a031030410000361041482544110801c078118640e00204102d2190002c00c242d0000c11003541c44440c036500a588040402c0c40f036005005020104140600c0700b000300a10402c01005050256141c0f0114592450201015400c250f1210841c140f0740e6003d01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 750803174 1250 750801924 750801941
    0x17090a0c061b1406010f060807020309060304080d0608060a14010e072109061406030102070f380a110309071806050607030801080c0a03020d02040216150b0a0504020f2209 75
    0x3c0140c403181d85050300d20900140e50342c1c030001c10700606004100d002c55010040307a595a03000c80d03400c1e44a48803400c02e5202c2d0300600441d800311307500d02040403904000010350799120b41d0701080d041c1318a5844442d8100000307000e1145040002d81d0700b0100381e049000c1c44200c4101ea002c4000503510845403080c00d001d0302c4190b042502c82594035803207011641c4580910f160300083c00c0d00250700d00041540d4080c01c1c24032001340540305a00c08504070290103000d15466030b410010088a03000c2071100b0004c41403e21040e9440d600c2c1904c0c00c01003a101da507030343d002e80c3c1c03044d01078101814501d850130701c04201464109040e89481943c420303001c01c095035450058500c20380203644500031507040c04507641c9841070501243d840341c40341813001c00c01030b81c2d60340080340203560507107015032901e1285969140d8800d8128000788060744a107180540000f840d840392514034411100121165507450a00080348944000803030100000c01000e81d411540c2141e605039110072035410840036507903510800c00c072030a04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 750804424 1250 750803174 750803213
    0x111070308030a05102106020c120918070f03050402030a0c03080712020f070504020c15130506060d12032414040501090e06040b0a090c030317090a0c061b 68
    0x2c41032100e00c100c10322075250b0041c000600304c003009082240501e00f441d07540079500645036030180104204101034040d00c2c0018282c004480c5a040072342c1c920b2000b03412180340360340100c0c88240b154407a1a04105440c1c0203c42c240c41301030180c82072510890103000010b00698161050b0506d4500050900c0e000760021406007034034a4540d601494075901d1444091040411944a407107003a0100358042040d1040390f00032200160360703007900c680f05070a00c44c00240d06100b6029031410070810669000b071035070225102e017043e44d00907a0f40f0720800c083c482150b400a800d50541d42d4101c140e01b4080d60040440542010003907120501508803280134000b6500900310a0824061740406800d0500403d0f0141000450500042c40760140703e40d51aa8000e201900b03100351000850700d200c203d684840e0819800100b0399007541d8607030401409450070342c00c11030360680c1c0c5000010350065022545030311a035030100612480c1850300e8401c07181c003c014441c1c5101841c011480900084030740c0945a207082c41d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 750805674 1250 750804424 750804427
    0x5030721030b010c020102030f07111201140106021504060504020d0b070306060f05030f0411010c08180112050f010b090f09150111030c03040b07030504090c12061e03020f0111070308 80
    0x980d040141940d20120255040c04044e124010050f038020080c2e507a403d50314480561240300c0da0401181000040e2a9181c004440c1841e0810074981034004203642c41c83d6911010702640d90700340c200d03915980780b00004900002c138400700c1d001500741d070041b030f4110340001c02d408022003282d21101c0ca40142501e03c140400d81ea820301300420340d004402801e0180003030800905615007080c0c21001620010402042c0c108203043c2044680e024203041100680c000320a07503251992414214490381c001e540d55030108a01c0c5051a181504a001c1c8a105100c540c4d040c3e5902d91a0001c900c41e1904207007200c580c01800d484840030b254030750f68001c0348102030580d40c200000c41c070f120025115003000c00202c01240c008104800201c0c3d0008110380440b5003d02c00c8030380d60706060074110b4650003940c1008035440c0c01d040724444090361010034082008074056081040584c0e0300c040141c141440703c0501c1c0501b0300e1403c10005854601001e00b4481418181411a0190396100c10700307181c1190800c8070503a20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 750806924 1250 750805674 750805733
    0x61c05060f0a0b19021203070203030a06050a0302061b03161104140f0414071710150f03020f0604050a0308220509060d050a060507020703031202040e060d050307 71
    0xa121902014025041c0c40d0510078905121030003406106201380e0030b880d4141c241ca502103142c802c21002c110303a80840036031a01d030308004500035201d600036039462207100c2c03d203600420185010750249003100c0d401058240ba00306d400410642c64099203000c0b0034580800e001c0e240f620f008005035642ca0a00c0340c0d61581d1400000000c0100300d60900c00000150701c1c081c000c1044040c2e02c403820a802a4210045003c074bc4411150f02d450420550401d80c1c0c0310281c1031544003503070000251240710044050080c405c44070540c000c404e02c0c2e41d50f03126403001081094420009400d144100071a0300d0409480a4901a2542d0214049501641c0201c81c58840010007511000460305a4884500c80f26150908249032000092411001a007924030499202e2a0001005003c10980019980c401d030144207a00c1c281801035100d60043c8000c1d00460204501e4004e548994422034096402c5d0217080e9149490360000d220382441007078000c40f098407003040180042101804440110181024280f18409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 750808174 1250 750806924 750806929
    0x91f2d02120a050408040e0406060b0708070b0f0610030e161e0902040e01030303050c091221030906070c051e0a060b0303090306010b03090109060e030409050115080402040b061c0506 80
    0x21001030400b10198600014400003030200c800f140e044a4a14800c0c0016840d05c0c2042e400804c500d40c48031b04000000601102080b81d20400740400d64010000040c4907560410a40b21000d0212a81580481031881d1649894000d0748004150182d4a00701c42039044000c1d8010380c49440c1c0d0300042800482001c42c2800c2c030b101260400c2c081c4c0340c1d0141c2075050515080c1040609603041c0130080c1070503102d80c001103001c0e52490a4800c410b40090020300c025447c0d00c400764541c081e061101c10703000c135030141c0701d1542c102c814200c0c0d000743d00400c024940c55440010840780107074406412074050007508c41002c4c140145442203080b880c46c0034043c4c4180c1c5070a00e0704404031030925504e64041d4005216585051340d020030804d0460f40300038159540d90fa200030b502c0f0b00400f913021000b401245804c030f4600b409030000000e081540c005800400083e40c07602d961b4640c2c95506860000017404407800180141803540015000c403501510080c02e102e00740040c150a1a1400c1c1401c024507600c0c0100080381c07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 750809424 1250 750808174 750808207
    0x50a060506071a070c0f060b040b060310060809010e0a12090315050709050406080d0311040b12041a133309020102160503070605090a121208091f2d02 66
    0x10124241a002170f421503130340059050144401034101c0b90303149450810750b00e075a04200d0a69100808407079036841c0c80385041e2801c540074003e00f400501d021000407882c100501c01c0e2244014940010503191010b59502c0f138900c03900c0c1c2c02c420104080c1480c004000f80091190311083e122118010409150010f00100441303960b40c0450301c920300744001003083d940d021481d403000301c1513844c0100d41140841d010044503c504d500040b1146000202c5140c424224040a4042d500ca403210f00d10000b00354581c44003a103020b03180082103030480b01451002400d858900d12003503c40720405060310030141c072940100b240c5001e0540c41c0d20703181c181c1c040443d0f0781406446440001c00049851003170918000ca55600300a0080e1020b020002807182c100d0340d5806c0b006030007000c910304016080c0c001c914024030f40000c4444020003280c1c1d4030022404a100128160a03071034801e0b108800303001450170b4454050158421403400014401c02111407810340400400504a007900b00035a5074464000e560028 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 750810674 1250 750809424 750809431
    0x111203030a0b030a030504060305091f140f0903040b0d09051005040b060109150e0a0902130f09181e050d02030a0917060a110409090f15050f0604050a060506071a 71
    0x25001031340010006500076065800b660083d1500090780d9403010212460b000340710200303a41c6413280300100141580203401038041101da1480c1081e06440364098148100e005803000c04160700140014814071041c07030081e1002d00031401000c100000951516405c0401d441004608140c50b10100424006018450f40d0007420a1802070103c0d40f41064400801c15140c4440c030800c1110b005286040d0f4031100b586026291000b41103589110800c040d4459150504c43c1c062204070748040000ca400380b52040000402400c608064400425541d008a100e40b040c05080031380505200200403400030003010f2110300c250340080d41e0310700041d83c02900222646d0b010740c00405001c02540d00d48100800d603560000301150000c5104818a0205901400b03a600f05824683c50036114009108818107c512081c0c00398003101d1603d403500c0440802d89504880c100342c0d04148002180d51814180e00080e0b00c02ca43e060001042034440d00000e259903c100010744a1414080d19143c20700c802c10101c0780c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 750811924 1250 750810674 750810679
    0x31b060b120d080414070504050a0b0a21020907050d020304030306230a0314150a090312230621010902040c1b03050a090f030f11031207020d111203030a0b 68
    0x840b80e011140040980c0c400410092881001c0c2410344030800d02008043d01412005005012918100d20750390020004d00d581b23240304101a410008c0e0443c90040c0c068440b03802034040304a01c0841d0b409005113008054480010401f08110310700002d074a502c081d43c0128446c1d5808148646400c0082404045181000f51452041d5820301ca00340d4030b5840750800c80340d101c407605079081c10040705141005444c4080c0d0110b0480b9604120344950164064080c051080e110810603043c90100e84007100d03c00c0c1e424440007440102d10455110045101c40d13070100c00107000340070031030b22181400f0b0245945601040c0d169104c1d00d4860071440c0c50b000310201402c81d4503044101503525081d40200280e0400060f0a0010000d116203c0c03d21075401b900181840000b412080c03a0389203001050400500d60550700034107810000310b10341c80c000ca10202412180c0700c02c1c5040c10143c4d002c1200201040008803000e40002c2c480081075240d05001030459941500038503180c2ca80f080000090300d0350005141c1c23 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 750813174 1250 750811924 750811933
    0x6010e0402190318020909060702120f03150a0b0c010f061202090c130504050c0417070e06040b010e1315080a050645010e010b1c031b060b12 62
    0x1c1040000c481407544812141c070300404c4c400c01080300d200c0d604000c2500a90815150b408212017484006407160280800e82d00719828030304641d074507515500070b0f10b1b00074541901c00c0001c20f03101b0000c0000700c1121a0001c003140101a074030115107649500106800d603107a511079944415640440c4a4080207080040f89030380c0701503843d4001160403100800422074040041452555143c041c01c0042c06030001420401081c01c4c000e8a0800c16082449216103441c02c80355400141d40c00401c0c040121010910003001e9915100f0401c400b4200c198241410420005040040790341d524014004444400d00002a00f0f404510301c3e0010350b100c1e8100304400c7c0d00c40e101e0a00003403000964107a0003141100204008c103031507000917a111700b89080c103039030315803407001c0380500010070703040318a40d110b040d40003000b16411018440303098407500c040c40d9a1004d800d66101e6202184440c000a5a9111740352140090016071300c031603143c0d4003c2405940395540c90046000c5810020200c2582c09114002403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 750814424 1250 750813174 750813187
    0x100c030f0b0102030405090a05041e0609230606010509010c060501090902030c0306010b03010e06040608010c080a06050a0f0e04050724030507140723010f0b0a0f081011160b06010e0402 81
    0x1801680c805031514002e52760f0303800000e081c008880801d40017125141d441c0444942113040900160402d400700f03031840b400b14040c00849014040d000342043c80c82c43c01404c2c440e5111001920303640c22450b013150520003036558080005000303104a90180022181c00140c1440d5801810318100519a07054040c0e8401c070018071030100e20f401581d0449590b007104102590f280d07004100a816240d10007500e035800e00000d040251b401c0301170540710b025010410880305079524100b20300c00e00184906402c000350003070f00b8003c5840c070300b41d180d912134065800c4414259884480d56040c251440342e01d1645154181240021a450f01440d40c1007161407818048001484003201624440c0c1744008008407801003810a4807200301740c1c460245150103008000705a03203c3c4040f005401502941e03442103120400210f020701c0300f04080030a603041d401c0209504441c01c22144010049180550060134092100c905001c0200000c2c0c0c0066201d00100c1409090040014003060380e503d26851090b4010b0107030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 750815674 1250 750814424 750814429
    0x150a021f050c03010e0901110c060f0a181b0806010308040f0b03190b181f051e0909011103010b12240d110402040902030f07030504051e100c030f0b0102030405 70
    0x80c0c82c15141e41d00885c410903165143c1c02401881710070484c0e41101d001048074a690100410a68403c124270102412603560310081c00044961441180c078643c003240204101040703a98800340003010610582400c01516544242e2400324242e20440e1407200006041c03203250441a5100d00400302c800d00d06040d410f25154424091002d40c01c0e034003181e6a14110280243e0311b00f03500c242c3c05072203001c503000141490301b82500700580d55010f100c1140c500c03580c009480c0c145003400713420002d08041d0024203c18607a04002c0840c0e0040d000d49039964a960f0543c0c204044440150300174064061a40d070348100401c80c82e1007c140061904145102c2114806d4101000c0c2d00c1482c3c40750400c440185200c0001d181502100c001c1d8050260020310114001c203880034258011400340a280018940340e5840c0d010031020780b00203c07001811600001c00524030b8041c0030040c6450507440409440604c216010240101c0389071002d103000107078a800200310050441c0c4564078a0007428405580b034241030001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 750816924 1250 750815674 750815677
    0x150601021603030e060904240501020c0909060c0f040305070e16080613051009020c0312090706090b28030f0b0f060723031201080d0905090411150a021f050c 69
    0x21300500410000440d1840b551b82c580c07040081e000c0030041200c6c0807400c590100000440c500500e400f610882c03100e24054503203904000d11443c080c60042c032160340d58880541080d044410b03072070aa11002d000100c0055014804403001d80886a9907411710302c0c144a2882c140742800c01d0b04418400d01805101c0301c0d4544c014020038111000788c1c04605500d820754002a04002c55010942c50f5101040000b0911070110090061108094441c0e03c80d440f040e1303160707403112820300c20003002c2140f1980c1001030510540250504071103441d48180f09203d090345010305440a0810080000e6032000c04200905d150711904c07190410503207002940d0091a00810baa0f80320307040e4040d1032000320340c428000800c54000000b00d50042d03001500d8aa00f00108903450041d000c0c021860980158044c5a00d500c0c07240d200002110030040000051307448685845a00d00c0000410035048000500c10340c3c00c0a04100040c51580f42ca13030300030b000c0616151050701c0404142e10502c941141030000780a4034280c041c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 750818174 1250 750816924 750816947
    0x5071a1608041b0b0304021302090307121505070507170a0c08090409050703030c050f0109030504030b070903230709020325121b0f0905100e0a030515060102160303 72
    0x8040c6010380302d41c28040c1c00c0d080d4a407110742e00c8041c0d040340400c410413244050b5000e030b48283d0302008a507661480642c00c0c1d000c0c085a00c1d400d0740c81f040040080900902d400618507001e06c11680c003002000020b83d00b500c00440e1448003140d00010004104880b803002d584118061201e41d50400c50a0700004114140c10390000e0000ea0004c200c411480c1e549034000e0841552050480e1403482c0e480c83d0240811800302c6080c1e07058041d40c110070442c03035010702840c2c030700543c140d480620b032a01799541d1a00010303001d00042c003089052400800001c01e108945400da120016085e403207404803d28282c6002072603000341254a0050060000b000e50190700030354045902926031510494018003110030175141e8282030f1f031040c10410401c00034070303610b200004003d08503038a0705007690655405444c0c6200c00d120b140c2d085105841c454039203a10600c060b02c0c000e01d00405040c4119600d445961402021600b500c20600f4108180000c56804008280c4401c9481e022100c1091450310043c001000740d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 750819424 1250 750818174 750818177
    0x307060c060b090a0b01181203080c13060306051c0f060209010c150f0501050108091c050409020c2503052e050405060f0a092307030c0605071a16 64
    0x411030010800d054100c001c8098010380404142d00d801c4807520050980a0303882c2c0e0200e0342c80003103240c181642d0f0841c58141e981000040b2540351a81e60f0846000314000c0442061800900c8010980414168060000c0849039030103d1100d082c107007000440071b210300c07100c0c038543c2107200d00300001005619003c4000d604600010703210f40940f001030b9034149051074000c241c0002c01101210701911a03110742e0f08005c10035001c104907030f03c407001035590040075250b0300c0441d44514821403892103100c0b41049100d08a2400034101981da0300101c007a600a004541c0c125004000210403801e4251081c080c12004030080c81e07800c52440d102d01c3e88840c0300d8078091050b075103861072070f200403207414030010092500010200024501810f0085c1c80e600180d4190f15a1a190008a42030200600032444c0003078010900d185441343e401c0c0a4801100984165155400391805c0000460428229000100703215104c01d0350303e10846c90800742440b260104019504200d1090240c1150300f034420000d8a10203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 750820674 1250 750819424 750819437
    0x91003030c2f120309012c06030a0203041502030112060b0a0503070f08010b01050405010504060f09050a030b090105071409010e0a05060c16050d200d050304090c02010e010504020d030c06021c1e0b030706 89
    0x2400f481007e41c00a45514642201000044c0440e9000c643d0066120314014004003400504130307086403042c0d100a22510451110703950008002c5020ba50045d0f070740080042c0541031302d5544a01017801c290075940441210810381108001030003080c010358681c0c076024a0520325190903d070001c0d241d0301407805100c00300b09081c6901d060081c00b441064000d018002c041a0060f40c2d01c0c5490702e4241001c032001c400550802010640250180d0310700b07540500000949420513204400441d0300140b00c800d201d910a50345c800016a03501c1d584000c08010700418080d001100e032480c01008046a40d0340143e015800741d00501020501c8106c1075140d51502d0071040300303030000c64000544a10400c5c00090079a00000074002000c0256a115100c2c1e8002500203121041c0044680e03401c0b14400c030750107900103040740c1c20940041d204c0e4100441c01441240f0060030400c0c2040d84480440c88490500b6040f541c6020790382e2000070b10b801d4039030804980b0340148001d8100341c011075281c088a12801003071122 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 750821924 1250 750820674 750820727
    0x10912031103070c0306150e060f03030d05070903140f07032a0602010203070207061d09060d0506010320041b0305070c0213050411091003030c2f12030901 68
    0x109218049528400000302c81c3c0724409400e0514101d0071510080302c100d4548103041c2407000d469907c10702214000038840c28140d50f110223008020020380c00c4560f05000800801e18125101d1050030300132006a0780312032100b400c52504400e50404200515003036030001c1100c40040e40c0019510041d29400760340c0c10303c03011540001014280001c80c030301c800c0d41100e46001c00c01982c154050340c41042a0707400c07240d0b000d41d0780c0425680c07610788010b80b0922240c40305101499042c2805005e0b0802c0000c2c4c0b004600c00394540b00c85e82440d400ba00102c4207803402c1d02107011030b00e4130205040710a4070200e408200601c6104240062007076081062010705807584001540c40c1e0069074125000340e000b070709807103c3c40c4078081e91000820040b601112140340d01e004103900350501e003030450b105811002088158a0a5440a94151201071b00440d00a11f0386600264981c0000c01c1d000d50421340c601e2080b1003c1c21540810400c1d0144405980040d8414010090303280e900981c41d010405030441e04004480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 750823174 1250 750821924 750821927
    0x3031f0305100e010c030605061b0c0904060603020a170604030c08212202060d1e09031707050306030c090a0e030f0c0106120b0a021c1a0301060f0501091203 69
    0x9090303800034155010300102800e0281c01c41d040195040c004a0080210900008090301107a01c0c1d401595003042702448544404d1042c0d0015a083c16418000c5401d09660500080d07000c41046030225181d60f19002c1c1001142442010440640240040210554030001c1595500e2800801c0034040180b8a414041844480022503500407001c1b40c0b01720400c40410700301059108182d880051030421540b05071084641144000742040d8000d180910700b041c0c0e46401e20160058614a450385807007540011026601c0b4403a00350041d1080e00e8034840314020050b041c0151500906000c00d00004100b007007541e9401140701d0050007800c64011030913440c1d141c181d000620740300d80000418440014010318254442c3d000c0c001180521000b4090340e62100307107060013a206410010403c0020703001080083e205900903103185d111507000480c0c500b1501c052079058417a0080c050b429003040c85240c0c41282428002e80c0301030031507108020711171443d290000300101c101d442000e80100840034008100b6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 750824424 1250 750823174 750823231
    0x609040906110405032103012d030609060f0b15070f06020a350105040522030921110d0f06110a030f0b010e04020a020f100212090304080303 62
    0x107a0881d03810031040711103010100e526403143c01a54428031444686c11010915044c40b00d0310111750b143c0003030850340703082902c0698120300143c10f84a809610f8818040c1c412400d070000086004090100301141241848402c44d07040c0344810340b40e64100344030900203845036491310808032884180c01d50b40302030604043c40c0c8010051401010b4070f000040440300d00742d01004051208644158146003480d00e40f25180641100215141c0e80c1703d003c0700100410b1030254491544203500d908180c0c10f03044d030034a400d49884501141117010030780c4200180200903294907009004408d00c1a035103001810741d210482c0c0141c181c89803902c075120542c0d030345003000300c48440094016480b1105010380191005c02c1100c5410038041e2000091600100302c40038049409a111214410b8451a04400040040c44041c1d84010004010751017080180345010a040006c680000c4003003500584074950400403218020010b050303004ca5500134041417081d10404003c6a421030124019281d41441d40b10400111 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 750825674 1250 750824424 750824441
    0x1050307030207141b1008010915030204090b010602070501020106060804060216050604080307081521160816050a0f09022107020d0f08131b0803160501050106030506010509060904 79
    0x2a5041444004c00300c240c000780c540e00740603503526a0850440c0c82c0050020841424003018009010705004202000d03003540100f0411300c690300c690311580d403250003140036034409a400b114041082c000420030710740c1c18040b11000c2c10b02403000780025464000014102400a0800fa00c0503900154500041141c2008034000c544c0c860305440c2c0c0d6181c00e052201d502d8008a4880002c280d086001078413150240c0801ea0512600405da04e180d002011202c030280001c03803640c111700d03114840b1000000320320802050f0040c00042c005103410188400907915956040d0f0003180180c10f24101400072201c0f125120b01941c03c4094010380314074114019031003601914044c130305043c43c02001e1080c940d9000c1440040504a0b460394400c41001c0041122210320071031b281e4020007004420f10300000c0e548540ba00100030400c03104a2030036112902c90f801e42d8880303103403500c180320900007140801100b809041c0c010000b0b8141040700303140070fa001802912903840070501c07803080002c900213150b403243e105c03a14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 750826924 1250 750825674 750825683
    0x10f11030904180c062c01030b06030907050f0a1508220c0e062209030c050d0804201309060905010603200402030912210a14010b090a0501050307030207 67
    0x50102d541e0440f24107050420180d4243c0341c01d84010400501400d0244140c1c6a0103245403201103001c0ca20310003805065413400e04040c0c888084034820307510280a14041d56400c800f920b1232528200400203511090203071580280d000302d2040045603404891070200383d006080080050b0780d149130012100212640118940c42e19440381c40034860068512020354108280300d08031920b0303c004111040b92660280e1240580400c800c2410015540013010110b2090429102025a590717845041211007404080001c0c1c2342070401003405803d4980c40300304482c5000303420300d188814001ca480e18004141c04d1a55580313a20341101000800d0344001c40d0075130041c0081041940b2840c201400e52080d91030810300c42045001c200052030140301b128012500f40c030060101181c0c410f6000404e4003c0d000350344040400406c0341c0d0680701e0400043c1c0c85031425007000222401c441c0d041118001d01038002405800041c01902199155106c1c000c3c19034009081645c0c030ba0b0b030b0342e0350120701a204985000b031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 750828174 1250 750826924 750826931
    0x30f0604110f010c0b061003110721050c12090a0b0d150906050603040b060d0507140109060914130204080d180503120315030a0605090312090c010f11030904 69
    0x14018a0601032001c440100c69520105141c64011158138030380d540082c005008810100b4450b141850952012401900f40444c40d006038401800b05500102015100d102c45842403050700300620800d19a440c849013021411f012920b01c0040c0d640c6a4800722100b510300000c0c0205007990b80551440050a071038200e02c3d42c503c20940240c000c0c02000c4404820460800c4012840800764050201680c0014060508507a16500c86003490344c1c0240c151904180d01c03c02d01404a501841040c2c00390800020010052468500040c003a40b01075000f20101304900e201881510080070956201000840c0d10300c4008054100c104024480d40d8046081d074441c2200313102c2e0840e00403d1a44a100c0805100c020981d911814561524480300100d00b03e00c00c100000b032846151040e01c000380000c09401c58100740d00544d201e0040700d8007600c802e0310381d600104600c0407480740001c460f43d1100c403002c00b4242041c01c03240060041080d000e001c03000d1084c00c40001d12104030400c1500c400000050062 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 750829424 1250 750828174 750828181
    0xc010f0606170c04181a03161d0403050a0305180d020f0f120a0c030e09040804051e09072a0c030510110a0806010c0b0f090d020109050c0d02030f06 65
    0x903001c032000320b031560711400540e0002010601ea000039542100e00c04510f01141036601c400040c000e101c03200342c0141c2c0380c540014402c00358408000c6160180710790341c088605241094450044403841980040480e8151010000000c1e072210a50b03644110134100451941c9415411001641d0040846880343c46170070600d07458641d0000c1c100002c81d20f04020703191044110300c1840c0e2200e580540000010108018021041d88911100201d0078001c0c9425200680c00c00c0c009030404401396815a100035020400740041d01c1c146200d22000b03910300d03440100500043c3c0100b1500300700180000180b0001c403003003207401d08400b100b0074135203070307c0d40c1d108a2401040e103044050b2884502050740d1900c02e4560300810b9007480e100d031550305c0446c1c803981c50900720151021200c0c070030010308203410001c0300c1e0000c00010390b1601d6520700174019011104043e107001070b40140340c40c0b043d40c0c1c09811a13041812580104002148000c0708440540d40450107042c1400440e29069203a61845183d22414042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 750830674 1250 750829424 750829427
    0x180f0d0c05100e0a050114070b13060b0402070c1a043c0b0712030e010c020d11070f090b0d02061902070e06092e031a0a200c010f0606 59
    0xd0726000c480d80582d41100490407210218803516580c0c21101c1ca00d400d125640c0a25100c000041c10780f003451745422015a41c040038140305448000b510064884440c040008901810b84c5810082c0c8085050040b01c0e2101c40070001184150409004812107a040b0b08031220101c5000d06200c8210190600b0002402004144048800340f908013848450007400d2503004454000c41e030410940714113050301030b10362070011580d075603c10f010f00d9501c5c0f180c216551020700440341891110f8014103600404404041c0007001d813030005144907041008240304542c02d11015006841c4030b820300080002c2840007150410100304000382d030161f03001c00c031881c42c011000300c00384e507424050b82564052595191b10b84062130098445580c04942040010b10078030f54040f004034019020a101d00048074103652031603844400d43c00a558815407101c0c0350b18a00f04186d1200c0e0002052001001840045900034946554103482c146030001e0012382c80d1a0017809410210442640301c0080001c2a5280c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 750831924 1250 750830674 750830693
    0x151e03020f040e0304170c21100b0d20090f160f05030601081021200303070f0c051e010e0d03020303061005070f080a110a08180f0d 58
    0x4200d00c00c03080340460041c40c0c1464010310300766010b181c2c0158103203410703c0d01e0075411a0982d00a00030510491310034404940e00e192003400c40020161a1920308400c038003a450501a003803000300001404c080c484001c41c4c60311038519910320380040380d0081c0d103100070b45690001c1e07185010b116445000031003409288030062450700c1c000c080107844000708040c65001950030052080c40500414400d1000840e5540690441035105100c5480d0b50010b607241c000e51165a0350007924459803a03040c5d4441d0701008600550000319030025401580310105c8840029a40c0c407808000074029408005039030100501107400d41c000c1c0c83d00811144a501e584000000c158824001003400a40c441260307500505090426000d03182d050740c041d41c40c40d500c1c1410310124074510a10101000b4041003540081118002c8414081e4031500940d0794492042400034040300004002c0320044e045083c1c20400070307021004a030f440322030000741442540d00d030740c00081410482041c0c0941010003103d901042020190 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 750833174 1250 750831924 750831929
    0x60b040b090a0603060b0406030e15040602090307120b0c0f0d020408030a0e0906010c1e0f050115080d02060403030506010c050f07030320071202041d1605060a12151e 73
    0x6a03003810981d43d0309411001d580c1c0a02c00d00341c507407400300024007241c2e2282d0030800048075a4000c0392104054501d09071170703081040b242502c8440c1c2c0440c44030311a00d010301c5201f0090890b580141260541c40e04e40b24031110018101c8425441c00140918a462800041c0c0d2100e2401d89011900d45a0300c2030401d86a900121030b0354000364088008000c2450484007180c064001a541c0381c4887c0758680e50100c41c00c440d50031032803401200b60b9131200010720004000030164031580004c6044100540d511103408401d421000c42034000c2004c890350f241c0e0003d034160384aa014603000c6010303120310380160780021f4034000c0544140540d03813000002000008202d41180d1182d902c414502e09144e03808240003480294007021908118410455201c0d405206100d85000420004a0610303160708230706a0030074203490180c0e9030010882c181d601a46440b00034000d01d0b040d01c06a14140d002140240601c03c0a03071604410366944212064101c04202418050181c00b26101d402c10300d1810820340e0320700c251 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 750834424 1250 750833174 750833179
    0xc080708120f1903020c03130906060203030609150d080a180510050423120601080607080402060714161d10050105070b040f08040f06080916060c06060b040b09 70
    0x51503200181d0400040319042e10114201c02c0c10b04208038403031215100c0c5181c000c0101034081c000c10150f4903051006005211407100c0020410b490403644405650450384180295002070040100c40d40b03840c044d85510418090105c0d0014424200150101e0350060003d00100b00c0070501420343d41e0007000c50a41070102c0c490043e107041c2c5e240c040010352800313400314000080c41403008004d603d125800702050001c40d24041c0c01c0b5203000c2030200e80b0b4180356080c090078580c0602d00400c40380e04244804ac1e00300a40b8505908503192a0300441c40e00d04c00c84a00426484488401c0c0900e801c0074000d8041c24482c0042e50015070303a4582d110490101525055540c0054100104149045070001081150f2040e120309041ca0110f03101e0500849005000ba12000c42c03804072000000d90340300c006c0c4040c05d038000207102e4417414104010041d4030001e10803e50307584001e88065202c40c1256030541100d03890700c4d01c40c0b140c40042c540f58014005075880308280441c041400320700000b07450042c18403201c05 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 750835674 1250 750834424 750834433
    0x30304031427090a0603051e10020a030603021002070e01030210030e0d030203061504030228031403041d3306041d06010504060e0d0606080d121a030309060c0a0c080708 74
    0x842c0504c40c101c1d0405c2c8402812541310210420300c1c0707a801002e14540300840c0040d601c05401c86c1d030700401603034088115940001d54940043c0110b00d4680d2060403080720a10040082c281824503070281510180006841115204102d41100b4401d4021a4416903600155800c0a05005c80540030350400e445e5584140011601d03810901005010744040b01c1d0010001848900420124170380d4840b0011041511011510048080f90506185d0042020403100035a42e0705d26101c0034040c121070321200c108200503010148290384040c4c80307400c0209a0003520034190f0710480c0805007050080f22405581041c8041000100440f400e410b600d031614858401400e11b039501001120184204c0c01184c000c940644128130280c241b4180300c41c1ca0510034440042c01549440341d85261201881c201d80000d00e0012283d01d444045e4000e040182034400096030310410484d0019440307015507650380e8090500813070010700424007000401040ca0304a48001b03042600c0b8039100d0f884842c2c5c0c1c042c0221504c00e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 750836924 1250 750835674 750835681
    0xb120d031d010212041101031401180b0405090c09070e04060f0302030d020f0d1407080d051504060b041a2b05070f14070201090906060c17040803030403142709 70
    0x10f000320b8900c83c105005401c1650f40d19603a00300101e0500180d40d04050707691404940c0e074404411024082c141c0070091401c40b294a00c550303415504814032312801103041c14103101c0d480c600001e042e401e94504441c07841940d03642220498001014000b042e80c03103824400001102c0c2e1038030038131006482c02603094511003a0840c01c2aa61900b040303149a00c07076840f140c0d90300e039090b00c504480c80c0036a00415041d885e25440762a030103d40e411500c0d1072141c1c280e0342c40034010040b80f80c3d00b1a14070440250f070b00340700051400c5903407442d6001f544510250410030300610344d10507002c1c00072106440032041c104d1510020311890000b001201c5600d80c068a8039110106072141c0c010030410300c442e0070304d80c2c680c5d881c0703030795811a01625001010104e05101e41504c1c0499400424000c0401420050b0366144c000e40b0141015480b12092014003000500c040006000c1d0350004011a40c0c05501402c0c4800140c1003258444040d1140e00301548900040401544030300207811095000c9010813030f183d003155113 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 750838174 1250 750836924 750836981
    0xc0b0619050d1401050c07380a06091128050307120e2b1701030f0503132c0103050c10050c1015080609060103120203040905040c1d10090b120d03 64
    0x82320040000c04100106912003400b0001d0881161300026108020400554490992090b14040600102c40c9103004c00d108900f02d81e540080d031006050500c1c00128040302c04009030041c070020f031941042203500a5814110f000c0c681105100048000403642c072820304040c9804a17580646403042d040c0211005103001e1440f88407111464448079100c0f5844d03901c4e641e0340c030007680100d000442c1d41d80400e0000100a0100e500e80d1802810f03500c0d00082c0300c0d00444440150740540c00b40c00541e51a403040140b000c5a0005408020010b00b0340d54180e03604003a040c20384e664000c0700c1000045200703c07181030081c0d82c22900f142c00c404581074030308860951244000d5440300d10841d41c1902c90782c814030041022800074980001e0004a80c01a286400e07151408003055810407102610201c1d40701504010030a0340032507481f01e9400b00fa18601036800d00c110345030080c1c2c0d8544519844140c680091fa070140d03030303008464030150400f9400c442d0605030030200900038043c0c1c524110310075081e6110024549 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 750839424 1250 750838174 750838223
    0x4200102160618120b0105030c0418062301080309091e0f0402060417010e0c040504030914030111041e09020405030a0209250c0b0619050d1401050c07 66
    0x1201c1d10703403100555040c2001124903502d85244950040c0015400098500b80c068403002c007240111000381540d81050241490580b4005400d8011131829498181d000802c80704405415400ac802007201078004003448034101c45032118001c00d04c0201e000180004001000707042c4070b1401d80d240c5480b0303951900d2200c40c84414001c251250803041e000141001280c240c02c5038410b200400e02400e01d601d6004581400b2062000303030711076030746d200d070809034802c0d0070084103c684e4800c4600780301034074041d500240f810040e407094103102c0441040950840d1b4081d0086400c4c400c01c1140c46460f0b56880300102a0490800440040321001d4100400d1482c500e0084909441c000380091a44992035828000b903500700600490284541d0f10540c605059a0910f1003002c0b541d035034a036541c0035258141280c100f0006090b01d403048100a01e0280690303046210300080b513100301c07013401b11018241059504d2024018044445511b02420030001c0419070019040840c01000c0400050002c8900880c0a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 750840674 1250 750839424 750839443
    0x5090d0e01021f05100816061d060a05340b06041505010e010e030a0503030601090e06010f050a0203070501240801020f0f0c030d0606120b01020d08150f030604200102 73
    0x2030040300a003d0084519507008942c0000040b6400a03000742d0300c100345030806010340340929096071400703010011140d10a205001c003103407078406500c0307815518001072164410800c60400703000010882c5284045c61704500c242c204c007580e00c0c08080c1400c2e20022080b8007104802201d0306854040803a0305400c0c40d00c103004020300302c85443c542950500005603000002003e03910704000c0c490160000071b8030184100f03007a05214a00542d141e081182c00513201c0e8545030003241034601250308008244ea40219142c0000c0f0141c104144d0712443c84a049095200308100907103a58241260802c450303210651400b8500510b803c5000001e45a2801c24243c2c03141052409241310103200242044014000821a41c90703a101124503100a02025100b42c0382641d00c000c01040394003054201d10b00640c000c04002ca00c0034400fa0000c042219800f0b403071600054242c200e1202c16018401030b540710254100d50340c61000b0101c074175a28107881c1000812051111600d041c507601031100ca07107540000b814000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 750841924 1250 750840674 750840703
    0x3240203060a050f0a0504020d0c091a030118060305010203040f1101032c0a1704050f0103020313110a082b020c4903090b180609030c0405090d0e0102 66
    0x203603160404000130a22110340544e4003090314000014165150300c02000e8a0440030400304001203d0752000c0c110b02d5250384510075003003003440811001c10180d0201ca040d94190b41c0030b9001045540c003580000d2034550801410b56200006020130302c0b9040a0310350315103114005100003603050030011019200c0e070f00c4812070251160440701440300e500c1404504041c40700e00483c0c50390211034031010740800c4a4007440109490028003400181410813040148220070308007946942410002c0d42c8645040c44005000d40c1c1c0846410400d03641e84080ea82c008019050489134450340301100d078001c0e2801c2c009400760070010700c200010050700110340024042c200624051840003d1550350a40030700315098040380c0515003442032035107007035220709602c1e103c2c03000304101d080d40451902a00500441d040f107940f1100034000d5050f0303040d01001424006000303a400c10b03283c2c00c00c0b1001c0381c81e103448042c4841d413150502041017200d070380014071404002c0c499601c0b00c600b000f01e5001661502d03000a00300c0c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 750843174 1250 750841924 750841939
    0x706151d0a0f110706181a0114030109031202030a15081f09081e04030b070816020606030715051207030902150a0807030507110604030201201306081f0324020306 71
    0x802141459000b000803000c052041b21954400755a0201c10741003260501411905004c018482800040c0800345001c10503002040380303444544000e4548001c0f0102e0138032880d00000065054955034020341407801039180c9548100740c403142c80e5502c414800c911002e0301103000c584410110b143c0d0141030340c8140c001c1d040d10314045a2105581110b60040b00c001d105441c10440040003510803028544664003036070361a28a42820917005c1c1142d180000041c04540c003040c1800b0440d076011818030115042c5203550164050b404a082c2c400303005400103407695040050411240c0d41d0150080c1d0320041c8210b8084200d801c981142e5130380da009400302440014041c00000740014000e50105803c807400381403600440c3c9044070480d14003042210b0460041c1d440d0103502c501c2c06070004c1180c1d444648610f41d1801c050085400d85070b0b00d0a640304880c108600b142c0401d0101407190407400c20445410b0802d82c01c20b4807410304007483c0c0d0024440703a10301085550200181c850a2003500e004500040004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 750844424 1250 750843174 750843187
    0x10c170f010e070e13020a0f092d030506010801022a0d0e030f0609010905070618030b0c09030d0c0203060115020c060714060103120e0d0b0a0b061c0f0b10050706151d0a0f11 76
    0x10000c90ac98201c1c1c0f0407507040c8180400407071000c0001d6402132942c00000750741c41010590048080c00c81c44884d00c10304030000d0310b00380c0c4c1369000302c1ca481014896150200c02884444002481d1000e402940c0038507000380c2080c401c2000c410340018581c40c0c0644211001150b40380000c44920150006d03d20800020400c244002600452159001186421205e08241e00c210000f81040c29007483c0002017450307102204118241400380b03a0045c07110b201c0c0c03211400b80e10007010307403a0006600081d1041e500001c40104100d00480300c01e800340000c0e0304a41c40c0c0e68503458050407000d440c1000d00003042c03003c824088249840454141d906501803945921030302d070702055102801d101e928859110f882400071840035101c4000d4505007a58600012605070001402c0c802140c00b00c400c20380c000d00b101c1d03076a47c01d0250080c080300c0c81c1542c4081e00180406210701c08009050107a003001103025041f07400360211030000e40d034441c0694a00141084010615002c0c40103e8003048203042e82c1d000c0c107005a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 750845674 1250 750844424 750844469
    0x50303070c02040f0c080604061406090904151b020f010b1003090c0b03150909150f070e0a260606100f0e04020c010c170f010e070e13020a0f09 63
    0x156188140b0160001c101006850800000d54018440800010f211601000030364509805130317400034960307507680c000c40c44a910040381c10b921960340c1e40c41c0103030040408a000c000b5002e4288885c5185042c08001c41084071401b49803024104440d040144100c40304071004110610842d201584002c11000750f103040c468040e0043e01d89184166040700e540340002030030030507403001548142c10302600300310207a180000300280000c016105010720703480074000140032200245015000303880040144201e595038101180d40310000c0350030391780141c584100003444c13030300000401881c00d044c000d004a201c0d606a005070364801089400c00e601c45d02607090218014010b618181401c1c41ca07142c1804508056404a8140d91003602c41039030f00d0f951621030091995100c03102e40b01036160907040000d00d04004040d031301190320600403800004c18510100e00783c540191190707060307441e003d070200c20b6441642c40303605c0c004c1d000f0387c480501080300c01c1080300c03040f84601448815038003401007213014802c500c4e82 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 750846924 1250 750845674 750845687
    0x1d0609040308040503130b041a0705030306010509060c0d031a0d051f020f180f0a12111c05070305160e01031202030403020a030507080c01090b0a0f120212060a0f0305030307 76
    0x815544e6010030442528554a64842c0c8005011025003007070b0f503030703141c88150864890011982c1b24920750510403400050008401c49400040134600390313481d041e15400140080c4103444141d03105200700300e1101501da4040d0000e0b0501260b110002c0400d18101c42801319152010000800c0742c0c00a0703140c0e06042840308400b4040b40b104e0003005082205020a580301d41e0f1000c10b04c00f80340b840c09072009140c2d00d820001918000410b030358000d0b01c1841c14031400c4005949403402494854110151a06600c80b54126605510922030600c01c05065092080d200c40c0c0d103020070f4825008903d40c0c00340040c00d8940c84400c40f4070310060b10103a6840d580b41d8cc0e000c0b003070410103801103000070000000540c0c1c80c81c600102960240024154003890302e041140342c0948070118a040c000c001008100701145001981d90306032041c100880c0d1004e040c10700311040b0180b100c40a580383d20108030807403619850610248122420342e20380c603540c0d8070344070005031403034640c0320040860b0300400000d03600a20514 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 750848174 1250 750846924 750846931
    0x15010518060d050c0d050a02040c21020f1c0b1e0d0f0203011418280209131b03020f15092103040303030c021b0a05100c1505011d0609040308 62
    0xf4240d4550001c01000220760340341d68101542c8540c040e02061382580303041e10031025001031600340381071084580e420079916006092442c00f603007070b8081422610349000d5001c540d103d4111110f0301d0070307059a0401c1d1000078001000b60078003610100902c0e0500d0003900d00a2002042c00401201e0000c40c26580c0c6840c01007449000ca0301075494095074500c07a8032005202c1d000b500744200d8101d1071800021030743d140c4581e0201c81c91600d50380b036840208854132665040511501607680002550f03512140e001041510b920081c260281c2c94202412001d00b07001c1d07081a42c4c422a03889240b4040c0c4000c002c20108024161032003104104070715046032500110318450300301c5200342c1c40075036a007280e68641160003546c0300b9004241c440c900030102d03d40c107100300710282060f44c03c049041d056100100d0032901d064010341d805099404c244d50807080c001d0084445440c0d00001c80c0340c2c852980680d00014200c02c1c460f20581610415412000d4915803a019205900103001d903032186d43d03241c5045541d1440503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 750849424 1250 750848174 750848183
    0x1b03010e03040902030601020d020c01080103080c010b030d05130b0715090f08071506051818010209040e0d0e060c030702060f090301090b010612020423031203010815010518060d 78
    0x200d450303455000c0180050001461281d40050b1607241600c000f9003005543d02c500c01c11900000d201c011180e800820b80c60540340c010b05076a4032400ca0fa1012401030104600565051150081695045d0b6201e001020640c0300c4128401040d81c3e143c1c800c4116004201c130003441d200c41c06050b40d100514907407048e15420b008800b030300e20710000e030744803c201d66200c0b0000f9101490a070844006040c1d03140110710040006803a04110783c10a2502e0b40074050014122011011200d103010710340704025015034070503d000501c10012680d080c3c06c20340d43c03003400d04250404030b420000c98401d1450030100340d6025000a0018514000156080004a0307002c80c0e40002c04220500c07104003640c50910518580a104400c05000743d4140342001d000d501161440c8023a43e4010801070118540d8078a000036107110291301c0c84034401b42c00000a04000300c0c1a00701000d80c001100000f905000010024840400307140c00304040e0742c0301c405003e030300d0032410b805940c0c078481c3c038001c50820f041c44c12900124901a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 750850674 1250 750849424 750849431
    0x123042d030507050111092116080708060702030a090e07020304030b011205010516090311060708030c190e09010b13032306130308161202040e09150106021b0301 71
    0x90301595682004054800d400040d804100c03002009424451200c0403c07440d1041e9041c1020030000075900418038240001010180d503140b102e15404006100002c03280e01c1030700410740d0b04c5800a568441c0d04c0e1299681900c0751002041c0654000300841da40c0d804240e40b5032944500b48100401c0390417003e0a024214481080000f0100e1100845140a8041190707406510304640c100b40c0c1c01e440015220f03c65441059445030542d40d000520a803c036588004143c41244071803001442a008040c0c000d81040c60000c200414141440c0040022071403c180da022403240c7c0d0f840403200040c0d0740340aa0303040044400140701c0402150302800040701c48504213150540c4a0b038805030940c440017164070f8813614502404500701424042158000e10100440310007600341d443c010812240a00704040c80905000d0100000748614030034150001b1101081d1750b03172070791a070100c0021401224000d105000703400f0404040c100f50340b1043d040350419801803a510f07407010001000c0c0a0401480c51740340d940d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 750851924 1250 750850674 750850733
    0x303050a0e031e0f0c06090d0f0206031015050702030d082a041404020f0d020f07200109080303040b0604050c040515090a1a0a0305042a08012304 64
    0x70200044030300e410030703c5000c140400010310060302e460104003211030550030103500d101c00303a115036003950161501180c4d0300d2080002e074182010354800185010b5003220f0000b0410100541c400084c00803180610001d0b00d24000c4680c08075024066800000e6040c0c1040310ba070103c66124101352508400003e600d02e00c03407800b0711199060051035014030000d20742e01182c10485c2c10340010a0b2012503105640641c40c28148207042c20841c460700c51140a80c0741d01188015410f404881a2500542d000c141000002c0000102c030a40e112400c0c60180010492103021403c21004403d0324003e0b5400b09003200980c503403004100c0503180c000c0003407440543c24400014142c0c1d0b000c079005c0e101e041010314140d80750008024480700c100560401e80c080302c400da181c400c1042207502103842640721880c00142e01e88503480c0800c5070903600070700542e000200b42a2850490314802c0d007141280c0101d4020001c0c10f24910ba2100c40382182d21100c14103144150008021440c41d01c45003900301511521010210b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 750853174 1250 750851924 750851929
    0xc040203041703041a2802070804030c0902040806011232100209040501080c0904081c02040603020318011a09130804081b040204180b0301140a020703080a0b09010303050a0e 76
    0x3c008550668240400d1040c05442e1111740c18419080300e203900d0b1845075000c0710300070002401843d010f02c01c4426800110344007403003443d006440c00b071603000c0c0d03c07050310720707034440910020790010700952040d070140c3c10000807403040b182030352003000340c2c820a4100d0300c00c2002641401d18032807810940502c200b100c414410f680040c050038015044048005071296082010b11003110b4058100004641c8809107000d01036807120300581d4030643c00448c0581c0c070501112469001d50750503d404465034000310303000c2155500760b005180718851b000c0d59404124101d5203080e00340d9400b020ac88840c450303080c00040490404034182c0c0c0d88003d101442000c40e81c0299280c1c001c0f17502550040000390005850305202205a00418000c403c00b19000d600f41801e0000c10707070714244400540c0c020f450703440c9032568607510290071a4520072000c80d04a0340394900034803018007a5002d40b400b100000c1c0400000b81c961711403407044c030161000140c8074200c141e080d035030152266030220b481e50f003d0043c400644100d13070307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 750854424 1250 750853174 750853177
    0x60c060b0a05130c260412180e0133050f0c0d03050402010906050c070902160f06050712151419030c030209070516120306120809030706020a050c0402030417 69
    0xf0400381e500080c90320304400000c000e81300c6045841501114000700350310005606034030035009500603030001c1115100a0b010344803c5c10144e4072014202c00050f00003406002c00d00c2d00d80c100c0e0350002046170690101e49d00c40707017990303072003408220f50000ea5064201500e1082015040128164800502d04070a52128600e0314011030b040d107000070b0b2544108411561700a800c08001c1030b903810101d05000b20000c0854840385103020340320755198080b03000560f004403a5034204400ea00300e40f0b0906c901c9014103051019000480300c40000c9225904d481c140907008d44614002d542103110f09c42140c07410020b042c0ba40f01120305800c0ea0050816001303840c0d00c500503a4800080d4410b51148840c1c5195105100084c50001d1140f03050050038045000440d04001440341d07007503481301141800c120210f0f810360050034640c001d071404490044034003041041d0380780180400c403400c5048030805a510a8202e07501c118580c4001d0040c1c009500d2102d807030600350050758001d4420040700c484440c0600301c49056 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 750855674 1250 750854424 750854449
    0x50607020d171c1d03070302031e12100609060504290f0d050103030e01111c02100e010605040b030c010c0b040f0803040302010b2b0f17040b1c06060c060b0a05 70
    0x70356903400703004da0340c0d0302c40d91000b03040400b07502541c14513a07140c402946a011702d2014000343c4060750112080e20b030405c41125280385040345604d03054149107800080100e03803070040c2400324007810303808229540a0404e9908813024070489076503280681c018401c1c00310111420f007082103000d03c400c000d1922518058030390540203801c001410340c5941801400c0341e95250130341d810b1000410009994000100e010800d05160021000c101e1422100072032401180003581003900c2d1500d00c01c608864010742150b0200c0d14200c03420f0080024090415403200118103000340894890a01000051000c000300e641c030a0048c01040000200c0f9107030130203203038000c03903040300141d56503494038001d072030941c6907255810501030f24100c0c540c0c1d10291004151130940000360582000c101030500700041540d409214602d808001d54071555148074185094109079200300c1c00e24410041003000c00568800c03402214100e82e965003238403104d6117030000100350403642580c02604000012442c0d841c0c1e5400c0ca9072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 750856924 1250 750855674 750855727
    0x406051b0f0d0909090803150120070305330a020705061504140c162306060102061f14040f060315060e010b190c0515070801050607020d17 61
    0xca1441c0b01d4002446809280c03c1002054030b8606244003091025007525408a9445078198120a1000040e034600880f413550003007540203550301c0181181c0100b82e0700304880c8203900f10356450400817030b10010302041c103001d084191107030b90010041140c40416181c012803081001032811880d501d401d400d2020888503c10581c000b2501c0a440e81024410ba616891801e000e00c03078142440b00902c0840d03c100c401072485075509031840e500b840030b0444090001000e41480d111409655104aa1070758000c8850502500610f000224807481080c0400c030906c40902040c81054200039000c8840c0791740b6000c07190040e588844860000c0c0482c4a1030b40618011041a600115541910303c2900c555030407110140c030400004001e400000015150a100d01d40a50458519507c004540390701030898041c00900c100180100082484002c1c01c2c01011b8580e18445140e803a0824050f80f032080f288000d400060303000c40b243c08920307000603002d03c00789100c40b078925188510b141c104645800040007031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 750858174 1250 750856924 750856933
    0x118030303060f0b0c0d23030a050403021e0d050d1e090c050d150b03010e030f19031103390d0c0f1403060307090207081b0c060406051b0f 61
    0x24a074030083c070340030060241070078035880d00a8140d09103841d4070b4015040002e000c2e10000f60035907081003512100383c1c2a54101101e03280d142c00305000c005808181c0d005e801600070040c03080e1207440781400100c000769081c80200120a101081141c450780442c40314402107170740f83e4072142a03602c500c070030510480c212000452024000c0c140103241801e40c1c2d110511455420100300c00003285d04003520307448110104d001800c0b414400101c0e01520015075600041e000c0081c150740b5220380b100141070788461042d80c034242d0003020310f0260200d0700f40c0c03603822007042c03428400a005500200c0030f12018459400c4000485082179034800d0a21030a00e5250880003004100c00e0800c000fa84541018245a450310746207110782c134400500015044030b050714081c40000000340d031302c0d1010090300f8020030214004655400751170800c079025800c58910168a071980c0b482c0e1503c01c01d030001c0c40c4200d80f900105810701d01440d02205030303a5a84001c0e040300c002c1801c2240400700350418011124034211100140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 750859424 1250 750858174 750858179
    0x7180b12060f101a0f070507080307030e03030306060301091a0a06020d12061518050607030801031a0c090d0317010902071a0106120c0c020a080d02010b0603060d030c02011803030306 80
    0x842c800081060b04414007003142008803900b0104204c15000e00004000c4c0e6601c03000c00088000d118100f005010341c40380c05400500018000010700009010742d994003003055091080503160b11003500c0341644000d003403005001820380ca5010601041c0301aa29003e140c4642c1d01081244006070b028502503003180e41200c00c20758205011014079140c1e11001c001003403c2c59600d60003920600820010040d0241e082c4801c0e0b0058140200034107002844152580310a2400030103102c0c2c240021244034000316031404c0054400d60500340129018200c032410000b000050005070b12500b10107508001e41400d4040c082003100713035140d0280000c5440581e0714401c50402d0340200a04200409500145500400c45070f540045206101d040700303a40800c2d100100041241c41511105020354400d00703a440000300e4020014020b03c030000290028041031000e00708002d41030004440e80e913000010000100d00091190300100003051050502040740a1060300c42e551184480d0000c50100345e80300c509 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 750860674 1250 750859424 750859441
    0x307020c030c0d11010909060801090c080c01090506090a050409142a040914010c0f140a09120f050604030507020a0b0f12060402091003022101050307180b1206 70
    0x1003420a142900100000107101010540c910a040300142111076180c803203165580c0304070400c0380100580403060001c0e5884494144c000c1203200c004a69201e03040200180ca00c10200b015414018161512524a440d00081c8004d030344c040c80842d0340c000b85d149070115081e03680d44182d00b0030030300462a5415160288140d40c2c07804000b40c10100428070500501043c4c40103544801000d100103039400b00321520f4a151102d8402e120400d42c00e020b5080c000e2040241c2e0307000c00c007a03004400136900d04504044e942c11460192180310740030400903008050a000e000c4140072008035082c892400a00100400d495403400d1a9042c1d400318005800011410154507101d2680700180908131421441c00c4102e01b58186a841113a100318200d40c0b525000030195a52981620a00300c1d014160b011040407a240082c000e601101c0c510b0019203058801c01120f10000c02c2043c1a203002a006000075400d0800c241b216014910901d05880d40740d10850146172241c10b01442ca015044005104a0810540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 750861924 1250 750860674 750860683
    0x1e0f050301050603030d02070609020d2f3706080115021920060c0102040f0e04030c08070507031b06020c03010509030313031710050910030c050121050705030702 71
    0x45903110303a04141c03d01c03a031907402104852a88104460040c1d903001180b900c0400f400803044060f6106048040340001c0c0503c0b003802d44188882d40414240b2440c0c460480e900e02c00245880c290846e5000192501211044507080e19455620741c8030811120345c1c00009180c0c0d4150f070840c1c4001b4040300300400c548414114980c12265990000d48031030b206101c2c0c0307180c88800d010400742206804980b07150700c0c040c0500032000300700c0307001c4c112980c1c0e10311050165020f94010b100303087c020741c1c0c0200002845051140300350700855260b506c440700b040c4546c403050860b41004100b981c083c05020741c0040005e40c0d080080303096540c15405604458500200a82400b0340c0501c00303802030341000b04210350914003004a9601c814401d1001482c28100d00381210b9200344041d42001220b205020720251684050261049400032070341c0110594a070f0005110380e1809100c018541d1140103014005580119420300701c4e4407030b0b8844001404101c50212046e5081074070600c020500010500c05d03025030501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 750863174 1250 750861924 750861929
    0x10021b210f010b031e10050406091709030d0201090503032a070510110a0e1002070513061a040b0a08070e041a040c030e0a080901020f03130608160215040501061e0f 72
    0xc400544c40d071704500d00c85d202c1c15222101d0341820707541c0000078100b11f1650b1000e031940b604482c0c954048010740500f854a513100e250708600c2031141c0c00140722040c0c414005c40348001e6010340914110b4440502c0541c24400c04010398140c000100849182c0110900141c403599016030014a03000c00ad4855980c116000d180e6110f213105410002040000e03003000c0c0c034051500080e110018540340145d401c81c100496030b0009544456185842e1121a035660032070415621481001c1900386041c0c801c180d001d1040d4030540580030030601440044901801100e27a03c03034414103040070725500070b0000404407007e001107000030f4990074200c503466082a100b0360190341a03d080c20081c10350240c0318aa03403041e004d60020f056160014800e45584d100780040c50010400b401100d4035140c41c201c01ea1f0792002d850181e6000100303808005452810094111a0020b00d103401a2084000c01b2100d42030340c450040c01543c1d90364a8000006070041c00d6001003c201917001401c86816007400b03400c00c168407556 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 750864424 1250 750863174 750863203
    0xa0314060103020118080a140309370e07030209031603050a05070510120207020a0b0c071a0906030135070f090b09070c1502030c0910021b210f010b03 66
    0x1090000c6d071000030322010241c1c4c01941c21310300320042500d0249903100e40024150400d41a04101c119000c4c103c0c0560046454688807c00500c40000b51851500b420f04c01c0900e01a00f481c04200d100c0d000c1d600030103c0e000050140c48440420320a401924549540f04540c2d507405403140ca410700106124920181104448283c084015800001c0c400600341010310340c0d0550014080085558041041d00100341318914280c403020b0400f5031a80f1080944103035025075400001d1916480701d0320f82103580001005000a0842e400c1001410642c4407440311418404101c00f040564540100001d0b041382c0d071888018075207107040240070152100c0941c8038002c0142404269081503440b9070006034848968502030000d68035a0030543d00c0c1d21000c44046102a02c000b00f44414001e0300401407403a580b050342c0610300d00aa00b00220f94440c05c013012400000c076500420041844c1c18426072003460190b900d00e44141000c00d4040e41031082c825103000c40b581d511100300e001418107010001080804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 750865674 1250 750864424 750864467
    0x304210f230d0e0f0d170a090213020f16080d0606020a050a080f19090e0c032406091c020a05100518060412030305101205070b090a03140601030201 65
    0x50388600c10850041d90b0ba081e00706a1280200502c0d0310701085862118a04081245c500010000e0043d04c1a141c842e8000410115000051384003910703400345200042e4085c2650320940007800c120002900030303505030300c0785a00800c444a20520010b8000c150680200d100f00d50303501c01401031004450080c1d00103000d40d001002d1400110742c000c195044241c1e017000d0003943c2e940d05022203071500d2050113000721915490540789042c2030f60200c040e00540340440c500c940e594450000cde403000e030700080390315103c2107500080410055440780307420050050064100e41c1454400000154084281c3c01c4050451088080050940c40c069070140d00900c8252540e00580c0c419103002884c40c801c070021400207554034029000d0310340b280012900146520350010b0b03034500881c6401805801c0540b07100d144020a80c50218030704000400d900c01e550b901c034000b440580c0c500310030b0381c2594101365210755104199a01c004041581041ca1711507419021000d0b00c201e60651002414604840f410382c1991100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 750866924 1250 750865674 750865727
    0x518012114090c041a100c020904060f0b0105190c0303020f073f11030d0f05060f010306060e040b0607020414090f0712020913060213050f0f0303040b0304210f 70
    0x26014113400005c0300540b0150500a00790105407030f032408041c07009401030284800c020600800b540700445d103030101e410038031158480c40011262070290104c0c80850018a00d55a20b019006040c0c65074081d00c81d080143c203080e401a052140c0341c204203820786051420a4071040c0c3c1c501c14241c910030045480f086a50031042071444443d10740c2c941c8031880c06011106103017189000c82041070b80d5017a101c1c081c007400300301101e54500c40a040140d60b0140150041c3c11400b80d80c0d0300038091002914201e0f40c410b01d041070410f04210250030300b9000560821010446a00580c031140620a14071744002d801840e5414000051868030496500c0c400e6240c10490043c4011241c40440c0d000103601151030303061684a989a20a000d81d18150050180b8800181004082c0c10b0260690032a6800c4a6200b000d061120600c120200021050341d0705400411003400040c1000025542150041203107991200d801c24100c0400c034030703984c0050085108040012820b5511624222501d00d14002440b440403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 750868174 1250 750866924 750866951
    0xe01050108010218191a180102070e0a1a1005090312070f0303050c1b010c12060e01090c020f0a030206061e090a050925050a060518012114090c04 64
    0x2c4d000315605102c0d0303030240f14a142c0f4181e80070f003003001303005030ba810001901d690300a9800381c3d92107141c40e1100541c60100350034540d030020134080211044400b00c422165035522242c0c0040098500e0614000f05c803035a01c2c405030f00c0310f1703070100a00c1d007a42d100d1030340e101c4880d4109464210001c07903d044542080010780e00141c40f0074000074540f585401c2c0466a52a810a0404203001c1c0c0a48500303600b002d0074900c8106481500100005c0080d034541d200000c009015a805554950003104890046040100821029944500c402182c28415540d19480e8013208600b40b030105001600183d0100741032084a141c95140c50036076500610840c055280c2e86004141030b840014180800c0c5952900019a170580510050000303007c5400c80c07416902400c25062040841401128002d0415140c0031800c2c0d8025012983c0070030070507810714102c101c154011200e80524903111115003d035031001e203050111501801d10062002d160701519403070045d480524085140d01210b05c04c1381130000828000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 750869424 1250 750868174 750868207
    0xf0a141204030b04021302131502032a0a020a0e010501030513050a06051b0403080c120a140f041503230709090b12070602060717060f09090c03100e010501080102 71
    0x180c0c0e01802c080303c03554a50002510050240780f00c6d240710381c000075120340b4000d00c0c00e4010060311517100c943e00c540c0c112000304070b0392400340e00007038072800d02101600c001354011440c0300034010500b1000c450500d29a94081020500c02d9030202c00071409500041c4119a01409000d5112440420101210701240c55265031510480c00180105641302c011440b0701510b000e07051070480008903c1c540d1650307a072130120b0441d80314044244042c050f42001c1010300c4020341c100c4150400c2640c0781d0b082d031081e403014860a58002507440c2c20f0f0880400001551032995409504250615140000e400906542d0000c1900b6100f200609c60300c0c64608200c40e0300d8206520200f40c45070048001028400d81011901d81181c45000298602c0f5403600094140e9000406a104004ca65580e044c0c0c26003a41140c01001c100ba14056800103400e207410140d41003070710b8259440381008080300c00096038080840c0c100400311200d10340740d9458107111140c00000b400f0b41030041055400171031400a80c1240300155 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 750870674 1250 750869424 750869429
    0x409080301080f15040318080f210408030717090901030b041506081e070509010305030301030317010b03041403090406080c151801030b03071d010f050607030e01031d0f0a141204 78
    0x3e01440c85424190b1201030b00487e0050100007007261150b6500490341507a5001c0840210b518030121880c82c0a196040e074140e030f0440b61154004e5041c0070f05076980c1204881510b03d100803998060080c48180e90f59503e0071802180038540a40030303402d160401489a8a400307155240f9681400c004014010000540130114550950380b5964401c0f0b1030511414624103030300440e032100000c1c00200034048007100440c1228403035180c0c00356484296800407200002441094400807003032000801084505800315070000116007900d00e4200b0840004003120040c1c1c10500055108250017095420008421004081510040c6003002149001c00c81e5443d480c018560405031140c80090389610200700361009000b41e050704a011b03040e05884641014070074441d05ca03240503601000103550034442e0440703500f2034040da600c81c1c0f03a035045801034002e005030381c00700c0c0c5074041041e03d501800842404140445980140908040d0f4107500740902c10300050b8402140c135802580e6490b2003542c00c4800c8404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 750871924 1250 750870674 750870677
    0x40f06061e0e0f010e090f01110c0d0903030c060b1810090f14060d0f080a02010c180303020a02040510151e030b030d120b120f010c21020c03090409080301080f150403 73
    0x1461ba20025441d04007600200320204a40c02c012001c9983e80c4500090401ea201e20380c00c460070301000c0442201d55181920029004c651102c8003000403c41d41e4000c030011a00240251084205601915a4408085502d0511a0f80415090011105e203010f40403e04070a54010300ca1945001102e1001c4000600140d10802801042c5010882450f04400803107400c143c07a01c0d26400ca5000c0079006c0c2400c10382c80c00019100c01c681076140001c1c9290344080e07035010f50090140001c1d0b41c2c00d1000810000d440e91a480034680c0700050134580c07503d90382348c1403e02c69440130b184200d0903250741180a00c1109c0a0309140c1800c2c101c00e07841c1c41c0051b0003400502070307150032801454004c000307200410a00311066007080c501c09a03030b642c60394000b44515107140e021000300803440c1c003404100c80d640b100c003a800540d000b0311980b880707860340581c0141c400f8001c0a015a46440d03860000602141d5000008450220000c001040103142c01d021801041060b10041c05100207803140900e60900c00500090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 750873174 1250 750871924 750871949
    0xf130e1203090c0111100507090806010506030f0a050709031e0606050315070f03020903060412020f0d020309010c020a050301021206090a38131b05130e040f06061e0e0f01 75
    0x4404050030000b5203030b190144102000b007400c000780d008127441d04038001c2c102c0b00e10603200009100c0c14540201c901c281245441c6400c203480e41501c900281001408220030000b4800012020070800e00b01140700c01000d030454201007456150407030a81d1000e5128034825040904121190529450842e5018015180000b40191042c100768024000d00400540500c144400c10007003007500300c003151202080360210b45c004050340b9011039980303c1003408040182c00920010340c00b9400380301210201c41c801800e01000c10340740d9020a003260070001010705540000024003200f030a1081a1740e401c089195001d01c041001c90800691018060b402500c0300640c0702c1500716004288a5107900c800e2005040c0c3d42102d0b80459214044c1103a000c035038000c1d00024140c20241401380c000c42c2e001000e05100340303161a2528407052181d50b0b00a0050315016402200100011040e1117094040c0240d410000320340c03a600191013014401541100407620340810901c0103031b41605a046046802444488 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 750874424 1250 750873174 750873197
    0xc0609030a0305160c080709050f06030703080a09081005040c05030d08130f0203060f04051c02060c0c0c09090304091107110d1e0b060f15180f130e1203090c01 70
    0x82c9130301091382030050000385201e5400700741c00d68040303150411558034403820310040e00c0e46003401e60904819149503505500c2100d04000103003081c800781914200905026aa1300e58030003425040940f6080d171402020b5848003004100a908018100076000540c010020520703000700180c941c210240802456110465562080002c1c844044070403590280c03c0c1c0d2113608210354001007180061b03034111f549004462007549a4030503084080d45010541c0c1c010000790321010584040c0d1f50160550340302c6400384481c002d0b025141d1408903801140b0060040d91740d2440e00e840788080311074000c2008070000e4101702c40404138103080b10000d060142180c9144d0540024a003107441d0301c41e500c810407888605045000140108144000c0c8211000d81c1c00d02ca4000d9508100a2a103240c2241140240c1007030025195000d0340002c55100b000340680107003074044459000a082014114404c16070540307429900c0c4600c41c00744900000000c0c00c10825003542000d107032030350300d60030b40040240c1000b4003a40d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 750875674 1250 750874424 750874447
    0x72603070204020f0a08090102030c07060b030f0114010603140c0a0f020c030d0c1502042d0e0f04030f0f120c020312130c0611030a0e0d05010614030c0609030a0305 72
    0x322900300e64000c204541c0c821407034001e102c0f01d4210907440804034450000090100c501802105d10030420005c0d81460b0402542e80c98000b800d40d40b103200d070144901603260300341c2c21003407243c1e40c0b089549281032010741d8507001d8000c0644d18000c00c070100ca45030501c103102c0d0002405045d10070840c0340d070504c94101040a41f00324907040b12030f04600c0e41807080306140400d0507080139100c403520b80100c03480d240d41e050198140d81a032103070340709000702c0082e0351509030368802c0074850303200180c0b03414103088542c0340d520110607100810903a1304125580343c42d02403104258210301200c2c07031119181401c08140030303a00b001804840012940c0042e164440c2000c00480d4401d100b2600c6065502035040b48038103005a2414100c45030480071101d4000300c01d00030900f58011202c240c074040400e4000c1d885c00b00b223a10115045200618640d400010301102000011401e008110250a50820122901243c01c003050715246c8039190150160008112420351a140400e40c09045034040c102265180403d401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 750876924 1250 750875674 750875677
    0x110a0f080c1618090b06010e030319180e1b0307050d0207050f010c020328031d0d030615050d05070c12051903020301050609090601120903170108072603 67
    0x18200640181d1407903002d100080780078401a6500070784071407031200741c56403044103d441070f40c0040c001c201c4120000340550310442c03daa158070000340c192818003d0400541302030340181005840406e0743c0e9110300520303110030200e0000401071004003040710f00340b41c00b900010960040d10544410070010004030510b00900460711400c2001c0c00c11951281e40e414056195801c112008641c1d50034940300c1214a44004199144400c4410200e207680b41105c1001c4032682a000c190028540c9503480c081c220040c02c800320035580082c10103002c1e01413400a005040350195044045070540000000341d03000c0c0c0c07190a5810218072281d0015150712480415100078a201c030000300707101101c00600c3c040a0340300024001a10100c1102400c0e25043c40041e4181e010034001c450b0424000d104007181840c02401098001c04c041c141205500080900c6606980b80c81100382c0c0440e07034986200320b00d42603070701440780142603010103486010700700303c429106811881c0d070142c0c41d07003c0c070079904104080510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 750878174 1250 750876924 750876937
    0x15090402010302131d0f011809050709090b061504060c0206090f060f070317061f23071a0403020c0d051c0908010b1f1202040e01090219110a0f08 64
    0x420300800f2590707a082c5d00524081c90031842249144020100e541c400f6400142410b84881041e0000c1c58038085000200a060130b000607280b40c459084d00282588641c85042c40c0280101140f000320701d000300c18030080b50195030324071405130300c1040200b1006070b2081c3c1040e43d051341141c80301da84a401c40002161207101c2c0c3d01c03041d40044000740c0b54483c43c40782802031158070b10a031220b803000c070805107500030700d003a0450328990407001c80049500440c060088401e001d24840c00c3c02c0000201d5006800c040f6a10b00703800e981841d10002d181c01c2440403101001c0c1082e20306c07003203250302c030710b81a40c1c02034681c0010700300740b400341c4941007000b81041014400080350907909120030302e18000d4103400404404603442030b14180c0d480c0071140343e000d0a0048001d1004038155004124a114220044510745501d580741c0451640c2404041444500550014000c0c204040c001d40ca510203120f242048001c145010810710003032150143d4a1500419401100c1d504a00409180815418002410301c10b01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 750879424 1250 750878174 750878197
    0xf1a010809100b1807030c170103170a230903100603020d060216080a030506120609060711071703071e0c0e0c1b0a0b01090c02070504051b0403031d040515090402010302 74
    0x1380c04001e02c40f941075100000b0540c0540c1d8440180040d002d48030085007080c0009021804032046040c4030841c0e0700018011240e90b0b10f810f1230080d04290502070b4007050303c221420b01070350006411040c3d1504020880c03240b8602d510412050b03113558006403142c0c10318800144080c0d008904480c0c0c23101036810a408042c1c10070342e119511a800c0b400100280301c2115414032032941880c03014410640080e005214250329402003c41e600da180742515100d11100320130784c00b486180b00110f012003803141000104006030b4029511345030070b0701d00f503241c40009008401650058282400c0401c126041d91001c94101040d40000ad4a03020030700c4826118451000e115144041650062010b00245010030703540545c50419490340c071444184162480c285004005a106007000d0045240680c040c40d0000300e00d80f0074101d0703060000b0102c43c0c503030011f0340103a0101f03a900883c042d0980f0900300c0710070b2070380c02150b0030407041c13522104071280700c580c1141507400741811000250841e402a411101c821004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 750880674 1250 750879424 750879469
    0x2215180c031e021201170c0103090620120f04020a0608040510090f03020d052106120f1605060906030f100b0d0606110a0c030305030a020d0f1a010809100b 68
    0x89001c00e01135444a01c203141412140c80001410f604040038501c107007002d50010700071021000c401180507000c00c00c010750b4019680d0508201c0c0380f034024000c6ca01002031220068032200503100313403403080320024804101482c52408220042e502c220301e12013070328001e007010f403100d4a480c14400d00d8200c0e20540000191b00e840e429400b4001812500c2400c540310b40d08407002800f0040044500b40982078030b402d500d000100b210316081110702000f0b83d0250003e41440c00b221104d8610302c1c600400003222703413a541c1000301340002207102c91031180064002591020700d0714015030089412440007c1c5005e0710300140c800032804001c50140314000500c803c400312511032030310404007030050400d8812480401c3d80c840d440d002c11000821407001e81904a01545a02851610f060707865a000611210b0b9040d4200490403d9403400c3c42441c004443d510b81c0080d43c3d00c3d0840b041000300e00c002070014180400c100400002c4900003030400980c0081c02e801103070b030100072400705d80d41158105d1081641c50f07c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 750881924 1250 750880674 750880721
    0xf05011e02012c100b0a141210050105030d050f0715020c0d27030503182e0e01020a05060121020a0902090f0d15020f092215180c03 58
    0x40001c0f106440900b8400d50b1103846032800b600d01218a03070250590030100304a0100000c100300b44100b0b56504002e00b0648076a032401141c6820503210400d8850603595810043c0031508042100742c0703480a1500307029290240d20407400c0d4460150302c50040000101788100c0700d00d26160b40545402400384811140400300d400d00c06007464945030401c0c10052400c441d0b406100c1518500d5000f10b0350400301440c5013142082c0700e01074400051040c00d0b00a500d084c6c000d44000c20782c3c0301d8150010480406c20900c0d140a000040175214119042c030304543c0400385c0d400201d000464000d0440d881c600c0490744817080d01c0311505030348031030300340207580f00c2c50900001505113102e8004100d903420031038180710310348078000400021170030001d07002c0e080d451803850307816074154141c4c010314601c0312680496080404810000302d0288440718901d48010080178054400c030710b00e000310318042581c48611420a402c22a50909000e1605d045083d1951030b6a884100c160007035201210488400c80c08400504 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 750883174 1250 750881924 750881981
    0x90904060e0303040606150203161502040b030a0b0117090c09040318060e190b04030f020d080c1b01360815070f050304020f28061101060f05011e0201 66
    0x580c0c410305a110740e820006449041c030109c100ca40f05660198840000300143d1034484401e809103002010b150703801c000116001191f480a548184602031001c01d0000d60400010403124045600d20181c00118040c001700e54804101e500b200d02c01515040b5035581d4508045650b071101c0d021140b8440c82e040004290540d120080410024058810080c101d1900c005620040d20034455070703088100922090000404800d101c00600d8001002c40760190303070b6a1600081944564445510341d8401c00c0d601c50001e40200c940a41c0742000d003803242d242d9082109800f08074041101c82030250a01d03c0040102840d1503125001034280d50040f40c940500d86d41e480a01c003403060f150200841c8a1000382824507101d441102e1045602410241c5007000c640c00748144d02c000392540c68030466460100d0041c0040c003d040d040200029552090303601341d248002402c640c800c1d0868403078501c007800180b245982101441c03440101c016400d076540401c0f080200d0051072403242d00c3c400c4074000e500260704074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 750884424 1250 750883174 750883181
    0x4030e15040501020f070303170705040f0f03151a01050c100f090b0a050c0910021009050124030218090304150c02090106032c190b0a0b0d08090904060e03030406 71
    0x1e0300280c08a55a0301e819075285c95481c82c0c0c0b84001000161030052484100e6403208900c2c2c0c000240c0c0c20242e05158441c040d050302800c02e60003154503090746400c01c00c14800c906e810400107409081d0304011004c08006000122200224054140003002071412414081003004414044d00d90100308042c020b201115005410300b040e09444d01044000400c640805522a05001c0d8959880181c5040d03440380c148800840300303040c240254003030324801500700541402440c550318420300c0000b580400c1008500d0440040c0c0c2c008c643c03031515608050005031244001c030301e0405000c0310112056501c1c04512451071045070000d44400f180800d100c5956034000c082c4640c454030032184030310542c3c1ca442c0220704403044c00050840500c50340c03118490030f0505007000702c0c40565140540f030b842c1d0125001c8484a000401e02111656990701c208020a00c00748070749080304504490010103000c0baa1164104d50240d040028401d0000001080420100c3e910072945d1326542c800392500c4c0e00c0c01d403c100008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 750885674 1250 750884424 750884429
    0x10050406020903122107051911100c080f10030c0611060c091008040804080d09090f05072c090405010902130b0105071b0506040f03060c0503070e04020304030e1504 72
    0xe00c2024011010200c01038107803400800f40c0150300b17960350148621a85a5a0050949018010104500b04803540d98410000c95034800d43c841c100a4508968980d00d004148912054041d1500100040007580b004405030045402d820b100c41300c0c0c82d010400790700340c0c2590740700a22104084c0030006005802400141e00c1103486000d50f245a0b4a10804100382d100b1940040c0e440400100002c1030b25000395035582c1c0090013103441d6400c060310b50b80c0017860071034030005032004078000200410422095000301520400103203000c0c403203414110800b400202802d05601000d01e01da01102894042041c600c1b101c44100802c600302c1400d190903e1402401c680347e0690040300504554261b100d424080c0c483c0b40c0106940340381c90846281c0b0784500303e45442004a04020402c60000781c00c0d559040a000070301600a800070302d1521350f14100080392292450501403003418001c1000e66038104503080341c541c2d0140c07009070707603680c480c0f030301726200d80b009002186d124915184c0021076070a031101400c103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 750886924 1250 750885674 750885679
    0x90312010e010f0614220f1d04030f02010908160507080f03161707110f0d0507060f0c0507030c1d0c0403060207060902030a0602030912191b0515150103051605030603100504060209 79
    0x49680d151702c1c0c2e9001408d4426048244241d0038404140080c2c030504910705600400d20002641c2a01a502c2100e10b50221020044111005d0601d00501005001c828010142034004000c500d0700c882c21241c0342e002d0b0340d43d42c10240100141c828180001c0010059405145592565032105540f50424004400a100e5400303074881e440740e02118240281ea20f500642c001004207151460540c003118101e03d050f04400400414004010010300104030040182d44101d01c2c584030542040201108031100c0c030b00c4080250724440030710503c811007008450035260022000b6948503031b176040040181039070340c200940611071600300900340119980618000c0342007005846292440002034500d40c041e50341044a41061200c20028180c0078000120001001d00c0308032075040381c16143c1f039042c104c19034070001e0404401010001600d9414103580b05800302403c0400c004e0904404c031841d5001c40f00c0c0320744140310b070010202e2080e540410601d40b102c01a914207201d54130f0940b61480203034128440c004d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 750888174 1250 750886924 750886949
    0x10609060201020c3309030703141204030c0f20130c02030904090c0f23040608030702010f031b05090405010501030506151809090312010e010f061422 66
    0x6440c0e2041c022240318803419801401407401c1c010a010600440b8040c800b040c20017404035010340c21601c4c40e903078803507071402002c0c50f12041c81d410003812420356038021800348581000f0b42c5003042112101240c001d83c16290a190000311458540d14082e0038800181035040d40010407a000c1c41403040241c0744050079901c10340f000840304543c0055492102c990005038000b03001c841014103242c0c6c82804c50034050404800c0700740d524041d070f1520b0013058101492104810390a520b511512005c4d000807624190303005c010f1185024440ca07101d0044100023410024202c80002e01d0034426005a8092a85140003900301410080c0c0a0455842032035158010b908141c000540c03580248038091103a80007600308204104983c1500ea00c5074002240850440c9096032150343c1a118a4003040c03080907031000840e941d81702c1c00224040c4102c140d001885226140340140076640c1906115421211a81000d07003a01004d41501070035805400c800680340c2e19924008505000c000c080750049984461079030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 750889424 1250 750888174 750888179
    0x9020c3904021c020904091403120606090907110a0c0f050a15090b160c06210e0319030b030307030f110604020f06031509090c10031a0415081203010609 67
    0x168041d2080000c031803d030007400002062481d0b002400840b40040c0001204616661080c1c4540020604000958000305403018109450044550441011540305040101080c0010481c0d100200a541003186082c540030245030f00301708065006910540441c00b02e070b2038500080d820301281c0700b00d80c40f5040d0401e000a000340000ca040ba100e001c2503507240c42050801c250840c86030310250f00b950801005807100000b1450f8001840017600442e500c43e03c0c200d10800075200a0014000d0f8900c0c0300d840c040e0030b1111490300004540e4105001500c0000740c0403010b409900034a050f0400781c0d014040061a8001c1550101d400c005001c0a61128000160b0180000380c0c3d404007140d0094112030a01c0585125207800000f071a8445001158009050074031004905022000d60341094035a00901500049140c00c02d420220b48030300e85001c0007800c403042c0c0c0312007201a40c07884c0180034aa90701441d584080b10900980003400b082000c6070319100604c042d00300c06030700074400c84000580300c8802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 750890674 1250 750889424 750889429
    0x10e1005012105070b030112020a050306071d030f240f1b0706110a121b090302061b03030c04031a0105090411041b03060513110409020c39 61
    0x54078140c910000c1c00300455800600780d40786030200600192400d100d180340004c1c100988400860107007054030040e80e1241051320620800280d10b4000b1072003900400200118150302c03d900461052070703807010a130554680b401080c180004c0c6012410b103402090340d1420308000b6111901200c000d40c600341042c560f1035070080d010200090315100f00c250360105004440312049000f0f08240c0d8000d8030002952003000070109019880080321102081c02c646d01c0340c0004c8000e1284101c0d11072500104100601c08002c000c0414145000080c4100d10114641d801e0901c05170b04420040022811295a820a840400c2050b0000d20040f00c551107245031480d2003090041e10a4100ca201401d03010598480d5941c0c001c000c01d240c003d43e90404d55640300c090340303403c4031044451214425100042d40c182440140f19840c41440c500501003401c10003100d50402404c000c40e422a201442c0041e101c08404010038140301d00c000002e11040a500d4501d04406107c0d01e02d20340f0005c0398810380d0b003a440c83c5810f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 750891924 1250 750890674 750890681
    0xf1c060906142814010e04090b060a0f0b0a18030516090612121115011806080a0f0f240c020d1806031509022109011107080904140702010e10 62
    0xc01285100f00c1032810484001c1590100090b00c50505000c4186d4040d440820101d41000000f9583c151700c1c80e05000c924105846440d019044404904115905010700d540191042d400034104014440b0441482c142e02502d266001d540d21009540f080c121907903160024120a0140c54003441c0341c008001000b0f0740010540b100194040520711644900d0b002c150307840e5081d01d0780716901d4007501c0e162544814100460502911102c140d10740c64081800c2d49100300e6600390401c4102c0ea11070b10503500810880039100009681c40880004805220f1600c51240500c81c500120009503c1c410740403040e990f0380020710042196400c45e007100010080c200c1d8500b00e204605d031400a02c518042c8800361107604142044074005a81c54100e5607245000030482c1c0c001c008010450301c140b000a0348100b15418641d070404850710007445aa04084102203561080c482c0042c100640001d403071402d41c42e40d801803000c4100e500d8034a40c403860845c00190207001c203000455003c1c0264000320310580540d11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 750893174 1250 750891924 750891979
    0xf15021e0a0206030405030c010603060515040e030d020705030d050735010b090103021c02120f041a0a09020d03080a1d190602070b04060e120f1c06090614 68
    0x300204018440c82c0c0038080d09034005081910140410000c14109010900a00c0021032003980c00195601e00701240041d501c01011ba032621582c140100003404400c00816110103152001005a0b03882c000e01d0b08500d10300c180207903447e0b8941030100300203030342d500222a0a0240c0c21043e07601280000c01080000c0078031104c00007103103440b0b604c0040c08034815000c0079081001041c100145444c17400148100c64000c032a43c203655031070300000c00888540c123075881c26400003402000c80354181000d50340e80c9074880604c1d40031100745040e44e00089002d4941d0b0407035040d041d00541101c3d8245441d0500402c1407130201c403810006420518240620050304072000c004c511501e016114070100c800c80303800c600041d45015203606400f80a6100810030501c20307031303018511a02c400980e610f0400714003810180001c07418100b40009200d6929070740c00110840c2c500d207a40d062402024103a0b04c41c0072004001a0300000c81c40be140c00c03c04640004850340103d000401122201d54122004501448200c03088 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 750894424 1250 750893174 750893233
    0x3030a11040803071b08011e0c020606030a061a06071406070e18040507030602030f0a0e0102090604030311071703040503060c04140913080f03011404062d0f1502 71
    0x2c001c084080f800d62050341080c1c40c0c4c078a03845000745a40d41685429204004200100c407008c1041e01483c941070384c0315139182c0c81c1b214005400d0501e40b0a001075201d440201c009001c968032003940c0314480011013046180c40c01f0081295071599a00d0600c201c1000702e90121100902c07078030300070942c0e150044950440c1e103031004040100a0003183c2c9004608000139200300c0e00c0d031140c19404400115207002031171203459650380d04646440c220300340000f5120030007605001640b0400442030140c8501c4201e50a032a01030402c01072128100224914208840e405824890b024492545485c0030110050048400c00c8046034120784498614100911891043d550651010352440b5414140343c074001d030340850f6007054207a07424110384805550ba440351110415005c0008010320000d410041d00000003407060b60100441d40c2484100e0b030b0714036454400900e83c400001441c5080c1c1a0b421403070b4000c1c0000085112000e50b0710500180f40f00700078420f010150181d005a05041094200b1a1140320400d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 750895674 1250 750894424 750894427
    0xa0813050d05130803030705091306050a050f0f030604050d0905030312161b030e0103060b031603050c09120a0b011505030a02090f1804031b0503041502010b0d0503030a11040803 78
    0x1c540680c0d840d4000340211910080e22103000502800500295104501c562203c90b950441c1004000300e84403850580450140703481400c1c405a01c60000b0b03401a10000e5408110742c2d50403400092490140c2c1c41066850321a240401c01042004101c12580d4941d0b91a03801e511910f4004040c0c890066400b804d80450b148000241c100030501b0b034007032070306650f402c28040007900c0b050000942940d4203015070100303460a5002d0002d503814860800105801030f001411821700c4c0490050610044400c1001c00d0b40310300120b00c3c031114402c21500c604200034036085800b41003280c5940c40d100886c0043e502a810500001690fa1000010704002c244075956a865a9964480c001c029002403c440e50001c68211516a40d030316080c84181140d00711543c1d00c680c610340341c41c00500456880a0810310203c0e22500d000000d1000425a001d8803240001c8001122041c40201d004011520305542c0c42800200900140080800254000c0da1044018001007903002e01078220b0b44140c1c4150742c0c0d103600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 750896924 1250 750895674 750895693
    0xb2b0e070f051e010c0f0b07020c100203070204151e080c0103090b040b04080f030a020c100b15030a0e010203010b0c060604060302010e1c050f032110030212010b0d080a081305 77
    0x312400d41d2860407814142808030001c00c6e2900001034012420440d030b54400401807040541e01041056603000702202c1c1a0042c0c03400c10303002500d0340a07055009000f5030b200c070b94030602c0f00c24031032500001d4030503000100583d002e40e04000c01c0c00340b4039100ea48218020001d4010070f03544a8060717200c2064028a007681e0701c0d143d995840214010040c800d80312041c05210601c8000340203070055000d5864030b90050f0b100c06402c0350050600d001c4030285c103406841d06003000c28684626902c036803a5902110b1301901e035039503291030501902d08980401400d501c000300201c0d5401d00040640170b01000c560450704140d440c9402d20044406500000c2d010078034200580500b407400601c0c20f042c80c102022161543c5480c1d41e5580e1900107828200c00c0503400115110304042001004500a81e0100d80d003c40d560900300e02d405140d510702e00001e030060340001d511180e821800d40001c0c01d854800307013400d0009034007801c0082d00d41d0404a80e40c0c00148581000c90944c00d01c5a1114960642101c00740c403110700f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 750898174 1250 750896924 750896959
    0xb0403062309070306110a0912080405090403110c010c0507060f1b050d0212030124020f0f07050f300703170711060304020a180b0409050c030607020607090b2b0e070f05 74
    0x32500601141cac581d1080001140a0f1900d42c00d441c081c3d4400e80b43c50a0740a07103000c5040c2000b80c1200300c5410000550510b80224000084a0003154480e081502c50000501c030300f02c03030000e0224485010701071110100c804020740091010000344141d8292801c2000303a119100d80e40c0700c00e21070a4400d0442503817214007803142801e0403494000c80d0040352188004401154101000c2030901d411580180604000d2400c0c030034803001110400307c4600e10000c41491992200344e050708140702c0c092082d00043d0015560070404035000c2c0d074211140c40040034001c01e0144696100d1002103c121510307040c2c0c401c442c00e2005c00d4a019a9008051150080c105082c012076034502c0b03500c555010b91074031688007850301c46105003081c450003800a002c881440c0c3c824546481d001809640456014108001c05903030b02512102c2907ca400364515a40c90151b01380489058103803034581902d410040200c180d0f141c0300c1d0b000440d41000c55040d20303001542c07410b400b250b00c0004c6c800d0a03005001c1d0f42c180032584 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 750899280 1106 750898174 750898199
    0x50d030e102706090b070203060f1005090c0c010b01170406050402011e0903021008070f0f050d0c120b01022a12072d0b0403062309070306110a09 64
    0x10041e41d02080d0b80b40400ae1580c84200c0303880000c1551840c044040323900506004141395058140b44140f651142e0001421703074150b618054000c2e803c0c0d4003031120866001d0030799213a0382e0f6503900c9803174003805460010022410021082d0003c58041805083c0403c07084080d07a0714000ca50461041c00300001c1124940e0091110300c0b02000582a44003012001441c2c00d0b14160b24110110041920503000d071009000000d424042d0b0075422550020120002c1032050005000202d108401aa120a107009e8110000407c41040c40708002105175002202c9801401030f80788034105200c000d007444281d4020301c10030412040070310404207107080790343d01d60001e10800099051409885040d04e1140d4070004100548070008450400c010720107000040d800030100321003034a40880305985418442c0401c6600741e00d00340ba40c500102484c0151090300c080c584492038200d003801107503d40c1d0b = true := by decide +kernel

theorem cover : BRFrame.Cov 750719424 750899280 := by
  have h0 := BRFrame.cov_init 750719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 750719424 ≤ n) (h2 : n < 750899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
