-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1984
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:13.53611+00:00
-- url     : https://prove2.me/submissions/50b84f40-ead5-4e17-91b7-c4bcc1d17d36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 356654676 ≤ n < 356834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 356655926 1250 356654676 356654687
    0x19050309011103010b0711060c0f03090907080402060708160b070e1302040605120603150106080703060506070305030112050a0219031506080d230a0309230606040e161e0b07080901 79
    0x8030341031340134808000c552274901c03003000000710701c040c4d50f405103031a464080100213291703000030505014800403d0400c00165213040c00c40b902039500c084e120382c945240c81412491040c20700c2c00202021100000e1020041e004400741c000480100c5120801020941100c0c0681c0520b100d030388081203003803088030f10354011244030035807002c070143c1120000c101307110808801340710030303800300c0003003603207007003803001465140c00fa02c0090304081d42c041d41380c10b000350350007041d40c0300500c42c41d842d00342c1003103d032001c208003481218001c0d038000748850200c11410002c118100c0c03c0c0d100440741c156000710351016441840c00396400300d801c16000f03013825804042054403204d603106d0b60b44060038001484c1d0700110092401424202c180f42d500007424210520380030030041e03050003406042449ea115040002c1c0340c00135400b0b6200d901940d002c540803004401e024038102208590300426188008040303104080810304081e03d00600b4000d00c00c41d607441c4000701180c8600c15002c0e1546404006441c219400b50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 356657176 1250 356655926 356655953
    0x20901062006010303030501080f0a0b04081b0a080d0b03010504170f040f0b070204060603140c0f0d091109010609060503040204110903061504050603030a2319050309011103010b07 79
    0x202070300701e40c0070007102089040001c240c0007213012030340e01c10040c000100104030b0701c03286840b808028038950145440707011a890300240020f08824000454a00110702211000400e8204000312140011546041d44064101e10132221000f854204280064901409150b0140c0d810920074404c40103090500700382e5034000700b503030802d0810410000940b114002941401800e0407418240c035854136104000c1501d041c0d0f44a54105401d1507440701c42c06107a03a400710380000c41101d040c2c0d034440d16150509003500958140c00c1d505850600385909210b481e40e00c608254000f22050002680c03100b00035561003805005da903000500601c00030340141881e40c424080048201c01a83c1001300341c80001e440c00208036601480c1c621884074404003400c2c035000d4107420040031005103040540040004207000700f10603051031001ca0341d00c14445d8a0401c001200c11403212100400d421011581000e010345e407064400206541c6418507014503100f03418141c0381038500528460740b52a4558881024a0700c03003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 356658426 1250 356657176 356657207
    0x91119030605060301090c14031501060807030b130207050312010b030403021902030c0d08071b12060915021b0706050a0f08101e0e011203210204030c0b0c0c040902090106 75
    0xb1b402450300400d020002000061640c1384410300c40d41110400c1c141000781840042940781446e6005010075500460100e80c400c4d00e52030000b03440407820000a1360502c000c0600800580700003082001d200c8088002c180e01094220105582e9985051401280c40f0031203001d801a0080c0320703001800403108410014070f600003011a8440120f00c3c00207960307034000040446100e00300003000800c002c04030103622090407010240c0d000b02481c0c6000f0390ba40c0b20b98850001d0400d56a0f12003281001001c50103940c409178001c404544038406056a2903040c4010210098640700e400800152144504229030507135038981c0e02c6d0700109400110a880300f00010b0f2010b45104d4001e200880c0b19150460305001c05030306440ca14645c107151103203405072108182c211001e510300302c10401020a401c048072114007000e0390002151380503c0514900240a95040188007c50700351001a0f0b144482c130242540b001c07118141c0d0601c1800204200c103da000110007034110103a94010000a40103000d90006a0b60 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 356659676 1250 356658426 356658431
    0x5041a0f1f0c060b220f15060e04021b06040c0b030103051f0b12010f0e011b2706030b040b03060708150312070803010807050108070507080306010509030a0501091119030605060301 79
    0x144e0000507041c004440500651200444015291081c1ca01502110030340c4007004214400c0d140414540c045054003405091040c0c0707201100554890b9411038440724181186e40707100400c11001503440d1141501e041e25141c49440340410011050b40480b4120380d8031000030301000b000540030410030114440c040355010741d14601c46150703858a030181c10b10091103200025080349182c0d01d1a0071100c0103854031070706a01d419511070803011200500c02108200c3d08060310340c090b030b400696000c0c4c2c42103200340c1d10307802d0745400004405030190800c0c414000100e0f000c1c444590000280369131480d007103070b07000700040c0f80300045001d0700c80d100c3c10b0665520000d810340e401840800d11269aa5020081c1124a95400001003161030760602610740a00402d18141c00517060200c8000c0c158010b112010b0110540040407424603805503003210340062000e0103030303010f1100a00b00036008010300c60003516404080c40c1c095090789000c8805035208080d00e00c0c0c0c0d075152421620b41d00d00500c1c005003180d40565 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 356660926 1250 356659676 356659691
    0x1803020907030902040614010c060e011b080603100c0507030f09080a0b0a0608010605090c0a03090b1f0515040621050f0405010b030a0317070905041a0f1f0c06 70
    0x315051403181c41009192404149400507106200880d411540711071a41c00c0700d5210318420f03a070b014000c601d480e0380045000c0f03103001c54090100d0041c02c4000c58440444406000340e044035410242d0b161049074220305940310b01c0b0780c00c40c03403105445e081018000007800c208443c50010740a900a102c03d005607107000c5da9030503150031410f8905000202c043d12140316903c200103811920f402f480c405020741000030b01400d0715240c0401c8003004058283c012030400450b85d00c42d5280b2079030125800c6178001c07030304409900382500400e83c55240c9000d0b00382c200c0000b98000c64141403a106002e0a1203600c1c01e00b41c40d081c500a0300b11a41c01ea600b413001c000620001103200c02c6180c90040b540180e104090f454441d06051400c5402c440c60300d00c0d941d00a422085527003000c40c0c1c0003030050f8103040c107989110f40140d0318603004644000340364000a03400342c50420760040080c1e1a81a848010748207450390503800c40c0343d80411403582c21a942400003c1a4034890580c000d21031070306450194480d85000c035a41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 356662176 1250 356660926 356660929
    0x203040c06180b220b04080703170c0303010e18011e0c03110d1e1109090606070f03021b010e0d240f0b010909020c10110d02030103060b0a0e0903030106180302 70
    0x950001100213052801198028181c0c940001640000d2400c0c1e5000e505e0989403882c03054681f00c2c02d10014080241030b12000c5c08100f41c55040300c40c5112040c064a9403981c540c40c200030140d00580300e031840c41812810240401c041442803072000703a010549905003001000f100e0b4007510500560004140d120412040182005000391010312031600d4042203540c04812091085c0c0c82000100c02010b040050b41d030254400c61044a05400050307034260700907602c0c400030440300d00c140d80c0c0007810480740c80505d0050547c00329802c0c4882070000c1d9a4020b02c001c05004403808031076a00020761050600030f00c040000d80c2c40808980d0007030280741524414506801e8070b400c44d01a010740469a80e11000051740340d44c0c1c4200604040c0c100b07090700b1800d001d212600b0341d503912000300d407180d18150b403042c01c83c035811441020785400080d090310666807503840740b80890150000c00352090140740400808140d10f01c135010180d10a8400d44015400d5070300e4010206c07030028044a058040d0f170302906010000d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 356663426 1250 356662176 356662199
    0xc02030106080a0204290d030c0803100306050c0f03130501060e0c1306210f150b09040615020a0b071701031a07111506040b09010f14040203040c0618 66
    0x700500302c041c040c00748650040c0400e42c0c2415103006103814614a83c000b41134105090340f44555019100281c006002d45015601c0c4a600c240140081c05e001c4200126040c0c0c15000b4002d5034401c400510480d12506101084c40c000e40051f081ea0b04824400240102903005200f404140128004180c3c01d071f070f0b81880c40da01b0000783c944010110b4001110918203001024042c0205182e00d05522480711450030040d17500004007d5040260703c0780c8900301d08104682142c082d5445000c40d2a00b015550200080c540d44101000c900940c14903400151070305030000a10402001e68001e00504001a0f48140710914018220414401c40071000303038486000b400f595011350302c01d0207106140e01000d1400404140700900312010405111031060031901d01080e203642c5541d09060074411529400c000802130001500c2c1260486c2a0390700025148568210300d008940c08060209031b00a4160300340401e9220407500506040c1000070308100ca240301c4d00201c81e40000140d180740c0442e895460300d001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 356664676 1250 356663426 356663429
    0x140103080703080105091e0718080102040e011d0c0705030c010f0c03051605041401020106081c091d0408090f03011d15010f0608041a0c18060a0e0405070c02030106 72
    0x40c98400071480c0810150020007290140601319110700b124502100c1c180300c90005941c890802070307100404036040e1030249240c401462500c095401000c0d0f00d80101c0d6000350400e22401c2104501800001100c40c40c0d24880d103082007608024001c00d948407a00040c6a034440c031000ca400c2d200401070740d1440070b001c1c400c642144028003400b244031445094010250380014120000d0304100b40e07180843c03141c10000f10341c21540b0040c1c1d400f2090a180e80142c0c010034035580000183d0182d0440d004400480d00640100200103845030243c094403803844010b0071400c000d0700d0540d11003990101b000314594101800c0403100040060b80015000c4002c40c1c2514800d09103013503400702c07103120060b150701c0501414410000c044a81d0166601d0040c440c004121284102d5052000c2000843c00317010f13012030307d656044000f00780981c1c0b0341401074500ba540d0740032048a254450381030490300c20a26009080720004102075580e001c0502c0d40a00300001807034064a03040501040d0407003200141c40a004500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 356665926 1250 356664676 356664683
    0x200c01030b31060501030e0a030305150d080304030f1b0b1306020705070302130902010e04050403020a0c0b04090f09150b0105040801090b06040e01290604090501080c040f06050a06030f140103 84
    0x1503501c02d50311410029290540c125905050828400f540001c07000188260b1880e058a404559a21550032445040c9103111506812520081c0242c0a0040410003140120f1180d0341d0890350440050342202d00b00c090850341408100310a009101003030100044a8100204e42085001c2615030f40e80c001c100e0303002c0395089545810681081040d86070003c441c3c100f0689a460500003100e40d81e00091a04400410701031080703542e80d002c1414140b007000050080c83c2d1103980701c1d00c0e2a4480760340c00110381241c4211510036081182c40340902170140118075659a12004403c0030050706408180500318480446040140034000028821400d0003175041c45805024800c0003400d128043c041691407900c03407611386a04002081e808080c5c0110b01030650783d03401205108440d44000050154820755014202980c00d00e8000700d607691000c03d0781c0e04101821901006203084070310383d42094401c140306050780040440300801042d4000e4000c60603003103c9100c00a8114400d0840c03c408200c01e800a4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 356667176 1250 356665926 356665999
    0x10b0c030405121c0302041214010204030614180c0627060415091d0105150f030a23010f0513021201060f12060e0c160506070807200c01030b 62
    0xc02c02140001101001c0c1c1301300c3e290540c600b509080e520404030140700402440c100d000d00f2180c50f02c9200798150340c051540441c040c0041e440728041150b200c402650100d108d004c29082e203540303258000580441c000700c0540501d040804070440501c0580c00341071291150a007030315400c882580c590300140050021801e0050380c0d0040c49100070310941c1d4940011510108018000b0076606600c020a0304540c0101d8074002c03601e02400c214900d90040c0071411080d0b040100c24480d141e00c464120a074403c100c0b4440c0c0d4603000d85142880c602003801c4c4210488180304100501c81c80c140f420518900f0f9421000141c17810040c034102509880c400d81c003481c00a01c1d424070007104141e1010010350002d142e49001e103c0d1300d003008403988185001800c000c2e0703060380002d044505507403400d0000d0040f507044401d5421600d01008003404140d4100c4d01000000c802b018085a09840030010300a400101070007002c8590003000150f000304111400c042c0d100a02d1042c0400c107107000d2801d44c50708190000707036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 356668426 1250 356667176 356667193
    0x190305060a060b040503070506091512012c01090c050702030a05010222030b060103090303060b030406050105330c0a0804240504080a0b062202190314010b0c03040512 73
    0x1d01c085900603000040c074420100001c0140f550009021360036510211050b81c2d640b844a400034139400700341d1030007032401240424a001c200212501d0f80d81250b90880481e407800b04020710414080b582250169000c502c81c0b00140046001070f80245015401420f01c90b2030a2041c1d00040c0c50559841000c40f407903900003a85280d08110301c0211100344043c0700c0f41c600c4907801c640d0351055000004210310b040542d2109003a0034944a5000540144142907281b0b41d03c0c101418500c1c0641006d000307807070288201c841c145040b03007841c2c071060b041c9100003009501c200c8030960896079168419900404140f00e1a54030b4404a08103a000b80014070014258000c40c00c0c1e01418001699000c120400503c035041c0000c10a60002003240781c00658030252903843c0b59240000191f807580c00082e0a4001c402406442e0030320385070743d4001c103010700c00c17020840401c4203041d0303080301519041ca0320120914403100c010445000703114007401b840c1c4c41c0e05068905082c2c40d000030035242e0040e114481d145502c404071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 356669676 1250 356668426 356668441
    0x71b050c0406050d021e0d06090305090f0906060720120f06060105032203020a080a0e04060503070f061103070611030a0f0c0f0f11061e0c1206040b19030506 69
    0x81e00c0c1c0240002d40365101364045036000a07100c91030300012070710112500ca245081c95601c10350407103030090f80100200401c00d19410014015001901a0350044042071482640c914019401a100e86001084185001841d0361243c911508203006c45040c3c13031040303501c03000c0d03039a81c0d9a80703401c00e025180040c181d170001143e61500d03044010700028184182001072013846040005114111350b80510b104940c8512803034124544010098080c1180c038000c681070b0b02072030b8091618500f202003114280821900c480425840340c100384118110310030100c01c10025a4090412803929000000c11750381002c0300b035140c2d2000e65501c80414100c100001041200103d02c034481d60381084100201040304c02c3c0b03101c40103405400401c0148040c40405c1c00443d0321644940a21161624480700b030307580500b4012142c50294030300103001c582070b84269000951148180e1f0655040038904c0d01003d055403680028040100155550070303400c91900907900c5640020b40342e140b00151b2180d00140154500a407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 356670926 1250 356669676 356669681
    0xe0c060d060b0f03040c1a0d1e110d0b1f0e120102030906011703072003030c010213030302011407081b040909030f0207060e09040b1503100e10021c05071b050c04 71
    0x8003c07140c113001c0e0b940d2031016a80147d0a94244d080300f18000203e4544091200768140c07030160101d000241050640701306800f0307c102a201c0700c1540b00c2e003480761003c0041000706011060300100f10403824003a6400040c0e03c40c0d05281312401000d404030f00d4064960f0b00b11420382c3d0084a071002d003584981c004124049584032083d09a29114001c1e50800000c0d030b44044480410911250a8140d410b000710700a54090049445080240c4c00841d544c4041130403102085070603100170340141d40303005412440d01c034144102500c40e070003960b108040e9660741600000480ea64a05c20101c9403c20b00000c02c0c106041e114012000c2e0080d12101d59110400b10000c1c5030107803940041007008001c41c4109900d0322000035264000741d11000d142940c4d500d80074500c014001c1417000580c140b1411481800d010503d070700c941c1c2400340c01c8042e24040f00300303032003c6401c2e48104820a5600c0003c1030900c2c07204096548040e810601a14203c001c01039920b5451103048540e03401522190040203940d44140303410b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 356672176 1250 356670926 356670929
    0x3020306060604030816051c0c050d0c030f0f0c0b070309020a0f081216050d090e010f14010c0f020424150f050a0309020603012303010e0c060d060b0f03040c 69
    0x4071441e0386003030300b9559144903a0103a0540c8a803040b046c0c000410803c04140a01008608856040d20f240c1041020060501102580c00d076101d01039041014001441503001000050705526110010021a0002c90b1050280c0980b403081207030101012001680d00c900403030050229035004905205640100001d000c01c9a01c80b585003080c00c0720821030f08d0f6000c155141000c0e40d03170401c50f44400311316030004c10050348203000602501500090602d0b05030042800f80654184034144c1c3c800340c0e2200410000b412480c0075419001440498000725580700b070341c0c0517400381e206d03652142031016558003042c01e680d400b4404200c40381c1c07104200c40c0c000d180007034030030000c2811314000c0011560005014247c0c46038070010100b003040008079a0310320783c081d410620f4040e030701408481d80d960351612600400f8181414407102c903004001000700c9490140104088106039401078a4820048010171505030320042e0144102511000000390506218010340a44d003444469540c1d40d2506280c052824102c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 356673426 1250 356672176 356672179
    0xb070e041a150f040f03061d190803040510050c0a0201150f060305100f03081206030616051b12130509150f010c080d0f11160b072102040302030606 65
    0x241402660281d54980030075688600c4207414683d00d24800c0c00308403d522540d04203070010300c1c0040b800410000c05601c43c0d4070004140000028102014401da620780c0d0b8542c5441c00310510280d01e010104030858001d5402910807021103481d00c4c0019030003415038800316004070704600d001c80c003100c0154080c013810f08a104640c000000c400d041074034102e1061030301e0048e074080554a80001e019404504481400381404c1640419801d03039070314100305e02c2d9104070140d600d15864400440c0702030800180e014000c000e225101880526108801c40f5690490b0b8508070300845240d07045840d080c2e0500011008002000306242d803450802c20300c590400e45030740854080c207a80d50800140711440001c030000c480d000c0300c7c4280325844100040f900891103030000790200d03030000303400042800340e47e01010241483c0e1a0034400d144030580000c607580a502c2d9034601ca003040002c1c0c600010119042c603a403200c043d0800c1c60b115060304050360300f0340c0da44600900040782d00107014415403500304a52a0300420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 356674676 1250 356673426 356673461
    0xb01080703020703090b070804080a050109061805030904110d0c08010509181e102307020d1d0d050d02060106110303070c02010e0a0302060d0605091819030c0b070e04 73
    0x105030340017050b1903007500c10740001300b8000c1884020050f0320030407a4006d00c000011202030726103900b40a4000e0000d85800c0314814034010204503000f41c48035440b4a2281c011000d9070510001e041800080e003441004401003000030020307404400c98501c070b0802c1c0301c417483d40c031a07400c0e6041500740199038402518101c403020b40d40c0e24030060040700055850000120144c4100041c609444061800d034103c00d54900550821514240407100c0c10040d41302c09178148403015207501c40301401e0740c076900349500d05c000191460300544161169415038145420307002c0e100e1a001ea100342c540c542070004600b003402c0181c0100004000c455400340c501ca88a65a004c003451030341c02c11b81f1002e8151101642e0003030601030340b87d8000800c1d9491070b01d64001160043c048999410048449a00a1209001d828460f40c26a0003240c0c11600b030009502e01c04440c0402005542222042c1a101e00c00200e021000c20903000c04460000c0d810807101c0f4043e09041e02ca083c00c01081b5004c21090f100c0306001000001e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 356675926 1250 356674676 356674687
    0x150315090b090102032226090f010801060e0d02030a02060c030901081503071520010219141b0708030a020102040f2916051203100e13080307030906050a0b0108070302 73
    0x904401245c80c0001b41c0b084100503a0442c0b4281c1c030b4104c80300c00040d603940e00702c04a00600c104260020861003034200e0b0070b42c038213202c400019100800c081c018280000c000d103041a00c1c0707091203164030100030300040807140b8000e06640040c0d4a5444a1500c41c160f8101040c0011503581090f4401d0b0442c2e084250f14480300c007c6804240c1da01d40c80e109110840000d44120120540203e405004c40c0c0035540d458400020f2120f1100c0c080c1d03100e11460f64511008040c60201c0b90b2040101810203241d00350040d02d0000690020911402c0601610503a4040c2200002c3c800400b0001001299002d8001586440c5804101805610f0700d5102e00510070700360145140c1401005017082c02e4a0b6005012911801146c0e0102641f14aa44006046210751004008006145030186100c0c0f0035940311891041d40b40d031031401e008081501c05440c1d1a0000c042000040c45240107142d001f01d49150000348180d1640317540d07003503031030940f80780c542d0990782d032200c2100d540d220380c440e40d204035a42010f5140a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 356677176 1250 356675926 356675941
    0x50405010b04080c0f2b0c0b0a081308040f091505100509280b0301090606030e0a0809131109030d05031302010806060c06040c060e030a020108010504150315090b09010203 75
    0x842c84c004031248200c0c2400e01010385540c3c2c1c0302250910a01160355011600c8000760008906804864161070381044d813a40068501c007121300300d8403d0040c9545030240c0c1c0e220002100803214400d203084404080600c00400c1d031060450f5040e00070710204030041034001c0d4151004a0400550b00518010b0101e0811201d03501d420800311003200c2c0d800c1d00c840c4124004c040290208c070742c01a840030301c107503401a8000b61140c11301001c5c5058503014501004a04d0703444a00794121180d0910710041500b15034415000310301000c0103092040c40181091001c0c2d50344940d24000c45001110741d8010741404122620103040402442e280c4141d43c0c1051491270828280c070490903000104000c0c1004a10320000f281510380e102550a0100a0f00440e825400d007441c140300e001405001c0c08001644413010b42e04c45103070000700c0407203641d0182c50340f020507403c003410300000d4040c0c2101106038090301c000010000e44c44209400802ca030810000502c54402d1406618206000d04002c0b01a030060047c044031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 356678426 1250 356677176 356677183
    0x50708010906141e03010905010c0309021c02010e0904060b030604030c03021b061b0f0f0307021203040b0a080a0b1801060f0309050705010e0d06020a08010608090f2509090804050405010b0408 84
    0xf00d40c030a00f03990413204c810000c1d0140200701802001035080c001c0c2010403540640011001600c00c40345180c1100e07454050b40b02c0c00842c05000790000704400202c12032800c00b4950560071900078000855100300f01c001107890410251822000110984490801d0580c140400702080c00f0300296080b1072014140007500b507010b00500c0c002411128041c1c098000c0301005140c4011542c031040d289807840840010391a500300c448182d0052015125030f4011400120440f0309442c45020100d04103000c050040352084001003151034000e41e5900b09500070340d101001c0100b5840c200c000c2620303941c1004001842c100719281800145418181400000f40c008900241520710a103401401c050001d00080c800004038903002e40143d02c00190006002d51000c05181a81c2854940049580300c00c1802c1d6a500d10380100d40000e6001100c02c1404081c43e5454a401014901404001151105000004c80308050001c8603044000a03041185040901480780102404080d07075042c50715201204d1f45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 356679676 1250 356678426 356678449
    0x30b0a02090d110307050a1211090103080d09030e1903060c09120204150b0c01141305030304061d03040602011505030a02010203070803130f06140606041208090a080105070801090614 80
    0x40d40900011011340b02013007030a000f01401020400d8450b511300760b940e43e8080482c01030790f20003c852520724440c241511228100c0707610802071703850301e411210342d078009080400080303080020780007070030031240d8170a542c81080c0728407640a810807074698544103040f50041440d5405011b40d034541044444144400805140d40642d03002c0350400d03000ca6450300300619500700558040021402e40329614055110055600b01f541c000c90303081c1c8500c5001c5c202e0b0807506074001c00c9544200001070014806030400820f0a00852000c4031403003900c041e080c00e40e00203403c42d40043c2c1d56162070901e10304810ad140c46c010603003a03024103800406500001d480384510503001d00a9440040413074400703210410045860742c0c0041402007003e420b464414041c0500c40300b40741d042c3d032842c0d0208140e440e041080760101d0b00340060a4000804030b0b911141e454100e1007000e5440004040c0014440600303004152180003955511300c202d6040c80c803004120b03800d603005207184000d0140040c20b9a12840390124 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 356680926 1250 356679676 356679683
    0x41e240f0507051b10020f0a180e0a1a030f030904060509060d080f04080304030303090302011416110a150501080706020706090506030637050d02091302060c1501030b0a02090d 77
    0x344da07640400f00e5240407119022803900074400100410000b0345a400b400d5004060f94030341c05604401070720040c40307083d01d000b0525054410360208042d000c10350302110031a0021011204003401701000a41889a003407c200b2058100048003e814502841420054441169245406e08102010600d24000f0902c01440d01c540010241c1d4500300e4541503800800c004011070b680c83d0b0f1649001000340c1401c15045000d50700b014407040c2c01c1300411858500c80c0940c0c400c42600070140d0b40c412030301d1038200d90400340702d401070b050048045640311900c600345440c0c05901141035450400150f10f0803149034410011508040030512061f54407129840854100702d0703080d5181d40303d203800100c1101e42404400500342d81c0e03110f20300e07100321038503511b4110026440c000c01a035a03880e001d01c0300344240388070005e601c240d002000900c0240f030300b01822100d0340040c010711300f40010810440d180503c07034030206180c51103d00c0100200308803040d040e640300080440540c14041d010b40800c444055400005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 356682176 1250 356680926 356680957
    0x180e0a1419080a26101502190206031e011e0e0709090b01091706100902120604050a1104030309090b0105070506060d02030102130f05100201050f041e240f050705 71
    0x2650035a00104442d218041036078032584217401c009488030170130f402c14400c0c4203074460031100100401b030010400b4000240004169026003d0680c20010107500042a0704400740300d0460a000007401641d00a01a1182280040100907100c41d099991140c079406030403240c880030200072901e540031065a040302c1082c50003145440380240160751010054110344d06500e542800f110201900148076401820302c11201c15a858954070581d099119550300d0012420201c0d0225090303080ca540480c0d4010986e22002814900f0a4251506640030f5402600002c554040c2484400440c0c480c0041e80c031000d00b4120714040b1140d03141901c412005000a208489038484281992001c1d011a500c1c003c4c0e251501c248240c503041d0316000350800f8081c25002c1d0454120014200d801446000c0c0181603000384003000ea030382daa54940442600858a01e0320700b10801e00f000001d4070218420081640d280007510903202d12400800403144841298444203041c4801d10440c0c9420030222204441d807090301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 356683426 1250 356682176 356682197
    0x717130306110d0e0303070305010b04051011160803040602060f01031a0403170702010c2606120102090405010b07030e030a080a0f0201090c080309090a060b04180e0a1419080a 77
    0x180c00c03003405210301c080b00c29030814401300740c503180210040d03103e00c226840400039a40c0b18450102640250b01895070010851203200311220702612049c1d82044681c400c9814440c0c074254103021789c50043d8403030f126650012509001c12038040c0600e0344d00c0600b60981d0f1205614549404003004100d03144d045028800c8000f140508d885040c09502045041c207070100c40c0e041c4084002c4c000d00c000360070303000001c483d800c4440754152840c41f090035858208900c82490380324802040744882110210940e0703503500700300010550302c460240d240202a510303442c0341c03a0311032824007920460440500c28842c0c1c0001c400200054002c0040e540341030003d1400040c00700f203400080c1e004180000c0c020b4440e507014100020b180700b00000500304130307100340c44001c00b94660103880002d680c40e9020b80345a544040c0070600804000301c648800798120700c1d002140e107242d0403140e241881500142569a980705d28941d0039869801c000605211a8000d005403481c10103403900c0c11680203121041d0208150603a2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 356684676 1250 356683426 356683451
    0x30c1b0114010f0602010c02030909010e06060c10020d05091f0c09030204060305011a0a240917011505010513090207240903090905190e01110c030717130306 69
    0x900201c1e42205101552561100d001d901c84620b140304880041d0708200c152010544007100740e03030707089001a0041c102079092180c1625110802803541e82c010701d05001c1d14140c07071010040c1d074110301c0411400580c1c071540301c0910401c0e110010b0000710103500a0720469541c099004800210000c0f0540000c1c0d01072101e1000c42d01c20045500180d405030801e100441032200c10f41c001c400c4030b00790303d0042c4060944a003d10030400305a103d80000d45403d4112800112458011040c42c000726181c40501191185410389260740a584150240d070b6503119901e114509203641e10f000380009080003030500c05003c0c8101d6071502107004401020703401041002c100318215021485c101c00c03283c89002e040c9130250b0840c000f401201d8080d00003c8001500003920403062050502414812643c5c0d00059100031240c80a000c0d07900412001d5075880f0701c82e0180d065160054814007940344082c1d81d903220f02d800e0040c80860400e01a038030300c0104200240d15484000d101000301ca80c00040490390401000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 356685926 1250 356684676 356684681
    0x411040f06030308060a1a0a0f021f0b0102070b0f0a20070e0a06090b060d020924280f0f110304030c03060c080417130816030314030c1b01 61
    0x203203005445824090702008040c3c012040900c203580c191102e007221507462160341c0f5034681d013031800c464440d010440c001c141803140200c441204003500485004002c4100322040307402c0d8001c11180510b80c3d40200c514650790500111b00180100d100c2c40d0b042020803041400f651181c2130011061190b030703071a00211140da21261104144448080d00c002c0c40d501e1801c40103c00c001c07200050924981800440c84c040707144119101c50001620745801d011a0b034a02200a602004095a11110220030a2060340d0000760000610300700069517900c0b0312044412016101d40e0001146016034100f0209007043e0740300c007248181e40450319008040c0c0c010010251001544001d4800a6002c00240841440315402100080f68807441c404c110314003082600b1200140280c3c5c0c0140300c5150340007082408d0781020081c1010391502c110801d0020740d41e845c0d80b0318109821003070040e03400c41c8007404c1040c5070700300c01400c142074040980c052451405841d107043c14851040f98000b544146074541e540f420095 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 356687176 1250 356685926 356685941
    0x18050f16030c23090306070c0506040305090d020901140102150f0412091703040f0b070302061b042606090703050706030203150d0303270b06060309030f0307080103032006041104 78
    0x20080b0350b0107112034030f92449648640c0c54103009205100128042e41e20920303081d0042600800605130580b902c0e6000c0b20b280d400610b04c42d03445103c0300c14030f002595031b440401d4000c1800c1c007441d548620b43c84001a060400d10040326002d4500c40003009041c070b80c8a0141c40d0710035884880410020103000301513809000da5044103152280840480513845400001071056640c80340c1c481800f56030700c01c00c80c40ca900c00c4002c0240143c003d4000700b21400c0c080c92038024035544000380305091a8441d1f015496100000184850260105a2034900d5030790600807070350041040c0380a499000d0854941c48c4d078070b41303291055034109540000061001c0c41200020a200d08005110040c04076041c24018060502042400e012140101c0a4211f12070b1007901184516817001e2622200d95912040000715000180b03141014003003000785603a0000301000840c414840758440c80442d5045090040200602c04e6890444c120381541007000d80303c0000e6950781c03155129091164441001001c1805407101c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 356688426 1250 356687176 356687207
    0x2101d3301031208010905011811210117030f040e06010509120a02100801050d02040b0a08070f030b010b090105030a0902040e0304170f0613032718050f16030c 70
    0x400c0c004000c0010809002c44410f007981d643c1c08142c0d8942d503050046403000c1c0310f03902c0c090003140e030715124501c40394220b2401c0145c1c1c80015401d20000110852070507240303c04140b103440c500b400501c07458400d07000803600e010031000298105182c03c0350401091159020300050584040005080c681c0315200319004030401800c0303003004402e910700050380c520b10080201d1142000340343d080d40e071f43d10a200240c100c2d9401003010901c65241d03024000100b08405016402161401c00402c0801c8104141030092240e01c0c2400f030f01c5441d44c03c2204120b0410b801c9061681010448511315a0f44442034a400c01250400001c00090520000b8001c00101090801900000c0b03030000c0c10948144038910b00e55080c1064506844c031351702c480fa880700011a100b11921a440d92003c010900c40e46c41c0c018191210144040c2c542c5507200c04d5184030841c3c0d40880083c461040503034411007000d025064001d259412511040d0a051148008400d240342c1c0107010583c2e1401000b420030700c2514094194482c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 356689676 1250 356688426 356688523
    0x30106200d08070806090708010501050d02070b0106051312020a05132306040617060f1918060b010503070c0b1b030f0405150f0a0c051902101d 63
    0x74200002d04110012200c0310081805030b4000388a0f81400c00703085106499554442c40180e08201c019034403500514500131410b60300380704800004144040580c060f0410303072203407610780c4902c00e82400460025001840780e0089400b0381d034010f0b2200e00450064420455114132800eaa001c0360070001c10f44a00c20000700d110100c00e4005105115004a00441060b40c0c01d000d0540c8a00f40507205101e0503002c240d0f039038001c000080f00705000c000c42a40120844500480491170310700307110203542d00e00c0400b04604074420200801c01c0180d100f6405400c50a0a00314150b140041000d007020b80e01090141180724800005282c0103407103000300c00c005070005041510b0342000514607035049002c42d41141c0620072040056900741d0740000c00382c45410b40b001d0792100c1e80e841180e6207024004849000081c0002803101c0384800035501217860101d58140c1c020019412000150340940c3c0003448400ca03100400c02040c0e504100109400201c8480842c0300014072000c161000446440c1c0301c0442c0c402d84 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 356690926 1250 356689676 356689693
    0x3090f02180103020109080a0512070201020106150f0206070801061d030f15180703020d1101020c0d0b0f060915060705031b0709140f06040513080315011404080303010620 75
    0x50020700680c10780c0e0003a40c0b482d42960b100c14010760341350390100000e003055011565854140d01c0c507000a155141c4184004034069a9844040d101030158803162404507021250203080c040d410032005510501c2464050303440d5140070000f801c0d0080c85803400340c12821071480401283c070108400e24850000104039031501c04811810042d0040a07290b482d2468250882012591400902e02c020380c2d40041c507041c6401c0d65941c80c024903110540da514154090580789a0b850759805480450590151880e01d1880c50040600b0300f040c00c1c0109440e204000010a0061141445984083c07204051300c1095840c40241041031450040702d084140d03142144c45509a40704020440f04210354218806011103950502104100d810031074050510307200c0301000a0300307482e0580110f60002a600740100c1c40322901c1d100c2c03400d00d50049404100d00200c69000d0603842d40c0c815109060500035580e40b906007030414204645910042c82040208604400f03e03421008031b00080621600c024030888e640b10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 356692176 1250 356690926 356690959
    0x8090f031603030b030a1a040f0b160f0801030b190b040f1b08060f04050c16060606020d0c05030724020d091101210c140c060f0711070603090f02 64
    0x207640e1440480c00a41001d10402480c01c3c00200313641c110b0361040c00285410b45c1242c00c19200075004009035100324001c0512001704514020590044048202280001c4a02500a805030031401e4040080068080041021070500461242c100000d002800702d20f01c08200c0305000342103038159490741b003442d00307690402503030856209240c0d1000c1c00440302c0c56054204010b0f503600c03c04880d529001407004030480c2580c6880e40c040c0341d000c00d400c10010f0a080d0b07030b0722103e800061148401c0303a21641e601070a005141e0100103145c0c4070842d80c40c020034540d0075913645540742c0c0100140185a6603210007051443c00101d000507036041d1409604540f500c0c25141c00c180500906081074590784000c0080400e55489280380400d420070041e249000c0703d485010040082c410001c0d05c034104010440060307109220000205401400c0c0b100500301c80c10171945005174100041c1410003404060000240854004288001254500d0030002194101420444102081200000c0d44030807100c002d003002c0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 356693426 1250 356692176 356692207
    0x80a061a091215160c2306101a07030219030c1101080105030312041b0b030a05010b0c0714150a0314061002031206040e0708030409150f0608090f03 65
    0x10700301140d0300074854202c03112890301c84031540c4803a8104241c00340043c0200600c4081e4640383e0b007003450004003068054842e0600c2c0e00d54080c0e400a070b40341c83c05004c0e5010808005454004d500e400e140140c040c17805c52290b078020b88440c40c0e04440f00002c925142458000e100c4694481440408001190540d180041c50003112100444540702c0300c0b0360201181d40301c1d130341f858161a00500103502d40940f0f94420b2061034001002156180e00c490740105038441c03c1103510004000700c0d088982c49042c980107a600380c4170160441031882105008410248178009290b000300c544007440c24040c0c00304040481c002541008040e0000040002c000021603803640c80360040e0300a0302e0302000781c0d89820b020820800e510511603401070f40280212040c600c0405015074008000a0001510360785808a007824040268800b044541010904001c0017540307002e0100c002c00c0c45010f4120050401c01e03611450b06490045200b0800034100103600b0074810000b031000e0344900001c0303c0e110009480e03160304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 356694676 1250 356693426 356693437
    0x70b10030803010e16030504081606110a030603020f0402071a180114060103050f0603100222030b01030512030f0705030a02070f0c050307060206090601090e0a06090c0603110910080a061a 82
    0x7007036683c0ba01e034445d669120b481540d00569001c032506207420006d03558001c0e0710540c0d0b803003a18600d40e9a2101e045a0010340010310b81008151000700f03110303240d8010403d03945a8003201500031801004014005440c0c0244641c4030415007a903221141c03550035000c280004078040d0030110f5803a110746c04000311b42d15038100c0e00c0751030241e030144120b0356004c040007401d400a84905d034250740444862281c409098001e400f60507940ba60908156001380b4110602020650003515400c00020051050140620240500c0007401011510b1030802c244c3c01d005181005103504100203000c00030a2181080d41c044620703080c1c100d0003004c0348518074100003000601c64410f4074801d02c00c440700007a43c24001301c0e485100300d00140c05002d0710b0b07203084441400f0301020795101c0b100c0d0140c03c4410001031240c2c41803a44040c0103615102e5258145000078007203d5422a203540000c3c0305001c0766940740e481d510b010003410307600e1605d070019440b400b1906000c0c281030b410900641c82c0d040c410400300c0d01d11101801 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 356695926 1250 356694676 356694691
    0x60606031a0619052116020c090c1c02070803091e0a030219031709031c0902060304060903110d050304060510030f0b09100c0c02010207080d05070b10030803010e 71
    0x9041c1540802040305500c40c0c41c1d0308140070450380b003030b10540901a1020341105945078001107121400d24981c411402c008440c1d1440349851400940b80c1d20f941006800c0204005486a031072500341909502258050341420440c0e41444580c07499200c0841c1e0140c41000d64003040c02030701c80c10019451a140c046004000566001041140c0c002c039034009004a45c0e15010380182c01c800d0001c40300f804104203106800d40c2400303001901c442c511918030107614032a40c1540c0c0656110300141e560101c10030694032283d00110b04040400b00540d407500d080700c0e001a0303c420b00060200d0b40303280035584065142e51241460107440020102150007800035845107204100410140d62515409070031144d05001c040c0c071040c20b070743c440400501200b00540e0055480130072940084e08003107003001610300007120000018007800040f000c40d60100200005010b01102400081c5000c0d40300400a0140882c06007940d0000008180d800502c0ca000102031a04070040710b54070360311030070068202013040c0e9840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 356697176 1250 356695926 356695961
    0x9041d060703051b211306112802070b0a090302010207050406140d0602120112150504050c060d090206040305070f09050402031c020c030601032f03190f06060603 71
    0x9510248a40300f458441c0890000c032103001d5060144900040d007001c0b904620104807815603005624280305442d109401307003080300e100b828280c900401139481c2d900c460b41d0300340c20a0011010302d0441c100849428125501c2002c0340b1080480d08070700d8800d4a40c020342c0f80b09c00001e40b8480c260f42c00303000c0c001a2070007030302240c843c2541c46003072001319501442a0010100d94001c0d1078030300c0c03a00c6e11880803000e00035007025003445889951110003040c20382c0101101081d07445d100007000030b05070842514803901070302006689019102c507911680030b039802134465440055480302d4030f006540b105e040c6a80150400d42c54680b00e25216548007414000d2803071030242c20030000344400e07050003200d2045a01501a1800b0034407440e40151080f00900a60f09600911816000a8504003c650b000f903000c0e083c1840c103c40305102d181c0700301c107081c0034000c000010040754103082d803400545040c035000400203046d849106c44c00c0c054070000c41d003400188130904000c0009440d95041d08040030000422001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 356698426 1250 356697176 356697181
    0x1060315050603010b040902090105070803101802210c0d061508100303020c0906011b0638060705121201030204110301060c0f08040b0406120e0111030a0c020309041d06 74
    0x401c0400e000034401d0b1710000004000600c034040a030b0300904261941810030b1814412286d44050550f002100e41e5600d514000340208070307500c1800c0640383c005220803070440c5070004e410301c584820f4440d48138003020000701078040361260411800300ca000e00d9a10a0811907030b030310307000003074081c0c045820240000345440010841c031091107544141107903030540050190894103801e0081c40300b0020f1100d4140320900352045100c0d14030b660044000c07840b5140002c5c0f40b80c444020b08081c2203284c1e410b2140c0450101800d040110110001602c0c41022200c60b034a854003440c2041c5080707240a0440852034020076003001c406040d008140c1624800c80301404140c602c41d08158440c08248200000641600d2400c0081210054858549402541c506180c9a244d010411b1298440e41c030800001e03540d0725400c3c5034144144034008480c02220001d101d180660310a601d05808040d0003080c15980e1741514030b4005008104076901d0800180013481216000c00300345001c0c031919908134885000c2c0400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 356699676 1250 356698426 356698429
    0xb0601050a02060a2a020f01060609080c010c11101707140912150c0d0b0d0503041502010b090c07031106160c03170f06120304120809040b090106031505 67
    0x1c0c0c8420000560040c0f0356580c503c1122005458907500124000c048080640b030f01d6240f0b00c1041d464001282c00500d614200721a0a41c21911240d0100c0708108011509102110010640b401e050801f460705043d41581b604100c120000820750180e4002001080540001d400041a50702c00030b100100d0300141e40c0b9820150b42201668107010000d0070f04100c050500e140c203828a0981080100880720040748102c0b14012047c0e09075406101c0e001e011404810110150142606000094580074140c100503911546c2d00e005500602500c4442140c003803142a00c00d40c895640300c48010440b000b14140208920015401020182c0c0090110414a8642d217400100d060165060201d02c411659180b00c0448540203005022010009100147d900c119031072162a4060b4031a241e0046c51410f1010402941c4a00d0710800585034009000802419078a61880700c400c4d41c1004038143d454801c18001402800e2400c0c40a03480070218002280d504d505901001d01941529200c100c050788910 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 356700926 1250 356699676 356699687
    0x1030c0b07030804060e0307060903022113060e1c030503160c0308060105090402070501021201060f090b0a0c060b030a150b010e060405060705160303030b011e08040b0405120a020a0b0601 82
    0x7240600031801c81c002081c0042c0040d4055032036402804266814511a0340da5038094640d44030054005921400d01e225410001110030b01140b15410351382481c00701000200078203480c1510801043c4246450521656190041d05182a451116179042460071518015096400a40d828103804104425021449004032210b0011541540708d10b0559615800111b820f64010700c3c1c00c540003070f000d00403000081d03c02d00141601c1c1801480d641300c65810418010103200388180700c0313400c002101c00d0800c0310350034001c211802441c01c1e141c54801d06482e4248400031b4400220880c0d090f00c5103400103000d001409181003c80d2100801c1840440100801120703e2501c400040e680704c1007c0000304110700c1e18070001d14015108030103071203480781006040800b1004550055000ca52070307010714429981c0c8006c4003040d80441e07084034400104001c0e001440154000d200901d0018200046020311030100408a45004501001941c500219000a403a9103280030101c40020304074011611560290 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 356702176 1250 356700926 356700937
    0x60a03020904020f0301021303050a12080705030f0402010306170d030e032a010929070513030f02040e01020a110c0f30120a08132001050f1201030c0b 66
    0x5100030380700d4885800300440300344011401a8075650811181e48902200d20a07031740211b0140001d0110401c0605240c0e821001000400b82007024050801884030341000a80342c00c00344812056000e41c0d25440183c00600544c0c0012110402203441c044040d0000604a02030070865607080c41085410110240c1d00e006020301c042d02d080500b066a04c09103204920720342214541000801c01c3c059580b1860f1554070b5403491184142281140c0b0300942c0c0e0002810343d00f000180ca400d9240c280318603d046210b01030f9000c01881c10007890310100555803603802c9104e1200b64000215582c0000c00c50242952404600182180c06106080011840c0110381c0c0d4807407c101804aa403440403c0c0e56588004046507040000110454214480031004100019078140085803c9564078040c180c0601222401031003c0d24498590b801c6100003001c1140700517103038248030402201d4094860058515004411050000c20b06c0411000da00b803900340301080c1207030302038103403004855104c4640600a101305e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 356703426 1250 356702176 356702179
    0x50a06020d020a021603330e010507110309011e17070306080c03030301030b010504090804240e040b0d030503090c1504060e0108070e1c05060901090b130f0605090a1208010e060a0302 80
    0x1c02050845450b000003003481c0c00d6202ea00787c44100450030741100322014460701c421981c1d0f56600304840c4d075400011104503001d90300700450410300f0f402c0000340346180c021141d5543d0660841d40c0d000300f5000300c1500909101d120745e085540c4ca800c00008000700b005100f400414421000407400314280441100d040e2504000e610100d6801c1c50240b001038001410104c1c0c4901c0108400a0120140c1080c41c01c8030303a02d00c2d14075130681b140300300c0281541e03c00c84985104070300c0c0c01c41034132103035071000e140d403d6a95150030160380b2503503400d409506002004a5454001c41c1c8090340e500c1c0f00c402c6a00070b2040d0354040d15500201c0c00000011604032004441d01400b0842d06030050250345001140344400c201d111a00c8943ca001d15617602c3e0402800351140c584a80d110b4003041c0410015004040c2c1c000e00800d429007050045480d51580781150341d0014100ad5503810108002800c140640460560401003c20720b2800541700200500b00034800d10301c101c20b01c0300c082020740c500403081d041201e40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 356704676 1250 356703426 356703443
    0x3030f0708060d170711031606031b050706110405040903050304061508030a0315030c17060603012d0603120216050307030804150c0605090a0209012c04050a06020d020a021603 77
    0x180c1da00c00c0300d05644401c0054900810640b41121b4036035082040c0745450b9000c10600851070328140c0702070150307010b20900291000f410f42e5a081d5080e131041c10f80320506d40100020441030240c22481ea110b12460708103540140c10311400e001807507003090086001e03c0c81183c080101225a0782039104490180c06000481e400070000001e10510a1f042900c801c1410507400c040d0903a02da803a0407086540b1f07441800c0d03000590704204407140c01030000ca50300800c20b800a11007502c210b4407040480c10083c04100402c008103c0e00080c8024a0b480003000e0356210032007480c0c00c0c441e1000070f5503c046207030b25404c807940d100d50302040c50b05001c0f80c00400ca0340c1c404801350406081249200c0c2c01c00008090030204081004a040461118000e8601a404103c0501014070540c01030204030441600108034402c0400c1d81e020003100342201c41e0907100e24070f010a0b2545e4403240342c01c60400545440203444140003150000038401c4d940e004003490f684640807152850009840620010300510004e0007146 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 356705926 1250 356704676 356704703
    0x50919051017130c0510030f0c11010b090c0301050103021b100b19180c02010212010f080c0607021302070302030c0319090806090a0305030703020c16081e060103030c1403030f0708060d 81
    0x1084200004030521b103040102e450904449524201c9032500200800100284425503021100703114103080280306030b43c001c88030b1038031141c135001901c01840f80d5030415a000a521280b031000304411413100030b210f4151001c10700d600c01804050b00050200c036214011036050740d00564a080504002c0713a4041c043c0c2043c81380500342d021b0040000c1c0d0b5094066540030024290841c20002c100390281c0240c443c00f080060918207c7c0303180515610001c4d004070010400d42c409a510303c00006181d115928016a03500d4003803804a041d40140e180c0c41d03c0c00d120100fa400c2e00a90341c1e8085c0704a17070300075594980a041d51028203c2e500d480a40e00060260000000a00070910580003164005481c1c2001362800420740c0711f03140f412840c000301101590b100f0009001d100002e03c080c051014045000b0041c0040702d8000b03d490b07150612004081c898658000803c00240c1c2d200b01da1055820425aa2a454030aa11030100d4604407030380b1001070280c500064482c41c000e07034480c2505801c9010044850b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 356707176 1250 356705926 356705929
    0x90b100c02060d24090f060803161103060a051e040206031f05121c0302040f0e13020901140307170a0605090709020c07060f0c03050919051017130c05 66
    0x1c0d4401941140f1403600d4802e80c1c40c07040b142c200042d82910090148181262606441d0400c4800139080544110305010080085a500000352220f803e40102c1e640c01e18080c91038480c0620703100c3c0008a406001c0c0320200b103200e040c680e1005105280d851409039160901d0b03a10380c041c940c0c044800030b5115000b40003254011083c4100b45240088007000c0f100055140d0300040c3d00a0301c0100036042d203500c060101c01251000c402007010211090130158100340c10a85000a214072600406080c00f801c9800145a0003d400c2c68010b030f190064401ca14a503150850520703014800071117203000f1312072a040014400b0100b40924102c600c01005440705880c107a076188081d02c40a4210300040c031410101084c0122240f00400c0c00600c403d005102e05480c1550150042584441040921040b008080c0204e90001c00300c03171841604030703044070310005187c1c06074201c0302e042d400480c3c02000f00d20414101c190440d4400185120101300c07419103568420605d5020110f209004204105c4504204140d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 356708426 1250 356707176 356707189
    0x30801060c060b0303042705010302090103030804240209030d0f0905060f07020301140601020f030a1d031e03310b090d0602160c05180f060325090b100c02 68
    0x482d00c620004102500c1140009180d90815000061403000102400b00c42011a03071000910303601ca89414000303585150001030141c901444090f003031115120002d010041d07140030080140c0b404400000014034035066a0b0002e4001808840c0039210340581800110700440704144400000d41c0c6000501c1c5c1440c09104181d0003404401744200c40910159006950031700071a1460300d06145a5422443e04100091030b1a00605444405401c2008400741c910f601c0946141c03d0703d43c9950040032018208082483e0124010b8092800b0045080d196a00c000100060100132182809841f5001ca0380b06040a0411800d00d42211025880810809040660050b00e140800200f603a83c81d800385445140603a0b00c03050038039a0080e0100c2180e01040a030b440140094901940d0611002409204104285030080c1040b81888900300014445507000c210f8030351f806a400300c0d1400d0710420310f0500048620703240070b20901c03103080406080780303070030040040d0700c0e155800c0d5a030410201161302032142 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 356709676 1250 356708426 356708447
    0x50c060a020d060e0a0203040506060607150b0d0b0f040302010c180302100c1502190302271507060b0f03031c090c0902030408030f06121e0709050108030403110d03080106 75
    0x30302c50f169440002e200202c3d50701c0c944101009040540d4a141c149005420039038020080c501c9440240459400700e101403040d0807100c049548005422034440c400a080180c410368010241844881004444d81a600d01d403401181310350005d0064201c252000c1e10300c5212142038280003440c01004002515200240908207505800c112071042108d81301c2010036200307406902c002680009021050144114010440100600e021410a54001503030925408220460884040f9008281856a0320401c1c440b911250701c02c040b60340c0324000e01c0c142c00501510090548200104c61413901d40e0306011084810b444100781e80034204401e20007441004120100e400d80e0507004140010582c00406e1000390700450003250460b8072031800c08400c588001005204500a150b440803401c0c100c4000a45510780c2c0189801224008180c020054940810f65210400042c1010000a48004c010000300309403405a0050038603841040140000d506298800900044c90f24004002c40d6200d041141c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 356710926 1250 356709676 356709697
    0x1a0d0207080d060b071109070819060902030a0b090f0c0301030b1506120402030c040b130f1103010303080415050f0c1c0608160e010b070210170c0d0606050c060a02 72
    0x182085903420184040316002e13040b064014000240c20400d01408a1000c20320010481d01164185440d4400910031200034255945c01c42d00709200859230340c1a43c22602c040c144480d030031512441c0c00b01114000d041040241030181c3c4c0d00d00c01003080c12010b100200e100340c44a41300395145901e1a501d40c68401d00081c13480003488525034030500140e66041c000d1440d502c4038078404805041900400d820401c2074000580320b286040322880d829100c0c0c84a031503503140c1b0185c0014402104505107c007600d9824641082c2880000000c0304141d04112080c0c056030141d818064448440341b290411035100303407105844440c40000140c2091006401491180e89610780049440b22602c0800f007542c1540e04104115000003885411640050714550018000c00c80e5520284d4944542456184940311020707002d101d0028031180c11034003500c880b1a82c0b08181c403c4406e40c1c51b065203003c1e55500a0f00000c01400d0505400265051180058070034219050380903018a841d80200d460080d0720048008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 356712176 1250 356710926 356710943
    0x15060b07170306030f07030b181b0f1804080c010e060411041805100506031006030b0606090a030c080109020306060904021c0510020c100e0a0c06180f080102070302071a0d0207 77
    0x29007039030411b000c0d42004620035080c06c1e455083c80781c00c650340010010b420460b01e034802a02642c941442214102103040305540034501a81c0903070105000710031418901e214100d03000c041c0010860303540000c2c10b4980000e0002c1002080e042c8410b910741e1411b41e000f50415246440c80800c500e41039106012200f07003014110b80c03950079a500c0d82d0502245c1899040c00036652000c06c00142010b0280071610139000c641000240d0455848800c050310107881207000b207a0220381641c2d2911408841009150041555003400d030751036850a001e010200700c00c83c001d0251002041c2d050034400d65140c0110707401000064005001135411034041c4206a00780d44510a480c25000e00c4d841602c000d1052003101000b0b01003500c1148038000944001d0450607180d83c1c02540c0d2075000c2801030001c0710546100e485d28a40454414132814600c2141d40c10454080060600001b240d070415030003004198880c0c0c081d02c1a07150746070304400170b21000340d80d240354891080020715080347d600d500a00e840b03441204403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 356713426 1250 356712176 356712193
    0xc01080c030a0e07030f081e09010203041a07061d070506040e070804020f09070306060809150f250c0212010c1d0126010608010b0c031c0b030a15060b0717030603 71
    0x5110000b00180010b8030395010000740b021544140140e010342310417280303000c01c0c50000d004000030f60380c0c4520710031042895118a000689000030104842c3c5458000c1414440500d40d07241660141d40c89807a03001c4c5601c40c00c24001281e081070001c0d40c003141d607980807071030055894440c195042e0200500c00c03640300c00440d94001e0141d8503081c81c5402a41159000510241000740181009001a0000c2d4032540300303245110f12494408040e0381d00007040c02400400d07440715910110070507468140602c0c001031000c1c01001c0355038051491006a07008071000c0c4c0c0d01c024500390360b5080722602210600020300c0160410007402800780070240001e810314150181c00b03c50101210900e45441d44002c05c10341004c010801e280d0b21003550380c05481e5070202c45290041c042c100c0341d640e100701081803024482d06600c401a20314141d0104202e0007004e4190340c00b20380985850b58450f0030410a80c0200c503d8000041079550f00c0c041a80e101590229542c0f0000c08c0c29040c520040c0c000521003581849030340301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 356714676 1250 356713426 356713433
    0xa020108130f0606050a210f0203150103110a0501050702010909050c0705010501080f06090f070509040c0905250c050712081c0e070603052203030615020a050c01080c030a0e0703 78
    0x200c00c240b90f4002c003c000781950400042001d020301c03e500c0544a4042194805501207800e0728031081d4070741c48443c2082031007644c40071900f040c000c22624491900c08800001c140520403161851403071085030007503a0726031500010340e000d018140002c0c1c00195190000c0c041800a907005603013080410885d18180380c0142d030345a0945100741c02c0034000d0b410001c03050032011400c00500350030403040d42c0034240d6200142006961241d561003100d10446541021a051002883c1008042c1072a14800d20951606809510036034141000800c88812110800242d45104805504d007080e404409051600c0c40e1581c00640c44000d5031060f0707100c110800482c0080810700900c42c0081d8002100450760700041c5200b64180340f4142e01c810140350a03c020408a00341940c5c1d170051051114600680a80e0503040803001028903070028a00d04d0b082440c44002c1a4001441d000c5461165007152022003000c401180c2902007130310716561000042c804290141c2040c3c10050b0442441402c03136a00954a44 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 356715926 1250 356714676 356714693
    0x131208180a0f170f0703080604020f04031406070207080d05070813060c11030a08030105010309030e15093d05120703050a0b010e060d020d3207090501020a02010813 72
    0x4215003480d000586078080041155034002003e412904143c00c042406541e15038038414110000d00300043c40002840d1907803181d041e143e4441800c108603031111344900e008644644040d003010110b1040e00009405603200084900c1a200c1e441f010308030704000c02406075a6600701800454a00505106c08904511608007090040c03001e03640e800c2c0c1c04030641c105041c80841100f603240c025000700c2740200205440404480c1111402c2c82c000403400010b04088683c6400c00050300d60003038140301414801041e03003000e45850350046070100e12460b01c0221409800301d05205100201c1035503099008903029010600340b0a0000d0708115140013110002c0d0480000119038000201c2c0d40c0ea018001500158843c1401c081e03400e00341441d0086041d030005615000c1c44a64801d60342d00014112030003034050b0020400c1e00340d41d45488040c600402021003100d84410540e6401c52110400561454800ca411000b150410b030040d0006a0041e00111030700200100345040303004000350f0314800a02d494 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 356717176 1250 356715926 356715943
    0xe2b05030a0906020d08040201140d09230c10320a110606030c1306081005070e0d0c092a03090215040e0f04020f1305040201020613120818 61
    0x9a020315a52040c20401800480c5240c1000d81154048104008065040250703543c01039024240442582c23076441c3d0f8180d051195820000080f0b08080d80903007004420100c0c081004542c405003045050300d6210b40e40e45080601107140d0040b605218450074602464001c0345101c6501408481944000081808800c03801001d420203c1c00040303040d01c59a001c20344011619905001d4561401c2040001c0e540ea882c0095142c440c00309004040c5462000c1d5011a008207110b505403000c04004451110080108449040c0460440100c51003e032909a880a00c2e0320b03401104018490b00703040c040c9000382078004014004030302088020094005408240c3c117400e5007550045034034420ba1040c8980b00c030000d0941c010480041c042404250a62144681c3c400720041d40d044050380c1d6400001c0c11080806801c50301f010724480104280d00b581e0700150301c524000e03000c8a002e40c982620344402031140130401340401c5d8114016032490351050100f160003890341d051480142c0103c144c04c40c10700420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 356718426 1250 356717176 356717183
    0xc05031605160e09071203120b0307081b0f041116020d060608030720010912051606050c0f060f0402060a020a0510020a180503070b0d090c0b04180c0e2b 67
    0x440013048002031081101c1c801a050040003116021241c2d07601811090850f001c031420151190b2040500e500c4c100500c20090080404403079259880c5241d101841c07014096040c0105007000c40000c3e90f08241c0250305090301580f41c5d04c1d00d0041c2018540300072002c0e58000300c0c0e0101454200c540404c149000340005000700101469480c007240c94094040d1644250481362103090382140306017a030300301001c541101e000c440310306560952480c0081c100032441382106c400182500011407003075030150141c000c050b01da10440ea9920942c02c0141d5075444121a150314041c1c040c0001401810101702521b900c6180b401101c141d4060f5036145410030031110039078038009078040b50015819a005421250849000c488000001e04281c0860b4403a0540e0050007005040002d8070984011568040440070f60401044c402440e101d44141c540d45d8494460203501c107903400c40914907140284241d2420b40c6442d11000707500080c042c144032006e41c0750701c410020080c0d4000c051559050520340750003080d21 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 356719676 1250 356718426 356718449
    0xa02130f060f0e01020c280902070c0e01030c09110c0105150f0109030f0b22031701050423060307181508150c03060f130903030c0c0503160516 63
    0x401d0801812010110844401c000c00b6601282059802007425140e1600640d1166241e0f442d0220f40444654460520000105030301e50010f0b41181c0740e80035018062280c1486400d04e652840403881040080c003000e06540b021880404c00001079138800c0c041311200080580c00c0210072031000d400c454045902400280301c13904c40d44030a14151401850401c0242061100325042d610303051341e01400041d00415044440006c10005403021260420307011034115608094881c5150007080c00404240700201c410303c01002040c2c61801c1e001d03500d8074206501000c24100c01c0f80b550482c0d4458058078094244c001c1d1748000c6414112082d6809024050400206140c60303a80c0070b007800c103c2c150b440725820307401220f1040300b51480116265000011040526200e80300d500014440c5040441499408841182551181101a04101d507818081d44040000c6651301c8015103a142c031904c40141150007c0081c44824031400c1d60700e003492801070742140e420b0b0300304000c42c00b006c4803075403c4140c0c0c440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 356720926 1250 356719676 356719679
    0x2409130903091a0403150c1b030e010201060e060108150a081002120609090a080d0b060a2708151b0c030d0c02031227070603140c210a02130f 62
    0x15409003c07180c030014040c805625080c0b65458100106240303078414a24162902a8122040c2c85080d00092611101880141902071480d0144c0078000c4c80d0100d50140d400c1c24000a203040d40310380e44520a52040c2c480d05100d50754034004294045a000340c2d06d0b030100011001160820f410404007e40420781400140d541e00040140f0142110040581c4d21034202401000f0083d040424500b014603404003105032980d0440d00310341c025040d89544240c00102c0499110030850740300c5115800c10543e040d13060116284100703d44a0b51200c0d000c0c10031903a11100801a01400d13240850303a1003007001d041099601e2800d04c610010b17511101441c0580e03070012440c2d510040b060312405c44a001540000d515155010540c0c203020000102030321140c0008100203000700107090300041c04051030303405660f0750030740780c180160041c449018841c83c441440000a800e0180c990102c405460100e038a64620506041d12124450b4000700510b00d041e40030311218062000707181c40789001d004840c0b4213441da00e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 356722176 1250 356720926 356720939
    0x7170106050f0604030f03080a090f03050d0b100827030f19020106120809030a050f0708070b0306060d02090118031a0a02070b0f07020a0f0b070e240913090309 70
    0x16403072802c0383c0c401d1504100810001c2c0d80d041800030190303814189560a692041903440040c000c041c4054510540c074000201055404002801c0e1896032a1040080d840d050b414050300303c41d0b41c000307080450821070200e81d00d005a240c103106003c405441d2a04901c1a1010b00f03415904082c80700c4000103000301c0d0a01d0491850506400a52128030080083c0340c9414401c4403046881840a886004001400c00302a1000d10080108942120444000c8102d0381c40c440c0d40c3c1c100e544a450014002d45801180384802c40044034050f540041805090041c2541818000d42c010742c017031414001a5290340480034011001c1c10010b5009400304085404080701b9184099002407440104074030420020001685034900d0320b80200e0130340b00e0209a940c40035401d80c82c0840e400c1000d001c09240d420381c1c40800212403c4d00d4455a02075841c21180791340070b82405440203c0301c03070740b02051001003981c03103c5001c10405030000040080805a01040301c011a0048800c1c03854282c3c0095600ca8052050303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 356723426 1250 356722176 356722189
    0x17090a031211030f030106260411130e03030c030a0b09070306081e101505040e0705100804030c060c0509090403051806040b070803040606090e0601090f0207030e010e030717010605 79
    0x1508280b002443c40e00214060f0748440c1c0c4014040d840c01c1c04000107042101d07031303038510200d002d0707010a180d481c1c3c1c0c0c1d01307060074000e103034a40303040b20281700c0d034500700c002005012907004080488503050700550942d02c0307e502c03036400394000a010007007450340d03040700700c9003035540d4182140030304401d8030001441c5050260b0719045c208010424a841c400d030400f00e000036200000c030040814180840012640741448210000c036a01d0790041d42d10500740390b000d020a51000c01c103002180c0d0300729064041c0c68203104081d00c54510450b0007074040790303003c0d240801142c81500499960351040c5406860111071000103000e107401510103a0021300c001c6051003040716403183d03500c0025070440d09141860700e0081c0c00502807154031001403c84102201060030403003180c03c108003a020512080c450403201c070621940d111424450728103800d00340021201032007614400c0310245174047d80d585660482c01070040d18500d0004038126054400d07402c0000d01c1c3c0204503c1d00e002c0d00d880e440007044440c17811042220 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 356724676 1250 356723426 356723447
    0xd0b040519080405060a11030a0f0201060e100e0411030d1e080c03160c020d0f300c0f02090a1505040218010c0804080d020102030423070317090a0312 66
    0x20100200d1140000c0b60000d402d8504448040b1500ba0740c0e9410700c8412034401d44000011080c0340300c0400d01c2d4000301d4101a1003282c146466008200c1265699094001198140c0d900903240303000b020180700400340c4100f56540103004040d401c12000d98480802e141030345014001c000540c121026540c0145917404000c0000128a07215940707050840242200303202c0a080c800d14880123407002c04140b405203420a0286400901e8504000200e0510b0b1140c5284224100c0b8140c2130009070074030000600f000030395803801044500c0d5201035411401c0d20030141d283c0003038800129000850b801a91003005861107554078904c0031440134900c5064901184082d04002c2c070a034018440b00310303200126a091940294241f03080c205800700e508240030203104503003203070915000321200401010740540045000e02e03c81e4884010311983e8000034a05101d8429412056411520081002c1030b941000400c81040c0d06282c02d251581c0e45000070603003956540110b41c9142c2c01e01c0c00301e800356080300300c1d182d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 356725926 1250 356724676 356724703
    0x60c19030816021507050918010b07030e0a0b04060e041103130b01090207050309100504032a12050c1005040f1d1003020a0608070201021201090203060307082a0d020d0b0405 76
    0x500159150090a030702500100174008014002c50117a440341e40f84854107440f50000c00c80d1000a507116481e4641a5100c041e050717000c2440341e0450205414400c07045002c454000f10850b0810f8100714040752306c200c2e44804140c0c0035489424100b2024a550010b5000d01d0040740b288600e420513180400c00504c0582c401a405481441004080340c404400c881c60100e044a002c04101e03103590b41658a406030f0f4201501c1d40e034a0740c00600001c241c1401e421000040050206100d40d03513019260000317502442c008246400014012400781014000401510213900b031060070700b91500140d280201031b07940031084541c0c5000c1140014072030107010740e801000d01c3c1c01442045040d5008203030698401e11648080101140c00a800c4510030742c103036180c210035016601c01c256550110007010390020358005100b0f0090280024401500040c030420b411140c0804e2025088091700e030b0713244004818525a040803003c000c0c940140e4070350b044034501e64469041d00d022402d25083c55807404121880b01b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 356727176 1250 356725926 356725933
    0x1c02031506070f0503030903070b1b0f0a030902060c010605130b060708030702160e1909051b060d02040b031b0310051003020c160501030f0515060c1903081602 70
    0x110000d101500301200341082035401540d6041145020840e0300c112000140203070001205110208038048000d00398140505c0042d580c0c0d40f21350040801c4c2210349d64075509100400c205040e030740484400500003070540c3c1e04000558000540101e00e1aa0084c44507103003595454074240a58908803040203402142c00108000c600c4941340483c6483c0f207500c201a04847c8088002051240708201c1c1d00381c1040c05440341c0b01010354658441030090410340d40075802e00ca103020741c28010303421442110a9070750088001c25118007601841d0a0103500317549000d07040042000303032111240e01800104018201d0b10a141c0d56441c2600c2803248402c0b541e5403400001c50200b0601c40408540c0110b41c0954600700d03659a801d410201c001e60080c850740044142a00540840d152010880e80c002c0c8126602178030f05100764410130315007004031035003140c48040840202c00d441c500b90400c00054a04504004c003250f20b049000000038105d056000340403400140b19504004192004200d14000e055032070004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 356728426 1250 356727176 356727181
    0x18060c020f0309030a111c2103090f02040c050c0303090318060a080c0f090918010c0e0d0f031808010204030210030209030a02040b060f0417010b0a06050733021c0203 73
    0x45c0e281e03415407030044d1500c0c803201c580401903520101654081c018081c0003a03048061442c04060305c032405540040780c0b00181c144109528003e00440240650102c2001c8944082e542040700421910480200708a0705000f0350414034010030013140606c1031140199118003403103a8a18000b10403051103400340406100e201c14194000d062a40c0280100d84000d231208000c0b0001800b17030040b12075003648080d0340010700501107140031202003150b0120009000c006240303403044d02d1070340b000c6e0110b41c1c0125a51828030046011311013540b80c928424030707003e4410010003d0103910545160000ba020b80d5000030200b045103800c2015858602007400c0650800210b000002c0c0c0724510f01401030301554417040c0c0031a0a580b00c0c0101c50701c004110051036101ea071240000c44c2d0403807051088620075807034014030803a14580303803001004850150342c406140000b907aa4030401d10903042c0e5003125100328070026410380c41c4040740103211004441c100580f145051403444400304200c03540174805c20303c108207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 356729676 1250 356728426 356728429
    0x70807050a03110d020d030f08010504051303110f010c0207080606010f080c090a05040e031803210c0a0f12081006020601170a0501020703030501051305150d020418060c020f0309 78
    0x100c008494000c080c3c0c000008419020501c0b00c180040000d602245501c450010581c000844100346003042d582c600d8541c0e2510240700886809403640b0960602100018001922443d50420a8a10f100c2650010003035640d120342521441110f581c00340c0c00142041c801300388200181035120809180048041d41d5020000c1c0c144400a0003d140340400054001910344074148200c000b05006401003060800c1c0810154030381e00003450300c42e00c4c0c4012450000452400081c1c0d588810f0a51b00d249080039100f0f42042c1e000d0380b00f20421252030292580450118071480d140710003990007886002c0c0302c2c0100032401800c00c2c00090030340701c458102d544240178039540041c0850549045004002190b14904c007454904282180000c209600009001d020136501d500610b04945041e210400400e18a00c03001007641c10031915440c00115103420764140e89400c190914400c2d002410010b000c144c03444200048042079403054039a0b903214001801c00039410040700d000c2c42c041c0805035040c07d41c80b20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 356730926 1250 356729676 356729689
    0x60821030703051e0a05010602160312030b0a0e010b070210030507020a120504030507120606060807020a02040f0f0507030c18080705040f0b0604030c0311060a170c0f1b07080705 78
    0x52402041541d14400035082110041d0080000d0404c4000d01c800c910b00400402d0180100b4055000103026500700d0700b2824610304842d07015290302c85031507404618404000c80c010b061298041717522034400c0f400090503282540c4400d020b0700340303e1503050741c0c0c51540c01441040701d04001103408040c507080801240c26808a2881c4956522820300780c030010700440103c81c14000c0742c01c090305034005c035040000e02801882e0b000170740d83e1082e401070020903a2120151820b4108035101c3d00541c0102c4840001450f080e4400b1803400c40102000a0350018074403080100c850444414000c00d607140c2850310001c2e00000c07405124401201400700300d40c140310300ca07034441003d84200c0740541d486001289545410742c10803500e41402030041503c85590b810403c100b014103100aa40b0110145200c1d951070038050b048820008103619101090b01000140031001200182025035006043c0000102c030f042e0380c1e00404001015010100606011088640c14001c1e9544a01c1c039a0303000f0b5000b0009a207d50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 356732176 1250 356730926 356730931
    0x10f0c0c200f04020408150903040609120501320a02040f0b1602040504030504061701060503011701151409010506030609060108070219150c0234030c0906082103 71
    0x1c010110074040980d010a4010b141000d02ca548240049808107581c0c000040325010710a04441035960740e15114401034886c0b0850040400090548800748031600303d1a2603c0344561184c4000140d10300d2046508580f141d20803280841c055111409400112503c02d0142d0003840c910801c62074580b03010289002c9043d40d108000341c0c20300205580144104106002a04680140c824002d914140c94000c101d80d0290103800041804009c7d10f8046115000350b06040e19441d407a202c0c13450342002810503910021803031203143c544d03c1c2c0380481290b02e6058003500003484402071f0261000c00700001c00c80220f6058004038041c1e0070a1003003040c2540c5404005400c21001c5c00c0a21180c3c0301d1040803404c01d084d4100c4540c0310001400c0f810b0030084aa0301810700e80b51200f03010060041440001ca8540b18294101b07a25000305c0705800c0d94012400c0c0c01c2c5101c403401042d01c400019966960f0741700041c0c0942c0319000e19541d41c801081101000d0088031900121044032079034010f44030003260b82d40e0002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 356733426 1250 356732176 356732213
    0x15121103010207151a011d060705030c060612030a08010e060301091b09141303030513061118030d020a030815190906050a030b010b0f040806100303020f0f1203060a0b0c010f0c0c 78
    0x5141f4016610b401c3e007250700e51500034055030f03518500c0b1005070340d0700c0b41c080d90b00c40d0041c0003c1108115071030001c010380f05a0a00c60b070354200305074a072151803102cac48405020613506550704c40f021000210101280a00300441c10003580d41c0a01c0c3c0ba100c102100d81c80e001425003041035100700003090410000d0710b0880c030f0703140c10000780c1c0f030b00d41301e100c60203900d801d0b40001c1085240003140000444004040c05c2e441e82400f01030517402202c00c09254075244102e82c88000342c0c0c8120a4400000c2c01030302d0725075001c00d008200340c58420604001881255440c01032007007000300d4220038043d09209006d000c000d898191103d4407032a01c0c503504c01e036641e1014450310b858040d0201c0d00c02690000c0c030f41150010102c41d01141c69500f00440c0745142d9a0040c402240944900c0c1c8031061006008240c104036000003001900d001915035240c020300b60320081516901c18090400825604500c00240c168070445c40000200749002030300707070000c03030f080e0803440c0e000e2101d001c8088000555042c0ca80346000035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 356734676 1250 356733426 356733467
    0xe03121603140a0210050c07050c010c08190e1e13180b0114040507020601120303050a090203030c060a0e160b130f151215121103010207151a01 63
    0x11a8202211042d035042c1c201e100300c0700b0018071010b00642c006a0702008001c0b101003044161070341110100305116000c0010110740003d8a200d100b580034031000c40703850b030041280b2450101c01c01094245d41e890044880c010070310001150420303050400700c4814001b82c0c041c40084e078840d041300160000d40c02c000d0344201217496064070843c4009601b0709500031940710302103810301d58480c8a8119007542104c40c0384d001d0752400000a1001d4800a41181200c090a07005508480c440d28224080c1c000203098141d0039444070319010050310b0400043c02d50602490203040c403414400040c4065907000042030030660b0044128510341c400d1034003c00c1c00c5940b034100c0c0540d00c900d280d44002c014038066101811029400c200005c400c0c1080050b922044a5940c2d0307100d10b0303650000c880080362405d0a1441c400c0346004010310102c10710300c14408915000f90000c1c445d120840000070700fa030f40868411150746918110f0603682c1c00060007102d04940806c0300203400065002d0000300b0b03454510500165116 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 356735926 1250 356734676 356734717
    0xe011503050f0f1216051911091924060f0207090e060f1504050106030b0a06090308041203050705010e01020d0b0d0203150a0b0d05161211042d0902010e0312 69
    0x10f0b205c40b40e0710115a00100b40c030851441e03800002c050b4030050801361041c03080609921000e2a080800a200c1d0090b036500c50491752a0701c85400c000d1000c04030b031019000215441c01c0100c400809003800904503555401c0c040342d60b02c01c000f0304080d040d50200c8405410710300854a842c1011039400d0f8840b0694030b45058540d10503410511080641041c140c200d0324050000c1510740d896000342920500a030745200f0141c4d40ca90b000c4034140f02c00d1201500945040c00b050007500c1101c100545036074040c2c5400740c241146500c4040c02c691580b44160000d0b035002070301c000000316500039400000c00c12180b400e4055069004242c817120382003150058000709a00140d6040301641c001c4042c510003420314080c0484600d4550707a100080050015034410004000905203443c0c00132810b81035100409007000c41500080c40b010380b0091082d50b2050343c03000e0050000d08050b0190503440300d800240840c004200b07000242c04007104042c400c0c080d070082c51070001001004d030100c5e01001c000e69686007140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 356737176 1250 356735926 356735947
    0xb0109060b031035060906100e0a230c0702040f0501050927030703020a060b0402030c1602060405040f02090108090102090d030c0c0509040327050a030201030f0e011503050f0f12 78
    0x1c141000000c642d5800b0030015402420002175218891082c10b411140c00791141454510f24980e1449142c074107a543d080000c2007280c140c7c2103c1c0c550404840c00184401c540e47c540c144068003114006040540450041c1c00d5190034010003801c1e021a02d4104015410000030034200c207801031540d100800080c00c103e030994001080450032486520640c1e03203c045900d0029202d034031000e82a2040d42c1000c10a48491415208483c042c244502c0410f2600c848244924114080711318280d84c03003207090000060725110b600600c000c9101c072500043c0e56004200000d0a0030501910131940d9a20512002c01c040e142c000310a268580c050904004020f0359142132800c0107000c3e008503070028140d8040c4420907801072104040c2d9902c08000060394518510054624203c0741314555000f91200e034100055406075020b642c03918541140420300c01c0784071680d2825100c06e04034020100300400c1041052200a000403196002c13414054110a24408030480da01c600c2d5440700d41001c0800107460010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 356738426 1250 356737176 356737229
    0x60105031005040f1d0c0a06140c1606030c2c030a0f05060f0c07021e01050904062403020c0a0b09150f01051302030405100c020f0102070b0109060b0310 67
    0x905000b0000d004241d8949840f44c05803140084040c05000d443c0e4420722403080c0443e00c211120000380500c20441d29003a011204030f9032106804040040c100308103030340302c40203006c00e002a0005446440c080c2e40b07882001011100f0000ca24030800920458030b0880c2406d82c0b40010720394039400b80c00c03c03207885544000303802c00043c2e03d401820100207220306000c01c600843d410740f00d41a02d01d16041c0e10790320001350301075901c159440298002c0780540d110041d40c94024881010b101c040c545107080050480120b02214400c0c2c00c03407105201103e8014a0310f18145503c0300d94040320303150542c2001c449110850740c1d889649001042140c4202c00203092210070460258a4114940b6906032424000b64050004c13100f03020b118080c0751101050041c0c044680201e80c01554408018403d825100b000c580041014440f00000c502800701c2c2d01c050080240007602c9514010380c1d40e590954581030040c0219400f03584401c3d0500e1042c41046400e110006a850845844044030742c8031050402c01c643c107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 356739676 1250 356738426 356738429
    0x140106180f0e01080f071802030406090f0c0f0504060b12090102070c0f050907050306030312040c0b070b060909074505040201030c09080d1202070804150f170601050310 74
    0x6a4a0301001403a062030500d403a041300c0c5503000303481c020030018800075155070b0240a0718559060003101ea102e01e00c139550041d54801e0041c40300040502c0c40756100038000b600103c0960302d00070007100c03d0080314548803220004240886080098500d403200ca90744501034580018685108000041c40340b1078290115541e141d401040c0c0c00f1010340f030b6056800e1080d0701303001d0280a0306c0514002030034640200d044030300030140240114203016015451f1100d1243c001d00c00c072030b01c00c03040d0030000e0484803010203840381d14456040b03074050b031415809100742108002c050214951041a08009080003264070050294010100c075404074034440d28115980501015800044034241000707080c0212030f4070150255100341e9090107480907104007110490014001c1c541503400501d0341c685040e024403031046000099050260070300500d5210b0340c0d99034000f5403009114090345000300d1030b0305034004d499984040b04d40c00c0442004050f402005102e550081c41e16042c080000080340946018000b040c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 356740926 1250 356739676 356739689
    0x6020f151909030c120503070c060e150907060206161e02120403030f02011a10050d150603090b010905090c040903120504060b01030e0f0303060d021305041209060314010618 76
    0x8410b885140080091001c224296180701c180740041c1365080c810700890303001e4445030380c401c07140300020784903070004051480410400b07110ba50300040d5080e403000020f5100d00303158009410a10720340300c0003a00b1b0200040c1101e045280305910502803607000b120074070f8243c15030919800c1032095400c0a92510030702d45803110345500089400000c060b440005031060f001c0b80e81c005c0c8981c03083d21151044062b103402c002c5130700031100b101c0351040070710500c043d01c1d120080300400710340d5101899548030000c2d07250b0054030000361100900ca0501c20f001d45a18010940b0b06810051441c2401e925501c52803c800300c40e10450721000c0403000d052042004901c102142c030001c0006040a160805c024401c1c052120301190502d01d40788c0d4000c00201d500c4007255450300c05180381d80c0e210340c10000920b80d1440c00b01d90125440d0242c403107000940c841c0504c16840340356a4450f41c00001d01c007418104299101e20100350424540d41e00105201d122503044403101d04110011003c5a40da58881024580204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 356742176 1250 356740926 356740931
    0xd050c070f0f18020c12090f12150f22030c0b0720010606050301090b0a1203050405030105150d1104020f220803090604140303040f06031506020f1519 66
    0x811054940c0e0380020440b0f01c100b145000541501d020740302130703000340450190150440c04401724401010001003000d010001c006131801907001d40003d01c548130b04031034048030f42c1c0001241070307022281c4403409030800755580c4c0c0320b6400d24020a807003490300902c103041511100040107030f40800d07000d5000714014039031050010a040c03402c0c5000802001c5440784280702060f081541405241d01172280000365a07440e65030615582c00e0011a0380500724445036641c104401500009100000300d251190300b81c800e81e54103603202c0c0380c03500305402d485c0007414034154400207994075125555400380301e0500a500c0502c0b20390110306200050001d004001400c003121f0400030b900ba00d011921001c6803815035001100882e420b4a410030700e5a01c0c003c95000c0c0d40c01083c104400d10004000c0070b9010380310b0f4402411030b0b20b0a5201c0221810854803035214001194442401c800c5041031140000040c2890784024600518100d509a0b030701c45181019918900032500411880402c1c0d400c82181d1303400e00c4205 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 356743426 1250 356742176 356742179
    0x12032a0a0309060b0109080a14122b05060a03031d09091612050706050c0304090c21090203060601051c0c020a0201080a1812030b09071107060504080d050c070f 70
    0x307009042c01c8901140c609181500c0b00f950f80d800f502d80201602e260074001d050000440c0d4078540c1101190720426410302c070b18040f14506c41f40100c0103102d44800300d01480d030b40c0400c1e0116500300803e540c091501d002d051408108107a01c490403603904032905464445039060b4402d85070340c81d0844000e4000e8220303804000300124004001511002451a50034404449989280b0f1424003118000c00134447c0d0454803081081612840141850032154400d0344d18107580c1d0350031a4101ea03442600140801d42d003003440481004046080281e02d400000240000380703075540041c2c5c803418001c010700d041c0140491020380e50691840030b00c5811402540411274401d031924007954445200342e04034006144000003440f2903600707010f071022450b85206a503000041030341e0f54200990400060104055807401c1a03402c039a107280f26036015070b0803521241000e0320320045050501500790030900901008100c00c100d00403001480e01c1800d66203260054a410319016503d01b000e03400e901c032030000d131641c000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 356744676 1250 356743426 356743447
    0x30908120a0c0e09040507141f030606110318100e041d0d050a020601030809010309060203180106050415090209030a0507170c1c031805030a050106031412032a 70
    0x2c500840c00e40354a03801c04410000c01a2804049500421540207590200004e5410380d401242a81c0010f08280302c500345d66158098a0a428100310000781c0c6032001082119085564980d01c41809000303903103442018017481c1c4501c600143c800b805440881c0e040b01042c1c0c410007840c551540c0040041c0715030300116180b0f645e190b6240440c003100c0d0080103403014450780200b0880b0282c81ca50b8003d05403c0e840d503121012650090a6468185616030700558001181c03403000718480c0c065403021072281700343d180c06a401c442da181c0005014614044510007079041c95000c01088030074020b80540d40e200030401190510611f100e0040c072600c640c6802107005101c520003c014001e01c402250b8101903848100300340c000c4108030400c41c442140401c800400e00c5010030301205c01202c0c0c162194583e0720004603161441051056844e0703551030b40c00703208003da00400c0301500c0020b2402442030802021401c1001d2002070100e0a00241c0307000101c05090301034103201560b08040031034985415490704c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 356745926 1250 356744676 356744681
    0x1501031803110705062515020712180602120c01060e09150a020306010801051c050609071a090f130b1306051011190201020f0703060615031b030908120a 67
    0x40c0c410b06580510240490603050a81c1914044400c1070321030451482458141020f1110700704c025144038014040c0464031042a0005110540c81b60400e40f0481611000090001c0f1130944038081a98041408000c095800201000540040c2c1502a076840008009a0051240368400c1a030507648400304641c901d03011030b03e4454502c0c0c0740040346556403400300b290224031049480c203002c82e2400d001400541401c080303c0c03003400c6100e00e0304201101c03291140c51804c001180c860220ba408240107004a40d01001d10440b038110b44a107260a0a0381800066501c00c420151140644a0104a400c01c03c00310740110106280c007601300309007405028a050080d1540b0300603e4007420094020340c0055100b201d0319201651800043d0103c25a0081030b140c0c4052601800c0c1d046102d1550389100008082c000600103512030b82d00007a0007031800c01010482c2c20b190080c1004d051030403c41d0f151a00c030300100703414994403516001903074402d145495182da005401803040010b444000b00841c07016103a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 356747176 1250 356745926 356745947
    0x1103070c0617070e060a12021c0209190311190905070810081b22020c0303060906091005090c1204051006080109030c14070b0a030b0f0d05061501031803 67
    0xb808000340e480080544500030301c0c183c01a04030104000b0003005c00c1c070544480b107035203154150140c5070032561034280003988103400d5000b40302e59000030300e10742c10705c1d0892151151414840c488208545035817500c0101850400d9428041c04101160600600c003480410000d020600c07820001c034106040020640c4004441808103512045800300d03e803c400110359102c1008043c0009403800c090060008030343c0c41c02d4913941c0f4020500c140400640c0140007404190000000460312031070b02c4010011115000b503c080d0041651409004400140400102c2510000c4c1c0c1c41c1c1c1003c0c1c640305500e48481c4200c60000000d44c1580e000d1004200c004119a2640001800188a071649454180d401c0b00c280c00001008901c81488040c0090130013031a504405070318070242c900c80d560f505140c620a60001403076500003551020030351502c0c946908810034510043c0c031140070311071981d078600b42d171514042c1850040842c0c102084a030f0384e00c0381d0800380341c00d030011145400c55481ca2a010f0190400c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 356748426 1250 356747176 356747207
    0x711030703030e0a051206070e06093303040b0a090201020304050411190e010f0e190605120708011802030406090c06020a05070b03060607020942040c020d1103070c06 73
    0x1c1380004661802030350170001164007801601440c0c0300c14505481d6059402c030540e400907010300650f455540c03941c00c0c1072981181020000741c65180b0100182483e101b501011468200034024080032540c0300044a91080c107900001907008036030300041c0d1035030203039601459000b8108100b60425481c020041e107489040ea400311082a03030340902c2170710f4011101103da8002280412403010083c0303d0400e10505640203403022148494900d014160a04103811030000304a000400140501d1004646030f1301c0109890701c600154105401460120381d080c612000460700840801c0c1401520f62007200001d50044094282a503590340181d1101760000054800c0e0203643c1e0001080e45890046900ca40310003002589441c1e03540d405c204481c4805440203030819080880312000900c0c450b035a038001c00d05c002e00c00403640d51f42c1b101200c07409220847c1030f003d5800c1c600308110840d000a200c54414105041000b074231545a080c55145018121020f82800d108060009010390007104032001c0104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 356749676 1250 356748426 356748439
    0x409020702041a03281406041a010303020d031e1b020d210504031202040828113102031005010503090307061d01020a0e0a0f0f0b0711030703030e 64
    0x180c1d407456404111a00d0f603a42c1503044410160780c2c41c001c1d0410250101c004074500c00071600b01c3d8840e03503e221101d00842450b544184c1c00d001c00d00c2101548054090b0707004195860560450f030307000703440d4280c80c034040c028542c0f542c200d05c807410850b24014003c03d2518808001e11004401990440150544808003600500300e50180040c0b0907112003460001050000c40342020300300040009102c0101705400b04520003910440b03680942c0014001481c1402c01891210001c6865400ca000c0c1c01e40d10452110417801c5240010b001102d8491803590201c800c0d040403c06c0f0042480f0303401d105c003541c50501061540000300703039074940e000d14002c0c802c41404119481d114001500c2d148402d54044040ba03006100101c005011500b18105482029a0103c410300ba490740c0582660068611507010a503415103284a40c109100c0d494001e205160f21400c03401c0c644429045c00d000d16014084681c8000500d070402c0c40244010f0350b400d1003028045426032540e03414018462a0060841ca00c01d40c3e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 356750926 1250 356749676 356749691
    0x501030f02041409180d02030309010f0605091b0904020f0c010c02120712021507050315040615050c0a020910031104090c0501081504060810110a020a031b0602040902070204 76
    0x25054802e031000c0d2640c0f0020540010150350812400c1000140141055243c41c0003102c9800d0081c805005400d2564005544034117040034107509440d001c0c506580481d141800401940e40e900840c030340c10004101502d00c070401c3d10b60082d5040c2c0702e0252015003160000901198040141004064594140c1c008100d1a600200103d8075002100309480d125030381840000b0100c0c80e032541112880c00c1c03c1c0100c03000009000f64500300e4510840b007400200c0c401108000041058105c034086034001203804200d114108200441d040000c11102c208008001c19260702100e030802c100480540c0040110450345845543c0c1168501c040c0000c5030106060b803ca00b4490810740a0700321403590044082500320300302001101c40d81d00080000c2070185090a00c844c06494a105000c064981003000c3c20701d92156000d0941a15800c0320783c03400c2914104075000ea081d90102d005503001d5414070381030064003d840056001d441002c0c0c405000a4400100010040d84a40c014a94148290703801c0c081d90 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 356752176 1250 356750926 356750951
    0xd030b300f28020d03112a031006080601120507080615100f080c030403020a0b04120e01090b0a03020f040807060201020a0311070f02011412040c030201090812090d08040302030d02010501050103 85
    0x81c0001030080d000665031341079100082c05000c800341401201c1080720191500601c4140c104c096001590204400030642d035074950030f00740702e130350128501100180074880c42c00c80c00a50718101445480c07081084080c08804024003440f120b80104540c00c102c03043c81c207180c0e4480011706250071101c0d102d1080e806104c03100c0c5002e8164040d151807035482c0d00c81d02c0d94404c0c0012500354001041142103001c0c01d40c04000055140300b6907400b4034050175003a04000102c82020340109080c0d81c1144c1400300c003c2042040d00036800895a11340d8962030090307141d055040d00a21a8059a00700d96494050782c07a02040c0194150701030300d80c00040d82d41c20700100c18182c03840d43d018410440041d1598120928900155000d507955041603c026580e141c60040034111403554440141d03012194100000410815981c1c0440301001a140b2a4094000641c4130143c8a585214880100d40184c3e04400f030182480175035410754000310f4015080d950000d5001c10003e000b813000b4012580400c1c54a801321501 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 356753426 1250 356752176 356752243
    0x30406020616081603090501091109070302040b0304080a1407051006060f0e0409050c04091406010b120f06030718052e180605041407020d030b300f 65
    0x20940681c60700e0646466040341c020043e110307400b1300400d161b102c4400c00c0002c0d10900c999180c003402201d411031240200010003290050160107101003600502c0240406c0c07503130301c084070b400551000c0d00c40c2d80c42210f06410748251005040b240414040840c0e1142801004074512241c002554420000e0a44480f0256030200403220f451000580c4114401c6450815610174a9090301407170403154403801440001d000e55100d40000c54982e240d00d1058a000041000030a01500030f0311a00e50811014101209100c03000800401600a2040120b41c9903107080c015017004d49690505400c03440701d0440c400000e0038007558540d00300b424a80003054154881c00310030348a00d030710701c4503000c086242200144000340c48000d0420110343d2464001440d560b5489102654400114480d07818a050795029060808070241101818240700103020569150a4035164100b21200400c40d040c1c00702030f0b9100c0881f0030102e028003038454024800b036045000035065a03810b2910144915031041311041622 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 356754676 1250 356753426 356753461
    0x60a050411060c1f02090f0d0b041b030203060c030906070801060504350a0203060c0403050a2901031407050a0e0708070507050604030c2f010e010e09090304060206 72
    0x1d44182980881c5086001050002d01c0705049a200342400703480440501c2008240c45449640000c9135003042c20308407801c0383c14040072290b400000040f91113190707640c00c0c000c00040200c40c1c1a071618110340c08500252002e0354001e0101c52513803030305541420103030b0300c00e89035010180f0400c00040d0480d0301c621940b40c181d403d242e465038180f620700921001c108690408400082c40b03030440043c0c0d580c1d14910b030741e200e1844003002401d083d411801410b00304240071345011a042820001813020510000b50380f040594080007080103c003600c1985088200040041c16078424580c00000c284402e48041003a41d10b4402d090301d0f21640d5440c1004520200703407040000302c0440600140031103008040d010fa10240b2424114034050b0565140d5050800844044021510004400050004003c1142040303e007503c008101c6841142012884000a9083c541006290030304c1d1401c0303074031900c1101181a405411200c040c20506201c9490350880e000341c030b0040c8541c034001003260300f0220b009074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 356755926 1250 356754676 356754683
    0x7050a05070b0f10080c2107180207030908061e060d020d0c140402090901090908041e0602120f03042d0605010e0709060f05070503120106030c0f2f01091202060702060a0504 76
    0x2181c81c0044103031441319010311f84003280c0c1c000d11a00282d0490401c620381ca0016084000590312078440c90042d203252040c4d080411194811002c000018002c0507142644101d81040000385554080004034443e10b41600250011901110201000f920b03040c050190703001d4000303a0004503d180140403c90252800684c2d201070328000400c030040c3c21f54000b500503400f510032145095212142c0c10800e40c000d102e204484006400100880c0386d0500103060a400c1b540380d800e107040500a8540200e02000c2c0000e041045082c40f043d20754029551401c40040c2c070601c00004803402402e100e4000d0000342f18080c0015240000611098412000c0b9005e452480d02c0c4c4100711040d0040031a00f94110349401c9031544005c1040c8c003405c1c62289000342c000c00711540c1c007080d01c40041c80d004142c81c1d11259010140044000c82051280480340007401124071401400d100548483c2800e01401c2455005495214491071025440354045405e1b48503e0660702140c07425121340c1086821541c0854018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 356757176 1250 356755926 356755939
    0x9210c020a0608222102030a0906050301060c0b06041e0b090a0203040b0c07030c05070f052106010b0d0f06030b07090803071a060609030111040501140c030307050a05070b0f10080c 79
    0x800b0021031045039131103518050034402000211110322410f5054240d0041000b50340040703a5404500e81c44070503031000d40f000746080d40c1194580040a0100500307050001c00311036414000a142e600e80e94464100c500310b602078504c81d520000c220310000c1c03002c80103060054116100107411082c4d18000c80340a181e0110111030259a803208010f21070700040c07812801c21400311110700100740c00b000010042d0030101110b0f000c00346000c0401c204c1c0d1900701300060018145680340c600200c00030401504585103044400d544586c814001401000b400052098452030240007005100d44004918420022034803007101d9103407201c0369103942e40200d81d401041680703091915808055045582600060003800950402034600002030a40b203211005108086006c90100900c1d030344072800b4034905404407481d906e44840702020036281d00c0020641403e008000072080c84180c812800c8404580d0800c1c881c00d09800d08101d021040603054036030440aa440450202d440b810101b000550100000c010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 356758426 1250 356757176 356757211
    0x1e150e012303030f0409050a0b0429060403060905010b030c15040b09010c060504060507020d09030c030f0804031a091c020a11040f181209080a0609210c020a0608 71
    0xa6468407180082400c0e007601061158007103a201100c0540040c0281c000301103228036040201e00101d501e82d0200a120f0750510300c00070300101c01d4020111424013443d0701e01421011900c0883e15038400c90344010007107403a00c40050f09204040d0300041c50800200d041e40d1300c0c64030520070000c00c0b045000483e541c9220422041080301201001041460300c10f0410108144e01c903241c280440b0b000300e40c1940d10f650cc41c0204094030341d06100140001409060001d0990b08640740e0f110700103040d01000305000041542c003000c0c00000c0055400942d840807020803103403030110150340252008d0310113a10074841c600d0b01e4010050090400142403030399500612851150382c860010041c0c4d04040e070360304599580410780300540517010746460b694601107080050100d40c0f92815012290024420030014280030500c510308020420b60400c0f90000804035044085041500759015030703610f580d030300e0045d4500010203103400900c2c9151080c003c84203400780750340d02c002c192060f100c11148540c041c2a009203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 356759676 1250 356758426 356758469
    0x15210402062508041e05060c0d08040f0609030f11060c120a09050f0a030e04061208250b01050414060a051e15070c09060b0901050a031e150e01 63
    0x4800150030301822503a0070000c042d1120f03181c80d44180c1100b010303100d134401c0c0004801e108180d00c100030700b800c0d1115450110314450168681c0c4540c0c0d41c800c00c008400c3d01103014005001c0c03130b62200036001401085624510302d8050000740b02401004042510307050707695164500491102d03c50380401ca1001d2810041c0107180d014040c006010f190142d94400561001c9801040480d500512440040000c4a245c0c20090402c0351641e005031710581c20300c241404074402c0280107290b9503a200c4451a111211181100340d88103005840b081a0b1017006400824041c9031480b40b8102d801c1500e081108040007a8030f5141d403e022136034150401c0148030100080d003041c01c00d26038810a1010b0b034544664840c40065694848107000701604e100126000c024018071041e0103005041c2c10300204025882c002c0d494415001e4170364402e05210000c030f1100342090094110501880700d800b045d040694190b4908001003401081000c21442250004640b0102030903220b8140e9280070072005c65100089d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 356760926 1250 356759676 356759707
    0xf02010309051c0809011a0d06020a1e030b04050f060a0303051b06010e16050304033507020a12020a020102150a0e1c0e1005030f0709051521040206 65
    0x71000c44152141c0f09000c041c3d03041c4050050a4210180c3d0f8080081c104107581500f5a010000003140c1421080f10200300c0b9602d5802c0342c60115408480941c80d282e84003020740f8101418503100094203200030140400c0d5a240c1d120350240320044038200015210201d03800c18038001180e4994000400c04420700109004001034000c030320307a030440c914400030410758060070072000381d05c00d011124080d005c0c05081d0241c7c00880302e07407a840d441c2030b60071888c041d00d004002180b80031251484220307180400280c19000a0b01850807520204400394600b8a008000c1d954401948280c1d0f0347c2403042408010702c0d101003102c001264050340104842002c46003c080c19003005040321052039610b10b090450714000b070150401072144a4240c0c0e4603030600e180c026200c080190384561140b10920140000507411400341c94000c0007070300402d56141c3e00d407602903c004480d41c0080c3c1d0300c051103402041009961030010020452082507160360320b45c180703a0710086008240da000751b003c9002d1203202c1e900078090 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 356762176 1250 356760926 356760941
    0x90c040311040b12010c1d061c0e030702040e0a0606150c0209060a05100c0c060807050301140a080613210c02091e04080c011506020304090b01140c010c09060c0f020103 74
    0x142a07541ca1420344555074210f52046c1c10410101d00d201d8044121442c4038001203138480c80c203940291030200d0030151001e6180484083e1350314203945003c046000d010410a941c40f00d41d002d00f00304960040414003540d101d00c1c04000301c1e00e803424038502282e01c20301c4080c04030001c80380f500c500041d200280e0030040301c1c1030010701058100142803000540d0391369032070722502c0800064580c2d8600d00c2450034000640c6209420101c14030140d44c0600030103540c028102c2e411030340c0f24a80f5010321074030311000801c180034030352044100340b00c2d11090008030000710382802007041c4281000d2518010040381c8605800c083c41135107000c81c00e510850300c0903003860b025840d0300c00c1c0e89480c12007aa0103c1c0c81141001c40041d1800e6a000e140400c41d03001a02003489000c4444101002c00b500e07a80c40d055000390769206500490032056111040c0031a0b40c1d0241d034402c032441c01c010200e90748405101503400d000b4845584100001101094000745d55409400c000c0e10385604040c00701340c2c100480d0010340103030010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 356763426 1250 356762176 356762179
    0x100c021207020d0501050a02121e0610020a12030203070f090302030601060c0c0b0307030c0306231e03060a0209030d081b090a15030b0906100c1b05060f09090c040311040b 75
    0x150f00050700022800e114103841800a00801619148001000388441c403006025007502c1c03c3e000c00304c0c134100c0360849006034007000031560b020140c89801012400c1100113a4001c1148501d006c6005a40781c258020f1031041e20a0354030042070350b500082c00c0304c414265100194054214000603c61144522101344400e03000e5201c1d5601a5510303c0d08624907130080385c0c240c0c00640d5583c101c0c400c1c0d0f07602d03005050003002d551181c9030b4142140524500c4c9d001294540e07a00c100d28060f41c02040b003a04d082503003942c0d030b002001d4421038030300586510040d500c0b0f1250070348a030241003c1940090f0007600d0a50182d090240844001a42900029003036840010810752010150200007000041206101c20410303141e41c002c90a409000148581c0d1840078201e00d201d00c00c503190000215501460f8114001d07007014540d41995001200f08140d682141c00c0700e6000000000c00d50500c220f500014450b6002c156407282c1103036241c4100d15424000d41c000140005a155285640b80c905900440401c440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 356764676 1250 356763426 356763439
    0x1e0604060e16051b0c01090e06060d1d0d0c0b01090e06040303020708131d22020f0d050712110301090305041401120612030905060a090e190606050309100c02120702 72
    0x2090404c180c80035000d0540012140c0c0a49491025540d003c61010700901c4201650400c40c10035500041050042503800f140f116540c5d0504406020030034410284580d882040c1c0b0b05a14600300028040d4000c000d007070710200300d108000100511244940e8014a0507200502540d4035075030f4040b0081e5101c1d00c0180e405900502c90602d007044901c0400d001460b008410904010001c0702e0248010703002000c6800c0e00e040c136100e050f0282c503c00b90100c03400ba0f0485183d1160505800040d401e05010b000c050a18401c0d8840451260040c1360440c10042c000d4015409041080c0704040c2a6440c588005001902c14007080000070907840034810030502c14180611810b1740d150b41e0008031501c542c4404c0a0766441011401450742164040d8040e00080e1005450304c2510039020b0041d200070b201d0120358041d41c0c00081d801441c075501c00320b0140a201d07000e012176680c0307490040550300243d500030590301940036415250305503489240c0c0d000841e42c001d042225040b51070030046400c48081a070b00100e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 356765926 1250 356764676 356764687
    0x32a020703081605060a0e0c01021b010c170c030723150403020c030f0309040609020f07080f0c030c030a1b0b01090b061c05011d0906011a090402031e0604060e1605 72
    0x410610016101c0c1d0031b0745400042030910343c041e69240440382c030049815900b0416058894a203000c4403003181500a007403444007800540390203c0c1c0c0080c211504e00d18018003250786003440703c000c13005100c240d01500e01d005421080744003460804000b50b00c50b400d107038410707081d00c0c121410550807140e0050090040e29484604040841d003002102c0c4400302054000155490061620f071140ba00501b0845800310304045054031015801c3c4195840506100004245c640c4194084811614140c3c0890b003079a45842c5807011302542c1e50054134000c0b012440454940c0030b05104410603140860f0805040d15840e46408911001880754609281c0c00010030843c03e400c00141d01640040c1130200da40002c0d0360741c9449a0100600b00c0240400f89856003030382809180c001c0094014150344000840c0600010b8000c118182c0744a944425904203002204000422140314aa0381c2d100c00711404220180c2d43d004100822641d090085440c0b1040110200f80d00036542540e600c68a80c0d1424440d2509 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 356767176 1250 356765926 356765933
    0x30d05070516050c1002122d120a0b01110a03030f060b12090d0e0607060b010302120901090212030f0406080c0408031308010e010b060706020306011e032a0207030816 73
    0x1111582081c3c5295001a00c1800d01c0c0c146035a510031003200910141854102018104205201d900c0344c10b441070501c1400100040d4241105105000c40036010b036540e0410a00c46c40018407041703aa90a500b032800d00e55080c03550145d984c14400c62001005066a0074041c4e07401e5008101052080000365680c40002c07601162070f400a1021500c8440d01c00d100d490480502c1d031070001c811650408018800060600c103440707200c16074140f241d1010010a40522110040307000b409008030f0507807520300754828004200380650010410b00c0c001d40310722074280391080d81d2170382d03c1c840d0450071160202c041008101c041e100d40c00850f00a560040780610381642d03440282d1554100c10400610752146290402c030088092040d4014103016000900c008520540052014068a070303000c2d0030180c000000070708513032040200020080d1380b607070014100c0400e0304000b030080002011128085540c2c0d01501c004070250409047c10080d2603004003003141c19561009160707004081c1c0400d0142e101c080d8007000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 356768426 1250 356767176 356767207
    0x9120c050c0621060d05030306010f03021309020c061311040b040f02071a15030d1209020307030302030c10060e06010c030c06240b070c1a0c1006051203030108030d050705 75
    0x40d280c0d03e15140e5600050142e80b084804000d03220f14451700040c003140001420100540340c0c80135007400d1004000c01c59075010b0700a0301c28500c0b0010301d0308248a021601030011703030241800030032000488955540d030700c0004071076031003208020f40140d02d03c800b9181c1ca480c0c10703041541c82200142021454400903c040700a98011080c2190740b04056844604024004054070741d01803a42c1c0b4500800c42030750000709480e010a041c078501081210000c0d014a181146c000140301ea901030304850100d544e07401e00035142c0e00001da10b03000c0c50068003510b50540c0200d02482d0251000201c000b0b40e9902d4010040d42c850307078892000ca0034440c001d1001e4011408601c95420310301800000b03450301c42c07420304541154541c9608240840304060000101081000d0707504801e442c112284814203180c0e10813004094000c11381209214400c1010310b0024410903044503044500540d4140c1c860344449a03556240c2c0000d01864032541d0051243c0c0c101c001641c3c01c120780150180c149589841c540721100581e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 356769676 1250 356768426 356768437
    0x3142e05060301090504062a030221161d01021b03011103090a170c0a0f080903160503010b0307060f0e01030207060204030602030f0a020a020a1b080105090a060b030109120c050c06 79
    0x2404d5645004000602285028140080010f401003c1c0f103078080002000303104502d610182c0030907a011406e1040c05600d49003042ca0544814400d1403286403140000041d90051028007001074070b01a041c021102c154421442c4100058014140c1040440911121560240303d03196040d925a00c91250f003007100401140a442a1000342050072010705040d0300c0100540005159103c00b0480b0301c0340c0d8000414100909580703c1900c003041403440c14240c4550007900107040d410300a500b840c40c02581000070a2084031070580082c8254401402010b8540c0080e01c914404910100c82041040c0e07c00c207442048500141001410070001e0b4440d00200d8001da0022a10030760300000703120380e2000c440411035107c8504074041d454020381200003504e9801e0580002c0800c1d001e100d260300d401440759409000307424440001c00c25880e015034056907508a19406950305803408828a0403418103015140d855604550301d07107003181628104444004695206482c43d0040c99005141552504000c18 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 356770926 1250 356769676 356769689
    0x2040f0f0614030408030f130204020a050c0f0f0303070f0203070f2406030503040b0903010b1003150e04051b0105070629040e070e04080d0606020d03142e05060301 72
    0x10215810800003414141d105103820300714200c24410807000448190861f64003d401004859840c2c1b41e0090b444512880c0f17020007075004c0d0020450000e07407540a405403044400c50001c07a0f17288107110024548035000500700340c04a8000300009001240074407200c46403650b8501c110ba180c142c0684070014201c803000c1d400c551035260621545400e40800d1115400801245000c1240070f18503030ba0350355244a203220344941e000c0041205082545c3c01e6001e1116000302805100303c0b280c504100a0080050058a190801000b040429008000c8404510599001c80200130340200f8200302100c0c012a0340506040050800924002899600602e50b00440b60807461b50300b41401d02440c1c50311408005500d010b145002070b8081e1a5800051442c21038124400b904169252130030f040344103110b4409030500040c1001000508142d00040f0000c20b0340103a68200500d086d205031061960105859045a02000303403141c001c85109401c20351591802416160201c99850000c00d0030b0745c109912030f5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 356772176 1250 356770926 356770949
    0x40f0206031816032001120e0a060501030507050109081b150c2509330f080705030d091d091c031d030702030303132f01030b0301052802040f 62
    0x200100040c5000d24170b0040710b8201040501d41081000030031b1f1071103401c0500442a2100c2e500641e0000c02d1049020154002074103110755078407818410ba55460510520380011284040060a01e42c0070070034905540700114120361658014040080304500e1511000a4500400c10141e458404010180603084201f101180503140c14800b035802c100580e00c40c110311418440c00422407505019000780c02c410302581703002e02100c9040c0e0b0307200329005c5030802d860030064460045001c031400601d91080307d41c100c085441144a146049805030003920800c11321210400d002e81042c0ca00380f04840d40420000c0c00c40702c101c0c0c04c2c64180d007041c180200b0312801003580c5084401c11841d003458000360044054004500e00b0340c1c9940401c1d56880028075000302240400702000400c16088503505584600d80c651101c0541c41c8507040301020040700416010034900071208401c0d003418007409101d4100d80360411442d1507210b44c1c41802e0403201c00e07507141c2660300704030100c0c1007000d50200f04094150400038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 356773426 1250 356772176 356772179
    0x110f120c010201060b0415110102160b04060b010c020604030816060606030b091602070501120609050a061d0f0114060d09030207031416030303020a0302190305060a0e040f0206031816 80
    0x1e402c560050b00f0034000f417802003006000d9011031403107400c8603803a54030b040510070b00240840c60080c000c203d00f07009410840010030041c000a180420302542c0a0740c020001044140015034802003046c2009400030024002003020600e01d801518594a0031004020114156500d94040301e40c9508400c1c0885e6a030309040c0c005003041c2c001543c0c400c114084d070200c00c040d030000207562228688036560401032828100b1845070b8486c3c100320010b00d018002030105003440002f0101401980c0100342d51008510203420745181c00500c114000d01c05403015240c203034202403c000407808600a200d4002208002ca07000140ca144200d00c5100e0003540500512411352529040340c3d43c2c21424480315a200e5a01d540c0d61480780c4800c4002c4a5140c00d0050f980c030030160f82a006401001e1210007422214a01d40d50001c0d007680080784203101c200e5480081e162150801c034108023054402a02c4e003500b00310301c0001030510720002c45e0403140b08101c212140ca030003904203140018400031400e07a143d90090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 356774676 1250 356773426 356773429
    0x20f03151906061713080f04030c090b10080c0d023906310803090106170d02060406150803040602010207030e0906090f190f09050c0402090d110f120c 66
    0x903180601503034642240c4041307400041d03110704980036000300f00f4000000d50180800800a045400ea50003c03042d450f165640c074100251219054800c01200c030b400c090444e102880c101038a45100d261585400740b043c1c035280c54030607480d0800d40b00141c070941d0070080d004040001006d03040102e10301700000402c000001c100d000040002e0070010046601110900054210126440c040c809106d640ca070300d04d68030210220010ac0200102401403800041403058950040d04840255100340c9426103480d00000f0a02d5518440d10340c40c0001a004040400c0024580d03400101041a000503d10141074440030006e0540d80f05900980150b0350000c2d0400825411807004d0034500c0b070890715001071b458800041400350000900140b0714002e030100160210201c0001f002d07c010723204204200008003280064010070410406560b140300301ca00310100c1d031409008881311614003400e444a95001552018003000800828941c022143c08000301075448400300205500352483c001c0503031140520 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 356775926 1250 356774676 356774681
    0x609060305103602040f1407090f0608130206040f030b0105030703030807030213210219080a0201111005040c140f1c050f1002120106020a0c03020f031519 68
    0x100314001141c1410000f0f5525140d402d451215107a07450400c150540c185600c41d11401c41c0382200940c0246403400e60210b000050b4860024400040d0b01036105803a1080300340c072511141c4c421411012134149051240e00d10072220709400c1500700101008186160340020402d4019401890244600907003c005005040700b074a0700402060307001d0b00d902d5085850007044610020903000c00c1c190006800c50502d80301740c0384000200400f032a105180c0700e820106d081e42050410081c0c1c494812080034010900b1610b0400007281d42460080140c02c50946c0151010000e0308150781080c001d80f0035020b0b0089840c0102032165105409158050b414010000c02c9014071a0f00c0034040c3e000710411055a80350901d0b11206103820041601442400d8601310b440c140e81040c411032203000e1300100300001809600a000007a0704664440da046e0b0300e03542c08aa98000e0b82e14050001c0d5280310040016080600d00c90051f05800b50030b40d1031042c100c221444c4a1b803000c0e9040d070035008984c00d18010601c0e162 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 356777176 1250 356775926 356775943
    0x3101a1504080303010b0304031e0306080d09050a0314120d05061002010507230904110310080f0d0c06110a020d0305091b04023702011503030c060c02030d0609060305 73
    0xc1180381858100300d8035558a001c14001d107074012000001140a2500444142c00b0600f0002948440007503906801005080d031403240300e100b0b105040a42004a0085c0702d800117a0720045d1900c48900d14546421012903e17030030300c0361164054140310032038003581040142001001948085000d091070b10600c00004000d503824021a450601400505c5a000c2c841981c4080100001e02e2a0500480e03080207601c40c60185c0d0798010b1402d424111803460f1840518030801081400c0b00070b8503a80e900e41c1d07444101c8076110f240d540c2c2003000300c19074043c05401140e480c2806182c002070b800e0703030382001c051807640042d0380d00016921030721010340c0d41030b41405140d60040c140b0001d0001d005809014000011016035914441c64003c903014428208090019810103da05030144c0e06900107280410060207214241d8015420708c4012901524140b00d0b24086035130581e581d4111108688421000b02241d2003120118001000702d0b00106220303000f40000b90036a074034006040c9145203011442d040c6070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 356778426 1250 356777176 356777209
    0x307110d03140601080a0e01020d20041d0a14010e060301110910140706090309090b030312130f1b14040c020304050112140c040825120203101a 63
    0x105403510082c8251502d4143d0001e03028280300040752268a104c41c003410140d0000e0106610102e0740702041401504018800c54240044192407858035000e0f140c00c0c07040d40030701c0814508a80310201900350440340140e11000c240400501d614070407401805416003030740440c0ca01c51901c0f06101c00b038a800c0c8600781c0d14540c2040414500084180800c41e50003402802409014207414010080c092180840c2c030104d51295040146a0403840c000e4180103141c06802d0801e03150600680d41030a00004442060411062003665603440714408050043c52200450340783d0182280580010740c08008203450801c10700041411030b040c0412007030035072401e140083c802c50401d4000001240c01100315425140b082c40c240007800000c2423118050300c0000c81d6003d02484140030005080304840282080d00c1c442002c1d580c0100c00e00200ca25903a0700342e01e85030b00c6221030b21010000c401c5c5d00c600502000744041e0680d104d9080d0586840c0403110782d600c0c01ca02c41d198101c0160602d160482e10303c00301420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 356779676 1250 356778426 356778431
    0x606030109020f060c0307051501031205070807020411120403021c09050a09050912040b0703030e010b0109050909012406110f0601030303051009020c0106260a020f0d080307110d03 79
    0x6071600018440c01482680d58003410001810000484050048402554102045540844400c8407032101c4140034403081d20710701c55000850300c4003071180d0116000745400410544c1000b00a40801c0010300780599142c030f240c1020450004070b4603402c2c024521983c06500a001c0750892120345520b21400c5005480420850f0700c0144155943d032480c00c800c0e101d014400180741d60711000000c2c030306101d41c1d019141410002c17030f00003074000302c010090070740a129075000d000c00740712050703401d098880080500e80420195a0300340200d00301464102e6000302d5840000c600301c201400c2c00c0c100720781e0000c500079040411840904c203254100c070400c010410108000e044498560b9407654407104107002c010200b5840350040b68007504c0e40c0f50b500c000303040c00e010219038408079824524020b280c1c40c40b408689190081c0800059507205100b0340f072200711040038104510302d5508108090806581e1180d03c0414120310f14007240700b09020f148540c123070752100c030050b00400e0941450460314000f60b400700360 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 356780926 1250 356779676 356779691
    0x40e0106180b090114030703020916030c05120a0c140f040f0518070f140a0c15020306060d050c0f03010b030f090a030c0230160f060206060114070506010e0906060301 73
    0xf2602d99105045990700d0025100c6500c20400007420701000d6032020350721011010a00800c0c0701c00089034561860292010000b419900005581501038908040c1c0290185000650b9074038894014401f0244e9910302055101b081c98103008a07074121180382c4482c06001b040610900305c110701d684c0d025210482d503c410080d4603103c4441e504d03500406000c1000915074003a10035078002c51101c1c440c80b120912068a80d100500d009064140c009003d850803184050004804219842101c2c000e190140c80107141401d050144409024007a104c1080100c080010300007144248010314040d20f440d1100729036a00f0424040804000060481c0006800241d00a40002e4100038040e402a60540384220b00d07454003412410f56440081c032400352483c00744a4201c00040108079280710b0702080440ba0802510782000d400d03840c040b8041d200250380b000020880c1503003d0003c140b0740440007404286000955034034142040000c1e88114680c80c805070621407240014041c466220380c069000f0441e44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 356782176 1250 356780926 356780929
    0xb04020f0f13030b15040f1b0f0905040606030e25270c020708011d070b160807080a0e0904020d03032004030507030308010602030a0210110702040e0106180b 69
    0x140301d034240c080a6068009074074907001004030921001941c210038005118985100103011059103035203400d10842c540034114a030048284903520495500701c41804403c1e110341425a041800082904144641c02c10005501c0e652405408003800c4159030100310b00c007408200034070f030441d000841d696a01e054051144c1d408401c8401c40c0c02c90fa00035030312105129003401c51041d40301c64201c0740c00c0144e0802060444aa07000648201103660010003002103803038540000c1d102002c84200c0f80c0150300b1081040210a10f80009001550401010042c0c8645d0b1039803000810b0b44a0301048075200c1000c55143e0b0010f400481004401105448014440c5040e42c0018489100035600905260790303090a4020070741580108803108007000c0c1615502c07501e034102150360341c1b0144001c50000702c1b101c0010640a20100544003c42c00903002010760f00f60141651000c0c04607094120000d12003403140c90056601d5004041030760090f403000103907250800044980301c800690001101600302411240346 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 356783426 1250 356782176 356782207
    0x90d12180608040303020d021c14011409160212210601140706050709120b01051014030f06061215010e01020f0c2209030504140a030f0305090a0f0b0403060b0402 71
    0x2144c0d06240050b0780b1503111074490000e000c1c51140000300c1c1d0b551a10741400c00541c0d40300807502e4104065810302d681ea0b0b0122075403659000240260400d05d2030003c01d40d500c00c100d00130585070481c1e0050300e01650706d41040c2c1140d9040341c08119104240329100d07201e04004515080c0d0450f130f080c40d0402008004101c500242d2003082001818207030b58000003240315100b440f0710409800307010340c142d242000604000780030103000e0051511442041c404509074078010000c1140141031402c505007941d8402d011050000c100078509904254200701d00604181d1040d40300384107030f800f1300115801084035030004149035400051107042d54011070b20100d009400041c8200d98034002c0741c5144400e61101c8002a1407440184034800349070030000c2c40c20415030000c000d4802d507a10f803003e4409981520b8104040d09013113200203000750862800403070110f8468402000c09110103440c400c8207070f039940725480d0031a0450780121542e800110702441080460301590001c0b0f8000c0304c1c194107100c000d900c110382 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 356784676 1250 356783426 356783431
    0x5030d09030311151603060e010311150904020712030b01170c13031407061d060a05090409050a05010618090b0a0b03070f0b030f090a0c0b0c03090d12180608 69
    0x81c40001c401c43c000c441c40401422203444100c0e40300011034100308145c03030060341c0d0a050400220741060800b14141c854440020b04803030300720b2050040c2c01068820300000103402589001620020407882c1c0d26a150b600041080c00e10440110b440d0b90980d400c0142251711490700c550400c82940c840f588100401002d013034014040d8640c2c03694070b40800c1500c00d604035036540014001c100d810038003c9400008150b600c2160016242d181d408101c44404007264066803440e84e038002018003401030305500c240d010f45500c400c00b410014052078551200e51030501d1109048641da91201001c6c01164100301c44040255201a0140404c812a80d0340e0206030f14010f141060a40d170b5007030311910703540d800c00c0250001c01e0001004003000e0b4903041990003d80c030445056948210f0700c000318079036410016203140e0340b5400c000016502c0b07003081030311005548501d181c9011484240040009aa00d0041c501340a0b031007000300070740c0703040b03e8a00034050007041d860b01041c0c9401c0c46820004140c200303b1599 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 356785926 1250 356784676 356784683
    0x10e030a030e0301150308121303090e07050f0304230d27050d060b030105010b0c100c0302040807060801031104141303090902040605030a0b0603010612020706060e130c05030d0903 79
    0x400c54842d8400300b07006040c18081955000e6010200009010850008080c40040c02c41e150000755034200900c00315192901004001401c000020071030401a000c4550b003100140ca80030b850b00340400c1008a01d03402c16542650482c00b80c0242a20301c0c0840c44440d13020f907212402800f0030140b00c1c28058203032072003042409441002c00e800808407240811143d00907240040018400b50b503203007003410003041c076040c0d8640298039140000c22040b00c44020354200c0303101940100409490801ca03c805480c04010a40034541c0078800070603041d40910009024200c1039580280562560415a50031010603030403a008515200c00240c14032800100710303600c1154076220005895a5146c100c44282050b8003152603e4030104005c9025a800002580505807070380c01801700d61480c1007000001e2000388a00c001017a20310642c500014034603006003000601504000030310940d81c141d5a59003583c1203071805001c01034608690200324001240501a080607401460f104005180c040e0040400d800081c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 356787176 1250 356785926 356785937
    0x905040204020c010507020a0b070819020a0c05100f180b0103030818070f0510080c0307210e0a141902150d060806180328050c0106061d010e030a03 65
    0x201903490780d4049501c25074450000b00043d2a0114000707407510035015088400301062004600d119100322040c82c082c08150141001030165601c00e80000d502c9210001c06100e03500750040c0100c0c1081c001c006951007885000306440c20a103001c1811505602c0c00690815024146000865145034405040d41c1d071608160019480305403980001d0001c040b6110030921a20401140005c0191443e004668003503842c043d0f04494078100f034410040c111485ca00704c003018030028942c00c1c4182c0002c0140300040c01424040f086580044080e504111f1007145c1d658401c2c8138800400628802c1d00400c0701415001c2d08880b00d0701a4985284008641e000e80300d1806c80e003030303100c4c0c001407401103070315007401910104159540c0f43c20b01e6413a11412a000031080510101c0c00105c5c400100c2200c111200503091001010700600703c0b1a40c14180e02c501200f00301e810b00c030001c0b100c0024401ca4016003502d4940c15618075040c000c10030000422442c150402106800805403a1000254000b0099160801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 356788426 1250 356787176 356787181
    0x1006150e0604090615080f060f041808040b0c060702030a050307230304060b0306060a0518041a0a1506030c0c0b0a0e0d030b0a0e0906010b1305090109140901050601090905 75
    0xd80798007454000010440c941080000c60a206200b10030703200e48140c48502281e0383c0c240340c80742c1d03c04045450581144607582010424075042c0c1c4003014445c00415040c0d40301c403640d214080540c0280c1c02038014000001410062090b04208482d031080c002c1c4000c0d0701d444000d01c40140a4000036040300b040c0840003081c410320501d0b43c4002c0800b841c8140141e5142e1916040001c0a0f20311a20081e01030b000740c6020816134280904a03505858002e00800040ba000701c0084e2041c2c10024415500b4122810051841d4007041500c14090009c40001081c00744c4000c00c011100c580c1c03540681e05040c03a1001542d101908a03030402240c2d9004481c900b201c0c0c0d00c0307400d40c40113000300720b0402c4541d02400e04c1c042c200c02e4042d8014900610155410403200f62950b0101543c0c6006582015460344000010058015108001c0c1100200b001c40d82c4021566200070408014083e00f01d01c81c001e88405040f4407407100f05025503405680c642c001d10150034210000390030301c0c00600901d4183c6445400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 356789676 1250 356788426 356788429
    0x29030603070314060712051311030f0118050709090309050105030405071a0a110105060f060309011506080703142a0702030a03051b070b0a0507140610081006150e 71
    0x5510085800c183c811201c8400c614045480e00d40c1101c0c6500420054680000300b010785104c0c16104400c01801400320701c080d0349840c203032604000001c81d49032042c0380780312000382c6080c01104c044600015002e942da406030316256003400030540100c4940c2d49000307990780200c1c1e4031810300390844100303080165403900d40e801c242e820591948c000340c09a401810030b820a401c44000104680400741c0c0e00d014036545104c080c0e42c03d0350740c19140c441e4011a03c0f0a01400761810348001c1d40c00503d82800000c054400720a9001400020b600400118607500b0802170a60f4040c06540540a0598801007052074004112500840c06601841a0410300d8054500b480c402d074003100c80d03441d00102110744c2a420f03858002c101c0c0c7e0180b6100b0212000540002002c000c002540c03809940e0a0421765050004119017203031290003d040c00d4900740c50300708001d0b8404000740441800f89996201381c0c41c0940c10802514034000c00b286000b1481803038030004008000359050608940c40080ca00189484a60030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 356790926 1250 356789676 356789683
    0x6030c0512040318060915051b10060312020616052b020406090b0403080405090a06150e100c051507050909070f0215071b0510141029030603 62
    0x1e0740540050260900c010325802a52103030445108144038030400c0c0c0c44410844410100784074004101d440d04450b0080607029001404000d1000d10780c000c07140744a09009450901c000001d800c900e0b0b40d400f410b10500c017501c0c402001d0303044113000030311980c28001c50b107800c68140019000d08015010403001a444907607510419a14094101c9050540d900c1e401c410003035103d0701c80c01e00030442110001448203150025a811603400c2144941003a00c6c00c070500c41c1d1400c004003904a071540c1c031540411784c0605102400c036001d21954034421010191070600c15455240e14600050007c20f1041e00c000400c0050417100004030054002000d859010b0255a603000382038080364030582c100d040101c50f2b0380c0090f504407d20041e07400c4075005116251040400c2c0400d80d000320000342c0c80b0500d01c0035686d9100ca801030f082e00c11011a0206110805140101d1b48600e82130381002c4144820300c12040071480c03101c40605080c0413420803440f407091900044107820340c61402408804000614240e4050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 356792176 1250 356790926 356790937
    0x402060d091401060f051201050408031303031d061008011104050409150e0d17010609030210140f04080c04020c0c010c06090c030c06020f0c011b02040b0d05010b0a08030901020706030c05 82
    0x102c2c0244500364988030512400b4603c0d0003003d000700c925003081c400902050240d036026a030052070360b0f440d40d140c8961008184103001d109400385071322140c000d802c2c2c1448407a10170310508104080c02c10b40c2006149c43d0170302403040d8404070706030781440601c3ca5000c1800c81114101d40003241c0018400046140c084d4801500c0044071485500c2c0152080c2c14420104d0f042c180c0c41e5140d541c01045413090300c2d0070307149004c0c00e0285d100003a02c1044148010b0400100004e42a101030030140440e0b5600d018001a546c0070f20b80314034800e080424100b0202e071082180721603488040300c0c207504000181070444ea0704c40d490702d109410030612100781c006000b403540c01120b00a408c18a0301c0308068603428601914000c3c0d1203a02d004ac810710007034900680003c90300003242d60059691340c0900c001c3e10441c401c0784400d004280d90066490100040c19a6540c420b503034024032600004c1203034556082041003100303240d8401c440907001008819000c0e81d001c545007066819508000820ba40c100004841c0c60290 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 356793426 1250 356792176 356792213
    0xb0406090c0507052a06090d0b070e0307050409050307060b2403150f0a0e0a0b0303040f0603060b160f030c05030c012004030206071205090d060e01140402060d09 71
    0x5005414000c1035008004140f164003801c215050040e030070a240d80a170110440301c2c0e141404003010380e141458980003c20103200c1c02040707268180ca442e180d05183ca141583c3c0940412030501c01d0600d28101801120001c0004440c200507540882d11115128450007100901490381d0b08804100307541e0b481202420105032014402010513010401c0d40e2540c000e403507030000e40343c3e038526407111450149550b02d031107800900360020462826400780c1c904140030700342c3d05865440b0949041181c40030005803000b80600264503521501e4040050308840ca079030020b9505520810a1550f840014201c8101c1250701000c4500041c10a00781200c0001101c6030041083c040001c0038041800c0541180d80c0010803034810707030301c00005014041c40b90311940c40b0094102c101030142501141c2c03101c0400c10051a282840e81c50180300000083c482d03120203404030b4a256440c0382c00e1a03251400d114007020721056055201817414190002440360240010702a1115190103c05040004000a40c07100021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 356794676 1250 356793426 356793431
    0x81e0a08040e01050112050411010f1e05070c092007170a1106010501020d0c020108150901180f06050105120403020703080d0e0606030a0807030c0c030210030b01030c030c120b040609 80
    0x45072548441840c8003031003071301e000548503010800c1004503841502c0c0510b520180d0100030030654401541d00000e0798001c0c0041c4a407030210907401c100742c3c111501101c0c4840c3d0301c065888000f03240060700c4405e82d030480e40e03e60b171910b20110071720504040da41900b00000960b00e603d4680a1901442401107521240003c40d800320700450003603001050401c0c4a60703010251402a0388031401269541340b80c10130180010300040030b04000d0750261781010313000f0f0340103601c20b00f2402095000c110000750030b900a01140304141040c0c807603d01c1c580316441c1603000e111020f02c8020701d8070000902d00d001701110324400c507090002107000c05008002c1c080041d50700206d0f00da266801030748100300903c0d1450305181c69015040c001285860003082d41c2c440290f100e441142013034404e44044400130008142215888030001e004409a51a584440c6181c403685e40c0204030b6024600c00181511100045602414200707550102400d4104032216110340300072200085007111200041c0c0640810341c40b041c201072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 356795926 1250 356794676 356794679
    0x1060212070f051515040b060a03091e0b04020112090305090603070201020c101b03020301030209150a181508030c06070f020c130b1810051e060313110604081e0a0804 73
    0x18140301240700f9840d01005034842291742e800c3c40180d91130b000e03000384c1c03040c07040080d82500ea02030750048020301d005001000b402c13510000356a805030515042500c42d0320003003040104641e0b1050460f12540c240c860240105038047d54040c1a83c064a280310f84552404400260518407d49c103445840480d0b004848050007200714140081c50701ca509061510b030b46050b4980218040d0007200d048a501500c0f00e151035643c007808201540048224980c80b11401c01c0005014103401c0c0c2e601d004030030080d000242d401d510059203000c0300c0c0c40d901030031180c8c000388024054040d0224041740d01c04040e0605241c000d020340781c01c07818142c6800c041588604519050101488103038030112b03801000341e42c1c01c4c0ca03900c05800000d04080302103580481c07000707004100340010300703003582c01d8001840030001c0d1204045a403070000e00c003504200c030f03807191100e207034000c01342405850040c640070b102c0103072615407416080ca050f690301c074040c0701e00cdc883c0103ca12180885040c10f0402c60740000c3c40c0c10242d041d8846 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 356797176 1250 356795926 356795953
    0x3071704140d020c0105220f0e0f0a06030b0613150923060d120c0221010609050903040614040f0806090d03110712090305071215020301060212070f05 66
    0x40ca81d4201d4400752240c06001100d5500008001000b61016140d4500701003603629014907141c1c41c17020340180890a01c40014030745e401c541c1c03684060201c1c11400469031900842400440c6c000a001c1000d031400c019040002c00c4010050700e4002006a030007807200480c1c44114406481100300a00401c1d095560014404000341c0c082804007140074000380f000c1d91070b60031034032a0000c241d4000f944801d9030b80040000559000320600c09000c82d0a01c065101903640015010400401103c1030306402480201003030030382842464050b00d4140d03000c0149062580110381d9034080c60080700140403403140d81c1c41000c10444156001894a0020520035031303201d080068407032106860034a014410902d41220440c00ad00841d03016024900750641800c0755911001801500740f0500020b200a514020000c01d50501090000e000340044a0600600a00d801c0a0300302d040401086100d205100505c1110381c0419019004d0b142c06040319240c2c0a82d084c240340c0125508001070040c414601e514102 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 356798426 1250 356797176 356797193
    0x7030e120313030e0a0e07050703021c0c05010b100905100905090412110a03120c120906062c060402030601021606211e020c0a020d050703061b05040303030203071704 73
    0x4184203aa8520030504d0503020700c04428010b00903044482c2d003032000540300c070f171040000e8030000c1e000c0e00c1121080d00108006840c00d018414100c0d002441900f018010322500340074282e004103081e04d03080c50b00003c001009142c00c0340da0003014818890200c40d090264410540040500f400402919407401c0510b00211510303040340f14200403500800d8910344003440401c0004006402d03441d40010b4181d070240c044014484424100244000940990890b4500703124030300f4528800d05001032840d0400000188084240080719070304092021f1641c40134001600d072030b0b00000d0644001d44c1726103c0030010303400e000001c0200c0d40090070b8807800188403035001000005045c420083c4020306510340d40c01400783c5121103403040401000c0001c03200c48046e0303a03000341041006801074078144256580090701500c3c3d1074a0955046d840b240c0c5c2030040c8aa1841400034901c1c1c4020841c4030b40e4542c250151960003036120282c24590b01000081c1c03105d000310b03010101c2d8440c030010312429280a1411901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 356799676 1250 356798426 356798461
    0x8070b1b060403080c2503020601080c030309030325020603091b0103020702030a032f010605041d120f070210050d11030105030c0f03030f0c1b090c0307030e1203 71
    0x120a62025084030100808110035008582642c0c62190310345d1107428192280c2d00c1203000303030400004440c10001c02c03040c40c452060418402d03070181c101d0303500d4140254176003641010001e10903041001807241036500042103900380049403030140e142d4520f03001c414820450804010750803103000402c00100c2100480c040c148070f100b40403043d0341e09001c500110100e000745a0020340607032043c0d2100b004079024410030840c80d40844d540d029002803910482c500303c501c5130351224040e13448010034409450b050288014030041c1c51502012540c0000701d0603614051200c650b041e80c0c1d0001200e001603140d078000c4070203003500038002d4542030101d00790003880c6600003c081da060a151460030b003100741da5002103e04a4400400070009034104104212050f09040380c12681484100110700d00c801324040035181c0783d42408090f220388070a0401e910a16410b10b2100344c0300e1803107502003207440b141c12000d60790801054640043c2c1d0004450f406c500d04100009130840421001c01004250380f0400070040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 356800926 1250 356799676 356799697
    0x9030f030501080304060e041d0d0f0206090616140d180203010f0b0906060a050c0706030c08010914010b0d0b130621150209060d0608030d1d06011e08070b 68
    0x8100da0f41c420790f00780c50b4040da000c2d00000800c0080340086c20b14040d04031b40f0701648040301c1140080341000c8164606110b02d2024000324804580484103541c060040d2a84001d101c0060301440c035140c00070482048140185c2014000505002c0480145901c240d4038504000c41040141c0c1080104c0a220441c04090807442076081c6080b5078105081400785200e418800341c61101603480b13410030441740b0b0b04040d0240f410000c061044c800400c40c00c01c0180000c0809e0f80300059201d40c3c8130802040c0e100c05800901c80f2a04000d40d0140032401400c946046505005e88c2d59103412846804030090b0400050b080e40c00740070403000c5030700b21a00f03510200840e1410b160302001c079036946503a03909044880d00050222405112100c0c0724011076001042e0b138410007005103141c00c60740302034007044030303e0743e00202916440070038100c4281406106905840040b40c4a03c0d14141c5411803e542d00d8905010314103d607903071920540c0c9101c3c05000d15101400c01c501c01d036006651101d40c8a11982c01420110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 356802176 1250 356800926 356800931
    0x30105360a030302040906140a09020c030d0504140123130804050303031807080c0913080f03041410020423040f020d0b0a050126040f12020a020901081204051306050409030f03 77
    0x8094004da40224002d02002c9c2a840301545003050800094000c4001e03200c2c207000400403c10300503074601c03440344600d2083e00110400c809244480317003110a100044852507044d4070140b805160a00c00a6a20014411025405120354a00071055001c0c070392001c0d802d4400881404450400130000602e0540440f0840b90919920034406035903072601e001641d0011400300100e50014511a090a4001c0c080c0a00b03038075280350b014411425078012142640c205038060000c0c03010010078045042c84107050b100960030b05080c800d440c80036514103003030005444d02c4002d81d0082611140c11584258040d03c40464803001844c1c2d100d0301501402d5000c5100e001d42d0788002c201503014502c0800400d01d030405959030300440e1001001d545801400c00c1c0c94000040701c2e91000181d58841010303504002d94040e26a5030810b2042c003025007011f80007072031142c211040c596061610b1000b07031821038104440400002c01400c2c8480c0013491036401c240d40003800c200000040c9031300301c064410362480c6c44e9002c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 356803426 1250 356802176 356802179
    0x90d060212071b140a0f0f0506010e01050a050904020d05060a091104060b040e04030302070b070c02120105010302092202030601080d08070f020a03050a020312010603050a0b030105360a030302040906 87
    0x1110b4910110180c940001091680900440e2411300c50041c480441c400702c907013043c0340e40c50b64510a00220011070301b0010500c9407104001d020b0054500400b0b5201c0713054603d5040100007480700000e8000c650040904500080540d50345e62100014160448251207403170504403103c0b4082c0c82075803003d591b40d20307208028100f18181441a5011150f200e29403d04040c14060f10503088607026009808058090045401082003203c0e401c1c069503542e1a110103035541807061050840d202d202072011645840b00410250b1500100c07982d08c02c00494000c48030520911105803015030030600a5014800d14001144600740040e84020300d50054842c510f20345c0d035a90080318442c40c1d45000c0001600880a00300001c0d0049026000c004e0960064906010401c03080b91140007090f0b101e040029140c60901109a60318820b6007034410741a07000340024a1300e100f01e00d0300d060911034010714409685c0e10741007148074248004008085010207589410300700d810002d002c0d4000d80100c20b8140d04d0b2000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 356804676 1250 356803426 356803441
    0x306020a03230a05130c0f0905130f081b162d141807020c100f0e120a0c0909020901060e03061305010b0a0303020a1502040b12060105090d060212 64
    0x254181e01c40e900000c9041e150b44024007000900006420210f00d51903000317041e0002041c9011010140c0801d01c07545418614180d00c490540e080940042c0190841ca50b41f5004680c03042082904107810901095803030044000200c80c140b0b44600c1041d580c05080c0454025003807481e40401201c100e03440d420100440c8980da1501e2103802c0c030850150008a1004100c0c01c065450b4a6586d007600514440c1c660307251014100300d45208580e204c0058001c10b51603038141c5840d00c2e01c0201c1109500d13010903640c11044001d0300c20744003250182d00c11000040300c540c512008006060785a90300800c80c000f0b0035134404004029120155003244078503c0d400021600c01d20496000640c1c00000380109003580711820661102812210243e8895407100d807235402688626050348000c0d0302c41e034001c107078000311070818074a10714000b01c50140300790041100300201301e0008240c0310101c0743c0e9101075525484000040c0c402c1d100725a039103a00005141e03c1f41091103448d5020381280c001c0c0300c40d5600550780341d94 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 356805926 1250 356804676 356804711
    0x3050d09050a1a07020d0302060f090304080c04050603010e0f070315051902090a0312090810050c04031401090f0309030b06121f0b0303040f08070b04051c020102160306020a03 77
    0xd9507000802540204002e0b45900303c6032980c0401c0082032490003120350082030036000180710a0700940e00420a00a143c03059014084e8401c481c0405903003010704242e80280c036451070801c800d20079074542011a84d56a030a6102040359480300f0129450806035420313090700c40006100503680c81015001301c0f01c0c90f001e54064180304000880311300c100032200000d10002900b00010403508032040220110004004804800c4000307100d48559110314642035845d80351071250121a107001d814074081c8048114402d056805980d407148042410b000740210142c01080f480001a160207101b80d03d000030307d03400645240a80380116103848081e564907052100c041f03584c49600714154082070090052040f00011b0b00c000030a644030110f00320304e0300c000291550300f00d41c2000d5121000c006041010755001c10010004201d884941805c1c58588400654080140344040801e001c0c806806c00440e071092006d01c50141e003144514030020f40f08c0c1401002504102c4410000c245000c4c0841101d03c04070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 356807176 1250 356805926 356805929
    0x14070603020c070e0c0c0a11100504030f0308071403130303110c060c16150b0406051203090d061107120207050301020f09060906040308071a071b11060405180103050d09 74
    0x80041180604c0d003280900303c18001803c0548400092011084400052040300c3c0001c0c090111580000d11000400c03e0300d28003a60441c0501c44104020400a480c1111101400c2c0d00b40c01c000d13295076500700e001d50b2884001c000607150540b00108010040240d803501080c054000d540800032081c0d84904400760748190121841540e00c0140000e840d9040c1c5001088800d001c0d80010b901610540d580c001200c1024001c0441039803250010030040c145031040718010082211001d04603400130f08045c0d00c074401d19000601484525240d4814000f05402040d042d00c5550b080ca40d507103503542041004844d5620700100140285000010740c0e18050003504c8000387d0000c801842c4c080c41404005541d80813144031078011000744400800310f140310300a828518028400e0994035a00903460b111072800c014129020301581e0004100c032500002201005c1c998030011284866603018005a50350043e680201da205400c407110314800c0381c11410060480388150215994030508500642d0f5038000c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 356808426 1250 356807176 356807197
    0x702121606021621021207090b090615070605060109050d03020d0801091a0415030b180c04020708030a180209090a0c08070311010f030915060e0f0910091106071407060302 75
    0x61400c5246103500000440308445c401001d44e641d1001c100b03c0d40e82400215030103810041d50350300c07007c005814004103c5070300c00da048640380c2c048500e03840300400d503024011014110559880003d00ea0742d01502d40c82014000041090301400b400d8a0025554501d04214000040e00d00c000050741e980c442c043c8542c071b00004031400c1140c50900c001d020080030004803032444d9201201c0c002003c110690403c900031405540408190a211441c062a010542602e03070701451041124101047c440d00540380c20665002c4c000c544901e070049102d81d560880200698094654020700100d02800030350707440d203a81708600ba103030b205548125450b120001031001801100c003404083d400c40d803140804148209460800040c03594943d00c03030b0043e0401d111621044283e441e4404d120700744103040d00a038403030303181c10008405184c40a0120b488081d411040660a0b840b25201410449075500e40c020000d405005140c481000342130054200c24164224405030141038404521144070703000310f402d484034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 356809676 1250 356808426 356808449
    0x409091e021f050d110c070b0405030705010c050f0f0309030106060c0b01030b07091a070209162304050621010b0a08010308030c09130b0f01030e0a0807021216060216 73
    0x140c5210b0b0031031619454080100b004020071071407445003030520440d00703075111a19a407030325810340020070b514082d002c0d0800390f5591000c0c40104882d54001840806607a402e103800901c043d02460024a4070542b41c502030824004d80c1040b43c100c0e00004050b240001040740280900b60b0b0360f80d0192014490090007624800c07070000148045502e030300b1800d0700000c861400c4403441d079445c44d003200d602d0f900b8501c42840050000d2030109514065056903080703400004410701401c0c81020141030401005050b0685640240d0b0100140f051078003a2002404082c1040d5510a040b00c1840804030300d0030441c0e408400c511002003243e184090a5903e081e0240c0c03124801642152100c090a8100800805900504124a40700c0e83c072640020881d8210720100171036070000f44000c00400c2c000202c1e20604040c03519a420703088600005014034805e030040d1280ba0b03914828008a62401c3c04055107040e98429060b20481c1c0601110340702044038555801c0da0f0082d040100148150a85031003494200d20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 356810926 1250 356809676 356809699
    0x20304050c1c21171305010f05090a1b151101050106020a020904030e24070c080d0e090406090c0320041104051207080715030e030c0a03050a03110409091e02 69
    0x200c010510344400c0d645810120007000f6414090182100c0444604042e00e0302c0d800107901b00103090142100d1a20101c80c00e1045152001d601d907039491600501030401c100c82100c88082110070b940c600c2c094440c0410384541021196001b80c43c54a001100301d00d198600800060003e2010610281d0981d00503c40291174580707403070803150b507005140c0044d445101c4440c4480710035104d0441c04540e51040000613141c01309814100c80400310340d40b051000ea0800390501d840700754044821096000101c40003000e90300d840c1001401404016070041164981038000300c10700c040e0010750f03040e0544880c0e10151010b0040240400d0f01c0142d900070310708800503c400d10140c940000480d404003981021612090b41c1d0741f032140d01e840020b40c8186600c90310300049945880d40750055200c0360010a005514001500800d1541e810008a002c1c08001d00428040900d030300c01d400c0071349441c01c2c0d0700700c00d501d86803691030690083c081200100e40e19100b05054021000e0329050400c41c050f0010b04149100307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 356812176 1250 356810926 356810963
    0x30a050703020108041103010c08071e02070b2110030b090109030813020f040c2007030b0c1606150e070c020a05240c010b010f180612020c01020304050c1c 68
    0x22440604100c1c3c0452140c06c2c17058064400748140303074407801244d031b80c0720041c1032401018086440d59140c0c4604500347d01d070503030400d940000f0080104c52003070b8036441d03403101c0206e07040da000d04042c24090803040703241080c071650841444503441568000c40751001c050300d0705d02c0c0c660308030b440007100180441c1455002840c0c00351250f0001403098005040450b0064035800040c0c00c9aa0a5030154081a0b43c007a4000740840360103c41c5800c8000c4070000c010080c00d54407094110b01c1c0c010010b1100c42e80c00200722401c2c803031030584215000e6000c00305204030400b0045804203440c60340100344031a071082c0c002905951052030072400c1d250300640159009400c0c0009e0140503039181d04096400700d8804e5422850454410091905014460000a940701c050000410400c1a2a41e074000c00009400c910441c9110140d4081150658246000045201296400a4051034403201000c0d4804000c1106014021070080c1010030b04a0741c4112202c10109071241c0c2010400300500340c40340030009090030303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 356813426 1250 356812176 356812187
    0x14040504110d1508190c0306241d04080c0f06070f030f0c0c0f0302070513020c0607030912030b031501031a0105030708280506070903153b01050a09050c030a0507030201 74
    0x42c603006d204208080350f00c175200c110580f80965144407900180c7c1c6c8416004202c80368414024082c3c0080b040b408a11070800782504580241c00074120900000e0300b80054a810060821078190200690342986030a14026281042e82c0600c0c2e40400d040100b500c00302412441444146801c985031710340d4182c0f01d5140d06e102c07081b080d2000c1382907100e80000131031541c0e106a003203074186c07a11900143c0c0c0c0d095020142030510130301038803130800d0506203040100050142802070101100794580002c24204e40030010b868042c900c50302c3c044c00102840080240300e00001b404840a00001140d40c003a66650f06065440c050391042080365040700d44000c41c51203202603801d107401c0d050300d010110041941c403140d04103581a900e42e808904074003410000c1185001d5000083e000903801007025455041440440f003c04c2d10703039010551854035401610710380105403481c40206100080241e894840c888500a100106d800c1c0c1d00d6115110000d0801c0c540002c118040c0ca6020018240c901e1131a40152507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 356814676 1250 356813426 356813473
    0xa020d060906090c1205010303140f1606020408060f07020706050901020c03031209060106030b0609220c02011d010635030703020a0c0e0f010614040504110d1508 71
    0x5185480c0d100008229205000b8400a007020203800a8032610940010342080303080707521113507640e00705401000440e401581d4640e9150700d01c040710b0750700c120504940000b40301e800801e4a01d404140762800600c00150b024005980b401c0c41160070503200c850010103d42030031155500160701c201010311229101364081c060a5106004444400f605040003a003150009880360110003501d004002c4500c03000c0196500600e007a040400400902ea000f14844d4270943d501c860090f0780641c0b405800403041e08210242c141064004c0112050790b0030002d000e084a955550b09400090400d200d04140601c0313004105e403410a06079103190070001c1e484174000309400814044030034607074078218414824002041c5d000c5c031a0b030180500082c01d1a0035036000e5840c1e000a401440007138108629000c4c21800c40d0306484032805c0846d4511408a145c0d0320600c203503084540c110b402c2c002c90f5080700308454040c0c940c8520070700c1c0a002e20469a1003241000c8500e02c0b9015080e44225101011100c0305907103040d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 356815926 1250 356814676 356814697
    0xc0906290c0c0d080703020105010512030901050f09041803020c012a1403030103080a09140105030a050c0903120702030d020a0b01060c05100c020d030b010305010b0a05030c1303031d15030a02 84
    0x402e0301003410001403da842c5200c0c01c0c0c4030354400140203000c00da420712800d07014200031203104655400600c0c0c800d0b503030701880c1030060610100007001000c0300004426a01100c400600a0080c3c3c1c4440108006a8540b580202d0241c0b0440305880050b40c02402c0c0324440005409000300c283c10b00c1002d0035500d840582e420307120f10401e00d00c40c0d094408240000c1d806140500d5659685203a14500201195051f5210b502c486a01201240d07540c0e92040807240c10202e00c040100c0c594441d41008407040c403900360802ea06101d00702ca0801807007a4000901181d5008a082d2286150001000c0ea140c000e00140102840340c501c0c014044980940d15078a8140d0040048a03591011542d520080340d034103240c40000340c1c0c01142c85001d001d43c9030041090400c800c7c41d00f0321155141c4000c055050250200d030500740200840040d04952082c41640d600d5108800b201e082c003a0741e410060401d000d01b450200d108402e0b1a40c0038240e042c883d88141411910450701072a42d03648142540080d0000360380c15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 356817176 1250 356815926 356815933
    0xe0402070807050f030a0e060a0c240608070614090d030f050f0406080906070918091514010e0a110a030c03020c0706110706022121040c0906290c 64
    0x40410030030002c0d1550300b444c1c00001c5036500d409803405400c10a1034400705201d039208201000c030050b40210b00042603030b4400441c45050100d0070023030351500c2c0740e03400d101c00031403400e44001b81c00324000509101302e6101da20f44000e0303800282042d1102d88035003005140c001c0b0b00a50040002882112a408034044500e0f1641c1403101801d4403a446900541c81080000e010b0760a01c00d030700308140151030704600c484c00c3c00340d0094904030460003180c0400d50a484038568421660041c01050700300c5082904014100b001002d8840103222074408080c01003004041c2c0b080d0010b0a1006207200d03c28110002c80c1c2d07501c1c1845081d00048010b09003e1584a00f015024458240c1d80381041020901900d0180c0320320050081c000f4031246030400755400034007194050180100801500c0d8034440e288007903180d00300d503115080e07a0b1820095201401c0c0c85203450303081c800c02c020f000f04074101400390340c4515800c0c00429035070b081c4460300609020000800c040000540030301c40420340c0041c0488040e074010f6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 356818426 1250 356817176 356817187
    0x100e0613030501020d050c130e09030705010e1c0207121704030b070305160c0c050d050319032301080303150a080d0201050a0b03011104030609150509010207021e010e04020708 77
    0x100d440d40c011a03100300d400760340200c0c1c1650001418000c203607210b451441e1190401900510b13080800d0322a20401d882034850754041401b04070180b0031100d00e5500715000340903601030400c110380e80b0908814500d41c840807100803404041c3c4041088422141102a45010841580c45025000034004c15111004074100000800523891803074041c0f0800d660b031000140391400080c50300e0100341c400c1000040210100848000074880503000c03081d1001030b2102a14144e480c03401d40d1a41c400c6079002540f201011031401019941030700708902007054618095a002e40e070721214081c480081c01a00a690030034400074440c00500381d070501c410382d0000c0240b44a5940d501c2c1060404c0308442500340103075100d40810494011500625401240a5000b0040c0c050000d0000100d4080c03070000501041c0c8404842c0c060110055400313554000c0c5140030071607400c001642600035480000120300490801d605200c4c04001e200d031309101c802d81070b1241624403ea401c1000000e50202d5030403103840e03109020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 356819676 1250 356818426 356818447
    0x706090b0c2b091a0409050c070501060f0816030c0e0402180c1e120103120519050d0515060a1b08070b0105090108070305100b0102150c1c0605100e06 66
    0x300d500034280c05814065071050355250083c806803d0750004030400014200c243c84800d1600222022600c05000020b580d45031041181031034030a400c006401e40d0300309040414961082140c5e0030856104908580c15401c50002c102c1013410303180320203481b0740c06800b42001502ca43c80a1164410310040541e80c6a454610855181c4041a68603511012011a40c15248041003000e40512000c5c0d000041c01c001e0001074005805405010041c1044008604128010300800540c1c05140400c555450a075000400c020078a80204020403400f40c284030108541014102118129400180260b454800030040503503c800c40c3c0040f00e0380e00e0070918103020208080e007002d4031615204000705445545481e00b00110410b068004400d075811207070080001810001300c03a9800c0c0c1034050003091540a58005074102180c06507408034410311101041580d004860090a115118000c14900c506580d103004080390454024260040040c0b40c81d496028000c49850180710801400c00c2d250032141c90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 356820926 1250 356819676 356819713
    0x91802040609020405030f0c1005070f0b0f060f0117070e0d17130b030c030a091a0f0708011a040e04080c0d020307121d130204050d050f010b030706090b0c 68
    0x140b00880c996400319083c411440c062180d2000061903000401d440250784000071500e8414107007110500c94000f03141710401640c2c0404100464000d05800c4107440c1c01c00c80300103100004c40d10603100300c01e20702d2740d00055070191030203044001da10280f5030721350780d01c0c0e4000b80e480034554001c403644001616903d80015500c0c41c80e0074918400308060360340f900c11701c150341a6000305a81120018807014030401170303420045c2e0140c0e540840c264002080c6026a414000201100300c00801c4600e44003004101c290100410803034041d031141d60380d2a0b10782e0313a030b03500d0440321854184510a0750001004104003c070468801660002e0040340d50314508030500705441e1524203204080405a0400701d00c8500384090f20072034140c1e0300c040d81801072a188520380d26400c01c0020044d4248202c00d0310503442d142440c0c5506950180002808600380072065082442e0354085403002c000c0e20350300f0551440040d09000c110602111443e8840000307103070400c18030051a400441d1186d20920400445190742c03444c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 356822176 1250 356820926 356820929
    0x1051b01090213060810110405060d05040b240f03070f0e0906090d0905131b05071b050315090a080d1407030e0c010509012c0111010c090918020406 65
    0x90001502281c1c1c1d00c140048600c4803e031050071035141c654100000040824050503540400302c0008240a00424180c000d0249400070b6400500c04114401c4044841c1d01c030310b00030350003001c00901550f40c000c4400d50700c0190900c2c028084420726480c400707a0900380c02e18030b99010001d0503514403e4482c1540390301d401417a40048170000e0b2080c144074041c0400e000541c2c00c80020301c0548034100200c0c1000e040d04030b1611a1500622060760803030915102030f409415140803841c036841100000000040c5240c02815055412000d500c1c100600031860345420000c03141c000c0c024290b511844808407040381c4004100315194007410311103400061007403004048841c504400020081d455090080858000900b01d0301803516108030310030f4010000403c8c2007400e02c00d02e012951030a80c000101d4512015003903982c2800e89040500000955a1600080c001d600303984881640380d803a9000c9090f1601030b03c4070404143e41003018040c40b050f40c0c001144186400103906c482e0102d0342d000c41c0446009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 356823426 1250 356822176 356822227
    0x51003020a11010c0c0f02040212190c17270307061e0506030c0405090114010f08060601210504030c140a020316060512090c0a0b07110105190e0105 65
    0x506032001504400e080d6220000c42e4003c0045001200003c1c10403880c444003e070070800d640310101c0c215075454045610b40000700580828a05110700040403118107111030001e150704291201c0b40b1144030740083c07407490080b8280054030740c03215844065050003504401020051128000480800400050034030030b00c101030009030110800300e81113401c1503403030580c5421410a41030040e0b541d000101100000002c840008058070703400d00580c010100b0000341e80c040103041000007a403c01e1410700d007084a9061041d83c00340c0e07035003600440700303820084210070740d030405806500e00d260429400b40d540144207050403803604840352280701e441017400d0244c0503260300806290046060030302241440400300207250403403078205400030f81107000d0001100301d006181d2000601a04007004040e80b11600507003080c100343d49980140d00a58080c0d00c007030f160390f90307001401d00081d40b061044401c031140f40c90a00d42c010091030404c8924000b8030b09042d04000044c000400d544052411140303a230000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 356824676 1250 356823426 356823431
    0xc0915020606191a090f0a050117060f0a030f061a100525150c14090f1504180507020601140103020705010f0501090603050105090a03020601050d0c180209012d0f0306051003 76
    0x6a00400044141c01c180f00c1c7c1c0a0b9850600402503641c10211a54030001e0000700d0010341c0c6d0726131001c00c1036000b44000c1d80d5170100418a0000a10054240100c8040d000c0e8805202c03940d0700c032100f8030000040d030030150780250130900e0140e0354501c12000707800702d80c0d240b2180c041c6008501913074070180c040da403206580d204141d08000b01c12000c14825100d01400c24184170700b0054200b11181c07158020010300c0d030300440d91004185076a544142c1c10240c09120b1580d2a61203585030007001001b421100c0402d40100c0c5010003003643c440c0009038180c100d074018035601f01e1064580004501a41203a03034121869900c9000c0042c00418a00482c1d0182604090004c1e000749181456425114003030504074064000c80c5819010990103c4c0c002d056803015103009140c1c070b40c1071502c401d204030320350f1206281e4204910380c82002c030721540041c80392410036a10403211b5000001d444041c6043e242c038111420a1071000c4e00c0d1074a020361039000905500d4200040d550b07030782c0c50109801d03c407a0189280000d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 356825926 1250 356824676 356824687
    0x1e1401151511030d0506040b0307031e0203070e010905040b090604112b1407060311030f10080322150f080a020706140108060f010e060f060c010f0c0915020606191a 72
    0x47c6442845040710040f0b004080380c40c6552070342c2075560309190800f80c3d032191040c0384400b0f43d282001802c00800101c15084050360b03683c1e29410041105807400ca81c443c0d000701c0800c014010001c7e40a0007982c01c02c0c8a10100d2000314100b2100b0f03581c52040c5482c207000b141e616440d50184c550a650031500a1414481d0807018008580c01e01040d41c200c10280f5203000078000d5070040308400d0b00d41c00300c4403000320020b54688052175036a074131441d88041030314440050084014030030192100c484078221210b4080243e111011413041c40112076540001410443c0c801c10b1852055580a0b001410540c00626100e4a070700d440381550310b1300c6898280c0c204c40c05d0040200b50810880c0f070b540304000c800390010070350501c0c40b10080c920015203014440c00e0b18640c25a07150b138139a0101d404841894000308203081030050110043d1086020700804948803084c00030b01603102c4030aa5004070440d50244c8442d9503800d00700941d9041441c16030040d01d000320b02c08a0300010030884803d01171000c20300244c071407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 356827176 1250 356825926 356825929
    0xc01030509030f0418020f180a17031c0e0a031e18030605040c0905180106050f0616150908040f0605341e1401151511030d0506 56
    0x129005000000c01d41d02c1080202601c0b0a000203583c259500d05221002c214841458400a40a0030305c9054010400040125100c148400116940302c07007561403550240d42e41c1d40c01c1c00e40e50113001181610350000c03c0310707003c3c07050352807540540083c0d0044001040c0542010f01131070700405c003d085000c1144448000c03015180b4035040703514152680f521903c0c50981c2c0480c2e41007038109100c0100b6660700d6201140410045000c860040e101d8100200f040d4035119a000220510100071080340e5460100042103e09021289840c1c103000a4202464894903402c040c600e4021a042502c1c0c4180c41c44103444070440300e01405044d50f004801d01c03a110b50810100b03c02011096100d0020310500700070040a12184000c0424014a0524000c00010707003001c0d640d0008880900c001c00005a26091000c843e0401030100b81c02805040002455a0040141c034200d030b50911810814807808602000361085114129130fa5450503c0c104071908558220945150842000700c03c01c10340b25010069035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 356828426 1250 356827176 356827181
    0x501030b0a0b120f28170a1704081b12040b0906040b07050604050708060610032c07150921021201050114090c0a080106030c020114010e0f010f080705090406060509090c0103 76
    0x48548181c017495851085076601c030000040d03815882c4050601152802820b0b00031121441c05105d4003815075103e14051610303004946c0010072041701e1022001001440c5800003610021200300740c9203941c0342030300307065106c2c4a6402c58585a64008410440402d000e41c21f900070b0000309104d50010050303810180740c82d900340411600180140d5100c802044001e50700c4801042000c0380383c0c140001c00f0000c4440995462140100c49985112001d070082042040007032288201c400c00340184151090b1180101d030304d050b0610a00a2680c020000c1c005805402d000101c812440104244d8983c8072040f4006e0030340724264000318864980da08514a03604288400c0c0d68810881076140b8039028918101600f0076006028540806581c0c010b440341d4030b4001d40c4a01d0341c000d0786a141000035a518130310515002c2003100d441106151800c000903400d680b1014400503180e5400c040d280c020b0408050081d0540001e000b6503a05891b0b4600064613265681c0b414001c0b089140034090b00d03000310001405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 356829676 1250 356828426 356828473
    0x90b030a0308070509010e060a08012d030206090d1a01050f060909151306030503030a06060201091a0c0417030a1701050d170403120503190501030b0a0b120f 69
    0x80d00144044030029911100903a840102e03420a02d407180c045100480d41e41030b4030006070350498400210100560380203d06603040303e41580c9038400c1c04d414005071529903d241d1a610780b0814205d1800c0c0014500308014245e03c880207050704d2050381007034541003070a101c02d84006c0302680d0003100500190500b40140c0706064419512a494001d400c00070410100c4001c00042900842e0417590103c1d6441000100030b03540c0d540414020300e920381c01d0441d100d500035540110461302d08000011b01c1da006018140c3d189802c00340c1809000f85240440d48400c00081811014400422002c100031800c540b450b503042c00418011900c035010120050506c666400a000d480f0400800402c00c0b950350215100d00d0399480901042c6c64010031401c403500303004a40008000e22151a520a2880d0f40b12000c2c6100d510691132000f004242c5407804401c8543c00c0c0406060324074084001400103100d5000482603030300241440e036200ca0720b461140d04002071340c24100d0b42c42d00415102c084800c4c0c0291440e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 356830926 1250 356829676 356829679
    0x309050102070b1603090b0a110f070807031b0801062301030b060a0c0503090603340503011406070c0902090414100e0606040f140405160207090b030a05070b04090b 72
    0x4102d40c01c1a00c10b644602510100b04551010514040c003018800c4280070020529001c00c01e45950141e030001d40101c0081c1c0c80c00207940708504602800f0140054810102c0310342d000588840c900b184c4404401651691080603808880c05c40082c102d00240b103010300a14180e15035003000c5007604032041561103400c04260402d805d040454149585040440b105e080c01030406000c40103182c50150300354010340205552000001c01040308905405800c4640c0444007030811500c85903840c0e04000d40c50310701100c4400140144018084801c0c035081d044c5c045c18004000798288403055551115050341504495202500401e001d02c040c2040d001364405103400f051a50264a80094881e07095000c6215031462903203104041801a15282c3c11280500b0300c0c810b001d20035a4481e00a0150b1046401c00580039614100004801808018000044202c242c2c0a424901d01d4080340c0000b505403e40300a51601480d41721100203101009054010080380315000e40b91894142c5d5072044030780d14800c49 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 356832176 1250 356830926 356830933
    0x903030a061401020d0e0a1e090e0303090c010c020a030b0414010606030207050c040f0e0a08030714070b06090a1506020f071208031807170c0f0f0a03170c03040f030309050102 77
    0xb0000e0b030b0300442d40d0f00d484103c5107428288400442c0001740c0c4540d80e9484080f816012505822058440c0d1020300141c401c40003091040062950409940c0d1004446610407030b0042140c02031107610a9411601060004044030340f496240d1300e401c0706060050320215050368039903600400d098802c2c05480d0082505050442c20a911a12174079102c03212000c00b14892550740d8035501e550b280c5540300440c40302c160b100b11820700d426490400c01a52040d514034000c00c01c0b41925010007200c10040703400860b07003c2e546031840e440b6901446108030300070344501d14040e141d18004079a090b00119510040400d0390043c0500b80002c0501418800e081d000804031700c2c400010100401d0103d42125007210300c2601c03420152003010710150900c40d2075044100c104d41590140720b5042b0300004c18030a000c00480300305040e03455200800400500d4281c8140c5c2090713410310100042040c0e10300001c4555005604d1500c0c200d08005030302d0843d40070750003480b906900c0d554144141540520950054402070008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 356833426 1250 356832176 356832209
    0x6140a050603012d0e010e161404020f040303030203040611130e0a0908030f0403020f0d08151905041a090709060908010b01050316120f0501080c0915010f020708060903030a06 77
    0x24880d1544c604103039508615200c19400c0e0b00b0f01e00c25400072045448180a46028036410070795098900294841d440c00c2d908013550091103403601d44200c40440394008106440c2c58556541034010b50401881551115941d12491680e00302450052020a040c001e059071030318180814800b001d00042c16102d0050310305421000065030200c2240d40180d000850880c55580c1c070b02d01280361005004200445004071020403032243c1d044070301c140c0240481500758607081406001e000002c1c5044c90102c200d41070044042102e41415806001d440c8a480d07200c01b00380c044103000c21549102030310b0381000105050010000c00d03500c182020050240311000340f044c2401040000c09502010700b40420f01d240015500388014011810404e511404900600030035101031501c0004040901c1402c41d68011224442941c2c0761003020544282e02d1100c0000c0703800007210044401080124100e0154425640d0101c2e4981e0200802407050313035440b0041d80d803454400018015214135912005d04500030069 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 356834532 1106 356833426 356833481
    0xd0f020310050102010b0d020910170c10051303030e010926070503070810020c0313150e010c031205040c0b04060309110607020d060906140a05060301 66
    0x702600400ea0ba400103900ba100c1468900394026403094081006203400f4032155040f42c94041c42034402d544500811000100d40ca08808190703001ca440c1d400d1610f0000d00c04000c001c0c3c03510f0700a05282d80c990700042800d4032400000d0170b00400125a01c0140d2190510750014450190701c00c145c2c2e03003441500c4c801444070210103507035409200800306450400180b08421075603044000c00d484130402220300000d401c01051240240020801c2242a091000010016040c007002c080b8001c2c2281d4005804c4001400c213280c140401c04c1c0008010907080340900e001500c00c0c0a01240641c0c8602e0304001d045126003003120303500e00115011580a81c50390100c00300b14410b40b8440e4109d5014030070080c0074020403c000b5840f4161054140c0011419044408003a00c900300100c0c00c01c000135045c191106044a40d50a0300744d030740b03040042c2072070300b4043d64400f42104144009112450314 = true := by decide +kernel

theorem cover : BRFrame.Cov 356654676 356834532 := by
  have h0 := BRFrame.cov_init 356654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 356654676 ≤ n) (h2 : n < 356834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
