-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2167
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:51:17.316362+00:00
-- url     : https://prove2.me/submissions/d6f267fe-503f-4b26-a440-3683c17d824f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 389568345 ≤ n < 389748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 389569595 1250 389568345 389568353
    0x150112090b010506093d0e0d08090a0b07060209030c010f0903030c14030315030d0302040302010c061815060e1015121b030f0c0905031209192301140a12020403 70
    0x840004440443d00322150b07400c6e03e540139001070000100c0c85040c8030902c0f1800c4090f48424410980d41d99006080300c0e540c40f0514000384000386036400045081d0004141c101c01c0041d1079004000b40034048089682d0240140d0045580300d03211030040000513403000041000900801c65495410f00c5500b42c00390154800303110900d1604120ba9008082c80075080708a00c0d41828408107004079480d1805615182c03c5400203010000020401090b6581d1840000f0155000c04113503000143d02c544a02d001e00980c44c04000544001e000740a81a049013000c5a907211010013108215543d81e12071081c0e4030030102080d18040500c000c0070940c1d540320300701518182d0322203140c2c0000c03901e10740740000c01800030084d100441d000900d0751028407420807400e202c19a00051100d107803d01360f0048941c0c0e044608045580303042030019224581d144c00301e010690000c4107001c9038808070354840d0046d0300314030341c4011155020342e0355441c0c6030004208981000184541d0f40c0c5003040384e50907805880c2c65a20f541e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 389570845 1250 389569595 389569639
    0x10b0321071a0a05090d200f010207030801080708071d070215010b0705011a22022205040e010504111005040807060e01090f03080315120105150112090b01050609 71
    0x40d0109071000c0c50010880b410b020340c0724254001742900010001c196908030050704000e064000c40d40440da1007044080340c414200000b02611036a03800a544882003403134007510f00700702802190154058003402003801c5000081110031614481040030078141c0400881c3c00000d40900034400f18010304806495000350400780900038090002c41665900a030304040c2e00b142c003090f00000c0f541030012501817445c4d5401d850400e1600d2421010380c1400b80301800315000f072244861814404900b00e500b02626404802107504440003550288161413a40710f10f58201c074011200281017a8901807580b00303a00300082c5c403015079109803c005240c00d4031132102c0d030b1a100c0c10303502140010b002000318421651340700118000524010032038a40840c01c43c0d50307170515404002c10140d8140d00030b03d04090305a8840903000301c8070001c00000c000504052000100303d04208100c01e002c43d140007a03090000000e0712a040442c1e4006d00f45060320b900b4042041615403003141060391052444c894030f007403200425 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 389572095 1250 389570845 389570873
    0x6071a07020f0118122a05070312030b0108040b0703090f060203010f0501020a050304031203021c1b0e0f09062b0302191113020408070602030714010b032107 69
    0xe0000c00b004080300d40d0355401d60b251400011240b14100c082c4400140001401c1c02d1803030980c1c1001c4c0500c00d01074074400301c1c441c038018000140030495104141030100c045403030420369008400c400715000324507074150280c0b0014625940060028030025008c00d4002c0000c6400414500d00072403001015115202c80c115006000e6903c0390f400401000300501064907080108400e002501140990343c032140d4490040f0301c805400044101e41211010f4030179411244000380b841c112000444140903040c00601040c02c00b5a1440d0300c02e241e1110b602d00400301212502e2004050031640b40c0780340300b805000b038000b901080c2c10500c06407409100030503080d410f011141c0c002030480c58980751401c0007032600c00801a4034188004031102039011441842000e40300380011354458128000c1005050000e204550165602c1c1c000c85002150603607020004100d010700600c1101c0d813010450489600f00d0303118090265040c0d0201128108094800341801ca035200c101604078284034113900d074910202000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 389573345 1250 389572095 389572097
    0x7080d0e030c0108010b0d1a0a0803074412040f0b06091303110c1002010605091f1e0803030a0c021006051012060b0a0e0a06081506071a07 61
    0xc011000441c1820000400329940034600706860354580144200144203a4900340e5055440da251601070340b00c458100d0b4810711001e4440401a90390362155926074001c800c2c100c600160036055100e0300c1d6646a41e00d1920f0740e5005641c4035280d03146020315800720710304d81e00303140996061020038101c108508641d03102d517025444103160140d035458448a0314400504a5124041c000140b1102240f0004803007200c1d035140c1000740d61048052085481c24440c0c0b03a00640c8010300300d141e6408c0701ea040d04000100c401c154bc84417110b495101d0300810704181a60f00b0b4180c082c6c107032000c000b86080701d2600c4906110703c5060411036034072200c0e018116801140c40340140ca0301c81040d0780800364100042040110080810401c15082c580000c1c1e44192800c000810000155032010003104d49601c03546c001d111666240f0350710814035401820101c0060686c5105000c007003030000b45140aa8582813089801342440d003861452081085481c0d0060740741911210203c41c01440100300d5520391601902007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 389574595 1250 389573345 389573357
    0x3090302030d0513140f120c010e0303190e0a08030f031b19030507030e0f010506030d090e0a02070f0609050a21080109180c0608040218151207080d 65
    0x9600515103001c804080003400c002040042c2c1c0d0035640b803081d6201c2a6500c4168001c3c04040700030000e9880c81d03440c00541d90001e008545c80c42440000110034403909001c0c0c85000b03001105a003010b440b0300175050403010090300384450707480645c1709001d2514101070042203036004a490301d000610396009000d40e1601c3c080000203018051001303032410640e9949941200e4a840000c0c00e030010758000158018050503240d5000c42c400c140170307820000c0006c45c00e104071002c12400d1004580a00030541d2001d0290140c60007a4040d1807041c041c01d0b0035560950345056890300c4a200360b40003940519401d450784841c040340200014414000d0f41c421900690007013503c0011340c04c0909440500c4004000b60380303440b000315254180c1080d12141140c0d144000060b00c0d4191480c44040c60b10314400041400c890070401003209600b00c03003618052402a5415000f0020104490306039a60560750405440051000100b043c0782c4020a03c001e00051400d0765840c599401c13089150001010120022800d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 389575845 1250 389574595 389574599
    0x1b01110406081b091819090c090605010c020a1a040506030c0a020d030b18130506090d0e010302090109030f0f060c050703021002040f0e0a110a120c020f10020c0115030309 75
    0x102c4103041c81d40040240442130f01d840c402e4000100d0318080300c0030418441e14103100040303820007081503078513010070b400704140400c2c40285007010b00503a090050008491070440046919403090912040380340c0c1c0985002d443f1801e100010700312501180000c0b0406004000204458407100060350045048070102d54458060342c030082d00b4000405402c030b042610f45460300d0125a20f103080b2180c156482350541607035481d0511301c06221505108054482d10604092243c0c001002410f0340140e0b09503034820200c2d1075440011016031083e440460f0018600040510110300c80c1400c0343c0b4072600c82e8841103401200d9641d45030030b681910002101245000c1103030707002e041c1c0502075080d0140c6010403c41ca05820000b00011444540c0108000000f000e8002840004d660303102c8520245841d03003040c3c0340d0302d28100080040452481f008030960a00c09540c1c0307045e00004000d50403a511a01809025111010010003500706000380f844641d21840034041c071104107418100614000d40c0d40d854458 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 389577095 1250 389575845 389575861
    0x7020306160504090b010c0c0308040e071403011a120708100605120f0601050c060f060f0d1208130c0311040501060807020d120b130605150f1b0111040608 68
    0x100038107418040a101c009481d04a5210048406981201d0000181d548000004a8001882070340003008804071020200500401d03601400440c2c441100148081e03607032980c101e407003402e0905aa00a214140300610502410340b0002113040708054459040840a201c00714201c0416210384000c5031140c024018048156045140035208508201e440c2043c1000031034028031000300f010140e85c0c508404210903030721800441d562031044070200c0e076070b174107119002408051701600c0691113001c6090500c070690404100d00c1001a4100401038045007641c1b02c15580d21500a0220400440401c00e280028244ca5240d030040c40c0208500e903004080d070341c00c2c4421508184c0000043c0302e50041041b081c2c590001e500711a0f00d1840c0b0381f03580101c5141e649040500f10b44181d0a41c45240824075400c0c041203030703210f88d00312042110030500185141d00d26090b2485030000e101c09410082003020781080c0000280300b00607628000000c0d01d41c42c0816000c8854100307401030b1000840c5102488000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 389578345 1250 389577095 389577103
    0x1709041a040f0e0715090e0c0a020705150d24030507030218060901030f02040609060905040203100b03030a0c1401090b0916050d02012d180b04121401020405030d05070203 75
    0x885070ba103000c00c4003401004420f030f40c8200c1d91142c54040d904101070000c3d428071a4500b45d00601641c0461a0141440b040d510481c0e00080003101c010300c00d0820003c0c2e01c0c43c00030b90a104114440245619260710f6002c001c0c01f801e5245070350701012001c0e15101c41380183e840c10190007540964081d0201e1400c41c81008a4080d89000c03420203983c80e00103009441d9903051040c1c0c1126401300c1604d4180d1003600c00304004e41071035400b49044900d015070010309400d03e5004a44220300c00c4081d01c07a00340388940701d201101c0410201503050b60080c040081c8950091200544044c0a10801003004a002c2e890b2400e5452240003102c079040f859040c031090340410070003c00b07440c07c6826110700c06424000480e070303442115034020741017080c2c5e0484111014480d490181142407400840441c0300025440900600701007441d1040320100280002242c104407410b98003070340e60410508440039002d48500c1e42002040a429015540c2000009420380d000c0003d03003110f007101d848480c0c4498042c0100346c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 389579595 1250 389578345 389578361
    0x30706050d150e180a0204020307110f120f07020a030b07020307020114030103020303160312111902010605030c150d0906140609070e24040905040605010b070804031709041a04 77
    0x400360620a09010f981d480310300e11980081d000354800c4080308081282d914000741290069080780c400003e22420690003031a00507111042e600300c48a15135685820303561364205042214151030280440b0505808480050400c83e00041046d070510307807207031110702240c00d05440b6040036a00002d078840855820484400c141036410008606541c99600030039102c1c801c10580e115100e52070840981010b0142e003413500241c0f4003580c200481e001003406800b031680300e40301101c800310000c0300003c1642e10501078502500d8001e000740c07000540940900c02001e00510880c0707440c140c05e015044004445118010002d405081c000c0313a07031101c10000c01448d01c009050715000f086100708000015411510010000b101030355806c1603200165007a840d200161074890504010000e00050404015000a401680140410800b90340c0c1d806c10759410344100100184003e00901c02003000c180c0400c1440b4800c1d88281c0c00c00c0c9440d001500060440b02822050b4070f0046943c0344000c881d040600c5410b403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 389580845 1250 389579595 389579621
    0x50a0c080105030d14030a020403080a0f080a06030f0f03093f030503041b0909060e190b0412120228030c09170f0a031d060f070305090f030706050d 65
    0x10344a03007040014500c085c50490801c1e03042c2c000002c0340109880b94121001103402020503500d400c0c10076030040610b04640d8696001590709408503001402c9481401c0c01c0f02d90190401d0514850759940310324820100100742c0030f0010001e0001000c40c11491000040300c006201502280021407401c010184030f5030070818001c1ca0010004000307504001242e402c40e070041125011103040307014215605141d904405002d80c10103500b1401c0060680000292041e04800c0e200940001d682d51655503042c07201c080c22102c004800f04002c80c03c030070550014441c440c80c0c040c841d500e07540310040a0740e004c0e01c0c034401e000450b0140d80500164520110711940002d2070207008000010b00e000303064211602600e690800b800c0d0924101d84d2007040a40c0703a00c2c6d4400d0543d524852641805000042c60000c18124172804401044231458004112a10902c402c4600d600f050107649045a20b90007016985070000d207491442ca0040d903080000000820760741e582c5a07600ca044481d048203540a00c42514 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 389582095 1250 389580845 389580853
    0x9061416080106020d08071805030d050a11060603060c07060f150303030f1415030307020a03060b150304030f03230f150607080909100b030a0204060e03060405060117030c01050a0c08010503 83
    0x101c030301944441287e4002d07800d840c290307130203441c082906101c4064903804964540300e21414202c0c03240d0000081c1648001548401000d03002d511801368441000b00c0e80c03564503401500000d2003103042d5038090156a40203000009540742540c171054100d4450000b03960950203024020000c050341070082c00d01c449050403007400421881c0002005111001e408041454008500c01d00551410406d803800290010700d841e80c800d43d00c0c100b2100403c0000d18039400344c961848401c031041c030480204d0740116415503401d000c0001081080303000b84180700300d840f080c0144d03030703448405a170b40e44003004c1c02040380e6400fa00c0503041c03980840003164211046503015200920481010500030b8041d104501e50644110301c7c00c3c1e45800d0f941e001014150070680390700401005214040255901604c00d0b01c809032291281801c10104060380e8590440b00103215620200050152481c0103134154110a00c3c8011039041056003c052820f48604841a101311940c950001950540c0300d80c0990042000340c02030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 389583345 1250 389582095 389582113
    0x18120304021f0f0e03010e011103010807060503040c120c08030304030e091302031c2115090621060b100c0203120403030527060706150f080c01030906141608010602 72
    0x20305603001e6a403c0300144440d441c14950b45071002e41156100743e400000810100650248240c4503400038061103260b84610300021a0f018010803c903402107801c030b892a03909074540304c0350507407508403003004840d8070f1007031000051000401c00c080e60240c0e110b07480e010040d48042c402e1002c0000c0045c0040140039040c500000981c8010510b00c02d14010001440c242d50031040c0c2c1074441064810312284003400c0311308803214080b490341c03140542c6c03183d03600d84002c400c1e038850750041640c1c1103015988401440105c00389003080f01c0f6070101780c50b5115100200e9880144800200200006d80c58000852042c0080f01c045240901a58080c8075021400c1ca00706030075900d000300640216244e0b19a40c84403a61140c82501c0c000d482e207809420005c1c03855542da0a1464010098451004280c11041414001007a080e1950b080711090b125820f00402040c001c100046010303142000707080c0d8241c0e90b07554445151070300040905120f801200864070f81d800440034020b04103a8164001c0301103420034400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 389584595 1250 389583345 389583347
    0x90b03041b08010b040e1c08040203010b03070b2706030c0904061503090204060b0304050c060307020712030903061a010e0112180f02090c0906030f090f010903081816030b18120304021f 81
    0xe07521f034007907038030744105075607528030101e030040240c00601c0d5814442c03100000b079102d14500c0140141c00030650114101c6041100300e240c00f150403840c2c164089400d10002c1d00c0214898040c1100160092020078140d0b07440c180c200142c4150910340340040e444141240542c00c10b8007a0301c0003010b458088a18503d0700da100c4580b42c0d2629243d56104600020109802d0b61003007000d04090210316241c0c0780708030010301e805005c000d5640302c1165085d085c109031400300d29140344000356090068448006504078500111510f0a05412032240c056481c018400c8ad040304c9a4020071046c0b04480c5401840079500420085840040c04600810000c200402c995140c400580350005000a440021a01d440701903c0c146090b2101444142d0301e8000000149940030b6802809006010140c1c6220b50b400a40d07992188040c10340d007102100b6031402003000600e0071548592100791039130300c1560b69030400006410001c10403072503000080040188030a5240112103583c154545000c40c080174209004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 389585845 1250 389584595 389584633
    0x5060304030302090a0e01090c08010512070608091e0a0c080a0c1a0c160609060512010315020f07050a0204050f0f0406090819031a04020a090b03041b08010b040e 71
    0x100600b010b801003115406a2180ca02070009450004080402c0c0d684440541d0f0041c68191440000201034600010311410400d0550031100f00c1900a449298200501601c80714009803110300700b445000324868102405207840b0801c641c40401401e8044800d05000d564803120741c200302c046410010055000680850520b0202d801d125507602480c0300d074070960f035110f0003485144040c500800403e1400705800c10b90060642c3c00b55100c0303d104030b48034602180c107030062690500342c6019800045c408200031007045c034001c2c00c1309940540b510004028080f1150020f007001c507650b504c1005010708628080c0181607000b85d00403080c03120703803512198401038240003420250416682c0c0c00a030f1705200d072000071982d2800312a0078400c41c1c500700140040003001810442110340c0480e00c03144600e86460700031030b110702209940c0c50340440e0070290021500da0000d007040320100844810114016503e240d0003002380b04e402d000003070a059607018001a034a000c11040703116081601030305d42440c0400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 389587095 1250 389585845 389585851
    0x5060105181f0e0a0609180506150c0601060306060810060806010221070b010e0708160908070f05011b02150a03110f03160203090f131d0c19050603 65
    0x110241926000b203251414403620a112000074036084056043d041a4411030110040e50508070719542d034101203076080086d0150841100300d07001c050b10140810381043d80c22440c000c0c4000b1204500000080c056445100c9502054100d08010001c06806120f0103008000c0d034102002a440e041102e240384980030b008010500070700c0c42c0800c40b41c0e4401c02540405a0000900301c80d03051203020200c02c107410004046900768158000450082c04000b00140261866140c607040d940b02c030a155904268038480781420881c0031200000c20b00410401413000300310710b10305000054188400104101002440840c4841e004105900143c6451140610302e4800a12440d19100c04080031030181846240b01c082000001c40d0116130114620001c60003000070111000401e1051001645c481c022000340650000000c0c401c488142007070740008010b034881c0240012240c0d03950030f441d000c1602c3c001c00001c1960015210506a0600c3d01d000ca40c8070711546c070703030914a0380ba007000220544001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 389588345 1250 389587095 389587117
    0x604050d050d1b03021e1303020f030f0d0302040905160f030f02041e060201140f0105060f0d050412080903071106090d020d0b04170a02030703200a0506041505060105 73
    0x1d01003007201180e82c0a0201c03520320500600c8540300440d0014017035089140c180d080304121034007020b50109000c00310f564010300403030000503991840d000c101c0c410185140740c540600500c0c841840c000c00a00c901c040200311a200140c66500349011082150002043e0060440000e0302c0104081d40000c9100003602e654507002c80c01351540c00a035006805140e001c4e049e00750318000507611030355501400750300f5030300c06a008201003120401d1000d143d0000341d51b4105010f01d08401400b4506060f0010008031145410a600d0302041c18069030444504460030307203c6541a103094424035512042083d00289140c00030340c1850781c80c3d2141c9040d201e003008c03014820400003d5000f0350f81c4881c0c0580e549550001c001680500881c02d0803543d1f030034101c030103c80c985a03038202075210090080984119200c260300450800050f583c0a45981c903000048101d00000e112121080d4031003000381c550001d21a402606403402d00e464203100050301030f08005a010704180400c20240d9000c015104503c0701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 389589595 1250 389588345 389588347
    0x507090e1905010b031f0506030a030c031b024f0905070909080a0f020102040b070605040f240506060322030c050601170d0804080a1d10110d020604050d05 68
    0xaa032030840e00600044c1d83d0b058040c02034110b0445840420101c01e480d100080c0d9003800399650b24010180c03621004507000b400b080d00c0c0b02840001c68426800304000304105a5a01e4004920b900050112203803840c0c0d0754265411414580010034500c00f01b24580901c114100d5410b034500c1581c080d982c29090030035105207541e8080d0100740241040600000d003190213081000c408c2d1030402c9005588554180c40220f07070000c1d080e400461052080701c00f01e810242103141441032558031900500005042501c085040c0d10035280452042c403951001551100c450001220b0210b082e10156840203180921410083c01004000090603000d101402ca480d102015491810700c0d0a5075103858031032000c1c226104000000ca200c006000e1641300641c0e0340b5046030305a01e250354017280d1214084800a141c4802804050301c1c05004204c482c90700302280340d032500c00d060510007081c4900804e86003200010300d520035a001152003072094000e482010710113041c481c50107448482e550383c0c14841038010018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 389590845 1250 389589595 389589643
    0xe01090b0a050714030301050306010f0602060c0f1909090c0c08120c0d2c010e07060e040e01020313020a08060403020a112701030201030c1805060a090515070507090e 73
    0x440740003183d45181d4803c007034002400e50b1010341a5030740c0090084030300074072840c0d001107070315103103140f0b450308841c03180e4001c107042d6607040300c4015285c000c011071007005881400310054050141c0402100c800c02503860110300c40c83d1071070200680c1c1040d000e210900050a0560010664101c02c507031603115044035510030390300c031100040d96911a03100e4a0902ca8a0070007520900710110400300d40486400c0b5402c1c22556a0f1030000b800c9920b030103039400f6298400c800401c44603000340e044a0301c5240041c40005d018091501c0c42d07003607a008845440c28400d49042d000704501e0410302000280c207882008052920380303507401951b1030711000e0001d020044030003000800c56550f00b41c1b07015000c2a000680d001840c49049088208400380400c0340400d04140031000300341c2c420505420f19110346800c05140c0d40c9484240841603110309581c40030094040c1c3c0205594644074844415240c030340410315a178130041d050007820510b60b030300103500ca00e0403c08501031154000640e040e8944d02640b041070300c2d403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 389592095 1250 389590845 389590847
    0x50f0d18050d03090b16050706080c2703010c091a07051f0b46030209040f0c0e0a06060305010e0609060d05010507050a080a090203070608040507090612030f0e01090b0a 74
    0x10300321752040c0c003030000c0000e1010360503540048011905100e5000c07525000d440340f0040d00d0140f800c0340d402c0b418000601462a0140b01000f1503074a10510030b609001d00d0400307101203400d540d100c90b280008104443c90410410442c8600300388509a40840030b4101038083c3c2d0f6051302d4100590b240b000005203448071b00b003580080c6d0700c03421003d40014843c0c0c80309201000c0c04007003039005440344800b603503441450101d0503040c22501d420034003514a007100741c24210350030400d80d032402070829100b81502c0c010b040000745041140001a10a900c00040c0c1c4d850003011807415903e407604031804060800300104080600011030581114080341c40707a8a0361303078103400300e100b07005103240c064031960030501030200c840c0d0440c00070b0a099071140e548118958484699030709403801107000940582c05134004200b0b070740c400c4580c240c102d403080003550b00440c0d43e01e04107800c2d01e480d6041020424280394142c000c0541001180240d10b026003403000b1004c0310000081c25030308a070312600500c0f81000410340c8140d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 389593345 1250 389592095 389592107
    0x702010e01021b0607030b1014070f0c050907020a12030b060904050a150509040b060d0c1d060a08010519020a0306030507121406012103031404050f0d18050d03 70
    0x10180d51008544862807108940d12805103071034064914007400010402c040c1c401e0003803011a04e000703407509540340c1f64180111a00000348841c400d144000744414400182c0f4440324483c014002d03050001070a051004000040b500074042c4020b42d804a800c031400587c0d440310041c1303031495900780000d02d41a4040454040d1040009540d48245007408000c0000010713030150041c0c1c58600b42c01b1800c00d4030341051005095080d00c1c05804025800001042490040001c0d5002c51060066a40c5c0c6a038070701401540d464622a040500a407003c101300f480d04208889200420860f4000e203c00d081c0003088038050150000d64016135500007a122000500907040700c2c0013107503c40e0444051036550580040d800c038030b100044030101405090b0312007400001520394140c5255040d17106421030321a6506009107401d2101310b06064841440651304c500080426100c1c5002e04042d0180507654008203003004641da0012060112028941460f015452055000c0d03070700a44e62074046210307030708090b241 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 389594595 1250 389593345 389593361
    0xf0f0a11040b180a0f1802091f0f300f14030c10020c12070206040608060418080306010f020d0c0201120b0607050a050d05041a0d06030b13020109120305030f070201 72
    0x100d28120f0a1120492007580122240c2ca0041020884040d180805122400902e900030758080b13200d0300415024521100e010541241c400e0f110302c50303590303500656058440c050f4402e00001042c8038400b5150030124050780544146c41e64518a0819075a0742c0605000c1006000352200840c40b6103010048010000c80b24100380d5101100c0000652082510103540601203000340c42c050708802c02512010704094078540da034020700340e900307040c00c0020848140e00d0061815910985030070200202004652204850500400c0c000d95a49040f0001600c3c0c0c2001c14100e000319800440213050032503004201140f6680e0910b00041d42c1e40b00c200442c006440d840b401ca503030100002801c0c1c0c00300b08001a450300b14920070310540e1110b101d10136054074103000700e20400440c6040b400c007120f010595031005045424148400180003a20794035401b034855800c030f4142c0041550248503a0540d03030400040070041c42c1003003205000180c1a0360080c0540000f51400440d1100c03200801c0050b4001c0d009184 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 389595845 1250 389594595 389594629
    0x313140a03060e0c1f1209080405012109060f290409050102091206070f09050a030303091410021e0913050403020a0f44030c0702120f0f0a11040b 64
    0x175680c283d4122501c00013505400e00c0e002c0341c031210303060480120a01407140400d420000f041d040925210040d1001881c86201c0620208000c070249d08084403481030406041c01a00b000034240703c4104001c007214111510078542004c8050351720941c8209520745c40e000081907a011600301d69500d08140a40240011141e0003440c0030b010f80350049000a542d44200e105554100c0d42d0a24400e0a80b0080c0c4ca6004150304002c554100f400883d020350410829035218440790480e00e07042400003400c2c5528a2400c3c0b403030640016403e1401d02c140c900816481c81402d5034145042003074800104400300f00c40030502400e485d6400202858002d00a1070b601c6900110444261b05040ca04402c0109038078000e52204d11400900c240e04901c448440d0701032484032401c0140044d900100070607640c2006018042d00c040411030840180c885138542560007079440001c0148801c00a02c203414504030b85190425079002014a0000c80c08030040d80c07044001c1900c00082c040138503c0818969030180300c03411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 389597095 1250 389595845 389595859
    0x6020f25023012090f0604060801050d141f06090c020312040606030b0405030310061b15020c030a020a050d080f0a0c0c2001020f120403080c010906060303020313140a03060e0c 77
    0xe440c816143c00034400e9507012079100f00c20b400010100541c42c0640d00406001840b10302c01841141401030200d20954002c08401d20718003a404500c0e8a00b56040e2003079040d050581102101b0520b030340c001c18029010b0450207100c450081d0b80d0003903903070003050702e1005009408804601802510342c4820061034000100e80d026141c01d003001544e0390700a840b283c144601074040040d215100f5420380112031a001e10741801504251101c03481100141000c0380361603801c01c8441315440c0c00300300078228100f10b500036000c1190282085130500940007120000e21005804001003182c1d81c540465100415620000d1400400760040761004c030380c580c000f004049902c40d05040080f0003000741039600c1090342120604203010340d400b038035000181c43c44580340d4418070041c0300140c0741001a21100f14240300000f140c1449495190940310964800d8015820000d200f00150b220038a040d07015007041c42d069900340f01c0071004244030b013007103110243c11144d4a03541702c030720050113110401460310010114 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 389598345 1250 389597095 389597113
    0x10f03020a050a0c0206160b01060e10051c1d100501080d05040323030f041e03020102060c070303110f22030c0501080403031d0d1d0a03020906010c06020f250230 71
    0x51050888203024078802f00d8400080c5051074070708140100000d0071a03603581d608280700d51a0580103076245203101d13404140c0b0f40054450701801001c40400c015803481c01009103030b03803800c01c1c05c0440c0e6041e007000071281c02114914507940c1c0c001048404481d40001000003440720389034050032401c1d40001d10701050000081e1940b816403c0c002400984034a03107141d04c0c105c7c0381c0740710701d96401c403080c4002405a084000041c9019042d82c024010080c041c0c100460140d10245009000344d00030403500d00440004078101030121004078000300790700f00c90580c0c0310354035080d0344070300c1c8907070070300d8800e0724100101400050308251194004243c91903011901c8164221111115500c0c3c0401e000e240c0c0000b4807554074030b03101100f85a4804039015000d421608081c0c00c68007880b409210013041603061010bd8140540040c00d148003c04281c41d052034040e0700d50008001d40f60f0320680211302280c4140302402000c02590f80d070704451041089550029034001d400300c80b216400b031009041d14030540940584 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 389599595 1250 389598345 389598353
    0x5090904030c1505070c030e18010e0903090901170f151f08010203070c030f0e06180301180302070602162426011e030b010b030a0b0409060b010f03020a050a0c020616 73
    0xd86c25898400d4880052007002c803070921144990350342010301c014080302d00400080031844011a0032148a04c16240741009000100c0da50b40420391141c00c030071120400d2524021420300c250010942543e02070089800994443e481d10b55010307144003aa0760f206864130200d8128500140d00928072400255220301e003c850140400c02403407416004118440c10404c001c0d81b080d041c022020070003c00190502841400c404200591444150780540d81c807444042a140c1e4500015002803083c1c0c010406136007003400003806c0640034000329018803200b000601a5910348810312405510711800c00fa2140c0080100325020486035041c140d035103030110810311021510180c8141038407508040d02100c0c00e142c2e045440001c0040c44054480f0000c940140254415400115044001e443c00852000c0a80000a08546501100b1034900d90f68420000740c65030403641c0e1022824150508506140462201820302d2146840e44010001e001c1e07003240031565102e09442d540095101054042d007040c2c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 389600845 1250 389599595 389599607
    0x5010f0f06111c0f180b040911090a18150e060d030c0b07121401061b05030403151a120303011202010512010801020c1903050a120209120601051005090904030c150507 73
    0xc001300020b2214402c0c8206405144a05400c80d045001031600c1c081c40c00d81700d880181103c4210062002e03042100041a40e914141d4102601d840b40111200421a5a00300c046501c898031a0880340b28490040066050401c20355501c44002c1d140d0b44511a100c2c94121420000d101c7e004240c01413203020b00c40325550020b88211114441c00080022510218a81002d25130034414500040c02020200c0790700d02041c800540d00e1480781c0c0490341000d449540ea80e202c0c40504003450039a035901d0002c80742204051041006048059803805009541c50140b05d031a03100500070440c401030b000d004d50045900c580d01b04c940306944c2d0aa640303034558560780d005000c1d50041142e07082c03d100700203911014040a4280b41c44456060701c2d018a010501a0f0548100031450380c00700440e90300b4440421035485241d455100c1314030040c082d000750740c104410000d00440611440080120520405a242d2a002142d540198150800d62034940c900d1070b0541c4883c0c40f040d0080d00141c142001e1041842d0006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 389602095 1250 389600845 389600867
    0x1608010e0d0c0b040807140604060b090f15150d09110108061009061b050a05010902100309020901030b090f0304090603020a121a060a090213050405010f0f06111c 71
    0x5055a4034080c250400301e070142d5404101030b100e11038410100c0c00155101008043c80d40c810300c00444400d101c0c61502d0300380403080f2000d888054072540c02e441146010240f10b41d00102d00792450095051841c44000003103a880c840b0b0340100e040079208040345c0200010b4036110020844103210101952400c10b80c011041c02e841070115411306c2c01f16010703240029001c504110700d941da0b150900d1402c201103030380c6044210003005402200d1b00701030100c0e20a02c41140498028400465800d6462043c00942d00312a00041c0400d8a08845000183d80b81d864881c1140e404c8201058251108200e0b50304011347c0303224264252000113070004154000b60009000c59000702c4841000d660358a04400c04009002c400403c03450808c800155168440202d2a802900251075002c081d03883d903500000b282d01480120580001e1a14200810f1070940144d90140480d0100c41c28034a203080340151034181540250780038440c041c810310380d2000080001e95548030f00c3c3c2d114002070381100d11029041100d94 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 389603345 1250 389602095 389602121
    0x1b0c080c030304080d0c03030b15120a180b1e04050d0e060a05030f09102d090c05060304110d0c091503330e010b01090e0106140903160801 61
    0x50300c0d00e54051030080141c0b000c03520b046010b800c185a40361001c40d15084290804c074207049c0e0350110070b500e949628026600d0394010b5168169608210252103240101c000c0801010505002e9440000400240200c150300d5000d001c400c801c0c1c42c1c203c03a40c101d40b03006402c0300d600d0700c94640401050020020301c40007400754546400d039100e050f00c01400458403541c44818007040c3c040012500d03005840c0c0002e40e10044100998691401c455007041c281c400c10002000030b0342d12000d80220703004103100000d0304060668000c10140080c0d50700c0081c2010140b00f1984512070200000d8240070103040081100351004000500e035007078603c0c0804102d10a8003500070f005240c40c01c03510b0120352081030203013980c1e00b1070b802c000e07903022105c0054001c8100c00c45012185004480000c078a08160059a9500d4500000850f4100709400014100c000d198020701d55038208030010000c05800610034004e01e038800078566600d4000c1000310b45030503c144e208030130300c008250b0005203034034042d40a005e2481b45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 389604595 1250 389603345 389603353
    0x10b0d0614130b0c030414010c08091e061b0d060806040c051806090a090f140f0607120c0908030c06012105120c01061509030c1a16031b0c08 62
    0x140b406580b100302c42c40200030003508140020880510711800550b601910410781d0080304044c00740c8107429510000b000c136011800c03850510410820038444401180c542101021030105004484c40da1504084c00d40c003050007860341c0c1c3c0030380c5440c0032085400380980104184291585c03909003d0b40d402040b10140d03401d020702d18011a003480c0001601d40c1003940a0310310042d503103580041203160f84c1d02421744141c507652840580c0004025040c44120079009600c403610b08500070000504228030000300321140d801c5501003244858202e0040d803070310760582c600021034000312070080d40c80c650550000f8042c1d1102223110b60b041800000d40f141a5082c4000c01498010000e50640e580000340c107005004e60850361040800c0300692010701140f8202d0800440c0c0c0a03910a020365050600c1181d4100160f0a40d50503c1800a24200103000303240c100300203031142450880d900316900601d0250f009140140184506040c810300e00844801c4681c02100070403481c0340750000142680c1d114640342401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 389605845 1250 389604595 389604601
    0x7030c03090b041404051f080601080601050429010207170d03110910031503020d051b0307030b0601050c0f030f0405030c0306070507030c060e01020706091506180c02010b0d0614 78
    0x42c0d1981920f00700d03030f021400d050300c0762a0202044080c040c020014002c0350342100c4103c20111030306240e80020014030024000e154180f030200c5007040340c1604824000d40c10000704040d80c0c2d200407031060302c40e00c015404c100039840081c0101c0c2030400710f906c0056250184030703007090200c4002c074086030074030981d440410034080c04404000d1140140d004440e4002c005141c5c0b000d0450117504261003800c801c5100c0c002d00e0b5202d90001d81c240d042150140c8540e0701802e01e20500c41c02c101702886007101c04900500c591f80c40e6a580d2251900024401410020007145a29504a04001c1e40e03181c3c0584606590305c405000c1c80c038000e260805c1c411940b280c850300b03039100c625080104d83d1a00860880c1d403000d180c40c00b2610300b82c80c105400402120322a40d42c5e090390900032801e10140c041c0d00d01c41c6401054070003040c28020314241c200b505ca00360041c034009040182c542d40c403170380681140e142100032565100c1e400c4141c2c01024503118090f000f0f0803d10000c000c10000340c0c070102c1d81d2200807042c043c140e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 389607095 1250 389605845 389605859
    0xb0f03060607213f0b060706090b041b080703140102070203070602010b01020705042a0504080304060e0111010b0306041b0e1504060b0307050d1e1d01061d0c0d1107030c0309 76
    0x103246003641244003210494414024402e030805d0343c40000203000c2c1482e0000c10781d40e0000300d13080e4000644030b50300c14505000402c0801c5001700c12122903c0544090b050401d038a480e110302652100525401c0c00104240c040c0e1000c4d0107075205960001d00b03039070006d6030f04c0402a000c1e14a0b404c10714014010704502017071a251a00c00d8104070211410321051440c40f5000b55100031401c03044060501c070b424003001420b03c008000610180c138260369a0380a0350741010024100801d1030560303405903414185407180c2074034002000d543c80341d040b045d042d8410506403980c041000c842d0704015068003407c1e08103c2c1202882e20000000ea105880c100500d41c1c1c0c8030307910940f03030005441d0400090010482c081000c20541c0040440c40403400d160720000d00741070300705000c84071044142640c1800302e00d50b12500d08020311689000301801105e01c00d207500d0040c0003030301e0300c10000e003803181d0040003003101460b1210643c0003501c0d1000c1040901d940c0c4500b41000f0700907440740c01c0c04034000386444002040d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 389608345 1250 389607095 389607167
    0x10603090f02090907051e041118010c06150b1b0105060114090402041503050702010f0e15100b040b12070905090601051b01020d02070303060b0f0306060721 69
    0x10780110388180440c285500300030f2406006014159244280d103c0860300380c1d40d0309038541044400303006006121260b4418841039807102d1000c6840d024090045040d4090354601c5495146000d21b42000d0468040c07520100400c91220000c1d0100000c40000c1100c0503450000d0107c00c0a42646411030540507040078265081220064000b94a41e0103030780b075860f8801c02030301445000400140c10b09403211821180c01300840b0080c1c000a4a80082c07090554080c41a50080c5000800034010850031106aa94810544180720300710305034880000e001f8010040340d400074000f0034104a5489658025400b41d0750450240b000c07510b66800c0c00325107000d019400e00c074100e030005060b01c02290355020043d50b19070032140c0110040440300c1d1440841000a100503c03007000078020068403000582001001c888480e00302c0b8210460412581030a29030800035250300c0301d000c0307800b241c0d990f0300c03850100100108903043c4045c1c0f1503109181c0e10f00541006407200b50300c0f43c8106040c01c0a20740c61070001a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 389609595 1250 389608345 389608361
    0x1504080c010207050613150203071e021309080a0e031c0305040201170f04060216020301060305031b030c06040609051005240d0b0f07020f0a05060411090108030a03090c1805060306010603 82
    0x4009500604014001e91120b07687c0c490000c50042d41e08005054a903a42c10a84000d483c2c1c006115090780f580852034680c0c0411a00314110308100542d04095480121354498121000144607201181c0c0029580401a100229144e0142c0800b031881f44c01c409009000d00303590032400320f00c035210620702d9241c0705060a8841c50f001c00e5882000d40741c54031080000d40c00742e81c6456480300031000100150304c0c00d0080d64025841040110369a00502d20728500d174008520711003d10345c008004030020a03600043c411f0f0069000900000c040c0c61a10b4070320f10303101a1140b144a024104000c01030b04106000350a04d409890003d154541d18030a01081280007281000800d11032182001c04d10740009051821340c0008180100d42000810501f818604102c0c3c9400b01c0d07440c0e01c20810801008803050360b08a8004041d1108510b65042a01058581c01043d2540d03003010340d6500003005102032152a400200100c9486181c06482c441d115000b5110840c0c1c0d0500138441c038000080c58622921511603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 389610845 1250 389609595 389609617
    0x105090c0f16140f0d080702010b0d022e030e0c0409020924030304090f0e0f1e1203070e03070e06010c080904060305030a180b03130b061504080c0102070506 69
    0x454001c61082800034068028020b607400000c10949201c4184100b0514000800483c003c00c17582d0700c507280082030f066000b0700c15400c41e4100491a1016140c2c11002000c541c0e0460b0340d8140700700703000601a900c40d100c8207100790020500c803403c5840c03500f550006070740444403800d4594050048040c132080e02d000c0a0005d41001a0700c0c0000ca4007a10500d01601403242c10380e405d4041c40c10000000d140d600306801582c0c4499032685404010f107220b2041100c1a000702002d171503014484e1110584030200c4001c10716040404d44a074402c94007061101d55408092503220303c1c0c8030700341388000400d00320b40d1400d40c5000e40325140e404242c00219a081d10300c2014141e403403508ad040d00c3d99454149410800e0840d810540fa40c00c00310001740144050100100123030f4501c00380c04407070803040b11011640e50000d2520f0404009003c102c40050551010f510740142c3c840c0c0070782d1142408074405280341c00c50507500820114022420f001c0101d020080c000e401d9003120512500e800800441c0c0c400d06640003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 389612095 1250 389610845 389610847
    0x60806010315060e0103060306020301141c03020a02270421170c0d090501061d1e040204180506040c15081920130501082404050c0408150105090c0f 65
    0x303240c451307a43d0410783c1c54185804100f02d940ea9039004282d070420f070800c0a060202444040701d506041d0b010019030768640c0101510710b200ca46003c0e4035000314100180c090b41c103001d00300e40261003000601c050f800c0d1040340744406190606200c1103040318001e25800080e000d020900a480c485c0c0298a003a08900e46070b0580c58480d203100e0840c0354410841c440000e43c07100300540100d942031150328020305a00705821101c4515061001c48420024a00c8401d400030345a20a002840c0c8070301560302c81c1d4181ea00080c000c0c0070140004241c404600010401c0c4100c2d000c000030056100e10400459140c0c6401c002500f01049081d100003404492181c078101503108003009200d0035402c074040300f071030340100c0081000f0303250351860030356201c84108558031402070f90070407140d40c0c462009544044804c201b540402410446e180b4000104111075103d5074440c03001c03403481c60058003180d004001c1c0c5811074034045500381a03840b0208003481600d105056110000300340d448100110380701404440f280c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 389613345 1250 389612095 389612099
    0x7030f0810140102070b030a090c050306090a1104090203060a09210c230f013c0e0304050d0b06100e0603040311030d0c0c0c06030615030b0d0b10060806010315 70
    0x1503106100d102c40d4450445c03081d8200060070550707580095006905602002c20040c090381000602c00318a94000c6000c3d90140f0100402e00c2d40120f0b1046046074000900110300f008040010007504400002075418010001448184961503000100041c401d1441802064401c20414507401041d9080300c007045030300e8500800a6408080d0302c00c0907148489503480d00424201c00c2d450031554040d1025660340d2014441254040005e940300d9a012040d0091085655640c0b51842e1a101c00c1d42140c40316280c80c400ea800c21002d02c141d078090503001e8110051201e213418006071003002950294021081c62010b0300600c1d04c0f0700c0c0700031480c400240070341b403443d225690200c6100991001d1001103010906c405003202525002e11401d40c0141e0781c48201482070350422400301e0704154003450905240020821407000607114240c6141d425040001d640d40344580031070f050001e00e00303008284003c0001040180404a400c010684155946007081a43d490005604071041c00c407808201c0c42d404002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 389614595 1250 389613345 389613359
    0x110d060824090a0b16030e011b1b06020f1c0207080a11010b0613080105060f0a120c030212010e0d1809050402281502030f0927070507030f0810 63
    0x40c242c1c100c070781c050484002e401640c850f0300e8802029a0700310f07584109640d0240501390700d8090200c014143d840204a010000c09138442c6054140042e00103000042e008211440342100b80d10034540d4011034203540d0740324100c01158030b95016008884200c0b0395041d0982c00f414541c4292041c0544c0412076902c2c20441c1d100c26a02c01c002c580e00042c2940d221180c440c02d54079084003805280c407583c00e821500038241007189007900d0004000500500490411404903074440040720100d500078a180f4064486605003400301d40e945070806500521000c4130300945d1b0a0562042d00c541801c1c409a031002407000c08101c0f0340c01c008100d154030307603600c030401441001c03c1940039641140c4000c1030205150049000a450410300c80f8070308400c03402c1220100401c85088021120341102840038500d00055200e00b8003003400703483d41e55401400c4042d43c0700c48641c10305070040c0c00d064000d007a480c564584014001d0556101c074108400003550440d8055055002d181c1031405446055281d1000e1800d09074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 389615845 1250 389614595 389614663
    0x91503050a0209060310060e070f0305090604120201020903010509032101030b060405062e030c05040602151b2d0306031009031202280503012601020409110d0608 71
    0x12206030b15005019a14184400c24803624008007501c0030860b0603440c2010300035107000d028020201c0be150a06040010151001c00d40c1c2d0f6100e40d110348102900b840e40f8000720f0090041c1081f264156284c0000d02000400c004060950000001004015801040110b102154080c0304c024854940c1e203010460f81e1402c0e4201e59802140509010f0507128612140100c80c41e031690031000050340c880c18042c40c40d0b4540940da00c04106428210b14192a18000075900c1e0b01d400c03c85241c441e08103002c50a0b18000324045890000d0006506444a012902114049030200800150061800a006d48d08140f9005403031280381c009010300b10010100131040302400407083c0440801503802070b0311003010101d1014103040c0b09030702075060b0f40219041e00b10000304c101c0c2100b0401d020b03060004002c5054a403000d11185100030400c042103041804015000e801150000c1030130310304200c0c40540c001c071a003028011078117000c04140700c1255201800381d11500c20300d100f18190310b0111035007150b200c0229 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 389617095 1250 389615845 389615851
    0x10c020316050a0206030a0e0c011b35030a060e0402010909200310090b0d020607020d0c0506040b0d0507030e03030a0b0a09060902030708070207060e0f0303070b07020106091503050a0209 82
    0x350583c0c111020607400205281d104880000c003544c0c0d50040c015262070700300b00c1c418a0020a0800340003e141d00c00d0042c060319032000707004000c0310710100214820801c1b550441c076180565030101d0100f00e418000388000d40c00407108014114075260700014040d1503203000602a54060310780c0c030740d01400c281002000e0261032000d4003007681404440364908103120029889601c0b06842c800640c1d0030100d5071400e0303900c4038980500c12495018400d02590f2031604a0704460760403188030447c4141458a80002d050307039448a58080ca020030005110900a0700030110086c01d154100710036621500160100c41000f080101141d00601c00203254080c207500443e09410010540c0258503940d00d0204c0031354105400c4020401e40200603c0300b019001003610b90001c600c1d001500e07100d070a0000c01002e24001c041028030919070403905055a450620844080e142c01c560105450f150025001c0c2c081c3c001c51080c07030442c501c0d14203501c000742c40c2c018080342a00da104001d00f00304000c9800f040014940a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 389618345 1250 389617095 389617103
    0x30403020c0d050f07080109110d020102120f0403060c05070b011406071b0e07080c0a031a031614032103180a030e0103140f0f1807060206090609010c020316 69
    0x54401819980c848003200c420503c5a8020728424203802c0ea12400c0c1010360340301c074141e681001403e034000341d0404484246180203941c2c1614407203107400101c5c0380010740540303a80600b1000400f8040d00e01040e00070016280100303018445104450030031030740d600c07a441c409480c8010500050045c4415124030400e0008000d0409080c80d4042d1250b0b03200d81c030f109101c2907030214090000c2092410514201e688801241415002490a00e200d44841c2c403c01a0150400d40d80301c0304070300542032401c0c2c08908040050201e03441c01c0891700c00446084010302900005580101080c4560700d0b000076203600750302d2080100303034542d828506590015000a025042008803d00300006a100100102e080050080d65800d80300010703580003404a602441000902a100c10308020b020280520010341242040d01c1400c40c9540f0320054907100e4281184d91281401017010000b1110360010364207020712995810356916490303102c1517608071b0324044031030409a001801803003003000c0362500500c01b40c0e001d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 389619595 1250 389618345 389618353
    0x10e041a04120e0a15110f0304060507080a02031605010b03070515090108040212240a090809060904110a02100e190b041b0b212202040905030706092009070503040302 73
    0x207072a856005c122065101c40b0014030f074070300c40721404c40003003114600800c040e4001c4c616050502d44c0003040340c0f0030a00050169180060307024011803007001103801e8a050504481035070a441c2c0b401078080c0a28a9010744680704000c4041503d00e40581d50840700070007000010700e040c02c0d41c001580d5116006005a0f030000c4414002c0d0920030040c03144c5140c955003070b001c01c140a030011019800c106400780100800c9850f0807003500019041c00110b6413000e600300d8030f0544440038480003c000d00410384007044090b8000c81d00207205a0005100300403a6810230041c0114030800d4003a079a0f5803040749101101e045a009071001040b05000703825001405400c0b00f04034801e03001180c4840f01099801a03052840004107100400610200400900740c0703a1001d01e218203041c803c501643e04a00080c1e810308030f007520b1640c115543e580c4104c0301c180d4040706507a00d48025090800041c504403000b030320740c6850b6200c84111010005030701040800014403250040e1030351082164180c0008208070203500c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 389620845 1250 389619595 389619599
    0x120622060b030d0206060109150c1509020d12030f0203091c12061e0824220c030b0906040803070e040605030114060a17031e0909010e041a04120e0a 65
    0x2410f0280c3d400c4808160020006814040001003c0304031507402a0962917104162111040d803207811a00070b40c2c0c011080301d101c410080720020040400000003035110b411081600208451180d4001184419450411452a502041c802644021108803200790807500514002181040782e41c0303a0704441d03151a00f041808041018201c071000c4c0c2012948072403011920901e4000000711001900e00b14000e4100700c80d0004103290910415105031606104100006600b085018194082d45910000f00320744040c107030500300c0380501039001c2074503840010400a0220500000e0080c021907000719040c1c516640c1c4242101e20140400c04668442d464803800112942c09010301c0001030b00401040107542460170810420891542c03280c04410620700b14810350f8040030050310f6802c09019000c807882503949410f66105d101d03003140d05034840208400400c11200c0c03000181d20640c13007038004100066901c1f0700c0380400d10301110001e050b840202c80d41c0c0c4c90140314042411082d0f0000c0e240c40000350b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 389622095 1250 389620845 389620849
    0x100c170a0504060b0607050c22060e0a05010609050907050a03020714010b04050a0e0d12061a0d0b0303030f060d0f020402030a02090102070f0e0408180a0306020405120622060b 77
    0x10806403403004845441d40c080c041485103e10455148400851740c0924054040e55101e4407000b5050324907200e14200c002c1042090040c108200d0790755040e0200700007907500c80340050060320043e10107680e8186000c0000c501c86014132802c0081c1d0700002d0581c00d0680d03d01804072026444204041c0c1010f8080c80b0000000c0e25000c81a409805140004a2896110b600f844115400141008080c50500040042141012440c0300312043c20f031134a00c0030112091030441c080e000f00d906c29901821801c40503140ca801c0031018104032030034000103100413240141016030301c4c00159a80481e5001c000c0c0031908914007040c04019241c4a0f00f0012b03110b01403500010f040f60800c546d403003030aa4001994010f60b6905000d40d03030103410324005900041d41404188025448000c00c000e1100800149240060481401c60554502c0091000c85055140c0c0303082c8010390414411240180c10740307107014000103004240544503600442244243ca51a0784842899050645099034069550360200c1d00f00c1e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 389623345 1250 389622095 389622137
    0x302032209060b03040510050105132307030509061608060f19270e060f07022a0427020418062a0906050a200d03050403110c0102100c 59
    0x14804424544e0702e0f0b14050910608040015401d00c800619204c010b001555540e452226a00700c4c3d960006202c0000c405800d0119412202d06000600f90100b00603016503d90000e5210f04028402d8490f0741d16400500c2802c5410440050046070480000480900f80103100d41400070009000600e0401040741c4104440a10b8010300340c41104000444c5200039a031554140a00c21308200b08080038604003250b444100c09460303206008070b21800706542d42d00c200001e0a20880031005010000da94100019006080b800c2103801241003500264101011510691420049203a541443c2a0a5007040010031008809035150144903416074041640d41c49500c1204c0520b0a1051400741016100d00c5425055103940c81001810403040c01899070000541c3e030a41c8041c1400b5203021416001849154001d9000c4081c0c2d114154085500c250b00d5004503010b43d00945134810000040c0f5130540c1c507500780d2808a405684010641030809034035a10058040c07202c0c0c0f03000442010018400011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 389624595 1250 389623345 389623349
    0x30f1a070f030501060905240712030f1406030a020f03031e04030203150106021b0a09020a0e4e01061d0c0406080103061503060c050705070b0304030203220906 70
    0x140035601c101e580c0c0c40d05886002e000d000b0301e0519a56130b614000010320403220341c14500c0b61500d0001a906441004401540c044c41d520203000143d964981d130009004088480407014014181016501607030000d2003154090100907024140781c003495000c0c480d801180030201d98061004010b10050011000f03906c282c40c421000e800d6030b9880c5180109403030305030340070700502d1a0420200100040c0390009031804600d2000c20422080c07007a0f44000038200d800075800480300740d0000494006e66076109441c004060011a04001e4404a08406d0a8400810910400400d807041180310400c0c0ca003c0c0b4440c01c8088400c0154000c200d0045d072182500c1e03541e4028403440d929101071400482c003d50036140d1000304a01450f00705841c05000508100c1c041c40050803c5959004e00007440d0107011030038001c0c5401640030b02c1200d80c80300005040754400340781a1103a0040d10408a4030092040c2100e0280341c06500550426031880340b078080e01c01039204000002d049000e00000d80401902440b00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 389625845 1250 389624595 389624597
    0x1b0303010603150f060905190302130c1215181b0203030702071d060103020a05070629150702270108030403140a020d121704050309010f02030f04030f1a07 68
    0x103600f444000100201d5025500b11001c0d0001c80d04c028800c0c564020b01e48411103001707d80001e80540c0303a40841784404040e40010790050881500e80030b081e445a084004062442d90b01e6011840b9130b50700b480f00300c0e50300c01212100741c4030380d2804200000e41c0441d036400b185550303c00080d400070307904200818804c0c042601d2003d43c001004200b40300d50107005001c0181a800300b6908103200a41e00388100200c010700e0b103418543d002c03c2d000f40051140c0180c0d943e02e54050800c201c40b0380111081c141601241400b004800d40419030070846050171100403019018101c0800d090008580c2040004200700d6101000080441c03214000d5660006a06000340a07000c06150340340e05504142c000091441080c45070741c1d00c44109800180c031599603805041d03410621184000c3c060780400c072a40c0c039520544d10705d10340c460b41c00d000030b009020004050040003600e40508803844034800342d031a4000c6840c001d11070b10052104001080d611407042d2401440f03501180549030745085216040341047e12220 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 389627095 1250 389625845 389625851
    0x270b010602060c071218031a01090c05040e0408072906040b010e0d0219091d0d02011509110d0e010902090c0906180301021b0607020706030209090c1b0303010603 71
    0x40c40d01804041c0c2c005603140445880c103601e0f500c500a010700e80b00760340c10030841e008080e0285c492a903000d0300099684048046a101c40d80c2014449003403087c0a6034100030f00d0810b04030752540c041c2080710116800d841c001c4600b80d4071610f501c5095003060b0025100320140c00301d2507502e103410300703000302c01500480e40b10f0400381803100900045405022102d8188088544202503035a1812861000d01d40d0450f400080c0c15072080002408144e664000211242080d107141c0121f168041d03001d90790300215080740d10450003290100d0aa0300c00c87d00f06001c43c5540744003809030103c40c0c0c1100c40ca0200703540500b85801c0d01c0901c1c0c48212580080d148500341d6560118104600d404c03c40250030a00315001d05040c4060503000031168490b80c00024584140c0160541d403d4074290147d511070b020326a0f02c5e2000c0c00c44041265100c0c10110344500042c000c031400803800e05c3c028402d0380c400c3e070405070206006070340e4041d070244142d202840c072070103590320700061426449c1c04000450103442255404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 389628345 1250 389627095 389627099
    0x20406030503030f01090605090408070f03030605190503160b040b0a02010905150f06030c0f04020a0c0b0a24030309090e0c0a0306020a0906080402030a0f02060f03040809131e270b01 80
    0x86070340748d0b04042d106600e24418000030130003407411b032000305030407030f002900c1c0034050b03d4150010a45940819044040070040002218843c0c0c02c0350103ca00c10f505a030030144008050985140e241d00401c8140501844140031a05034140a000074038064000000c03002240d4850718074080045400840000c1c6a80803c40400c2c1d904072107a40012094000b030041400c0003001601c45154025074a010ba41d001c6550b10f4102d20500e0b52000706904084035401c1030810182c100042d003842d80d0b6445c80e500d2040207024000c0d680300034010480307415540d0bc5c01e106041c920b1040141c00140000c1050348540280c00f140e030365400703030301c0c000440c881c0344010795072050080701400d000c21541c003040921a14908200c0540c41c04034425a526510103443d102154151000a080340200c40b58140105800300400c01000280d0f001000e00400446a00a0070082001e00318107803801d0303011142d141c02da0a510303550304020b2070700300840e621405600b0070383c01ca0118032008498180d407001031b10481062001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 389629595 1250 389628345 389628359
    0x100c1e200102031515092215030b06030705011b0f06020c010e0a110103060308120a27061107050d23130e010608090a0f11060a08070f08010f12020406030503030f01 72
    0x14a104005c1012419420032a840c000078100042c0d0401602480c0d81800d03034010140c14950002402c240c18600c4002000d803a42090038490303404480080c0030b03101e0701501081c1c541c0540c04104c84030202100c2c0c40c0d0b1702c00741e503541c0d08421080c488084826130b800380400c0344c4041c070a0003203804a82501000b070020f05450b04000707240b405103128040c141460114140080b0b4041c1040340c0c880843c2d02c0300940c1c2507d420309110000c1038045004000540b090041e1076030703400da0903801c1e00564040c440a02c254244d4100401c0c1e10f103e0241f005003194824404054000e001d583d0030400303945941203480c0349052031840003039964010345841104100912041c044952500d81c0075024098510b001d040516002201e599142c507000d41c01f400070310303420100400300720702c0d10801180ea003005003019803585031811000c0c210001c143c2d07070040418800c20f0403290462148422030f0481d14007582404d029840c01e50700d40104440c403c0141c5e00541c4031400400400d000700000c6003e5540a017009440b589445a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 389630845 1250 389629595 389629609
    0xf03180b0306060405040207170406080a060603140f090c100c0512090303040b0f1c0501060e0d0506061005040e01082d060601121805100c1e2001020315 67
    0x80145911000d00c2804220f8031201c042e5000d9881c00d581c010f0ba1626941003080543c401c240c1010103c83c00040d0210700c00b544180c00c20300401541e8400d10980703480309411340a03200701c14401050841400005204c3c0804040b102e07030000b0880080d9810841030901040d01c1140904d0010081203404003103030f00b0050204000701d100740c2e000114508143d4214002900ca100c0c43c42005058800441c80c003491464400480306910a140109501c0003c44013070b00b0081d00c400d22135640481d4031040b2210031803c0c20481c540080380e200e40903249994a110401c03583d080140c40820400000388404900442c2c0440343d1400b9095940003032511400c0e0500300e2003000c042e0140c035007000080d041c00903002140011025002502400c0048140c0004440300e8010f0580e580329400d826891000b0382c041c4072001c0742c4000e4089216105002c54240d902e4281c4000070380c1d51040078030042d4141088151440780300b0762445400480c03252041008104991826078005442000b60f125110254001c02d1621072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 389632095 1250 389630845 389630849
    0x60908211008070b0405010f1707120c030207111e060318010506100c0b06041b03050420030303010e04050109150b10030c02370605010302040501050a050307090902030a0f0318 77
    0x40103c030303042035403400c500c1c0954800c40b07050200e404500354120780a030070070801c0038511108002c0645054038008020b5035001204544d018500740540810390703c030b070003205c5e12b06400460300605101ba10041c8207182c0200c0b59015803070885241045001d42d14a4021030041402260801c0b0041e510700d0482c0c00c40f030024207024801d1030380c503600c0c41c880c64114841052603500320072a0b003441e595000106000e132582580c403801c01c015080140040c1501980458001e038085d012500c370b0010313010742111481001032421640340d4024401040142c001899596215120b00004681c2045c2075a41501c440701c02d25074498a191a9078440000c1d0501082e90090059907140602400d04d917000c2c00b94946002d441c1860f005da403443c0701403105004400f0400d54000706c108000da4545498140600104801c0c04124895030a0200014083c078104c8940c0080d1100200a4508207141a0b0000014010404100c1c0c160103111a4000071034401c02140517014042d840da0503020304035a0410f06d540f20300d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 389633345 1250 389632095 389632109
    0x13030b0f0604140705090109121b080303010803070b19090f030f031505240a020c010306080109030e0105031308031509070801080d12060b0f0405010909050705070609082110 76
    0x60b15011002d014003c070386800030b00b1410900e5480100c100100d44003200c9400c025512016401d90324200501e54072110521015a081c3c552801d48036021151244028461000076a00c00c3c0212000706290028541d0044000741d03a030002000003859a105952480105a4000124000d04401e00d0340060a1940703000207807030100a400f152400e2210780907458011107024442d0250708500c60b001c4940ea00110101c4118501d80303420b10320745c0003035803010f440d54868002803c010b00001c618005001d0700341e00c968181c032051b14000700d4000440d155080206800c0d11201026000004104402b0007180201106a09044043e100105100c0c5880020b40030b0407c20040030300410129001142007500e40e072403840c20f80d0b80c01041003418006045590003101e040c00d030010705624880350702002030080718002e803501500c03d0399031006001100c1d01107881c4070119104121240008040c0e074440d44a0500c245c4d00d00b81005814271002d8503400200c0942107801a42e1801e1103810114000c0c1d00c0018414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 389634595 1250 389633345 389633351
    0x1e0f0106090b01080f01050d0605040f050a0b010812030613020a05040909050102090405061c0204020901020f1005060f060c06060105160f0302101802010e1203070f11010f090e071413030b0f0604 85
    0x9005c1c0450801808c03c00c0160403560360700042001c102d00c9401c01c45036160000200c9481c0026410003089100e000c0c8129800b511070343d6480c2304580700d4042982e20505004000c0c00056022950020103940f20210000422904200104004000d032080410582c010000161140d140100f07010848001501040c450b54100c80f00d040380c1e0000000c200c10850303044c0c401586683c14400181c0c500086101c0015440c0120340c11480b40103125803040b4031602040320f00000c0c089042040c0600ca114500d044000368120a0001c0e0541d4080c0e0010240080c1004480132078482036100c00c08105d501000440058000e00105a009861030080030075280c0800823480d151070705c50b8006070200c03000b254124003600c0c00f8860880070110a00a90b42ea15400c00e440048000c014070306482d0328000807030341c030303012680c42e805101c09140f180c2400010740c3c0c55890b50000540b2800030950b4040411050010020740400c0000f8081d9400c0d5030f450000c42c4100050001c2d801d00019205881c800106418090780c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 389635845 1250 389634595 389634599
    0x70611031f05060315040c0905060d09061d03070b0702120d05240d06110408010203040302030c1005060a12050a14101a090105010c05011803210c021e0f0106090b01080f01 75
    0x894050007480c405d104440005a60300410001d0314001000e0780902e03800840071890010061440d04101e05040c03144e80300300040b086c1c201c1050608002110b5201c240d80c001c1c0b048000007a01d01e150b00c2d03000985801100c0d011180159107a50070340c04246031000703080e120700600c1020000240d41c02c981d000c808014180e0412040082004010f0202025065980761461401202140000c0703402408800300259a24a021700300070350340394800c112240e01c42c850140500030004081c81024083c1c43e0007000751400e285841160300203001e84250598040c00f40750320b8817000a1992641c881c1c5070341101c002d403621001c80701000c0200d0700c0040d001418551249600c00b619952218494155002400c0408130310280b400c0080c01011440a00074000000400d0013061540105080c9800300c10328100c0318541400080c844103a4403040b03640320169010200346200e42d080194a0032003111035908880e20400c2034040107094a44940c0070038019941c42e070041c00d19507030003289103038010190005491154 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 389637095 1250 389635845 389635861
    0x703030807051303050f15010b070503030103020906040f0e33010501080414060a1508010b03060a0209040e16150f0e0d03090902070b0609100602060408070611031f050603 75
    0x10030001c180d101005030010300c40c00c004440c0064100590340000440704c00c03000c41100c050f44d500043c2e000343d0f0b44060080000455202c100100c50256501c200a14103591941e403d010074000b01400172903016403501c80c481500007061041c1000112424000c0c400782180c0e40d5601d42205190881d9480b01d41c00e003810003d640740c009849411100203282149481d912070901d07030244c0d0410700c100011030003954180f09414200d034000841804510344032030798440d41d664000c0d080320342a1401d03c1d01350f00709200203200545c0640c040d004018002d000814a003403000300030340c1800310b83c140c01c450155120805210180103c0743c912406009411701031000010300c0c1c0041c08402400151503c035064150311501050b10580f0510002c001c0c07135105540340d40451508011181c07049540c680180505030000300040c3c000d05400c0110f441e00e40180c181900c554403002e107070303600c004030986010b41c54085048405811100940c07080514003d00c0318229250420f520020a42d503000a00c1101d062080c000c020f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 389638345 1250 389637095 389637107
    0xa0b0d020d0b04020109050907030212060604080d030c110a0b010317030609010b090607060606080702101a04320702100c1413150225030f1202011b0f020609070303 72
    0x400d81060490a8a60320f51004807804d0446810850300002108180003420b50590044c100401000d019030704240e40381014403406008511030140d4039800200e9001c5007500030342c03143e9124a0390346805030f18200d0300301c1400c0c0380503020b0208448141c08040100140729a00c0306000c0100c50f603581c298a941040400101c1109041c092103215180c0012081c025546071411285802da1011051080550381c1d080030300300a40840d111005030050241e14003654903544105151010030035804020991294148001001c415030340744800e5590214044189100800040a0301182c46000d070351441c014100a04190050304110f140340c0c03c1405601400d030b04102c180d241040c1c401d22507a11a109120031010079038150f070144a4540d0f071540c020360400d0f404039024a403105480101c0420284504c440701001d00750f80300c050440d1116188000001d030800c104111030052070710000c2600c44502d1030300401d03890f04290380b0000c140c500300092042c80c0c040c01030580c41441c0c1c1014000f86881c549001d401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 389639595 1250 389638345 389638369
    0x13061a090c070b041e020901090c110d27030c08160801050105010909181211010c0509030a0807020105071e0b06010201050f1503161509170a03080a061d0a0b0d02 71
    0x64007817403002e1004a140070400003101c00e8009101e044a5650359040300020280c903c4000300040240300860b0300344100144050005201c0e0b900c0407040c2e55190300c120310080e4038000306c211032114644008086034000000e4806041d030580030340803505886002c1030364102a80d0105170141d040000401990f0b0300032203850110fa120240124001000072072659202c0130000700280b503841a014030b00200c643c4130301034112048011000f0081c220400c0e00c103071041c1c0642c4d1a8258150302c160b01c0d03e800201c580004d041000e106050403400d00e100c0380d480c0c0380c1556500c00540b0768111072615000622030f141d032106401c0b0200780020052410064250380c01144000c050ce40d140300060316840c0b46da20304104114000c0c90082121036105c0c0ca80030750351440316a1041c8030300040c0f60801e01041030401c1c6d805a09802c141d407002003c2d032074080d03a400d5030030000040695078002d580e40c00020781c3c2c00321540342409000ca010150b010741d25180600034215850510300501400f00004200f0050300c0340c0b04000c017 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 389640845 1250 389639595 389639603
    0x40b040f050307060806091b13031101020712080703020a0b09030d0b010905030d0c080c071404060801061508041a01080307020306010b1312111228080a03020313061a090c070b04 78
    0x260b00c8e41c0d16620100c0960104980615514000800b00e43c0f01e0304040503042034a1142040c43c65180481004a07a00d000301e025802d42d800e00c0394200300010b0000001442c050303109006075541480700e5210801e0044c41100d40c0042c541000444403d0b240c0c2d14814041c01d68800d081c0300030018180303404a03941d04103254040c0e0a000160440100b400091420750711032440c118100c0d004203454005c0041500c25117100d036802242803080100d60700406018050580781109041510201d080d002121003842c050425183c80901c4085140c680000829050103083c29900444c0d41e03616a04c180352402105a0109242030001d005c103001c000d9071008042c084075403031041500c0340350190400c81c42c500c004000d110b5100040c2005d00d1181300e00403652902269640070703226a44d4011006424181c14801c50003011881c04001440d01c0034001c1d4007454000f08041254100701c88503036a11811207550b481441440c41d03020302c00d15032500e044900d943e0b100c482c0548950500c0c0c510303942c48404000142c4018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 389642095 1250 389640845 389640859
    0x11150a0c030e0a09020a120203090d1206080712200f040e0309030a0c03020a12020609090a0b3a080703030504051f02030105010807081e060a0b040b040f050307060806 73
    0xa05100d521402c107036100090020002e1a42c5812000080d80b0080c030107000318801b00b036982002071075071080c1c80c844c0c6111406054502c140100c1203410700540c0351020803480c0e86070004999001d08000031000760408152540c1140981d05260f40c02e00f141e001500720a9031214a24a480d0f102e0350304d00d0384c45c07180c151004600f916290007018254007880c03222541510030400c42105200c0c00c00d59400481e4000d640d014901074496030001c020800841c8069000041000b440070641032180b0201e911540c400c0303000a4074800800010288402207042e01c001940e1514002c3d4481000303c00e0814040d03a0325500382e01c010150342d5520190003501809414190344a0000d018000240160030024003c03084c420300820801c90610000d400a0050300e002684580c00240d55500801d00203005083c00010461aa0201c04c240c42d00400c00501703940c1c1001d0b0b444800620a8805000340001c0c0415006040d11a410300060622410003540054403907802550104805a0050200f83c2c000f5020f4801c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 389643345 1250 389642095 389642117
    0x70303141b0a090b0c2b0e3a0b180604080d1b0504030b100506180310020f03061c020d06020906190c050c010e2d030d090311150a 57
    0x20f48021280e80c2c0034882041c0700082c1e52002c801e011806403c40170704101031003607a16144900d1846800700030036500200341a40055903803072825005c0100c0013a802a6118156086801902107000004118020544440c4000d40401140d04c070035aa100c180000c09080c40c1000400a564a100117040a808010300280080110b442900140400d8a49800c072400a580c20080205164410b100942d40441603c010800c00d8451041c0b5404480c0010703c0d035030a010350360381c406806800b0005403951522541e64142d01d804054005003071040505140281c03a8a440c005001100f102641203403510040017442600603a0b44841440e051034110000585035490400401c6103449511100c3c02260302198014501e03a1340f01500c203080a00c1203003503078a0100980d00544070180a82c0394a035010040205180d05100c481804108034145620002c5002c40c1c13100100c0d0400450703580d90b4001130710410b8140306006616a81c141c0d5150180c920840002d8410500e04160207080c0c49101040780346603003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 389644595 1250 389643345 389643347
    0x120d050a090b010e01061215060e041512140703050d0c05071d041208040c05101403040819020a020a260106090e100e03040920040902070303141b0a 65
    0x110298080c0c2c0070046042550b11548a0440440700748a510009068400e04054210660192103108070540700c03c203112504252068a0f6403150075902d5402070f9039022a03c00000441c1070202c000c0c4a442c2c00b05040d4181401c2c0041e845070800e00591156101d8101040003850010f1001c07040100d40c80d28403c2e01c0c1c2c4500d04541400070715806007042c1c0c580340242051103540201c0541c01240302d142c0c62007420f0b03402002078844010072035014203900718000081101d030620620750402e50b03400340740c0106d114184117403030541c42c2c0041d40c0079540070801044c1442e448051070300011ba100b24600041c40035584941c00901440c08502401510592004644a0040840722254107030208a80240074043e100c46800c1c2c010009000c0c031b08420300c11a103200c2c03e4441a072040740030301c0d1550030245281608200c80d8601500011b201910100c00c98410a01a2200323031000c0d20280200d0f80015a03200c02c42e0800a00303070b41010403121114202d40091103a13500c0c180d100d020a111a42c603c1a840f88030f0010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 389645845 1250 389644595 389644601
    0x3060c0702180103060524030705040203150a1508010b0f0f09040b030a0b060901050a030314090102030702060a0e011218060504061d071a0a0503070813021c020f03120d050a 76
    0x10402d500794111000120030040141c100c80c0c4603850039000c00d07051015016004521241d920740310b07038040e00002c0c001d000604240d0019070303111070105070f00c03942d88c8002d0021483d6002540c3c8450740e803807140f044002045910140213401480b15800032400d2001d9580c1094031885074400251329004006000c40e05611660002c0030582d0004080c0d07031188555042c16003401208441c540c0c030032210b001c0086843d01d45104c40d1010390740c0581d50451206500030700414250300c40c11103141944424070202d001a0368031002021700e40c0c03942d55101000501c107800500604014204141c0c22810041c2c5500d210b40d56072125442541c0008000c10aa03c03035046c1200146207010f490960020603000c10b208241001800e10226100d04001203001501e4180700d043c80c0c0119245040001c9007000400d50705031003000140c2d004442079122100803241b9030700041d440c01c4180c02e06002007640c41c80620030343c90450320b104150701054000d050000500341c070841c520b02c41d022450710141e581d1004910b403c051a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 389647095 1250 389645845 389645869
    0x10b0717030c030a060b0406020c0111070b040303020f06010b0a0507060209040f0e01062301020d0c140706030501140a0308030a1109030d05040305120711060f0c0607032903060c0702 80
    0x556003075500e060440421005500c101ca40700f12082c00c00d18000741603030b8403c1c225000c48282e0740c0640100074048004484440708002c0110451003102c034085a08224100148015031180d00140403e40c1e907004000d003050720581c88201130f500107220034035210350490100c504455003c1001603803400c030800000e00800e0306528a0001070f207480b03001441c1044c15800740c0c050b80d50138004a0920f4035851302e000c0c0411411440c490058005440b03d034032140c040e54131445414030800c0381110703501014079402d141010396881000081e445d080100000e00d114003000c1041001902c03100720f51030650311121024030003e8592400b480c1d0ba9025000600010030984440c0c500003004e4131420340742e11800801542150109444030f001c1d01c00340045400522040f95641c69101882c0790f81080c18804122054120280f181d5109e2420461000080810b0002600c00d00150701c000602c4031045215015641c1500c480c10824511814070b850a0741c0d0004070390f0740c88550340c82a15641e80302440400c800d44508 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 389648345 1250 389647095 389647133
    0x90e04030f2010181502030c040b030901090314070b1603060b04090b030c0d2001140a03091205071a06010504050a030c061b021f03061a07050708010e0303010b07 71
    0x51115000c0e031040c046420f10914030440c1091092600c10191058002103e4900a00100800b48080ca0000c1035070081e50f0f010074402c44035810969108445200b543c411116054a40d54502e82002095009855540500ca2032a003a0b41031081c1c59480c0030419401610040c1c200c82e0000301034200b07501c03c4e00008040d05078000d1560301c2c0c668884041c0d01800c2d42c2010316100340101c8030500d0007810002a0000b102e42c0001e00c601b9280007041e0a003040803880c01a45040000301410320000f407800c80000e10401003c2d0340c0008485e0b03ea8109825404070811108040010400c40300380800c0c4800b1809801d0f00c250801d1a0098a401005a83e68402c6900c8250407800007c800001d201110700340000710350140d01c5071070b105015120240070301c40103164029404a00b26440401c20340c0380416981c41511a07040c00036400340c079030350110f0822840c45104028110700040e68410000d0900050b00101011002801070390080c08006071a4001401201c040b80740101e040e80c1401407111f5106a00036078 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 389649595 1250 389648345 389648387
    0x51c140a050703061a01050a0c08040e040506040303060e060609150c25120c0618050405010b0a1701050102070e0a020706050c0a0e030d20032701080106090e04030f 72
    0x100340307801900c42245100c20f42d0014502040202544055403141e01412016516a8a4101c800c6400c0d180c00107007080c01d841c0102e003400b000c00c40000202000d4021401203000303054601d0306180040a486854004940300d801c14418081036031a080140c81c00a40101c07110800b980074000344003194066511031069074454541c0ca01d4482c0c074080e91480c00907200e107000303148441c4ca4125000e03504842c032400030000481c1c000e08121162050001000d1182c4440f8031607050303540c4400207026603200782c20045000f0030002c2d44c44030040c0c02006400c01d8403018031011585614106c0080d444200d14814180701e03000d1040041c0312120701c2d170304a4020342d5000c0e030200800d05082e90444401d4005125850110f22000e2041845d89400540d40c885c4a41541c1d640d40001786212a02d82048915159104580b100f800340c8640440030704810800c1c4ca00041c1e902c00b611000300d00041c030705041a071005040c4140b0300c0c02800401b0140d81015030040e0107040107403041c050040e0031184900407041002150358 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 389650845 1250 389649595 389649613
    0x1911220908071a0609010e151e0315010302150c0a05030a080402010905040e060a020c0709060b07060531150c0816030b09040f0303060e0a051906051c14 67
    0x2000d00140c0b050b18050300c4078945a81c12418500000201030304e8069111402c0d0380104241510b50b00c8180e440001840100c0b04000c44a01066034041c911701149002c00b0070700301c80d0445060070013480e000c8000000340d0a0b4a9491a0080348441c0d402c0c00140854050009580345881c0040003200103071a070000403070359a03880707030100285582e01c2903070100c3c0083c40a003000a000c0c0b40500072512000c0801000c1c02c40383c0c0700c0105c410000d47c8102c0d1281800c2c09102000203c400c0c543c0f01b0030008058032405030b0f9803652146014170440d00010311280128020b00340010022402005500154458414400442d40d050521405900300c031f4240380403190074010680009640f00001ca40502d8041c02102002c650752001581074a80c52440107800c060356400117004928503c0c0d00c12407003406400c00040d01034480000004684003258110070441c5c5039800d1082c00126024000e803104e0846500304000340c2440e00051070041286000d0b0141004484104140302040c14124184a45201140ca0100d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 389652095 1250 389650845 389650853
    0x60621200a02070b071e050c030a03050d1b09060e0a030f1406090705010f050f0403050102040b0a090e0403080403030510080d02011a040e06010b030a06090906060819112209 76
    0xa0702036a08003005000c0c0b8540000c2000c0c10900703035038a255203d600710800d650b484503c1c031280c4003c5101501d951207000074211039501d00b4040001c1a074001d40c0d6031030360746003070074120029a0000d00c4403840310105c0001c0782814650107105c480c2605c0c0240b4181e80101c4400c2c0003e81d0b1a1865007000d0003250f007400380f170000c0200e0704208850f036000c00030030b551555841081e9281c4440091084c0b501007044c0b112403020303040c80307003005149015040c005c07a405c09490703417203941c00ca1300140c12205000200050a125082d041000d0600400f51941c00c40d040703141a40d002400308801610082c10325171a000410401c1d50701d01600006040c81608807108461a088002e01030101d022512403411035003410510203040130700881c03500c10b400c0001050740d40d10301138050603030354030080201a102c0d503115070100d00549140a054007042c0a10307004600642425100c908103d1104035214901d04041c203018002480b118102494000071641c0000504c40c80d40d802d00d1101c0302585000c40186050b030080c01b04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 389653345 1250 389652095 389652097
    0xd1103060316030c0605090619030b0108010b04080d05030402060c0f240c0405120a050610061103090a030215090a030602040806070503040b0a2a020105041506062120 73
    0x840e4101e04481038050211200000e50606020150101d0408101841114000c41c02404d20042c0688403510f8000702d1441c2c100702d801403484500009031203ca03103040c5580d001d40300c0c5000d0718180c80c116143c00d10740305460741e0782c0c403e40a1041c103010021000500313543e200d00680b080301810340e0503103400341c2004411a49864803030f40c100d0212003d00c4580400e6000c564030880c030402885c1645031629040c0001c10200c41100002c103525407040e007504d80d000510900c1810b00035000202c0305645503040100107401907a824955502c50741c4280180c40381a030301c900013002200d40503501c1c80c00c0000b420b11400583e100c1d4120b021f0708071400040000801905500038021503240c00c00740e50144c0c4822504480341c0c03000343d50180004561034040340c40810168012103143c0626001442c21241c2840d0740481d00020b01c03c40d0b40540d40d038804200a0059031013040b00c401d1210881040340a042c103c0260181481c3c0c54501f1204024059041030807050307a1088a05040c0114041449020080c5807955 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 389654595 1250 389653345 389653351
    0x150605040608010e2a0d030f0314061f0908070806010812030f0711010b0405010608060901051203070f140102040f150503040803011202010c082205180106140d1103 72
    0x55407814400251042041c03251045903c140e50140a00e0314400302c0300d004d07220204400c0340441084020074002c603601d10380c440070200e20a4550204205074004050125203e0442100c100d403802001c2180036900c00000c01d40e45045094031070101d4154000c00c07036100030290032002d43c1d0f1180000100743c1901c00a2840d040380c400008440450130442030303984403404160f0700d011038178103c0e0010a00301740c0103002807401484600e00014000d5a040c0000301a00e00a0b88504003181c0d00109000140c10301c00300090140500351a0014925003001c59555603125055002c1c3c101c18840c0c140504101190b4615003105090700002d544480c0c0300c040641103d1001e105104013540d180034a881024068002d491056030881e50340760460f0700e0208548442e130308006007241041115182c4c0000101801c01400c002d1110312400075a611800c0da03844d000c10341d1900f01512803605032038030307810b60b070440c1034441c0c1528450300e0031200350300d1200721842289c003443c0b80e40e040c8072382455a05e000c00040c0d20007a40c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 389655845 1250 389654595 389654599
    0x1811040f050a051005040620030711040b040e0d18090606050a0807210b1f1805120a0201051b03030a150e06030d1107091508060117070918150605 64
    0x8080b07543c0380104200760081040d864085802440200034044c000c0c240c4c0100c0b031411400b0306000e140c508500b1420740e8042001160400b1310030100013510b05040c40346407840c1c0e1080d10304000700c2d084002c41596501103031411504001c080c5648200d0780c41c286074800b008041ca07000c140140c035180c8101400c40d0f0032443d40200003c0081d000a800c2030700c50074886000116454070b02c2d01080101803000e0190002801e9241c2041c0e00c0f05142c1344a09440a01c20700b01000c40c1d80f4443c85100901c21b0b41c0b44e4801c1980520b1090304040102c8590400c08210014401d038242009551031024007451210a0340807068aa01408040200040c0c104640c1100c0c0c4c400390300a6000c008592030720b07000d8501e100261000341d0940d000d48015200e444c006d041c0303a45001d100d10f0850340240d130b83d080c1d00c6069680907000f501303c070f011800003002100030070401f041c0503208860420500041204281e6031300c1c00188034104405407078940140568150b241e90305c0c900e40e08a030320300f25841048002a000340c0401e11400e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 389657095 1250 389655845 389655859
    0xd0603030f02162918100c050c040504051f092603040303110903070909110103090827130c0f080610080c13061205070c0c1811040f05 59
    0x100e99502c042004100610303440701000d40039052192000c0d603603400800c07620000306403041d40b01e014a00b070b03c040d100d28280e440e081010720040d031080c081c1c4079400d448401d00f441401101180011004110810310b0300c4280c13800a02d41c1e48a05045141464450039082e0038450000d0285460906802414a51b80609001111038011792084900c02071070000c204102c00043c0046400244643c00075003003401c3c1724030090304022821300000e0134100c0da0343c0180c02171503a1b01c03d070380100614a00c0c0d803001c985090904102845107a110401c0714441c1c40f0012140c16440400148200000494070702031030300c081d022013841d05082c400342009002008140000c90010b940c0c404249200e090840d1094502401818408022034002c0d1400f41014014880426090000c68000328110390810001c1290b84d8604040100f403581c800e08035030014000c001042089e2924002041285000b2021180700b6070400e924040d5003410385000b85010000c85004010004000500c290700c1d020150030396400311619 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 389658345 1250 389657095 389657117
    0x8060a0b0a05031506030c040306050402030c030106080c04140c0403020d0c0e040f1505040302100f0e0f0d120204060f0f0e040504080903070b07200612040b16030c080406020a090503030d060303 85
    0xc8050f020031034000340344500401027480040c7e01d54010940092019044500d0381800d040000d09413401030b0030060b006c0d07004401d50b81d4186414000d2201d03244c0355990f8101641000000c1d40030714030481c00080d00911445c840b800c2000b14035100400107094902a54141341001d142611445120510503541a00340c00d104401d960102d11600d0300869154006081c0001c0d66925080a8907001e012006801d03071340c414200d071103170301400312074408500d07900600301e5140f24050140800340c24a00780f03002d4030301c140070600c000e0341c0000c0140c80d480d48504109000b0310240c00100e44020701c2488035508036003808103000c104410000500051303001201940c2440d0f85070511400c00b4000c1120180009000000a0b1003216042100c18590700025150602d80040c000c039400c0d8684003078500700c07a401407500810248142c400000d0010426070300d014010030341010001801004080c20141c0003650010721103058600a814650082a01400b81c98a90450000c80c07801030000c1d200c2034010418071045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 389659595 1250 389658345 389658349
    0x30a080105010f020c090105130e03070506070908192613050307051804020d2a0503010b090603150907090e150709050a1512020c0c0a05011e08060a0b0a050315 70
    0x174028070f202002d08018120380c40e003410890642849561030003402ea40d56034402c070b000c01c18402801c0309805030000304401d041000c4000d051150940c04200540c00c50703160424600c1c0951003600e18260804c0a0102c5407040c00983c01c600c3c5d81c42c0050090f0901c0010710044600b0030300a0340070407184100c041c1ca04880c1d4a1041c411908c00c0c1400c4c1c040902d0140002400514194044060301e50140c01805100c18000280301149000c40d001b0289a03194600304200c00e103802d001c0d0580f0030000b5a00041d25040c0000425666086850a00d4140481d080000c5d204041049954020400910203100c00c0c44044141ba889800b05030440d000c0151540010f046140030b00404400c035100946030610f0b4030300c0e04e0144a41d0045010702c4108000d18a0a41c2d041c000190003e00501c1c2c0d8110042d24110500204021803034a00368041814840c103051014190324141c83c00c213644501c0c03420081c03a03070f80e0b8120001d4510b280603000081e100d14041060b000860340403001d035102c1c800e806480003a00307010000b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 389660845 1250 389659595 389659603
    0x2031b2b12050a0509130b0a0b04031203021c0e0f1606031a030a03140702130e0105160503070e01020304030b010305070806012103260a1e090c060807020708030a080105010f02 77
    0xc0f0f04000700f2400c0010035130904158411400c004002034001800d0360800d000912420f41d20b03480000c501c0c2c00406c060041c0140611151080c1c01c80d81021441e00c040a0721118000d8002201014070700e683d00305003580403c044c040314400a0490702a2600100c880c52180404002030140a00292421407594500e00418a90030903001c8010010094102c00360340440316580415070410001c0b40a01c41040183c8480c043c1d000c403000d5034080441c40449801415084801c0245001c0f01c0b80389003101c02002640007411640c0000c490f06e8603080824100c40180d00d03500c184c0e8401000c21040100000500030081880b0003601c04110030748140b0390780e820001114015051400256100041041000a025880c0c00d008010010880081e0030f45180802855250450f044608035440b01440c4980c1c0c0d0354189481c01000030754100300100ca00036142e126a2401c54024501401414004501c1c130307034001c2000c0b60040c0b02c0c2c40110b9a840e900058000c107071900a00c101030118500350392403544240041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 389662095 1250 389660845 389660857
    0x1050103050c0d03111603060b010509010905090a0908070b0f1b040605250501090203070f0b03060402030a02090913030f08010e0f0a02091e130902031b2b1205 70
    0x80d0042c49040496002c00100d5410404202c051048a4a4915002406200c0c80f1442400e00b043c0098441c075501f0040c050f45d4840300102e040010030400f005a03686c01078068019100c095a107100d090f5200001030005280c403401c007501c05a8042a110104910031851502c01c140c02500a074203902e0303649520030b0003e0040d4041d140d480061105200c2540b046003c0e183d04200300b01c40c140f141011703a24030071800002c2c945c20341d01651900c5922043d03080802c0000020140080692071561400b074845c01c103800040c14440c8103580000c049040383c91541c040e0b03203003400000c1481c107080c02e11542c40260040e58500031008980d851203648041800f03640100c0c102c8014040071803c9075100300340030141401c01840b040400e030b400d010046054441003209140000180381c6030070405a00300400a074500d620715440386050074800c8040c01600e000c104005410124007080300d2140040d4006007140b012541111800080c00c40c5940c9441c60804035084402e00407040300900c0440c102048034a8407c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 389663345 1250 389662095 389662103
    0xc030606060d051b03090109030207050a0f060503090a140307060f0b0a0e040c080d020309010206090a050703120509040f0b131a0d0204022701110a0210080910090303051801050103 79
    0x248010b03030b20180d00350066a44944005401c144481080850b000c00e500292103500b56a0356801069003016010448800580400c64031200c005241510100079100f460141500b0040c0101c0032440c1014100101c045140d4072071910313a031540e11080d28541d00c1d000b501e4256125800c007100d48044504c18072411900740c2020b4403000085003002035803095040050802c0f110800304640005004500b403008840301ea10307c4d0301075036481c240b0400080c41d18030090201340c9030b904900c0c51000094800a04003084952203240c41320003c81410040e40c2c2e50213501d02254104d4101030b05068031005e83d60040402007011128058000001100042161000011502105850f01d0400400d180158815286030700c01440540361250441d00c8c10040650406011a81000c0507101c0c0700030b682040140c0340e1a00c03681c0007001900020b800180031012420300b01c8050001e4000442d0040100340500005440480014403108250345401801001304440c8010003401031001c05202c01010f005083c120303500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 389664595 1250 389663345 389663347
    0x1031a070306030f12051209070501090530100608010f06140306181e010603020f180106050f07020409110a0503010c140a110f0609010c03020306010519210501080c03060606 76
    0xb075641d90164044801e0085410300205002d01c03141d22820007d1a80300e81d0004000e455914179000015141440b690402c901c00c08085400b0106500907112042d00c91540090101494600c8880c0300d040101c0c2111012000c3e003046404945a80150841008208480000c03c0504d9440181081025105802a901d41c00c01c3c0007003115850f624444112081e054026500030710003020700d2900010b903807036826120340d444000030819464641c083c000540426181c2081881e0380c0650749052620502440040c4036000c1038500c0445860301c1642d0030305601410030001101d003410303d05034440c21200414400e80c40200701040c241418000d0a4a207883c0e03072203a03101c0074000b4103524810307008003030007a04200d06528170141020b000c02c145042c600e00c00c8054107040c1042c0c0095402e4a1100da1500e0515004005214540c0d81c09011906d000d003207c10305881c0100e0081c0c048400e49481480d0a520920712120b4824940391342d844a0b0486481c40e08607100340c5564010705d600c540f07080307512560220b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 389665845 1250 389664595 389664623
    0x60507020c0d050a0b06042301050901150c17040e0906091006080d081812120f0f0402060a030f020c1b0a031a0406090807030f030c080c2b0501031a07030603 69
    0x1880e4200ba402400017000030030b6490411a01414608d00400321000300c1a140c00104150b003400e1480902500b2911484a800146000080c1981c040d005008110601c405101c450031000d070010f039400b82445414490003810604000f5656100507281c2030018002e80554100e034810600c54001107a0f41d00e40507010010903c0c000f59180392005148401d0000081040391184000b44681460301c1c10418080b600e0705c105904800d0b00e00030061030141c000841e4000c0c05514031804075031503805641214660342d92540d4440c21405090500c404856031800420302110115000c03d80c01c00049454a5041c00e40c0703004010005006120710000d485100188140780c440c403969906540e0040c000d00c808242107000f90340b405460340c0700c1401500090034406000d0001541401000c0010f00b003442c2071007040c28036a145d04003620400da8071561850610b80340c044901105a041c9800041103001040250380d2070400c501000c2082086541c0d03500000300144c0ea0900038803503041940d4110640c190964 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 389667095 1250 389665845 389665853
    0x12020607020706030e070504020708030106090905040507050d03170405060718030b0105040203270601090b09040c0905130c0b030f100e0103111c0f150b010212091c060507020c0d050a 80
    0x30480f1782c65420036010f460404541c82c0c076140020405030348103413005550380d0b07d80100100002c0e510b41106034554200000d01c03001c5000000c5000036180c0c2114801e664001d2131a0540789001d07542e14103071888104004100c2842804110b4600c1980135848014139190710045102c0f800056000041009461200521039414242c0c040d662020b4004800e2081c26032a0b4140714800005d008184499803112006208022060050107450b0b4016200f284903400c0950f00d610b540251401382038086551180011405405640600a6a07030421014000f072a22451107440a500840b007040300c0728080804034180d09103842c0c0c0c200403582003400c03a0301e550b42166036201049480240c05603102e14044050909d43c1c403914640354145100791700440c02c0d09100e1512003024059a10400072251911120000603600400c0040c4002e0380100e0459031602004005000b1000b0f000751240008541c0e1031160411201ea40024065004d54007200c81c424203140802201120303010000f0016040141004002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 389668345 1250 389667095 389667101
    0x40212130503040b270109050105070222060803031605030f0103170706050106020102070510150302121516080603011109120c03190c0b030c0304080705031606091202060702070603 79
    0x80307101d8070035240340c039a480c034500240f90400e8a26524002107050101140d80340e0031901d1034078500a00f02200324510b0000040c01c54020010068007464061310320034140b4411601c548a0b81755142810000ca6840b44805075683e0412101084500e0314030602c0c000481c01442900c0c07007141001507200300390b800d603510100d611070030750160056010b052201d070000441d24000c06020b0101030b0b00050b20740744142000d9142c41c5e1899546001e1500d003603035110451140c6501542aa901a130352000d40e04900c04842e49813030b541c1c201508842000c06d00b8410000480c12081324903510580d80c01c0d20716141c01c02003500701c5e20321079403514000c0820841b4801d2030802c940c05c9425244a8015504841c1d140300109003003c007a40005024040a0540d031010031154043d07100180201d004000d085140050910b1000e12020b003000e4100c82002c91002c040000030411a00030060201820200c60720300d1801801422408000b140c0307500c04560b0812103a4800541e4600c80c0d19103600820800c0e01d0000c003035000f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 389669595 1250 389668345 389668381
    0xb0c0618071206110316020d030e06010b130305060403030b01090e01050603040b07020a06060b1e0c03090607140a0305041a2a0a0b04054c06031e030905040212 70
    0x1455210b010322041c01c140300300910b2003500f02030186d1401e1021020000d0030304400043c103a081c0347c03a100507910b00c0200064001c0c1560000d0141c0c9030703942c401d180c0c00030380356009078002000c07803040d10100402c041c1d00d6040400081b00a0300d07184a150340703d80007039072000002d028090704041d080c0001707130110700000c00d0280c00c526140151241c0c3c02c0c00340ca840050380e42079002104039220000d071a205010001d42e400d4140020066254241040a50b1140d00c80c400e141e800b5115000100b8100e0600810741d980c03600000242040728800b00c0f051070040c009411902c2a21000b0205084500e0321103040c204a440d03102c01c0d01c00a140c1c070444041441c0640044030111640d0780305200380f81e0b0000c1c040034070490203a40070700014848011440d003a0b00703881e10116803e01803482230280c08401078281a040082201c0c01c00b4560300c540054148220044c9003c0d440179007a015880400034159008103850344031140255600c00030251240103110a9100c0c0041d000c0c1e0b5546a0303c0003c1d0192100b031200c2070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 389670845 1250 389669595 389669603
    0x190f02060c13030503070c24090e0c190f0201060b03010501020a0b09010f0c0302090a0501110601030b07180303110615011b060b040905100e0d120518070b0c06180712 73
    0x42e216180d03201c030391940d00302c002d00b2500c43c0c2c0406d40a11441440b0104040c14404205952001c004095030047c0a512507105140340b480d01040441c0304003000d402900c403d106244444005030900300c100400c88190341d40e092026528220f0041040314884048038180c91040c0c00a08000ca0103945211170240c000b41800d01c103540c3c4a059281141c03190062000312441030380c025848801510810a080e1707101c3d4829814800c5030086170480f082c0125640d03045079000380140340240d491007805d4402c58800800044e44008458011040642169000403000c00c500c00f2288240d5400c040d040b001c03d8100e0b0820b010440c0748800d29a4080c9038014804134504c50300c00800d0101c050381c045400d4542c0440c080f509a08001d4020341444070522666071100107820040031500b880d802c000d448030390381c0b0184228103070b15500080d1800b42690400c4052410803411a91411340c0d42d40c01000c0c0340c100100c981d00341c0c0100c0c40403134030b564003015030040c00004441c042c2000328030381a20030303030400c0c0c05160403a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 389672095 1250 389670845 389670877
    0xf0809072409031707030e04060602060105010f0e0405041a070305060f0609030109021c021c0f1202011410080c06072a0b120103020a0e091e0a080c03190f02060c 71
    0x300001314080303114041e9510b00c1c600d0035162001441e0241c05603901c4c09289000d680351440811200342d0001d9828112182030030448104274070750f0802c4278540a074145d500d0300242850288400c00c0030b4080b41c0400047c00c041e8152460700c40311411401e0790801d48442c0d60020010020584134a40b240003082e02c03690003000012050f00c654003044540c0c001424403006006098070351402d504001c162101e03403001c98603207107901e070166903140e456111440b0406031a521003e13510a500034003d52141505089100d4000c200d80740015940c1c0702207005000e00d0f051400781416a00c007e007000e0b41965a003d0f80498071761403900350001c21901102031341c3c1582481000040c400104001800d00500d103107c6000703621940c942c118010301a0188035680300340a02c405406c100030003c0d0010404105080c0544440103190000841d0b0b146090b03d10711003c0c0089da000201c030140804004000d01143c0256400800e905030030600549145184202110168120000060210f05550b006003070f1a10100181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 389673345 1250 389672095 389672099
    0x150f110c150d0e010e010b0603100b0708040b12070f230f040b0f04050901050d030c06050a1b0503041b05130509070f0914010e1005091302040203070f0809072409 71
    0x221080c0d9002c1000790f081650b41c2c4042e90b0344034a0038000e98540c1202507844900e58140500100141145445a400580c0d80403c3c4001009156404c690042a141c9852511003821f80741d03030f05025006450a001049200c001d061482c0d00403005403d0351a58812540c0011244694911155214412880000b403081101058102c43c00b0050f0160703140c109102c41c0c60700d003400c4c240440316006130402c61042c400c12303080b440000c0d0701196203040d01d80c3c00100842c00b5201c20352940050b050b0005040110440c1c20803487c14130307034000301840c400c0b40a540c8154405401e68818520b12000d4010315810021409000b605c04c0e003150040c50700203e08408560000b0b6460f40b40d52402c3c0c01907007005030071549800150352840042a003441c050905100d14000c14108001c41da020000346d84652030044155500140c100d644000c1a050305a40181042d5a28901b182d0018184460100501c2c0070605100115141d42800a04c440584405000321200b1700c07003100804924007076024030b0408002c00c1c4a40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 389674595 1250 389673345 389673367
    0x90405090c030705090a18050f0d080105100e15040611010f020f250f060614040b010207090903020304090906050402030f0c030c0103110d090b070210091a0402060f04150f110c15 78
    0x40c800559001e040070300b4000388240381d41820f0040018ac0f203400c0092400050110b5942c03d0184c407100146424011518003240c0b0218545800522203032402102c04200082c246801004601031000003030000c00a40000c1c1404100b00e008410b032103032209006000c00c8c003840c1b0007403402c4414005008141515030406a5605c900144010003c690700c1d92900783c100182d0403409a90841d0b804100d03005d11060100c600000d60303c2d1103620440000310f4a03886103030245402401110090b0800c0081849101064244074020300002d0709c04902030b01c0350180381144c812001c1042e000f001f1004025003081c483c101d004601814000e205d4001410040081c100402c0891040c03a80c80d0340310b5485a1440d00d0300c00d00c040d00b841b100d801d03083d01003800c0034864400644403131030080d0580b4181146801c5a212070011500b01d01a945207101003280c0003c0c00b15002a02c44181640d6912541d28260080348031601203c00c81d9810426400c03a62003809003d03610f2402a05281c0f003280b101d0041030401c1c1c0306420b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 389675845 1250 389674595 389674631
    0xf0b03011e0902030901020d0e0118020915040e0c010e03281e2d0506181906050610030b1c15020a0c0b07030c0504140307030611090405090c030705090a 67
    0xb01340b4a207031f50001d22502c01c1d036074038040c1c00c80110801c0b000300544220040802c10756109040000e2042075440002050072075911210050850094402c10190040418441e03079403240c2d60481c0c3c003054802d46201c04515000680001a481d1b455000000b5691a00034030400c0a001e4421039003c840790107040076004091300010780c0d8070b0003480c01b43c046803624021a81c071601600749400080202400c1240460030025525411002c40d91100c1c0e40b100b40d62548a08046210350204043d00c2802a100c00f8030117940c01c0107010b004100c404900d0422040c0c0250304540e12080125080b100080c15880c084a01190b01c0c02c80a0042c0c00390307112450405074000403a8000603421000c10082107081e0709000000101c150300400d503080401c03824070307020000f6015009034421006600040c0030361440c1c946090000340002c5a000e002807001e65400d000c180240d40000301e009008520307200001d4680100050200b81644015000e0041541081d00340003503d180104010050340d142c5007285141c0c00030030b0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 389677095 1250 389675845 389675851
    0x31202010b0607260c0c09090705300307150b031204180b0d02031c05070503071a07020c061e0903060f0405060f04051b0d0c0803030703060f0b03011e090203 69
    0x79115205280e05100104c03001106480c1c030600c40c1c060040d00740300c6000203102030b804403040b00d80310415075419120614059064205540045641301007008400c05d0350000e52020160f00c45aa4844500c0400782d035480c0a5184080c4c903003144a008100c10f02c2080d40b10250742c1c00007400390b0b101a113038481e80200652150740704400012009002103000c5440344a015203a410488980d0200c80700ba800003070351003d82621941c2403001c80305000c81114011021240110380c0502501c0c1c454643d130070310300c004c0074a5461001c01d400300c40b00012071032440820060802c0000801880c101030002c801800c80e403299422035107903404108034204403564100811752040c0402c9070000c407249050314005041c00406056a24040b036050140000550085409407140b440007608910340d1001c0c00000b510303100300081c09480c280710315001092a80c0c011004500c251056103080c04102c2d6110f0110386000380a20a41519000a100500c070460307200f071202c03a15030054040c48501341d480318a89400c03a4826 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 389678345 1250 389677095 389677103
    0x20f1e03011a01032315030f0f0109020f0f03060118060b16020f09040807020402070305120a0e060106020703150509120c070f051e0103050712060314011410031202010b0607 76
    0x403084085503038140560382c00009481501c09070481569121000c03620040c0c0282c0101c01b10381130106076520100040d0508550341003c44402c46040c81030140241300890f010390159440441001540c1050071350354515038405001011543e1074410320700b0825041002e0000c016460315000101d40800300064202d249148803142101c1c1990300c10044008003807403206001d80e6045003000085410b0406541b401d54060340c02580d25032041c40c1c11261403143d440704950420b03106044c4075403540b16a000c41c0812100314210b8184d40d03250326050381e58500720f110040200c24864041c001c1c1030340581001d41c1100d408030454540c040c1c140780c203010541003000c3c0c0004940c0240b004001803000c8034000c800524054610003ca02c030704840301320b00108090003940c141501c030400b1070a4148100030040703020041c1038003000655103900d4403a01e0403405030501816903003004848041c107900011828017504407a1003280100d0b2440c0c1e0f82d600003d02c00c8444a065550303d00040104e03407100d1740141400c03485 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 389679595 1250 389678345 389678381
    0x4050a030f021c02100c020a03140309100207050105040606060e0f0d0f020d0818150f1605030307020307110604050916090305061501230306040209040f111306030504020f1e0301 78
    0x445d01d8801210fa114101c00c0465100b402404042600840e44d109d240c0b0380b00502d150307030342d40d214040c1e450130404111700b1101502c009409003d0100650129018501c00d4006000d584e9a402c03044841901941c051980811044420344e00361130310700c0c4900d914612a0044c081e1800903a00051020000ca50058500060014014218200c0300306043c6040d07204542500c440c400c1c00c04860b40c3c60150182c000596800081c039000344280e001c00152149500008036a680e20701721000030b4480d000200e0489801034203031502c40c0e540c50580260380640350040c04509181d40e0340006d5281042d0540c00709818041110408000304100b444901d00c590130040215007208400d0000610350203804206a400d051461003803580100f41c001220340140d02102e000d40c40d8402a0006401080d0340819428018034001860700001faa00001e0725401445092a00e41c00d0381d01e81094007a502c0864009603c0400c5100e9540c1c2487e0401034010fa0039082d910ac513103485980300102c0c0c00c44440c0520344506000f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 389680845 1250 389679595 389679613
    0x6090f03061816032102100c09091d0c100c12030b211e03040b160318080c011202040e040c150f140d09020d06020d1404050a030f021c02 60
    0x1000209403a8501d0350f03821411500d035484290749000401c015806200c151801070407403034801c0100307010046600344100200d001c000030140c1102e52500c940c00d0030707a042c051140e120200d0781d0004450301c0791820103007448446000402840076955198801407003080200003000c01c010030104401c0c40002e840001d00c50032550200606203150743c4000030b07080b440c0e0340000c1c121340d00464110010b103861550308600106500c8264218095a000b5200b0f80901203042e850812259030760400c001e00903101d20b0b05400e5840250010b200280c0030304d0f90707a940560750600c02540305400034040602ca02c140107003485d0300c404400081c0705c415101030380c49a903d8001031000c10400e80ca03003019541541400395070321001800c09000c3c00034081c4400700c0140302003410a0461603a8000d083d03c1640103040f25203a0425151000003034204d400b22141c02441d0404030101549035000140c050358110000b005160368540d1b04a60b0040688803513800c43c000c5011480410480b0800300c0700b101ca094001e40101d071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 389682095 1250 389680845 389680891
    0xd0204180902060a0f1407050105060901080c0303030705090114030702030c011a01140904091a070207140604171c0c1506050a0614190e010e010206060108010506090f0306 75
    0x2040304840056100d1900d89120300580d500f60031074004080c00e04014605805800e0240c0b0000a0090380611080700095a42c04200065002d0341c402c08040307510501c541d8072484020340d90507401c91050b415600402c0818419070040024151a000502d03251881c030401d1600e41c0389a03001554241c01690012039840895002030082c07140b0b54144030901d5212054610000b000d510710814242d902c140005002955601c0302d410aa5240fa0071401a141c01d9811b105000f440030411240c0030014010542c0100d0000701280074400740b5580109428101030a01d801444040352a03000245640305540c0d19010310045400101d0f941c5001d0b031134035081d4002a040110300b0310540034140c00c01a1074824103203d565a0340ca0540241c490310310f010345c00d1551251345c03010144602c005c2401c07043e1a4044d02c441c0e5a42c41228250b1101d0300303036580b04010000394016139586600f50f41d0940820071206c0144010305144010340484030000f008846041c00c41d902003410600151055021350901101802d002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 389683345 1250 389682095 389682119
    0x91c03020304120c021e010e09070e1f080105121e060a0605060f0f0a050d0e03030103061b0e060c19080408060705070f0f03270314010b010909090f080d0204 69
    0x2440f40340c01d020b0b0000f03500340c1c001100702d004038040d54112498100441081e0348104e03602100500041e003407403a1400d1200c4050501e401180c1c0d09889000d1000340d1501402d81c004500400d401030b621517801e680d00f4141049042c0108401e00b4141e407290750310900b1203003041040300d680381c0b807000060002c0b403c1c49002c178030582e0b0498100074000d04042003200c428800650441c0d40245105100e90344070b0748040e00c203c6070b5215481124020908010580a00303500210080d4101e0b03100c1e003010003226400e010b80b6134817255100d041c040846d0660b200c100746410034400406c813a00e94081a07500d00c0d481d503103803003030440e1170384100341c0f00c10001040a100b4024100003041d0440e0b25420014140107407596590300051151000918507c0021240b00425001d02401400045d0038002c86004144010740c0b03020040c12407100340c80425444078a03c0394100c0610036480c01e041c060307441065440c01c5c0020040036100720301c011641d1494081441000c600750038081e10300d414001c44007517580c2e840d1101c15000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 389684595 1250 389683345 389683373
    0x6060504030b010b0d021b030d050a051e070915031d0a1e05030712020c0f09011a0f0d05090a15110d0b031c020f060f010f030803091c03020304 63
    0x14410204001e0010409154269045811130910590f48017442c00b02280030380940040720f0310000b0101c1c4028403014021000d000d40c0701695000700500d9a908501109a4809880740c22a0703c0004110500100c0b298102d5584407105003880d860469540010480340100c040000000139955051400c18540c0714040d000e010320004024407040c45903803074a442c41a00c00300702d50100b400a80344281000f200740140c881c0c240e0440b0b41d000141c0d08410001c1d464140c2c04c10304078811604400fa0017070394900701d00b41605881c008004007518441044604030340c0d9001c4402845520801e01500b40c0840c854001c0901c00c43c90000036183c40c85181c50704021241d40c01d2030401a0f80d050000b1031105003101c9043e900c010085e48004602415840b0220342003d8080c00404945520032298406654001880d01c088510250444401c0e90300e4144032050b80390203000300001900d1000b402c2002c00c01d02d40107141c102e80104156035a83c0a40c200c0070607181c042011500100307030044200303c03d0098400d00008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 389685845 1250 389684595 389684597
    0x191d06030130080a0f1e0503040605090105070e0d050c150c07090212060d06090b0106110d021f020714060106030606080702010209210106030606031121030403030c02180a06090606 79
    0x603002e554802d01d203401115254400c00102650307000c44903108804011442c1040d403c002130b211001c220003060f07039200b120305036100c41c10800401c8091105226242c810740807039541400320400301e410030600d420302d804181c505122740341e81c11001d80e071121005003d48110321486642c45100e50380581c01d1141d0b03a880701c0d8649106020784140c901c41402c54070740c01304003214001c0e4550304901d0420004c1c60060409069001068000b090326070700140150000148602224003045604034100ea448040003244411583d440b004060300b0800d68015111840c411082020005107203601c0c1c61070316000744e100200190321003904015071034124441f56007216a62000b075150076007260220b41415401c00102e01c0502810f8014a10f0313441c2940400e028590182040c405160b0301c7c2442916062100d07803c510031401c8202159000c1c81c01111618070300ca07000701450900745113450585812a00d960143c0e080500240c0c10b0504c03c02040d1038600c01c18032104001032050070611814100c030842d400c500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 389687095 1250 389685845 389685929
    0xb0a020d020c3a09030f020a03060507020604170703050403060b03010e0a0503030a2012090c03010204060509090703020301030309150302160b04030f0f142a06040314191d060301 78
    0xf40290703011019400b60b941120003500d0081851000c100710702069070001d40b205251200b4040110b40c0811890f00590268004003010401500c131881c0c7c0e4418030710000c022920401080001503960f40051401c01801000000e0543c01d00d03404e182001840b41c0100c415400000400c0380d14110b0344540040e007600c2c080c0d00d4614496032030035a0a1446900d10034068521048005a52000e04200190170000040c00030354885540340030140054201022440c0b241100900140040d40b0034820f880c122505641da02000914080050f1500c9080318402d20405400f00302e44e02705046078800940e1000e01c40d84045003240381a06008000460800315581000500048607058681c0841d0714500742c9400079003540d407240d24a81d10003040b64040b40c1500d015694454490b80c25201042540c0300b64061384038090b95a4424030381c2d903107034030a486a0001d50b00004c00007a0309035105181321f1401032182003060140c0c0504100040b540c0c0c0003680000c507400049240e4446000b90030001c102d40c01c184d80008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 389688345 1250 389687095 389687203
    0x30d05040f081209041d07081e3702040908040801150b03061e10090f0e070203070825200102030304050303011a070b0108010609180b0a020d020c 64
    0x75141407050712806417203180c07201d860903441c1d14180c00500c9555004411928096603c6c24156154074400c03410b2002c440607034040e2040110003003580c03502c550081c1c1c05034040034007025111550440700001411040001c0c0c070f140d070042c0c84511925098a00903c0690b880302c0c81c000402d820344800c038500d0032502034600b40400000c502c8000781ca400850032620810400e00b00840494018101c0b00d0b0160b02000e0f4500c1c04001c940c100d110768058601c049007087d0710949491745031180f407000341e0f40103006900802242000c5890a006400d4049120a2108446c0c0c82d00308000201180300805403500340b02090400b1221000d0000d02100000030b00280d0b065213081c2d201d00380c03680414031440d880c00e0f11f9a105200012841c0341200c458907481340414840c1d503144d810844c002c1c040d600030304003070a140c82c10321004100740025864060364040e03224895962000311400194000002d00b100b0b1903001d03c120440ca410500512a803a03074103d00303e150500c1d030240881c8912100e4001c031098903d5800750 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 389689595 1250 389688345 389688373
    0xa140306060411070204090609060b10050306010c060b041d01180b180309030a050f0c0607050d120b03031803010b090105100f0525020a0902211302030d05040f08 71
    0x586900c00e01c12039002800140c01e060300e80013449240c40080d401403a0180c00d07010010164020300b0280c0c00f810b000c1220400b82428010141480d42030740000c14428400550389610070704d140800b03c0d04c20000070a088000e9070204050750280002d2144100080701e140192240900c940364049140b041e50340340c0c00340310343c469655841e0301030800b9442c503095102e040400032080040f2070b0340c00405030499001c18003070f0800984030082c01e00b0314045409000202c20051812006640406400401400f04019032040c241c2d500c4d41d003500780080d0f4075140c4071a82c0c500d83c0c0c280007400000d410551350058250800c010142191000c04040788580700c0340006004035155000a144110305504140c110586c1d040360a6815024526400402d4140b8078051500e82158150114856209440480e9441d455041c80c90903401210070617121180d1143d0310300013001140d41d401d6008840704820100522054011038140ba08480c05140440d000060421003548036058007001071542201600c21031140e010703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 389690845 1250 389689595 389689603
    0xf1805061f05012313080c04060e06040506122a040e0a0f051504080405010f020105071b0c0b0d0509071202013603060c023703180b07020a1403 63
    0x10b000d04000001c0c00305840b021001c0315158514a05100c03850720754580c80c10320b010042d0346008140e0b03d030003603400f11911401c06014410694980e00284e91140c1c1d1118203005c001c103801010307503510500c814000c500716081403041321040800035403408a00728104181400d0509110303034841c09a8075007402621401404250400066880b48001c1c0001c0454100031746005445507020243c076002070284800c000d5144010000c4610a8031401702400e42d0746810707401c880c4111080000304c0d002c1500700b00c181c0a85074401281a2040c000d940c280c5450700240d0416410002070700600541c0ca0091100c000c5d0100040d40c000d10150001007860307040e5500080a4400302024044808548100b800500000c2c1c810400d5041510601716001c0383c0d28109200946540440300c0058000c80d840c910907140a400e4011170145003000031030100b0315180d00c06501c401000001c0e410411010f00740540f035801c1d004000010000031440c01c1d1a90b010340100680c3e0350a5034444014a40070401c0c0301a50b8401003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 389692095 1250 389690845 389690849
    0x8012304081209070b030a0204150305040f080c030f030406060f0b030103051b12011505150f180f030f0a0b01120b06120709060602060406140702100e010f1805061f 72
    0x500b4030340301c94882e1050b0358034050071508210701d02c2001104010080005e54007420444091040c044a40c60001e6400c0c3d00325482070f903000d0548114454aa00400c0c5840002c003120301103102200d20b00780450180012580083e50304542c47c5031a01020003015101c00c0c40f65011b00007d86140c1e00e1940366a58155aa01117003640d01c2c03c000d4400d6039900e2a950302c3c1d241d60201c64088000b44100301c0840c00700c004e8805503024540c8165200c2003500000c0c4032000035509565075800b02e1301d03e003540c00c22080ca940300c074031102a9803140e03c2e4926000140c03000d0010b07108032506103000f4104003d00d890000d19800c07058000c102c0d41c40a50240b900803880ca2646e054000c80d041e03500f130110300c03c881126400e1140c40c0d008621807030305200d800540c141e0300086403440b42d80510010040c2c64807803078041100b40402e8943c0401a03008455003076500340660301125444200c00000a140c2c071101c801d48080c0c40c40c0d0500004040f0155280c9401d2090503c001588880301d0f05e40040340c04107990002aa1404034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 389693345 1250 389692095 389692117
    0x3110307030e0109020a12030305070305011a0304020402070206070b0f01081203060d0c05091017010c021c0c15020d0e0105011a070512040b07030207060512071214010801230408 78
    0x20b00c01c40c40802d200b944603111168010301a215181d0722100f5041035a12210b100300c0000345401c0000302c45078481d202d2f490590b220004807002030000141c1583c1181c00c064416a4420f600f003062038016030346c0d403000784821032180c1281095858020080f48098005a100c10328a030019102c039600c850114003165132082c3e04503200c2c60070319210b05000030b000c4100d400490b0056404000e00c14091002c0440d40200d903840035501d1444140c0103a86801c2e2122410301da0701680c070085c441190501d1021000c8500c1200d803520015640458942000e05d6144042c0e001c0c1681d0700140c4001004502d000718140706600d400240099450070f0007409403251075803003450945c98085100400c011041c080001061841d219040d02c450312000b8000003940040000c601501c01e44000250131402101680c0e5201d24080e4401c459644200055818907410003507003000e5956000b00348a20141501a54041d00a28000180c1d9039652041005512000e4600111806900c4100000200c089044441200c05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 389694595 1250 389693345 389693351
    0xc2b0305060904060f02091005091c05070603050735150a060503070507020909250602030d0b01120218040f1103130c0e01060c12030204060206060f01050409090b060f010311030703 79
    0x2120a031107009000e491f00680e442442040242d0710313154440b01070145901d0855000550101c0452500b844010f401d0303008280b80c020340c8040008602aa01080e40b200050030300d82c11019000861000d18801e0200c12800b00528500c4004200310f41442c2c0342d404102c0003851300c40e14000c00c1c000744a804c0c270342c0700341c01c2003020000c0020800f5220744250b420340f6a024201403c90b0902680d29900c5413084000140384450803051010312103458010130742256840e4000d507150000c03681aa001a10040714070b94144410541c0300a40744007a40f00a1032210314240c55481c01c40301000c1084166407642d16010b00450400b00d44541ba011101d044940101040e003c03800100e005162040c0f2461640d8003004c400b10405000066140c0c02c49813849003188a1034901024292402064040340128040e00f030059118000084890800a079640800d050505010342455562204542600c0990380b0407207051a0306401d000460500e41076020040d4800d007028001c02110241540b01404020b021204040e2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 389695845 1250 389694595 389694611
    0x30a090b0a020a15020412060603140111180a030c03060b031c050901080a0e0d0f021c17130501050106050c010608031222080f07110108010f05040c02030c2b030506090406 75
    0x50b03617134115001001902c100c50918111030600c9030007081644000d440b6406400102e404403401842000d0014860b41c00700f5081003002004003c0e540081d805180d0047d00400000c404142011a1207005510814000c00c0b0001d8031814182028902207c0c0341c00c10010084000c0e1940c0c00c40c00b60b1791414001e00c3c2000083d9680c0c202400902a03800e14242c0501913104001180c0b68417601d085172642081e000c4030903410b940c052500d1001000041c100c0041c031a80345c8100318100a5043c0ca4029010705042d48800c409519564211842a8806000324600098450b207a000a0049000800710350000e503003010381c0c3c42c09524000c1001040c5000d00814000c40d03440a1407044000d40d401600b20150503140d000c00c910702c174061352050328103039965004007031940718642c0310b843c000381a0b411000d80400043d1428040c0006031006902c0001540801c5c0b04200300080c0400505000f030313803251100d420301c3c0026502d20f00e0810f0a13403d204109410700042094a8a80b40d48040d00503600200009a0076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 389697095 1250 389695845 389695883
    0x20d08160c060c0503061806090a09050a060507090609050915012006010305011a0306060f0103020a030902151e1305010e1305150901050d0b040f02041409030a090b0a020a 75
    0x1041c0001d02d101e16003001140381c16404400365100c1c005c10f071101ca4a0034010110410309140441d401c903405140c490024038456255004903444510900c111071801e46156203000c1900c208849130700c0040d210150400100e5880203a420050505484d803d040d4204081c0181d07040d010f0740007084c1800001c0989200e0f41074085403100040c2c205d0f00c1900c60b556103920307009000c1d044016080c0807110500d00421f219244c04500d8a00503400101001e20440c4020010b6001c0d41082401c6000d0540d030300440c0d0007503125040007420640d490b888003580c4000320781191156000154030020b1505040c8209034560000fa515802900c009003020a440014100011500030302051510034440c2444284082071a004204410f040c0c0b00312014081681ca900501006050308032016016480400100340403c1c030880c840103441e400604003017600701c0c04e420b801e07240c0082030f141c0c41c1450307000103040c40d419a440900390014010f075180162900207041c2e0029580d0256000140c04c100c03410b60908208 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 389698345 1250 389697095 389697107
    0x140706050c250e070905030d050c0d180512070509130b040822240206100501030b0f03030406170f04020105121f09060501081e180723040c020d0816 65
    0x201008025100a898132000080510714284a101c0c028420b10403480c2e4002d000300c0c141c0d039014400800600342c3c0c0c612813000725004000c06255003910b1080d1000442c8035120101080780f0000c1d00e80041001d20319040c18007a0745c410041c91a40c400c4040f491b42d01c00104916221074115400ca404c0d107899000d0703007140d41c080134141c5048107556080702a00080300c00c0641d0020590504a406032201d001078528144e840b900700f1a020000e44444600030700207503029501c80c84441d8400350030803038189100c80c003117841c4da03000d600941c000c0f070440e6444408400c5401220755008514804050f06414154006001d500844403420790900443c40091114a0500c40b18070803034066800d5070a040f80d9072212700740103104a0103201d00041140c40040e02e002441d019070105000081c2c511a89650341c11408004421000014601401a000c00040412649107410f0715901071790408682d010b40e040402080710801c04015042d174000d102107030103890b0881045948803000d04600c907aa81d41c1f41c60b04440c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 389699595 1250 389698345 389698349
    0xa03120b13140604111909030c0e012606190e1507030f021e0901120504030e0a050f0d0201080601022509050f1030140706050c25 57
    0x84500c00101c140250242d401807041c2d2070070100c054102c2c1d2a03103003c2c001550704c00108030107210ba081081698503440e0545000054203c1d1a05040080c1c5035a92510500c80c50740c4452206c0c011a0018046029041c05040d100464507542c1c510030003000c0142600c8400c001e2040d2410f0303111000440c04e0505c140c10200d44200c81c4419203200d1455195000c0c8140026102d140010b490114003015058943c070840e0355041151000d424030031402c0c54444510340c010034889041150802c903000c7e04042501509004074032989600341e447c50040140040300003103900407442000405140d1100e0b0b103512844d02226502860241c1c42942c0300c8006034580001c02d8040c00c0d08802100d0b0b070810300d0401014a2054500c6004140300ea504d80c4c000b09010200b060b10800a01010204104200084000a40c071440a81e05031a462310300c0a0400c109032000140050b10280340d010340c1c55008000038002ca4014180034205035003802103110185546003c2492186900c2040300c0b07801c100a04041403640c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 389700845 1250 389699595 389699599
    0x80c0306070f0813240903020607020d090e040f0c0609031101030519050a020f0406020a02040e150c07030216081b01030c05070206070c0509190b150a0807120f1a0d02030a03120b 78
    0x385c038100da21009001445102410341c0140070f11804940303007500c00304031103144110560320011540d0814198020114025000f16200030420300b08500040c00709482c90000e062035287c1c2c84850b4a0750500a4551100190003410149030000308140286640c121501c1e0101100b000201a603446a40384005d104940d4503249210001ca40051140c0c1d00003282031035244282c07414003c401d00d40986541d80c40041c2d4221812980b003500240b02c0071042400382101c00c0c000e01c1120011074a0150566030710b002070300f048035182c0003000032400c904104d010a0701540400e217820401074240f004000c040703000e05000244035010000303004040c8a00449017501405c4020128061400c109007662400710441003c4902641030400030140c525204d940b11000020b0304045a00e0046005000c4a20400c010071100034400950b2928400560612841044412a51000400000c0446501d5085010404451081d400d10260800613100031410000143e0f160510140c407903046050140544a01c0020076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 389702095 1250 389700845 389700893
    0x110715110c191a040303020601050d0c120c032105030a0f0204090f0b130905030715090507080106080c0f0f04020a05120a0504110409030903110607020406080c0306070f0813 76
    0x42c2140c04003007080044894072004943e8000032401d211580c1c0c0103c0c40040c0140c0c02c036400402407414114008601c5c54440d000600200e51100c01906202c000000159102d00c144032080c8200f0008000034406000305901e682300c081042800245103100081c0910341064860003600c103030202c6034058401403c4444420b0005045840181004007006031031144034100c22003840d44150f0721445800003113038000d00618900710755903c1d2900c0c4030b55030078511903c0c00c0c0d5901080001c00e1090000d40c018021601c0049169481e12041500d41541c281195100d5410811529102d0f514141d4145481d0004d81c0c1c056150030104600788c41c240942150312068030449404c0281c40011a800f9511035441041e04460241c00c06d01400301315100000700401040b0b80450900109120090612101720018080da00e4900160f0106083c3c0e04154003035407440e440780d40c648507140f070103001c3c007684209070746420105080741e4040100700b032030050b0030a141e107600c40a0240511009520b020350a84011682e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 389703345 1250 389702095 389702119
    0x201b01021f02031e09071a0c01020a021605040b01201203070c0507060518042013090c02030705100f020417060615040f03031d030a0c0303110715110c 66
    0x40c8010f540304480e2000c4040712808a039452020074020503000d42e03a41070040c4441401c04224003440d22190000108501b07003808100844402400100b60071102903014040d802c01c13182590200c000d0035040548904e0521219031030350390307121140b02251000c040200c00140071140005040404414144441e50720020810103044d420290b0030140505c180101d800f2140e4a85084606004025407280c1d9a5142d003217a07802850690041c123820906c0d14828224503a034038684038910740c41040c40c2c04212003140700400c00304625226110300311078140045c42c540003655903240d4a070007100c071010546036524808e0f110a4072555050710081c000010802c501da40e01e1810950303a500b0704440d060700c07401d90085854421040041581e00311607441003000d45190541c2d0f420344440b5400c00a1000c400b58100400710300c0e03982080310b00c1003a40078595240e030590550030014140c5044541c482045d0340b06060401509013010380c078510000741450f000403a140e4504009050403400610603038854921425 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 389704595 1250 389703345 389703403
    0x527061801030506071101050c030606071a0a1d030f09090a060b0325030b060d090303090f0807021314130206070215090a083013080d201b0102 63
    0x4460b005050903243c603c2d0302103000006c10300b030303440071120080781030700500c040b4405041c60b40c00307000164030509422079030001c4c2071a009282c0304100e0320480d000d44c542d0340780080c1003a01c112080c14200620040c502c0c0501640064030648034000000e80951170341000180c600480c0e600c40b01c0034140d4100005d659007000a5190010f00b185400014150302d1a840c0c8115140a4420148000d001a118600300306000d5221401841003540079002c2c56120030150000410030308c0c1003284507209048164450185005000c983d801d480c240004091a00f04212154000d2952403036101c400155034808104062000c02d0150007803540094100d80d100034100c0d40089608090501301038155144a40156102f115039919a03506c408000c40e4894480c84425043e00c0020002680c0440f110480c904000f8101c8224038441a9011480ca900509004148154010034016a4200c1c1d0301400d80189480c50600d0f40311040044038001000b420986410301e41d0092141440380408401004107426032071301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 389705845 1250 389704595 389704603
    0x1401180606050301050f060105031b040803070b1003150515130b010f020a0206040e13020a08011b090b09041e1401080f060108060721090f0c05270618010305 69
    0x4000c549050500401140d40d00701481114890304002e04102403940300e01e001500c0302d81c0081c1101c3c00f0708441d988100704d510000c0006000410b4550010b540d501039a04212911000c00741c01e807032103800355035820000300c0d0342201032451042e421000007500e44c50300d040e9580100c0c0c01c16011a0001200030f120540414254003803402d6160a80f280b045808100b503041740c464540f114000d41c05002408180201070403c0c4510b903000700b00a411500303001c200d40008822136211b5100c8001d1780e4681c022480100c44040b01c2c80c55101240c1420002c00e07040c00e0a140080c011604420700487c0c1e20111341c81c99140c000000e4400500c044410024441505000000c011090080321651f1040d246a1080c640300001d510f8100c8601c0b00241c4210785500301d04443c90b120049a55202a04c403141842883c2054441c19024a00c2005040b2014606160044014859130f100d5031045890a0542c0f500c020104031039981850402e0301e860040d40d402000450350500d8103051031b880c11040002004201e8001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 389707095 1250 389705845 389705891
    0x80d1b02090f090d0516031b02091612051b0a03061a0702041b0c0b07092408130209011404020403081b0f01020306010c0f02060d0c03020301050f030604050a030c1401 73
    0xa0f01c4c1c0c00d8051540c140c401c0d00c0b42c0540542021008548003001c0391142d10000d2000f100b41c0490340300780c2c9181e0005100040706941407444052060381c8100c8554111005418844081e0030620031407401103141107180c0310704d50012075944800241c2a500d00c2c4241d0004002d840c41c1c01c4840c0703885d40e00711701d40d1026400c1044c089019070701e030200740401c0320500c11038480038210640c3c40d005502c016542d48040004007420700c005010300c0c4400805c440321152981040c428510308001449585500c0c0142503050160540607041c080e50422000f5850300c002050568600c041101e1404040070081030003803055510141021201042c0781035402c0b600e441600f15485860f045603035560002010508030301c030030b462a83c0420040d03550b40c5e0001d4890101c140c007640c00141928100300050405030241e510603c0d090000a03400001405036152002c0301e011402010383c010003481c505503440c00c3d65407088403806418040e0364608101000141b00e000e8820b4400300000307101040010f01a030903028241c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 389708345 1250 389707095 389707111
    0x170c09030c060702060d090f1502090103051815060f060c0303040c0509010b040e040222050615040308120a0e160501140901020a0f02031608060103060606050301080d1b02090f 77
    0x4040c0920986442c00560701100d8006150318501070f2108103010050009040c01c6a1602548203150081a0030f4a0705404c0130110700009661402c192000500b10b5100801c29150015800c001d05121400021012104130400c4030000043c1c803058001010702559001720755015074000b80d2898030301c50100145000b503224100820125441d1010071803018402d0050683c500010b01c0200503100c1c0e1008519005400501f0b00c181411032140e00d490282da074507001b50a816155000e00815050403001601a100b044641a08260866403020300c3c078800c038405200c1e11229a008500502001d5001c0408607258100b00c036084613403c2070403911134400d4490301d4003242c0312000e9150449070705000c48603c45016400b074916540307584c0c1e40705115648100140c0c0c06102e4030f041008040d901040308030103881494020f00496141d490481c00b0364400380c0180c4204141030004020198000656040126681c1030100d4003158440c50228145400e520281d404100702c0180816a080a0141da01880301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 389709595 1250 389708345 389708353
    0x9010f200f2b03021e070b040b1f060309050708010618050105040c05042c100e0915010303140d150602101a12030d0603050102030f01121e03170c0903 66
    0x881006280102055010031540a00030b007100b54405209a0081070120b005010070512034034507900900705034000e41411140200c2400a000071f110452070000d03803042d940c11007100012811041d425500880740300301801e00d5200d01c4148104102444208045d02c0c088000700310980e51a880b101060403618426803107140340100100c0c1600b8640114039a042c000c8c3c58041c600b038034181940d600003840f46035000c0007000040c9050f201030a2900002c0c0030700610021401210304100300d44208503c05082c0c01c085500000181065000c81103c140c110303609420400c01d029007088000100348140c6c6282e00800303107819203030003080d924094044295641d960880d0030641c070412929007281c0340030800c001d020142c8503078081c2c3c0d49080c61000e007036075100805403820304415040800503960b072030f041203c407170350040b0401c00710485210310f00d40100000c411003c1901c0581d118000111011060b803440413049180000500d401111206040440c1101e400316903d0421707400b5046030010000c00c1d200b805 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 389710845 1250 389709595 389709613
    0x213050301092105040605180d0c151413210515071106100506180409150509070b03010b03040c03050a0b010f090209130b0a08060703020c060609090309010f200f 71
    0x40710300c05039400d451b0140c55152070034030100c0603403d42c910200801544807072100c070303003200182c011340201c001481ca64903100b03441c13021100c0140c6540c00c00d01c1c3d184502c15003400441100801e965648017246ea440c5c91000d100c829085550203242510800540706100b66014200e01d5989a0400340c4240e460340d07104180d1540c1950720b1501c0d00030503030b244000798001182c1400303d407810000515540c9108100e0180100c1c40f48042000d540031541c0540d5051961080d4041070707110340c040c01d03600030400405802c03840e06150b01013425000600550024000210000c0c2c10803040d180250081d42d000402c80c1c1d1103001c203143c403c082c100b003402081c1035100c2c00c13075000a000009000366100314500601b01d0801e40b0420340c040d00148021a4120b0740100c5900d40003403450800c2c410f142c010f1a0340d5038050b03658030310381043d2890010f0281c00e0034003d41e03480b000c03c102510040b060301d91700c140c24a030054614122000407510600b4100c21a28030303107949000911103641c00142c440015000405540c4151 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 389712095 1250 389710845 389710847
    0x114031003030f0f0e01030e0c101d0a030503070f03090302060304150f0501080d11101e0b0d0f0f110301020307121d0d20070f090f05011802130503010921 68
    0x1c01404194008110440c034145c0c0c4640c001d0b00032a804111810860340400007280c001202c0c4a815020701c0c002c18030401d81517070001196100807462100641d003d079a824a555501a928800c88401600d0004441c21141c10948100c0e2054029600101055100e0030702e414448415808a446141040d14004c5024220240c5004d42412544240090702c103030b00d1141c1c4166000920b00040443e60b00a82105003201d111610500350b010303e20040d2806a41011803201007201d07401c42c04148640c10070b40c000c000207086c14003424441580b2207003802180b801032420440e503a0307102c1d00503640742d4004810006040d42c0003c001c0301044010205105a40c002520142c40d202000c1c184842c40d003140e00d034004024001c2004004090001c4802400a0344019019081006a400c18851030600100400c1801c0c03040c015185100300d0008108800d5143c02c0540180c10404500c141e58160046010740074130300c1187d4650014400a030007809100000e1500341e00c01b070171688400f02d10482a846042e03480e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 389713345 1250 389712095 389712107
    0xd0602121f0b22090b18100b070204020c0d020c01091a09040504050703061a040c031e0b27062e050d06030f061506110312060114031003030f 62
    0x19038500300d408010341408820525948005000082002240b020040790211041e02d100280b540f0803000402850450802c001060303111a00074100c0c480e0801e220542c0c400c444104100d500d608c0d400da50700e9080d8170200b000303030240540c502428016044203114480d00070500c0361a003c000d07a5209000358950000e06003807407643e41300702c40b410001e014901040c1056071000743c005004800b202c210595075074464041d6208104020000e090300580c11701d40341818010444242c1060034240920b07007003042507050300030b8006d002010550b15541062150344621412001100307803c1c101143c40e48100132074135024181a241d0b80c0c0503c9860088803082e0011a100c00300c008001d14040c0c134240100f040864458204000928040d5a5200b000001400307401d160035246200e40000320b41c52610030000c28914405a2144c82441000404400d02100100c01c0fa404002100b0f590121602c1d01d40040340c441c81c0101010220000000c20710171100003004020342141e11907590126440c0100504450b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 389714595 1250 389713345 389713381
    0x30102070f06200c0c1504030b130201090f0f0812071214040e090d02060f09071e0510021e0c0627060d060f080c030303010b180d060212 60
    0x3100c5616021a4002034107074100030384515003500c616007910940c88484102e44d10040e1215110f5104090700b002e00e045c0402201110564001014202032445e1a101888000103040c0132040d11001c0202c0304581c0245c04240c090304903440048062038855881200031011801002040d20903414a8004041032a00300c8008a41c0070035a14201c031030000042e101415034141ca00030414092001064240c0c20401c000d100b000340346d005107403440c001c140180c20840d0260083c16010a08010414401400075155081b150110800303080300300d0180e0003005146d115002154003e12450041e80c080ea070000d84ca0101c014504003d111101c0e10802c091354a60798010101d030812014070100c00e0441d0001c400c91036071103810401000c01580e090000703045902020940288690303504086c0803100c0d01070003002c040e104450050018080500000e0341d0b9010510036100c9483c400120401100a01c2c0d4442415000180010312110920714003c4065086800c81c4052090b10302c000403030314140300c0380d0401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 389715845 1250 389714595 389714603
    0xd06060212070c150c060c090e09060417090301020408060709030b0c250305121008011d0a020607020d050d0206040624140409080304080702040b01050c15040f06092003010207 77
    0x803002d1300d040c50300c0c144c9240c2055207400b4052211030b6140414203074010485030007120303600c2c0000d540c00d0842080c40380501400b4800036920440c03c104c0020a1606800c8078410700307a44150b1990010400640603104980154000d80031f02c01c180110b6a40000b240d10641c1c0c4101c031012019581e4030003039100d5000e001403c0303415009001030040358594115020105600a1802038a4102c0a080e000811f01041d10000c52a40e02a0020805c8160030300c03903881350281e128110850800801c001c1c0b6941da040b100042e1050f100068610304654403040b8401c1d000742e01034181c071601e205000c0042d4903010200c4040da1547e040c40140b440c0c2c04500b07540c0243d0488504140d45100e41444408048140070103102074001c0c1d640c00e070702804505880007551017a446030004542d901c4a5105210030346d84c880d90058140002840044040003010414640c1c01e01d02c0001c03031105a9941c10040214540054042c1c104ca14090300303002800b000c24070101c4840d0300800460311404800041c10308078825280c1c060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 389717095 1250 389715845 389715863
    0x108040f030509010522080c0a050f04020c1903030209010e1f0804061806020702040b04050601050708030907240315080a030e030c031203150d1211010906020d0606021207 75
    0x90000303801203001e41000714045c03400504140700b03108800310040000401038008002ca0303508100c074003006c010501070040e081d180880414500008103000c4101118074a2041d90082080c241005c2c04101045800c220444001000b442e10b041c094020742c000c1c440503000940e0351100103900c4c142004190802e001385010003504401000b0104c40854018100701d50003519031506100a1101a4980307040a008500050f80d90009104001c12940004c0e01c40e07010b1030500041011503030300b000580c1c0c00207030130642c04c030f070350381d40740e41c003c0d801d00a107504082c44501158804c541d440c850401260410400351320208008209198080d58034200c910401016600400340030001174030a03680324085480140480d64407801083c006070600101c00c1c0100103403c408002c11002051255030003843c21740585021a1000c101c3e100d9100c1400118100c40c14005030b0400300452031800d6100c8440b95812600442d103d0581c40c080360080d0805100d00340040c4580c02d5603540204151045461065000b4044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 389718345 1250 389717095 389717123
    0x30c0a06050a120507050a030608010516050a05040306050a09060b090108030a120b13020703090605180103090f0b09010b040c08060a03060507021006140405010602010b010807030506120f0c030606010804 89
    0x8403102ea100034441001c004254000400c1d80001d406190f0182d041a21196101c1001c4180101100c5a039401030140d03a041106210203140101c1030b10340440e41c02d18180755200d82900c0300351464895030344020016884c1c901041001100d030790081c0481446283c051246402000030807001c01c20a00445107503800801107844524090300302c000840c21108004981401906d000640d4500c600005551407a000100a03080541c00345042000e0040c43c101917050001d00c0300800340050384d00240b503061647e1884004140100d600c4030b00365143c0d110200034a070b441c00594841c0a412844401c134029400d0421080e1124000c0d9a003503c40c92028201540c0a4596120040a0000a0401d0055004605007088038030614060100681107242c0d0207401200c07038405000880300c05078403a00031a40350800310400344ea441a40c031034014800349400324035504c0c4c200004040750300b09140b0090301d00c40d41d10040da8104d0041600c201e1740c02c0850a981040e502d0200660b02c0c1c00d070444000301819851040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 389719595 1250 389718345 389718347
    0x70c050603060406030c0305010b040c020d170c22080d020c010c0b0703020702191a03060603180f0a0605100608040210050a0c080c0606031c021011130320030c0a06 72
    0x3031030b030007240100041002543c948503041074080329081a503250351654100d41c032904140c00307415540c122078070080c004102001c40081c140c04410654071501e10003600410450700351007098400d040350a0350032001c21500d8500c0f802c01c0c41c000c1d100b9199a4009c02440400860021509402080d07068403008102e0302e150b9034420880400030114000d140d0700707100a82c090307100c01a0741e2107502e10b954a00380e032403410300003440d00b1620200c08943c4c1c542000c0040200c280c451900380da40000a50710350303050403a01ca142150400040d00806c240b503109401d4044140000c641140e4014480c4800941403680c94a40c2101d244e00c0841d0040d411602c0700d900100c0d6a841113000700090345080c40c01040700340361961001807590182d003000495900100034840783d4541401115054010264103140c171020900d00a919140c042d00d0b400300003666040c00484031349110003180c10101a00e0102016103407039103030400e0010303500510020074031183d5094481b14240012009100c883c010310101d00c1c01c0c90180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 389720845 1250 389719595 389719597
    0x306080a110607050d0c050624011d1504230604061103160b040201170610210509011e060501170c0d0e0609010f02040e040219030b01060c1403070c0506 67
    0xd5190400b00801518011600502c154107038012582d4034448030306501c0c1081440c2c20000340c8102d0b42c2200040113420140414550010030000c282800e01131045400ca02e4041c106120090302d8009034141c00d0240b40d40c02120050040d510b08ac0703950142c80080030380c808007a0308d690114503040b29007000103200e028010840d4140640328502100d25213541451806a2002404401c45d4030100c41001c0c03100319a0014220040c04010300ca1840452400c000000c0301e05002a0b2a041031181014020640e071034010015030903080d03200707428441420a802918020100b40402a800c0030014217030320a4a5202e000300d804a550503503894400303603070003107032400c0d07100c0090081900804200030004100455020f29003640500d08050401454008905429a18445240e0350b2091040001707000d107150910b94150040d4050301d400103240011032000d5021819500080c084c146007400004815601003034561140b8400c10106c1400d2420032000d5603030707005032140100a001c01c45070501207424058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 389722095 1250 389720845 389720873
    0x4090507152703170c030a0c020103060b070c0b0c0c15041a0720040605030a151104120f0f0506010e04120903050c13020405040c02010f050105190608060103060e01060f08070306080a 80
    0x40700140f5240e403600c2c1c4d00340703551f110310140404148030038200340a40d82c00d13101d01401001c600303000d140380c09416074980e4003032003950052107051907011499001200041000600d800070181c100003684010f00800091034000e40701b01031500421442801305445070f903040c0c8a1007a48406405150030221924403482c8042030340e1141c1040c0d641500041c6c0d41c1d010000060884d00641c40191419070321070382c900075656000050282400d04010802600c2d217404614680c02b60098005a180c50907840c203540781d16020b200c080e210348624000814181d01c40c2c25241d025911954511030b468010240030303900210726100c040d205400010a00904d4289420188840602424014501602d03070000504440210984200503951045614420142403090030b001d00021900080541110395040700340c0c091a010f40002c11250a002c20403d90203500688050700f140300c6603944031343c0c682d08000c0401406060f20000202a400491105402842048143d85142000d01044989505d07050b224490380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 389723345 1250 389722095 389722133
    0xa0203130209040f0308060f15030402060706060b0310050103180b131203020c06061801050607140312041509030212130f06052a0c0d0204090507152703 67
    0x210200d0005a803100d6001e44980e00c1005004c281d01c4090030010035a2400030300e2140103074080d5144003100c0d0740320784e248030100e00d020744420780c1da80e12407001c01c240e4040c10794000c000c0e0b03043c21408200d034204030001e1842888403850b004181e682e60401182619424020880e2801200b96110049107075081201d03403107020261454181c1510750341e0040409039980f0414006070340800c140d1880c0d1014401c0d00d1f0402003c49001e079070303480300107160722407a001031142c0b030300c9000e000402c071082100481c0a203400b003045a040d0390729640191122a410601154200c960f84190891802d500b041ea00c900d001d2690507900600c0006021940d000d03180c1c0c010003881000d01c601540002d6444017100165000d0611940d41d5920b036040075a01e14510a84a400071560792106000c0e1080340c440011940c0d170307904d412a41e1b4070141440d030010030300402180001400c07a00a038000440c105940c6c1c121032944003002c1d074902120085038032072010f03401c088000c1d20000e010000c008002040020788400744007546 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 389724595 1250 389723345 389723371
    0xf010204051c02120f010f0e06060a0b0a020a12031505060309120a0309060f060602060601020a1208040809062a19020d051c09180b130e0f010c1e02010c080a0203 71
    0x4c110403d501c2c00703004042e1054941c0d150400721040d1443c50144035580083c1c000200664105503001866034034040c05103040541c400700e1a02d0341c4601c2004044d040c95080341d41e0301441d00002d000200075002900c0540d50501254000081c14246002180d1164051034054000140341040225856018600d06002c1649581d00c03800810074512928400803d52000055031034503084020341041c500900d480d056400402d4071801080205014840301c50583c9843c0c00c00780e64500d8443d100c1d00a1484c4643c01120200d02c5070700c080031136146885507240d4a039848500380c00046e1040c3c1e07142d0110880c00c08040400c0e61800050800b41300001c107030f501c608142d5842072003110007440c0c5004404031b10400611104010420200b8612404001082140060214110903004a1107072000e192082c04810740d9031496a140e1401070202880560265000303001c4084a424010608414101280100d1011151158507140144107680395108a600c031541030f0350360f04103000029003008003d0305d52454 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 389725845 1250 389724595 389724619
    0x19030201060f090207170f070f02060403080409050612030a02070504050a02070b0c0417010b1008130c08100609090f031809060e090d090e190e031305030f010204051c02 74
    0x320b000049030140c015040d00517110703034050511035504c6c00002c2c0c40c2c22904c2401c01030a561059020126458160010003100614030b00c0d10104009210f603600240c003900002c6000f261120740d0b074100d54081c0c44100c41a00311030398040d41c480c0d1244620320103000964008075040240e400d1070b40003141e000c991000f0040c1481895110078050b5042180e402d83d0700500042c0502c03407200c5000c50300e041101e00318020005204240d01051100410784800402e00c980d01000451548010511540c9154030218500710540c0d00d005596175142034400d680c10035410054007250b01d00c60b03407203600601608048640b20561080e00c0c180d902c8082401004444010030801007504c007064024200201800240800b071480c040032500d04041e00c04422104210044a040001c0c011400c00f05401c40304102008500e00b8000d203402e0001c000a000310811404041205000c40072100c00310400c40b14183c0c181c41080307032a1144a03080384614000c1c0c90384030f40250301344e0058455001e150901188083c1100d02102 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 389727095 1250 389725845 389725859
    0x20412030c031205010b07020f0f120c100816030905030d0903051201050301090312020a09031a010510020613063201030c0b0403080d0203060f060a02160b0a021903020106 75
    0x500011003540424500201e1800301039000b100d0520401c50039004100e0765040c08000140ca1054070030282c40f03107682881c5d003007642e5900c21141740030f1007009024101000308a030041c3d840d084c0f1441c80d00d218400c00c0c0d0a0000c0c0c1d034001c0f03c18500c202c0001000003100c2c3d4440c003061300140040001920640b00904c1030001c4c00c1d440e8856003803458041d07160f5581b1107032110403c21407600c3c140c020b0b0b8000c0e4141710300c0c40000798100500051901542e0701c00f50f250015070000f01c07075041c030030351000c0c0111104034a50244e05014845150580348162215040340f007048074266070311001a50391806003188507914002289183d44842c0b000d89841d24100e80182390b40b41213040d885254100c0580c1d102601e8010410403c12160440040c000d014040e400e1601e1a05c03001c880d40100700e07804203501c2e00000060101c3c0d545d16101c00761864010100c0d0345520300424025610030244099040090f840e000100c0da80c8010002d5402d0002c86500a1007105550562009440704c8500118103542d02c4882c046042 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 389728345 1250 389727095 389727119
    0x1403011a04050909010203060f04090807022809020409230c0a020a20030c0114040302120304030206031f05040516120e01020c0d020c0a06090506160b04060501090b0f010f030c030204 80
    0x113000e144001680320b042040411200c01c404034400740c030403803500d101140050b920b10300f620003007501203c031030040301c0f040080c0d0341504d1403600b0100c0c0310f100d4099001c80c0045c115405801980e4505108201010044545410a1503c00c41501e0300d268004d000840b0340640d1001050800f669105661041c4015680c1e840348450300d0600321301400003000340600c42d0804010078110b01d0000d207080c81c0e0b000301c0d88011400c14411800003a00640c039030b2004120340007040049800665014180903581d01e40f000508661170800100b9260010101c030000546207003030f018286c0688a102c0c428100b4490000c070540e40c0141c3d03400b01c01c0540d42c40342c2201000b12030038405410240000780181010381000400242001204848144a42a87d00c810700c00158003e008800b030300d6041d03a59582d196035120381400d15040c4000001c00c9807500004200402c1f280c0d410990485850354000c0c050a0ba100c020019455034821490b40001c00084650b101144240c00c85070170000c1a040040c45c1c26190032804281b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 389729595 1250 389728345 389728351
    0x3021204060c020d09030b0c07031704082d0906160605011e08060c0306040e070902160b0a0506030a03120b0333040f060902010e120a030806011403011a040509 70
    0x5000e40c2d500301981040c1d01480b041044188514104001e41d0035a9110fa65941000c2e0042551600c0414802d0403d40190f011a1580400c3c82d0034020a151601e402055035200340400240d4262039108040c0002101c0704800032591000c411905100d02a0b0038080d00b9045080000b241d01cac1030b04000400300381c803441102d010700246400a074140c0c0c0382c101e240340300028640c01080c031035004508000b08110f00c20103803904180f04a5001c07640032640d05c0307540e2400d0b240d60081c146042c4000f030300c5590005880f201200d11440f640d48113a03036545d12a1060100c6130101c0d08140c0540004508200281c410170307458548001908000840f5490003010a01c0e11a0300141c6814910b03038440500c0012160000340c0000300402c079040e01183c501503aa000410300c1040008100a40f00c0f8440c0d1b013168021450184442030250121f01d4252000404a54904940d0f03401e0740891001d5002c14029445100000e585290030404240307564a002d203080c030313441c04c110000030b1100c3e020310000c200b60340c8a828284c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 389730845 1250 389729595 389729603
    0x914042d0603050c0d230703051507090f08191e081b1c03050c0913090c0602070b0f0306030312040c030b1e011e0510020f150f06060a03021204 63
    0xc40358218507000d4503001d01100344a1040d103c0ca800480000c0500318401080300c8400d55800303130100e5006c04076140c119281c20041003805031185416003001c14040e5548940d0141d82e0380c00d50582e4422510307541c010540950f03d4242c00c41c14049940340308030b6621804041c0700d1190b601d01020311108600f240d840d0682c0880307400000140503040c0b141515441c40000d08028050405001b00c2508031400d45202021841419100c40000340c40030800c40035600c000b40c000e40016071800344c07280a0300c0146002e03041150310310341140002c201c11b440010701409440000e400a49411600101100c1c0350300020031980d0305200401940c0703106d0303850f2041c4e180520710964214038002c0c2180ba00706a250002480900d00c18000352400c14400034541c2800d045524140740c25400750341a400d0080c8640d0309400141d000030070f54498a1a0550028910881c42d40d02015100c0701d0304010050402c08000303561800f006100440440c10503c1c00000909a0b22040d0800514261f003035800040b0175801142c0640d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 389732095 1250 389730845 389730851
    0x5120d030b04060509040311010f050c0702100908030a05090301060317040512030a0c140109050d0f120b030a0204020918010f150206070915090806090105160914042d 73
    0x40102900341c050801000300c2240c042c440c05041c0004034014450051003e0308210744440300c040801020352080d14101c99080d000c4c8001d10341150036440035401000102e0107001c1610b0146100c5120b180000141d4914101440c03078171105000444840d080441d0295041d5a81c1000100266052501d200c1c5819100c0035580ca8501d0a030030044240c00d5626140c050b50410041004401d6000a002407030307039400105007042c4889556814010030b040b01008180d0703c60280c9040005400c540b01c48000d01d0984e40d4108001401d0300e660302a20b080c00f05260b01940b01811400040c079098000c0c084942c0041c3c0414200d0303400c601c0400d81e0b41d07000e90280c140c00700c000d00207002d8a8a24100600300300310742d00003440c450402046c018000300603442600b0608941040310b200c040d01c10f01c0b14100908030700d400c68156003070103c000c60007000107803000c1c0c6004141e0043c2000d036501440716403007140c81c014504082004c8100600002d4522003c58848a4504d46244645000010318088104071036200c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 389733345 1250 389732095 389732113
    0x150504170105012402150c0c06150306070306120212012702010f05031e18010c051801020606130c030908041d010e0112060e010e0a200a030b07180512 66
    0x10b514803c290302481c181301a031604401a15900040c0745065007030080c0010794039aa407001629264090a4075680483c0100070600103040b01c0301170305c00c22180b4202c040c1c2e030240c0c03034100c0282c08440d01d511550240103a00d0030b003040940741521101285518410010034403440541f48041c2c842070641440400c00c19000c0040d040d0350f446080d00c28100c44a003071480c030794102845580d1800100181224583e0306100014414482400411180018200090152000400001d001e0f80c000c12400d02510b420034040010a41c070000352140902c0024003031890075100c01c903480010f01015a40b41c3c0c1403507164180c07840002c18180042009201400320266031607404035501000c2c1c0e0041c4c1c070040c022981440103020280c04611820b80f05135100000081440b141c0300918007511207003891903000e0050b000d0041c140580039510554080510418400081200040100950241c00041d0105420038005001c25000319510489000341c00740c2100ea05584600040412407810740020b4140c02035410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 389734595 1250 389733345 389733359
    0x150303020622021e0a06030609050603011406060c01060302060703110c01020a2a090501030602041d13020d02031609060f210305030c040807080705130b03060115050417010501 77
    0x340c0340e044512211101c094030610001c1d00903450b22001c000e8403545451540141440703a1040300100b62102603c0d01d0403e60b500d50005d00200709038820381000b00d04010000b901450188950305038200c0c4640030350780540315030050100d641c20600c081400f42d035840c030740400980e0301d05000d03180151107699401c201502542e4010300702442002014150341c0809078142c00180c00c00d800e00300d001260040d10f010a60b950500c2e4000060507070000e0303402450440044103012680c0c00910998100800d266a50620858981c07200542220b1000b000c080031410800145010300c40c0c003000500003400c8034030080700c02a225400340c031594802d0391120342e1042c2c10046092503926510041c8005540c17030440d40510000c01028105841e001820418000002440d256005040d02c2c0030700090300072200c0c101d454900c06a0349001c14090ba03880380700201010b00218940d4040e1000095000d07020780340d164030b0255106107840403d00a8002e0040601c0045038504146002c1c41d01800b0080c000f003502d501d0070503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 389735845 1250 389734595 389734603
    0xb06040e0d140c0309040204120b01120807060507120c020703050c060f07060216050706030f0506090c07060f020c1911030327010201230403183615030302 68
    0x58100c80307811002007425180d8014425a504022500049650f41d000b02c6000d0304503c65458480d9000c0c1c801b040104124144050524880740308200484890340c0b03a8010711031490424900802c02c400402aa6000600e15000507030002458202003100c160305e01641c00680d90740003144001a40b1102e001c100303011741001405518035083d100580307050005031001d00d0510995101800c0c0c2900043c59440400181429124441d04842526070301a11410001c0192089101c00c8a099040401007240c901e44204141d0045079150325052030b00000740c0d1520058841c910480d000c8035400d010f070542c5440b0602400780c88000c2c400501e040400c4c03603d04070380c3e40542404c40a0181d8000e0212901200c880540d0500002d2a00041900354103c080101d02600c120416290710301400700403080d90307030a074080c900c0c000d9200b9210440d12030040000592040114450020783c001403600c200c02103c0380d01440510140d42e0900102552060441c060507140035110b04c56100600000c00c10915034144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 389737095 1250 389735845 389735861
    0x90b01090b0d02190b040b120f1e1302060c030d061509062a12110a021c110306070804021905030d0f0302072f03070b16080d06030b0604 60
    0x344041007280326250214071400d4103003000a015034006469000c140010788a02c0c4001c0c0343e0f02c410b459850f40c6070171104040303801026100c2080c8504030701103178146e120101c1991040308c0f112030210306403000e01e8407101520740160400f44c02711a520296809620b8080040200c00361600c000d56503400d448045401b11685039000345801504001a420781641c420980b008640030740c40c0c0160b080c010480d180c0044a900c14110300541c0000c08460104000560315104441d8951140301d8000708401c00c854490f40303949002913001290700f0310500d980440f0840c80141c94018083c00d0242d191200c0440d16200054400c0b07404140b0f000100401c510380401c840d00202d60200e40111440d26000120b55505890030441702400040001c00403103a22982c1a16421034211403003507047c80c01486100c641022801081040c1c2c0c4054201603003030b04000502d4011140c68900c00b038606143e030416000b080c00607c0c1c04803640c803c1004440d2001c11a80180c4029501a80b04015142026420403085074801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 389738345 1250 389737095 389737109
    0x9030a200406120602130b1309050c070b0f150d0503040806250e0f0301090317010909050c0915030d030606031401180504020f0a12061a03060a0f090b040303090b01 72
    0x210140a028894403280040c260700c0940540c81b03c2d00010301c0160302116400490342040041a41203d0140c0b000c410000c84440b400100b041d41c841c0704035a80d591082141c0503044031062404181021a020000341e8000c498100702e0240100050014445a00340b00060b22198008242070185075814444a42c020040301e44201c2c8040001c0300d0220304c1404010001c041c024005e20855560311078540748146444000c0082000900c40c3c40c0160100740c03000c0c10004005071400c00881d20481c40d10070182d0858000c801040c05082c144100324460000038280146e9083ca58000710140d24100f00c0d0608a42c010348010031000d007041c40c02400c489281e201c0c00c00072204140100002c04810546003141c20401c0d070003041c0c2d580c8a002060300c0c96a41030245401030800031002400c02d40d100c8018240601c80c00041c4003004c0c000c0c0b51102002c8200c04160381c10f4000782c0115802900c281c1c80486100150303800131030880d100341c84402c1003103811601034000c00d40301c100d01c0041050000080f0302500c50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 389739595 1250 389738345 389738351
    0x70605060f010212090a03060603061b08060a090b0307050301050705040905090a150b0409020910031502120117010603051603050c04050c041712030103240504050a12030209030a2004 80
    0x807a0300000e5641981c0160502e48100004502e0b420b40c0340c0038044006035801c40d000340f0030565245041d00080400000d556241d601c2e000000f441d130b51003892145e001e010000d02c510358503402e245182000b08441c2c21016410722034410006190744080c0541ca106400b50344032591103614050800c400d0f1070000349004c845d034000c410790b0700010355580d040030310f010031520b400200d1100c0c03100898000d06600c1006907024081700c082040e40c600c001300c03650549201c2c000a40d031071183c0c45076140a9000d443c25680c0070b0320010005004844e2203504484043c3c06c00b00020070007039960b0301c510b4105410310a220704c100c2420b031010b0041c05000c0000c00312010041c2c42c01c0100d444c25500292160050b07014401c18403d0702860b400d9110030070018100e016200708643c40d80c03541e4920f4030101010109070501101c42d000c0801000c4051540304041c4555080005486500c41a0b5220703a01050007a02050038546d09200d582c030036480c01c0100c0c0c0c4243e032090075811000240c50220400081c88110090f210b242 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 389740845 1250 389739595 389739619
    0x1c0b100201021e1e090409050f0c0109050d0206043f0c0b03070207170f0708030904140408090603070c1a06030f0d0c0609030302070b0a06090c1e11010e1207060506 72
    0x8031043c13041c803000307100d660215100c0404100040140c128144080c140b442219a984405e890114202a25840c01d80340c00d5009940c1d0014400003d541d400c02a40c8a10b0610041004071032500101c49241034070701100c40012107141c0c4a4401c0040441000a403089115518040001c02d20390310740640500480301d8154540745100a683c2c13000c134001c4651011001c0403080b07108038100403034545580b0400640b94603944803400713a5920f42081407210300c158248003040e00d0500035400210300131600f00211038a080c691900b400700681c4041e04100c200044000e2050210f18040d001c0801c41a90074500125030511808251600b82d5004004c84642c001d40030246110317410191a8200c0d607403012004c0307440722813814140d0003400f50316030180262681ca801c01801d040340d6401081a0b0300c407030104000d200d4440408a030001183c51103010603492020100340298040d56a11a01e80d48060010460000d018103503030914541d40c208031030900c004104002080002d0040b1903000c0010340d94118998 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 389742095 1250 389740845 389740867
    0x1020c12060a11040f0b180607080403080703090b04080f06240f1203030c0403150207030f0c0c050604090905010f090305030f1e010b0d05100b1c0b100201021e 70
    0x500d01420040b03029640d21801c8812042000a94004181e10410100d00396500c1d840a0340682c0515400144501c41c424140300519000094849582e00006540d0030f0030304543d01c105065201d58015024064902c0c0b0014441010300010700103000307100050844007030b0b01c80000d440c00034040d242500c40b1405000f0a80c4400d421204544c0e140011648002108400390101d6001e95076062208180d000010401c07600e03908c210020710440f0f2180c0e0040c190304032212a50f408038061400001e00294000424200c0c0610500c40081841c7c0070320710315030b030aa640b040058000d0b07100d5400b001d40c050301c0780d03c1101807000a216121000d00c035010103002d250416903008001e480010445030740ba488400100e0250044049507103880c5280035031805095031594071412140c1c210913116000c1d2810704000652a48001d40e5410032034511101d180d04104460070621500940314010389803582d507414040f0603507550441c24100d02990381d000182d50720144018060100c108a44031001e404080210f59000c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 389743345 1250 389742095 389742103
    0x3110f04090528020a0617010b0406050f031806040b06040b04060e07030c0903240617060402040f02072a05010801120204090201030617070e070f0c08030a14010306050601020c12 78
    0x1060551803000780b4215901c100014100b803c18020750880b000c07071808142c464000550741c040d0704084081d21480e80e46e1301701c0303a41c85211b280140030000c0da0074011000070700d081d503010750307003000620807104c0300780d413500300150703c2c05501700c07000e903801c0e160442031060318105881000703088030f001d403003d00c90035040c1031a903a250140640a241010707601d0107069011446840000003441d8082c0410003100800c00c1030b00321000d01c0c41c4856080a25000001646270510080d0029031413480d00901880d41e107036000c00000301803810410504680800400d0001010503030307013040d001301110990900c116400980802c00300c00c0c0e000729051090301e000510510400c00b5030f51510950444003c59003000c075100407000b400844c0c2c0f1110035138004600000301e9000206150094400015000355180c0d2034200c21510244a0403103040403880454188000c2650940110b5001103851004240e8101c6002204c6900300260710a807106984c550a0164940c0c0c18000400c4045048550065811100c5089619 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 389744595 1250 389743345 389743363
    0x6041a090c03151b03041a0a020403050d11070b0a030617151503010f02030f0f0f061003020717072102060c03060618130902040e06040c03080d09080403110f040905 72
    0x3c10015800040c075441d0314466200403e2420f001c58903100d040900c1e003554900010044a0414a0000c0004200c03810500c256400c6039001002005d48081503c41500d5494842201032568084c0301004105c160002000f4a100d031010781c0c00145aa1401100b003d42c1c1c4490061a222a00868680603c5110a200168005841081034100340760b440000a00510b01c0d5604207007141d001108004001d400c41500b41d110303024216800e18140c0e504014141c00f900110744150f070151803010f010907950710950203442c56521072400100c134209840708126084e002000106c0d00620303071510b004000e1007280801581c003031142c00107001e00d0504021401c0b003030000905583c05104007150400c40d00004128600201f40b000c5d00c0d44a4003481c0c0c1c43e4040103403e040320140d02650814800b06440540020514400c1d9005940c10510a080d079848002d10340c024254076044988038407418000c01c2d00171000304021403140e146c80340c0d851514001d0050994000c52701da03101d40d03e8041d4000c086000030034441c02c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 389745845 1250 389744595 389744623
    0x108070602070b1b06040b0703050f07080115090806010e040c06030506030703030f0e0a0b030603010b03030403020f0108040f121d0306061012020d0e07030c1512180506041a090c03 79
    0x1131240402100f03031820540700e0301c0c900d4040c404e9000740030920461080e4076001c1c0e0859602070010355140e01c1000c180c141c007a507000002403202001080304441411800a20b0219031804440e816501e041803032402100b81c0205a140c140b250500c030822080c4d00c0620010486401c0c02d0042d490f145001030f841d400f030381c4000741c140408074803c2030301d04c1d11500c0820411171006080d0f01881e61180010041c5820485800b0301940c40c14100c2605840e00100390350440b98004c1c2440a65201403004460804010b402203440740300d218082d00000c1c0300e008114141045076991881d080014503500c01d1004200c050031303806500417405118080e00c4031070440080c00d040f4185059064103454100000344160007a0b2141c5074500a0441380348040400d1020840e4042c0710710000305a100d4010b0152005540c40c80c801181d4034100c0303400182c6564010040d00325030381c0300e015070b00f00c11601c409d81491030481c2c088a0489041181c4040c80b04410480703a00f1500107402002c00c0c84403a001b10b641c40c03a00c00c21307480c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 389747095 1250 389745845 389745847
    0x90e0109141f030b0402041d01060303020f010204080705040213030f0503071109010302030c0907050408030f12011e0909020607080c060f0907060f20031c270809010e03010204060c0b0108070602070b 87
    0xb17070542d211604840e8000d441407990840184212855500170441c0380411801405581240351000c1c4050082c0c03001d461541700039088144c5001f0800000390300002e00c0c001c91580401000000c40d5015003031b1503a10340950061a0f0350140b62400e0280041403041051045c0700280050015840004500907001400d84540348a80c0f11118103880c140203550082000740b200203640042a08894060710b80969500903042450b601d1303440c01d00e8002c5d40f4051071600a0340014040200140301d402440200340098412454590781c0e40705c8054580c0100b4064406900c1003007888100071714006042c0d8880302d8000508800d6003881300081a0b980d081c110070f400c000001c10480c1d0003101c90740302006003074010700440303a4422440c1481080f450f107010106204901e040080c492408464004fd101200c0300ca502401c00d40b4240e645c0038051f041038628030704002518035020002e46003480108050b000035103440e030301040f5502c6c000a42d41c40503008800e00da00706180403c00290002200780943e080c0f48413031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 389748201 1106 389747095 389747101
    0x1403060f1302040306021303150903120b1903051c0c080a050304060207021302090310090503040314030c030d05160c03081501090e0109141f030b 64
    0x2240d008860050100c0451a02402a024024240400504294994607060700f02e0700031280207040d003c08406d06000b03112840c0d40440c03201c0905c40c4280450086542c000306003012a0340c0a074009a103a586240d950741c0c807144104144243d80003190a52a5071f41404c90b5692040c0181c10300030200c80300a028801d210300c0d800842180c0100c130041c030707040c10520100c07140e900041069039101d1703091160a006070b6807010703018260180c4620250301c0d100004205401d040944507000109407a2448680000b5404015581229081100840c80d5176081410300e00314824682482ca65000005450981200540c07150307001d45c000040d1140905600502500c4411580b50040c002c112a440011a00b801d4605d40c0c0911040600d00031880701e540d503107120f21000003030300005813440e2160380e0625600c25901e00160320405240c209070a4650308040610034040310300000c1c103820004000 = true := by decide +kernel

theorem cover : BRFrame.Cov 389568345 389748201 := by
  have h0 := BRFrame.cov_init 389568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 389568345 ≤ n) (h2 : n < 389748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
