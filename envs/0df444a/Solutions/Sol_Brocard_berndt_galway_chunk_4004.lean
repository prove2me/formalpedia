-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4004
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:18:32.387299+00:00
-- url     : https://prove2.me/submissions/6b4c17d9-2a6a-48cc-9104-983acbba7bb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 719964028 ≤ n < 720143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 719965278 1250 719964028 719964041
    0xf180308160e010903030c0507030c060c021306050105040320030601090b04140402031e01020405030f0c09010f0506030408070218100f05030a120e0a090f09150207110f01050705060406 81
    0x64098100000d8007440901c24000707016000030607190b4082180c5903a404513428410104d081e211030180c000013000141d000d00e01c400003407a4075aa00380304150f05004020101d11000780b03101606191000030040c41c2d80003006d9078210303034014407200c040042c0b400e100442a00d00800e402d40c140240070020a0300e00156102e89030b60202940c04000d006000403080032210800c1d84d010703605611140002440340050410280640b5203100058103243d901da010a00e00246003a195085412100b16802d041c20502c0e829401808500d050b55201c61801001c1501e41c440070700b001e8202c400c001040c20554643c80d403005220285140c08464510b0f0010707101c000300c2050f010318070149040203000242440c00244252410390019580050455105000c0d0b42150502c089982c02400812000480c9105c600c200040405880d0010481220502c0c2064049515201004c14103106110300c00120b142045850745542059490500c108000001601c40d070056090041407441008100030811026400c00b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 719966528 1250 719965278 719965291
    0xc0b160c0f0b01031109131106280809061603110c1f0507021f050402041103010b0a02010c0f020a0308091e031c0c17060a0911221202040f180308 64
    0x5c0d100b018071040103c1b060040e01d24800030740e010702c01c41001c2290204440b44000000301800d203000c040495108201c0c110140464003c600004007100c1e054000300c3c1550300c00b0226014000625150702103000c0e00048115507420107555088458404011000b2104c800c09150308980c100301d440f03451017002e00b022080c41501c0d0b900741341c04600303001c2c0002402c1900d040b0707113040c1d01816200d404451004100050059900a131180541c20700f030300f0300c0d1000b035019090384101d180c0d5030302c0340080c081c3c00d44032400001800c002030510595034166012400d0260213a141c50a206151204600989403201a081611810404180160b20705800000030000840e80548041225000b0584942100d8070750ba408804200b01c1038241481c4464400d1171035110000070610700000d0f407902032180490752a000c0c0403100c2000041d8100c1075a0603881c2e00011442060084400c0d02c0c01c203941801210003400c0c000340100c2c0c83e900b03040b82540346a0003485a42c80c0300d400c2e915403040381d03040007020880260b948 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 719967778 1250 719966528 719966543
    0xe0a1d030306030a0b0901110f2d09061305040606030c020709050c03010308070f08070b040204140c0d180f0305090a060c0c050904031209050105070f0c0b160c0f0b0103 74
    0x9488514080300341c902c1035000602400808002ea113811000340d50040c00c44032155690344115031041c2201000d804091044001d05440350461603401034400c0c2e4070048070182c1c2c1d51014003c660f030111042103450984d403d49003151500410901c03840c80300a96000154064144074010a030541e050740071500c5441e441c1d00b01e40c0180d6560250314102c62080d81e603680005d00420050000c039018000400318940b1822750034040024585038400d00d80c010101c200d40c1c2c5008807007848103524140c018100080740101856115040404450004c0d02c200e4409031901c40c0c07144900c040da02c801e06141c1c509240c02440a00c03842c0715a00d030003441941f1180080707216108600c0040340d464030402c0c26540007070307204010310342c102c0c1007100300280c449004004074100140c240000e00d061485000c1c00c903802c0d210360004101403c01602c0a400404245022410400e12090340d43c04949800324031034200700c002100c2800d4015480c0d0840340100d0003000900549001c03002203041160801d4154103c0780103048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 719969028 1250 719967778 719967821
    0x30d03050609220b04150c031b0f020f0307051509030c030d0504080d0f0c02190506060910030b04030e0a0f0b09210111041d012601060e0a 61
    0x540403224241c80c0d9540100108002070250720100150303110303c1185070b80070002e400041c0c1d00e281d00c3d041c04039012901ca1002d0541c0901c040140c0c042c812054440c2d013014030214981d40074104070340282d03032200410440103241c4020001d000b405011010035054080e25078841b01410030a546442e4040c24059460702e100002e9600d01002c02a02c0111031070748007444c5404040301e0b01c0000380c1405072040d40e0280c410400700f1881c40f418406c11010041066012a580ba1205000381c1089000c0da0004d031080301d44150f103c0050700100340d9543c0000211064101a00c1da0b01e001c040300b80060704010031101440060009142e00f0007031800e01e0600881e4515005c6407507064000d04040729104254981c03a0a1200086034900304101654144501c0d201e440a4001f07108482d00b0b48003c0f443d13524000d1400a01401a01e0003030032501181d080c0d2000581a5500d04030081018810550001001003d1100013141c1c040c0b0070341194000300f80c03007c160760050404140c48001060700c00c060000a210200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 719970278 1250 719969028 719969053
    0x80c040905192306040506060d05063106140609060109030b0a06120c0f0b1309020c10110703031107081e0d050f06132a020109060903030c080906060603061507060501060e03 76
    0x240d5140076803240150128ce141e142c0060800041100c2c0260003400c41c0000501c480d40e8406080301ca2402040081202c0710324000300950564080c0116004451300e404210306640c2204821080340d9010400500c1c6640d402c40401c0149042d4000098840050458906001031040c0003810baa21a080da40702065540b480001d503889806026000f4200f99a810800081c50354080c00074460030038142c4030410403003420740341241d49120040d544020041030010a042d410702c20440c958031455496443e000d00e64170f0720b0480d40100012441000407041c8100346801040059450350034454801344814145910242c205410440b14180503007103913000c6030010750703050051071502d011048441c0001e80c2d00041e02604800080e0220042d5900c1c0c2c04040001545031081441580c081d640c0068040300f018002014088003800505071039000c1014411590f03140d1f01182d41140b021241d01491150251005010b80568480a03150b00d20700000050550780240c140a0615411001c2d01d2a80031840c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 719971528 1250 719970278 719970289
    0x40b03011707030b2e0f06030f0b0303070b090a1712130f0201030c0212041403060921030a060b0712030c020a1113060803030c04080c04090519230604050606 69
    0xf88805007803220b003400400c02d42c0611880c0c040861922011000a01140540c4201d003040746520000c980005c0050070001150b051090b000c0c55a4011002d014402e00100026564051080040c0c1040070030808265544000c000d44288a41d101504444507020f08141f00380c241c100e51080c00b41d002554002449000e80c104c0300700d0081c0d6102c81c1e1401c4585990300110024a0040c180c00700398803076001001d10038000800584010702c3e01c400d21a0f20340c4440018181442c001810001c0c0382c1c0e000070045007107e01c0322248506080440002e264481d0740e00b40105000c4c110035404489a500001780020a200505050801402090302c013030186800d04d42003260385141000d40900510750740d5141c0b21003850282c46089261410f6200840d45076110f80701141035500644811101c20b1000600300b108003804c1c841001010411a42004100c90540350303036403148401c040c801e01451b0b8012001040140191080c1030088007444104c101c04481880709950302d000380c500303548610400d800503c161801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 719972778 1250 719971528 719971543
    0x250203071506060519050418090203070501080103080a2106172a120c04022b050717060a0906060c020a050409240e0a0b07030c0206060108070e01050c03040b030117 72
    0x4130742d0380310b2805020601c0c62214440c4181140200302c01008006400d02c540041070080c400610750001c0d90343e01510415140c00302c181e1040741848894001000440c60407015911660080d0a1414800102500c00c00d008209044008811483e100c004990580c028203014101e0580100711040c0e0381c0c100403d45c45a0410a400440c82c00e40700c00c1c4034100e03040c81481000b0844020013141c491030140c8001405980200c08145103080c0e600c8082541400525002d510304c01c0c0c025400c0005041100c0b000307008480703a0b40c1041c625030f8000c002c5045070b150300861100a00110b0402c11016841d502c008120380e01d108400d82c401c080c02400400c05192502c40d06c0e860740e60000d0740700c6048001090992402105100c13000940f83c1e036048007504200280a09882e8a224003441c80603894450006400c41d07061860400c00c65011808120490b40c006441c43d41042050038125810401040101c3d420300c200c1da107400403404081000240600700c1400740d816101c650351248001e800300891140d56041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 719974028 1250 719972778 719972789
    0x7080412030213051825020a1101051201081605030114160903060603050a1217270114070e090f040b0406020d02180306150901030b250203071506 64
    0x4a980c01200c4a020b40e0051152082c600082101076035160001603440e800c480c01558031074041010842c4001c2c038408105010344507001c14084142c15508000d64968201400070b19039814141010b04030fa010700150303180382280405951242d0303140e03100ca6031075004403420365104490705070011400b86018015140801c01c96245d940c15035a070090628004140303842c0e10018010751941c08004110b26006100c00355025900401080525241400e00d0340c29920b4014100060035003d0520095000f141a030800b8118070500710740c5040e00100d02c032041c805d0300700e800290318081e04e01840e100550b490501c1901652204514200e1500601c0060641103482c5d0344402043d500140008000c410381341e030400c1c05903030014203211402c1b26070004c03030b400782c220b44210030041581a98146410801c80d07a0043c04244a2881440080c011401d030460602000b400307440d541000803010003d0790110b240903500780d200003000c0c200400d00070f074990740a01d1059030341101112640302d4280850081d4402c895 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 719975278 1250 719974028 719974043
    0x609050a0f0303060b0a1e1419140f030402010c03050d0204120c080607021e0c040e010b090903090a0b0304110411070302011b090306021b1014010e060616032f0105070804 75
    0x200e4030307c40c030010104e2140400203004ca0205103022504142d4090310542c840007128030310703032000704c50040c0c04000074802d030107031900301000259402c1d011401502c2d0025820700308140c0780b842915090340c05001e5002c61040151010600051072000c0b00c400d00c0c00b042c015041c90181c01d803900091901c95104403644000741e0300c240b075601e54030485040400c4030380070880300f580e800c80400d00004050310300c0c00380000b0f09070b91100c1c1c20190601c1d0429059070804c050100451828144502003000c95840f4400c28110207800710004061104c6450440c1c8080002002002034030400c0d02161401e0f04110001d40066203451346111000800b1055420354000f240c03541c80c1d10a19540e0b0b0b510203503202281484a40c180c8094180c40341c1c50030407005c0d82005e45084003150369104444e0781c9040c40700c140e001080104404052080a4903070800300d038010361a00c0c0010b200501c4505058074a151810b00300340195070200c844100d4003044d40c0c8110a569404c4000b400640ca4001046400c0b46040d00c0150015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 719976528 1250 719975278 719975297
    0x81018060302210303160504080d05250b070507030e0603070c150204060813060f0c0207090c03050c0426070305060412081009150f03061d070e0a05040609050a0f0303060b0a 76
    0x43d051b00411418016075881c0c070038030702600e8044150521020754142d1020030808a02c0e032181000056034040850302c7d015210764640100e03161030390400406000c7c403007404000540c520034140b00e031500f502071481c081c00301641c13418408001010b07040e20b80c0c41592100b08000e105040d492942c002c50342204c4042e074030041c0c00e44680f8031001d4581084e44040b900140c0c0e03114040700c40100b90090010106550b00a415460310b810251820f079540102c1c240201498003080052414001c400d440070365088494212041246080c103202e100c1c010001d1078082c1c0b0640c04008100480086c445100390f1154950700740080440358140d52401e8291503460701020003880130f0004a107290b0004090b134801007113003070302d0350350310041c2c0541c00d55984c00540707825448901003000c294412081124045041000b842868034088088283c5c010242c1560040c9440b00041800d0105540111400a40081c02d03a03804139240e00d07001e0000c6000c204110046414180001101950075096441c043d001d41c4070201e65 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 719977778 1250 719976528 719976541
    0x70804050618031b01020609030f190323060117060f01031a040606020304051509101d0618030f01060617131403071103031603081018060302210303 65
    0x240c1212103404200d00505001c02c0d8a56000c000003e64800380490302c0e000e0510300400282040c1c001401d0718041e42c0104813020010391450b04946001800300c80030081c400403e20104c0240c0b40381c0160191600c01c41000c07109003824540c060f8014042621485103218050720b14480c44403044501a910420410b0381014a500907040380c4101050303021000201d514050008040356203541107000140c4c03010900384014240a01e225060a520922a6040250400c0000c072444480744000003004011148603440e0a1b50840c0f081c44d4040c0100444c7d10340c120040001c81c07151035403080314424411030000650b040c034184100d0056030116552001c403050198103030200141c01402e040c2c4503008001352440420350741e61060304d10340c080c2405195100c043d03081c0400340002c4844107d2080e0001c0000111040100032003104d40d075418240b00c15986e0300d160f0050b24051190380034000000e6220340049150410b13500945c04d5901c00c8450540c00382d5940035104920350444c4000e08607900403c00304a0703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 719979028 1250 719977778 719977789
    0xc090c0f0519030f0c0c02031911060d0603080d05061017012309070c0311070e160e030109051608011413260703080726060111161a07080405 62
    0x8001900740410300c101104141130498081c02032031400500740c6601c5400b1440c2c1440b010240c0c20005a01040d43e1046860302448020300781c0d100b070300c01e000004440c2d14a035040d410070401150448a495194907000c0b1014016010803562688100c00d600b0492001d9405002100291318080b03040c8886130b0700709460456099200801d41440041c540903801b12a40d4080e2300d14071540310343d82c030110302d80d6003850003820351046842c001906400250040c8007000854655540c803000c101c448003180c000003401a41c2910011103002d401d9424400c0b02020301c040000c0c2c0248000e0500e1008440565464000c1d0032100105c0035030040c00c1141020401e0f00d0300840034202850b0244920400c5c141c2d0920005803400010500003582c544007080460178160041003c0c4e906c4101030410100c01e46981254408920001e0500c0d000d01c800d16000c00c1d105d9109003c0300b566048568121403d000c03600c007014400c13030981d100e80d03445070148124410040d0841c82c10f5542896218030000d003464101010800f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 719980278 1250 719979028 719979067
    0x60f0818120d0612111207081203182517030f2b06080105060103020702030309010c030915020102120112031407020114031602010b100512150d0c090c0f05 68
    0x11445071110070115810900d603d88648040c440c49625034129044070910480b0201b080050b00c4640181c00104003400000c943c8200740c100b036a030115541d85d540700410304030100c0e1a2a04042d4400d1020440080e20010581030140c1c0c029a912040c940da144440c11141a64080c105a643c10902910188030030720000303404801202c0000021038540e4484c00103030600151500c004a580760002002004e40030710800ea00070320286400d501e04000e58020960720302c07a400f0034904204103152600241407094600380c0207450440e41c01d0310080c0400400a001c1d4209060149425240700000140081403801000fa002ea154030350300740070701101c05a21132070381100000340d061020070002041820755038402584200b80302d1024140c2c50009002c02400c607810340c0701c03103400303218004102e9481603040783c143e501c900c04040170240c40d5902e607001c0704403c0607000c00054000040403c1c4604200440208105544809104205000801900b16903140340140001d020502c2000500c0c90318003280c0144 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 719981528 1250 719980278 719980297
    0x809030921070312021f0c0504050108040f0b13030e09040c123002060708041e02040e0a0506060909070b0409240b0d0b150f0919060f081812 62
    0x4a00c02a600e440300e40c0d0742040030150030016045400d9070b84d1505545140ea286c440c1d507106041000002109000d06203110318055281403010040014040024444141105980c031a07142c2c8002d0500c6107058154010503441200801c0c04640f1400707160401b520761030700c6182c0268110f110f007450255281f007000c003256003d890340081d000f2181c030700a01075101c00351a200000340c3e9401c410401d210017810800c000e040752003001501d10600003c19140610040000c02040100045c0345203407000600520840e90b40d000140510b5942009000000c2041031166200f610401543da8074291203d44a2100e030042544c020800e20040c410800194400414841c22400500e03200140114050440840c4d5104065681001910140f00d14980c0600c1410305030a503100400e4802c0c004c000005802003031074041c0541c0010440158a40d140c400f00001000e000e81030700c5a1039242c40004085a00500140c0d0105043e0408a403030410502860a07036411303403c0282600800d0b041107032540c0c0d401840329 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 719982778 1250 719981528 719981533
    0xf04050c130332070501031a150d060b0c0d0507030921030e030c01120207051612050d0804050a03080c0405060c030c0709090f0308060a090f0b010809030921 69
    0x111007041618000c4102460040d01d00030401020403140100e8030440381549400d400340c03a80c4420340f24a00241d14400d496007400d02043d110220300705060b10400b050005035000c0080c6103180c01020081001708400c14140034288030840e11601680581c0c882d50f03240403d80c1d800070840120300b0744900044c05169100740b5002107000d641d0341108900002050100c50380c0c6c41d090306108105500620403000c4601c00760054400140c0d00303000a001015a510040e0042d42c000481404207c400d01c10300c500c00d00c2c9290107500d100d4589811090780701190004941502c1760b0b10800000500a03480c07144141d0303114004041446080d80c0488441c407015042a0300b02d141840007050035910400600203140c03103100155160007030000391a281c08802d90044c0490381c031384038180c0c02048189010513451034242c1880c4a403602c2c0d0310041071100c0241c2d03110700203071854440f0000c08084150090103c51401f44d8a0094030f4a41241d110b81720f1054004107644188200110b4004400e02d525046d511000c3c60309 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 719984028 1250 719982778 719982787
    0x613060803040e1509010608150301051b03191805010c090b040302040b120105160224010e09070b0a2601053a03030c021623121c030f0b0f04050c 64
    0x2185c6240f20030380148020804000c01c205811a02655860700d0003000c038000e000e0340c10052041143c110f15900c81045040000000501002080ca803040a8610950082042c0c07080317115012041c100c6228102c50179401d0180400e0f19522580001c410366a81998007890580745501b004001c10310b2000c096003003d8245650060b260081c45001e22800d901001c1d00c1018504200090820103009040300d500102e00a08005078500010058190380c003402c2c5440c159100d65400c03a00e0190340d0350009045c003c0010f41580c0032a0b0140e150421110a9081070310103080072082c031001401c09015031034002941005421102d10080303a121000380d1581d03852901c0346074400c0c80606000c031012050303000c80e480d202034a9040307030304204008507021550782c44907807103080821a59041000c54035220f2601ca1000c000080c0da62074415100f507040c2c2d81c1c1c08807220660700c4151a08440f042480f10300120f40350004060201486010f59803185070020b00d1901000e200300100b000414002e0306c400c3c1000014403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 719985278 1250 719984028 719984071
    0x1050f190b09010b09100201060b070803041e050106090b01020316030e010c080d1a03030c031e160c050906120c06030406020906030106050d150335040e0613060803040e 74
    0x182c50750107003401110301550f40036018103002a14420004c010116850f100c810000383c961801580c2c40360b07a100c0d80c29031f81c0780ca032804c00190340c02e80f0401d1907040355503000c4c59404114056002c0790484050b00303002d0090142e401c0c01a0f880c4d004450000c00d80d04505801314000a10400b040c4014140504115803569074544990500703400030210b601c42295190043c181440d1034503903204014408070020351400325516500d58503400342079600c0350ba00c1c0c580380d20960455410701c1038445550748170201c10310301b03c90f606100101c40c07054441c548c01951018040b444a04218034110a9113800300d0080001403071708818000f043d0700080042c0c03a09542440419803954401004500a06103030317658a071034010394004007040342d408a01c0d5818102e2000d20800003d52840100110301a002044c84010415251480c03e07060300c08038007400c5070f4800200400e2458100c1011800b03900d0a031005602d250b81610008103e5043c1e00804c4410360051004010702100860495845071500c2c3c0201881c10409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 719986528 1250 719985278 719985289
    0x24030b01080433090605010b09010c060b0d02090c180907051e040801142d04020405150a120b01080105040c120305070c1508060a0b04140d02030a030203031801050f190b 74
    0x5405100f255894004100a010a901502d030152020701549441c042c141d8001a28410380e0140c0204000c2c0c8a40c03055905542c0c4a40041140d50050044c91041c034100d030403407030701c0e60164900750040701440c040b4031014140154a107100f00700d9601c98524041c540707021144034045650954084030390801020841380428040d14020302054403000c5418140288882d407003c03000050981144040c2c907550719103101080000c2e4001e90107580004658480d400401200c42c099244190030a81000700000e0a008004024480300d00440e0445000e0f41c032403007260700382e6400f500d015041d101600e000340040c01c606019060b00c240b01307080c40c61a04d01c1139a03030945001c070680d02010502c0c00810f00021815040f40c03026500c66001c81d1070f1401b003400d1401c0d05015000f5402042142105d603800070503203803039154035203e000740c00908640300c82c416850020740ea5401154041c0d60b0b041400c1611300a6441401110f000b5480811008801d699040040a058160040c200320664882c8240300054541 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 719987778 1250 719986528 719986613
    0xd050a150f2d0e0c1c0b07080c18030a0204060b0408010c05030f01090e240123090109230405280c0b0d11030f040c060906050f030a0e0724030b010804 66
    0x320072000346034268504001c400d51b60024a84801e2110900801c4621808a02226410110000300001b50340e083d102080c50444550030080d000b0b8079007c80030032040500307070180007141d50100081c802c1e14004001140ca40c0002d6804820404030b0a00603c4441d00b1078015a070003800041c01c80b140d0320030040343d8429403c03008884c2c80e0348044100c014800500c4443c000504031400c0402920010807500100704202014480c00c1c8416a17a1140200d00500e412620340d4505c650900c0c0082038200750410340c2c2c03a0b140d008a403803007280d0030600034603590040e0b8030410b41980c0c0102890f6620b600d4400c1084d0517a000481240501e540d4100f61101ca4a101d80a11301514505210b0f03840c6203072600e03203c0741c40501c2d90006401e00c56a140304000065104046851145507440440c1d01c1e900d4007c5e541c03002d0125400e40400c80d003d450303000b20b07503130300b01d2880507000130035190403031950840440054088031818a40300d400282a0301c0010013080842c0d04402032980302040034201d142a102901002001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 719989028 1250 719987778 719987809
    0x40504110f0310030303110309060415110d230609010b0a17070e03060619170102040e1906050a030314070c26070e010806060d050a150f2d0e0c 63
    0x1103201441850707850307c18202e034000e480c030460f461402e044904603910500103000a008001b80d00000411048a0b00300c1c04c2022901c00145880e0300748000144060b00115490800c0e02c640b03505031440a9a00e159601d000700e07400790140c81d10b41d00785203144c00b880e80800c40c0c4005001141006180800b90001c466209034000d40d650349920750100304041c10000c02501c40b0740b0600841c402c5000004072080400102c4003000c9006000c410702441c028068055641b000c84507041102c20030100981c001c1900510b050141c00800809403101c007040541011400040c0004600c3c9040c0e1408005d0344009010307080c01440d01d4280076544407069400164135824240c45075994104203d0511020820003010b0f0180c0d50254082c0c0d07043c00107813035403000010207242c841e000e0092070006020b020300c050002c0c66080303180000d104030324886140250004520030000e152400c41010301504101100c06006010700c07405021410217030142c5c90280422001740041030090502395015a551110521503694 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 719990278 1250 719989028 719989051
    0x6090605160f1112010e0c0f01021005040302032515020304151104060f03091a070909020f190e100302030c040801060801090201030b150412061b020a0c05030d05040504110f03 77
    0x181c04284820340c1400031030321a4580c1048800c284048001c1f8200102e42003d407180e48010300f000004030310303110842c6d002280d00c501e050240018140d001c4020128800301d100c0740003007203803549408200c494245c1c002400503104203c000c030a5942d1600210b030418022141342c8143e2010010240448400d0000a940e5800008040103510340200c2c1400c0030000c20304041142d074405031a2500010000442c070100b0480e21f000158905006072000f50140480d14411925001850481c60040e440314090010421036582082d014521036200e005440c0c4001c3d084902150765501d00364065040a043e40303190420501c80811402c40c24480c0303500500b40400082070915140c0005821240c49584c0d0394040c005070040c00030820300907804c072411079040314003038407800e00e050520720014000c0c1070813444e0f1158a00234556242c2e500141242c0124024118010285d40c2e400805554000707400803030012413810b100c00c001c00d00d41070f885005440400c081c2c60340340920315000100194002c90b084034510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 719991528 1250 719990278 719990303
    0x110d14070e0c0f030c03040206070813060905060a201c1d100c0305030a02040312111c0e12210c0d0306140d03020703050d032406090605160f 62
    0x78516030308580e0b00450303004049450000f0814140c141480018207448101000001041c11501e40d80220b50341c542c0c0154425458200482c0103c88a16180c40303150001044500701045500d414400ca9020b04030540b5841090105515994003034585120b00100c42d00030b1181c48411010308410103001a842d56a40c402e4079220718440001c459141704043c3e002d247e0f84008015000e07000080c0900090300f5080c40c6882c0e40e00c1c1700d1282e02074422908014040c01c01c0c600e06c804c1d01074200c0000700d000c5102805445c420421001c041203102040040c150015003107107903a9541e81802000040300d000c0c42025a80d10301e542e50329911075000b0404410420b0f041c00192030310f900d08144140d0000c06c04916060001624007000740d440b40281c4407506114000060304441054003c1105070000d5038404265002c00d00e210708054020040700d01c1d402c01550407010410a013041c0582007a0690711603072104100a8208442151720b60808443c00d85a00c0908031964041800361004250482c492000d41103003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 719992778 1250 719991528 719991539
    0x3030408011e0606020a0308040609170c010e1605010507030c08040807050315070c060506190e060102011d031b1213050a08010902010903120e0405100e18060103110d1407 75
    0x14101e1420650380b00340c03410b40c0500c29642c0c00300703c3c4120640c05192a103006d45950070218002d00e43c00c54020a45c60800704403400041034440500b14403c0424000c025100c0000003182c0c5451b540d070703005080d1034403403401409198020405024028041d243c41441240d0550746c0186561054200300e400e544416410480703440e08000d00c3e203040c00c030f1441e4000f503030410701406400040d5101001740f040c0e8036a40001c01c070352540c07d60b0780086010541c03941c5440d07a0fa024042640da1342540c2550042d401c210300048071100508022400341581d10045182c8032820f500c0c82d2400c030b0822502c0d00300d400b62400d100d5140f480c200c00341220740101004540c000d49841e08200c40001c503640304045903414030516001503038014424078112600714046214100004008658a061404001e0780c094500030500c440c02c1c6040007400240d810b54650002b0548411401b0340e0a41560a00c03409594400b03001840080d05d40700c158a074882c809041a401d03880107995070b45942400901e01202c550000004101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 719994028 1250 719992778 719992811
    0x30506011415031504181104060f1202060a1b050f0106150203030a0902120a060e1b10050c010b060f030415020901050d0e1905030415140405040c020c0303040801 71
    0x5401d0300031240102c5030064203460750600d01005007003200c039600008958026880325081081e004a04c40f0788021641c01b2498080d1008800a0025004519007600032603040f1100b140317030f4281c5000300404d06001d0442d43c01c110f401c0d4424411603040004941c20500b03c0444802e11500c414482c402038000950049000c07400c4985590120355540c5000341c100d104981c002c03040700e070032208140f03010a100300d507030010507003103030305008000e82c64481c00c3c40b40c005000c0c1c0b42d400a4100d0807450256000002c400d80c0c03100f018008400410b60225425006044050041e801045541c0c0701c1000480c1001d01140012000c1e00f12070354000d20341c1c2c030003c01c002c100031850300c4110314864031401c00c5040003001d9000a08601039050345102c00c587e541031030340c02c24904218005d0046030780c10203a000103200d803070f00301d460303800a1282c40d80044070024004111405910185c0c2da240c600342401d810113151004000283c200300d00c0e040d0660007200300072110341d1000d000400142c12400000701c2d207040042407038032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 719995278 1250 719994028 719994059
    0x9141201050c07141c08130b090304060e0406052b06060e073e030d0f0b010f02031204021c060504030504050a050f030703080c0316050d30020d0e0703050601 69
    0x350b19800202d00c1c417008501449480400c0c03002481c00034959a544500781c075095020076409002c0100c1e15003040aa240004020030945c1c0780c968a0104001c100420700040d10f00300d000d4150302405400f01669441c0d99441c40142501c84000e610035520140e80324201101c0c0c441e00030004d825510310800110b01e401081d14085100141103581c00a0310100d50a1441200f07502000c50904507400420341001d4100241e9054120448040000100d44211103005207a4402c01070b010030244510b1075440d0b070002c0191204000340c0b402080711035a49908011062000341c1880d11a20848100c0101040a13489154482c0348a0344980740e45a00303000400801054980c8000d1007030441000c80f503115240441d00130f00302d0f54444182c60712001d91620305802e5018a40101c4a0070300c0c18a038590a1040026402100d0711068540322134101508a0b611011106d28448520f642c2c40300039044007a943c0c1b54000c00c05400300210000700003a1941030142040100d41c02030712943d000c400103005042ca1a803000c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 719996528 1250 719995278 719995313
    0x609041704080c18090705010f020f1905060717040201180306090c08010e03070f080903070e10030c050901230303130305010b030c0609031509030405090f0f0c0a09141201050c07 78
    0xba0303007910700301e00460303511b15560040c0350402902c100c18007915070080088004454000090703519110b0010b9180855584c081410340c2d15201d144080391101d40900783d5041e03c1c46084d1342c11141a5100d030010765441d40e0360311074882503040300c800010100e403051041e00c400300d1041c800760090300c1ca4229100e096454030000c41c11160010000800091120a00094080e0340f20003480c0d04d071207491f0006424070b220341d40080c0c103c031811001c2100c90100030b100b0b40207483c45035030b215100c19228000e008804909000d00d60300814405544c50006203400c0e050300416900800f20392401c4440d415622440f005a44112500ea45612030f00c0c0080ca0b09200c009070581c01a50014100704d54440003075139030500003411641055888001c609140d00c18405c46000c1c09016180803c40d0170b100d5501d01080c1c0c003c44907000300000e544045050381003403104035440d0003160b54492400130304059208010740071441c403071544000d900d80107000e080780a004280c492a0900b0900d0b8440f022410403c43c202c1c0f001750304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 719997778 1250 719996528 719996569
    0xd0501060e0a0e1303140705030c1516090905091c1715090c070501090611180f060d0f0902030d0e210616030207062c01140609041704080c 61
    0x2002804180030604080c005c3d0585003220118992482c17911040c0f044503c0500039000008411100940024004003503000c90340c01c801e5251350307010408000390300810604001415461042000140c1a0011a0865480350544444072a40398941003041009810313103001c5140c1d20310290101d008628460340c400003218407105a031440c000060600d800040001485901c04681c8100f400025071016075150b03480740382003002c0a5101701d240425044080022051599490400807608009211000000d0003420690406031168449005454010302d989101681c4d94807802c00360f5400c0000e00e101100b035031a141144103600080c818032003540280000400084842d0b43c00c0d00d82c00140381540080d24020a6a85c440992800c034040d108111000e4080d031700348101c005000c03800201001c1310041d211200740880303001c0b802060a803400034500f285841e1030f600010300c10342800c00080768003500c1000900c40340c500c0400c2d108200c2d005900320a9440d801880500580c0c00d2041140641411507244c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 719999028 1250 719997778 719997781
    0x2012705130b031903120606050702044a070f0f0f18021c021305090106030e07090b0303071a0105030115082a0409060b131401060807050d0501060e0a0e 67
    0x481d035134440b4500d0309000c00504007140401e1601c110003081070407085007001e001c1c41c2e175074100c000d040d9009102d0aa21036403800b600d60320644089551401e102c078482d15a43c00907868101e501680300d00700f03816664550f800d0103075030a00540034030610740684000307100456610b05150700c1d00c40c40803c80e00030108480f285081403050400210100644800f699030260380c40c0301302070b4503900358600105c5c00300c2c16a00214170328400307921240c089002d460b0b003a038001c1c207182e0340d8840c11420380b61400304850943d04642c00030b00c440345080e0072582807440c1c041c0489240491316a03802c483c5101c1004040e094040d40230040c8140d02d42030003640100b00310354403d52009410401490345540c0b00c0084071031040000210210908581800400e15110080c41081241c0150600501030a1200307041440340300c1c1c0c8554070b0301103651440355075258143c0b501e11554a03800d0403019286a80c001c1c03c0354050200a0104400300d4001b8021940608003994414458160b42c07002d124071701c1066000010807046500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 720000278 1250 719999028 719999051
    0x1b100c080c0a050412061b0212040302190b03100306112106010e040c020f060c03040f140a080304031707020d051804020702060c0105060111120a03090201270513 71
    0x2035400e41090009003003540d0341d0441d02c03040d80c507413107141c1c03100011481e00740c000780078462144c0c490b03102107074602900d800070300e0445401ca072282480d0001505402040c0014030150410210901d45409504800180c940c1c030740100c484c80340c0040700c0c0c071803195040700c00c10b004105e2980214604c0e0039070103d07102e0409006095220700081301e240c800a09089800002d4840c2e03115181005a0a20203403080220744051100251a014120842c4c81680b2910b004155186001c0045a1049821800051002c0001d0f07070340001e059140c9004c42201c0c4212805031300400c40750402180501d1003516041501081081c200306e400c031008003464103640100d08421281038110080300e024001c503004461121024070300040007401801d02c00b03900048003082c0100349007070551100c0d00451090b00d0301c0d16600d0150205075a10500301d0b10a44c070559081c01003540c1c2d18003d4000900951050401c00f5440c01f801d501080040d0002000380e0f1354004050041165042012030f9500c100f40300c41080c00010000c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 720001528 1250 720000278 720000287
    0x50106090b071109040c03140f0d08061903050f07240305070c0b0c19030b0a170a200114070804050112110d092003070315110c010203150105030118201b100c 69
    0x2b103809900b8418000c00241403075446c003c64030240c2506904214006890b41043c83da1010150384e82600c6101d105008200010400c1d000310000c450f525480010488404048010b8440a060f140612007100d24100000355210700a82c844c54040710011380310304049000d2031070705054513005424107140c41ca0380c3e02d03240c40c0c811040c41980d212081a020780b081d4003142a2800030042ca001d0310440a5605140072a140c144429141010980e80c1c98810810f000741d40761a4850b80c10b00a1020004100400c015409154584012114140300096041205a0200e510b5201680841d1100c0d600c8240404100f580380707070081658103840520074074908180c0031a0340c5030600e01016011a640100c02248408aa04048602c180c1d014000f41c80b50004020103020790015070b40700d4030031364100803903003a25481542030341c0c102c403c0c40c8140c2102d51340142011005005440e8107840060740c465008807800070200040c4000307082c0901d0710b500d030401010441c1c1403000b11090b1184250405500110701c6030300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 720002778 1250 720001528 720001543
    0x5040206090409030210151409160e0103150b030417040807062715020c06070c0501050a120c05040509060409170f0409060308040603050703050106090b071109040c03140f 75
    0x82c0d400141c40e5045040c242e1900c0d1a85103902d07501d5042c5100902424483d000241c1200d84004d64954542010001c12120080440708046000c403000e10400d1100d12821034a80094418140010600d00c04060490900b4454110700100c101c00410b10003000101c10609810503005010b031030a00d41028030041d129071b0702d44070304420030070031003210a02c0c403c21868031707039880c0c00151080c88032603070351041c24952a402403000e40244c0114465440d16042c031200707c4000720350150564040c682064015034441d0490000c0b0010030060340e4445190661911400049101c1a2100b03516a0700d00820001c103410010491030090741401650f1000030015030165101803400c40c0b041e80c6899031040720f10420702881d8005000141428400805e02c45802e000308151545540c090042d42d550074411b4040c0d400070300c03c110010301d24023002c10440e036002028001161040926803001c40c018000260006000c0c0c13000d4500e146130160170005c1150045040040400030f2020700500d200d19800c080c1c4a240c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 720004028 1250 720002778 720002797
    0x304060b1525030e12070e0906100e0c0a082701061e0e070f0c05030a0801060e010507051f090b0f07260403051605031c060f080316051501060c0302060a05040206 71
    0x5e07071100d1452080e00500c0b0103c090054440110000c0c03822107050b69481900f581d0340c0c5914116040f0100f007a0344d601013010710803142c40381c100c1d18106200702c003295041d60040445420f9040030b02000304085d61003068001903042007001040f09400d000a40744140c48100c1585031f24805503404121111851076403580c84055801c2c400c40d000d291890a40b40103a000c103000703105000008a02c030f445500701101d18169191580e400416820600040d116481503240142042c0d0003500048208100004402e0f040c5a070380c10003080418995841410004080c0c440f039020107185030412424540c0412001d111105100c0300c1e5101c100012108015090b000c0c0014013001070010702c5041c43d14031224400440c5500004481d48e5041000155000300c8038070622214040c10b040000a41001d41d070340c0b001c165442d03807014500d4020011080011801c032802d080f01e4070b0180300b403a10b0140161010550081041e9107507040c140d4040c0c42c0003030034254020081900c540c07504091101603114401a514480c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 720005278 1250 720004028 720004039
    0x6040c02070f290a05120c0408101d030c1c02070f360b04060f0b04090e0f060f01090507080c030c18060a120b03060405030702060304060b1525030e 65
    0x4410f03004141100c180d514020b83c060100254854140754450010119201c600c402c0d242e40340c0f207030074440da254403032407142c1718155112490024040102e94010300f00b030201c07412042a110007020ba25801d681009842c00303095040544000c44110781c00450b403111245a00c0505100713428680d5041c00038800e40100210005094a05070445203c652626084480c0111703401904210003415005820b01d181d000d40554140000000d9150325105400203880d0300080c0c850078141014080c400400031001ca103141846850300d5140c00c0c000074410749004603c1805018003a44c1058541002d94cc800b0f4803000401200c40c0401ca180300d03001041d642c01140b0340e441c84c1d03590102d1a074403e103480c4ca01c08003540c0c06000000e55085064101c0001f414107401100103104480d00b00c4205a1142ca003214080c2154000f04002801461b00600a5502500c1f4180c001358009030700000c80d4550041d034241c503550020005000b115800e4420f00209a8494240521451002c0b5039000b40304c0920f103250300b8020b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 720006528 1250 720005278 720005309
    0x501030e34030203070f0501020d0c0b0c1e0403060e151302060f13060906021e060601080613090b0a050a05060a030b07051c021e0708040e1509040b06040c02070f 71
    0x1141030703000004640080880d24599181c0300c5210501401c1e100b86030142c0b00d40710414140320b020745c54410015401002050080d1380d01c01c1d0503510f951000c403c0c01c1459001c214001e0145062801920145000d500c00061074014044428901054107814540c850440340c00c2282c04d504841d5102086941540d0054031440300c50f01e2030915004140e4035801d8400c00791004501c00707078403c1108080343d07000c0e0308549601314140406100d81602c40203411864004070000788455000301e003166001100501840d0400140904610031245440012a410301e040000d000305404580109034110600308400c012908102d80040d580c4541c0e441b0041c954000000010242806941601e0004c8001c003017100c1b181c400703050000002d5010790506c0900721501030007801402d2000d000c3c3e40d021a40031210918260921289507801c44000b4843c0641c0c0076100d000c0d8000b504c5043d0740320302480c441c850702044c03402c14800708019104100d42450455000b032808000320f030784c068a29402c5075601c0900d150700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 720007778 1250 720006528 720006613
    0x50a08130501080c0d0b0d020d051b060408032203020a0b070b010e070203180103180b01150206012313020a170105120318030a080c030c06010b09060d0b0406051201060501030e 77
    0x10f6600c7c402070b5100150308040ca0071b114010031080900d01c11076410008140c050820411140114010f180709540f0a014241c0d20320308112150758400016041d115901d980c9900050f44100140c105061a000108801040101c1d2080c01409070810407101034180c60302c070700d00070356034010501e10900d45c030101d034104400340e406980b15038165070b194800100090b1540c10b1520b0108028030801045440c0268010100c1c2d10203e61981600e459843d2011a00c0f1070400c1c4046154403030303150680c8090ac0c11101038100e00300e48010110444a030300d41c18005800d0513a03102522005034000d03030140b001804011210350012080b160542c10b54000032900451810109181c01003100c8000c0c902800012001248040007003d007104441000446842c0da8a030803072900702d0f004421003103400c8207061081100155040d00046444030001c1d00c000381c080c0c3d5800000f034421540035030b1f000c0a03035035031749041c01103507814000d007944034500c800200600300814188001074680c10084c80c03c024640c40401d1003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 720009028 1250 720007778 720007789
    0x304020a030c140f0a03380708150103150506130b0301091b0306050901030b04062c010b1e0909070b0706021209190816050a08130501080c0d0b 63
    0x80c40c1c00100c060b0055403140120a903a44007904003a100d81c1c403580303242901d450545400410380b40e0000d48950100718420048070045010400c184290a040d454644844039208083d032140c640c542e1018598148150b003440700140e4103003000d04150404450705102c100110150003181d4080e5107803076503070141c0e00c810700038910260061005d1060000c000100011603401003106240112001d024003003050005800312400b522545402001c90001080170511407800c0541c400c0c01000c0108403a9500082441003491141c0403c000304006011810212024450080c8580040c0c0342d8240b40340d10340701800c1241064611f4188540c0f015400034201c0c10003800203000620798500c1d290307110b040615101c0083e401c50100d0341d40308041040003030080e80001500d41d600e500c1c0220103e200c0222900d41c500194803010030345800e01541c890440001e5070401001c003106c1e014a0450f03071128050742c44440c0d180d48a5011504010154050042c01540d5070221001c4c200c249000103801d801000100301d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 720010278 1250 720009028 720009049
    0x1b080705070506180c13020706142a0c06070206040c090c02120a031509020423010f08150a08100b03030408150a091e0c0801231f030c0e07050403080906030402 70
    0x190041030745291b9001c14002c5030044c01c80b5a224040a01490f0b070790004840700700004a5900b034044100c400f4600d020000144001308440c0c1404206140001042000740380caa420b81e004030059110742d040005115081011102400c0c0625080c45450741c0480003d64a02610855582e60400014222501c1e0f000c0e900c1f0741032400c103103080703000c4065031481140000d42040c442e1040c400e20780c01082550b208600b2551914040c142c442ca000161100012200c04d00300904048801242000c0480503549034240c050040071140000c0051004144008080d50141e06142c1d009910500090105143c0403d0559401c0400f08801100303942c0d10400c88090040300a000e444002624800741c00d003010214501d1a0758005c0c242d60305030950360800182212544410401a06401e954a8107104060341e035998011445e603030812840080400d8180580c01c0b681d1040700c0007440e01c0420000790390851005903101c1400d0034001e040c10b2468542c1c2d801e80c0300c2c15100c1403295800100040c2150b8403c41c844 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 720011528 1250 720010278 720010303
    0x30813051510060504030201051c0e0616091a090d060b0607120813080d0b0102010603060e07050901271d070602030319051005010c05101b08070507050618 68
    0x9901015141142450303800098804035040e0384000b5000c95114011412a021642c0c10f0390356a1800e84406541072030809401c0644904584543c003281100c201006400d0043d0404002c200c400c034501c0310701030242001030340104900d040049036004940d194005407402280295203848419409182c0a00140721711800316622080c0410740d0360034412009a0a0f41c004000e8a940d00f0a48601c05141c005c9034000758020109882000148814119500807450480040c0008a6403584030766a000640740349500d011030701d40c0a80360801076890002001e500520310862006da11001000040e03044414114088621580350800815202c004032600d00b10020020b050b200c15548840b002905c0ea403055808015070401100071140146951140d40d0191000ca0901c424452404c0010b440a8007101030545103030107200d05e03a03200c100700d81c02590b001c000021a19010001c0b41140503142c240060051030800c40184800000921b001800c02d80040c02c1482d507980514411072003520380510000035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 720012778 1250 720011528 720011533
    0x3040311160f1805090c100203122406030c0703030527070801060f050105070b10120b040203060109050903120c090a030b060307140d0303151517160c03081305 70
    0x40c5145105000000d6032078400201e02c0a900031140f52050700d0301a180b904041d00203183e40e00d06842c10001105603200c550054a04102c0a0002565035560840e4008101c0070603c2e41c0010f0100108070141c1110b108403036142c154200300300c200d0110700400c9001400d250355180811040b560001c040703040035452840000304100001e0ba2a9201c1c051485180030640c205a80403d40041d443d004500391101a9243c0c0c1c1040b0168442c040b0040000e0034070608407001500104001282c0c25248400c00e00600141c81541414418103140070030581c082c00400e4503150500c144510040101d071050618141140c044c2c1c1c442d040c102485100e1500d40a41c00464490008200803400c0300c05c512a55007181600d003815569030300180180044a081940800f480c044100028065840303521615128401d06035815218800350030282c2c0c0031500c034404103e00e82d03c556003010402000c1513200e500001e40c510703240c1207224003401c0b0f014540ba004003031001042c002a0b4507901981020721039038000d401c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 720014028 1250 720012778 720012823
    0x608040501060b12041401110708091e030c010804060209041d0615180a1d0a0c1401090b0c03190302090f0409020f040f0e030a0e03060106021c0806030c0d0305180d020603040311 78
    0x40000c56940545c130003900590550010a3302d00c0105030f0400880e900140242c4801088030004658203540140104c0e03031264280a03489443d01e03244100b500805000c4c01780780c204403038810325511f0a00010542e90080e000219580c0468890042c0c100135007003241c0400001d0349450071004003500c2240c50351600130203c0032489480c8080010469070302400341d00400d40654840769081d030f03003456522000b07011030940001000342c0c000d018003c02100c8030700015282051811524061100314050800000036004100c598052500207170402d00800220b8080040081c0c65004c1107a1485454044e44101c0d03450140340403950094000c001c0d0300780302c5420307a0380d10001500c0240c02c4050b403910580c06403282100200d402030001503202411120b02c01c00300c0c0100c1b4a4403080300da2020040c034807a00341c002e0f001c003244c0d01d44410908021040c40782e21a40d88402d100c2000030341080f1002d800c0c42c410a9402d07184005600c5a504490308590145800c0000e90317200010a49086034a50202001801d01d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 720015278 1250 720014028 720014033
    0x1b03071e020c040c270803030f040237121505190905060a0b010212090d15020a0825140f2104060b010804020306070c02010909060608040501060b120414011107 70
    0x98940312134170a4048402913029440c00103811001d4036015406d0954800c1003c56011426040b01c554064401060111607800204030020142041c44e0b0080a51902004440c52071a0300b044140c0a070229044e80841da000c2c0361203141c07000c041601a2702240d82e550f00468042081604001d4401c12448402c2c00007400f540b810a6a5903021540c404041d171900c2100d840ea03600c00300d0880c1e10080c0020f44d5904040c0176208121040041e50303c1168610080c0300c1d10884124140040c00507c80103446081203071402c00c401e01c22501c01840440141c420580101c422039400c030420126010320119019140d03602c4181060507840f4520b80c000a80032090b0ac52a80700940f03090062245101d104144404e12108005445402040c0c4001b07503d0b404c90400111003902c218240881c503801403400701d007402d503192400c4080b10160303008800022109030402080c41001d0150500810003014420b20381400c000381030490800140c002460201c41c00000704c08114250005801307000141c2d0455075404c25807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 720016528 1250 720015278 720015287
    0x3040504060801090209010b09041e09020111071a03130f0c080d08040b010b1809010618050d05031c09080a09210c05011206030f05061b03071e020c040c 67
    0x51086511890900c98045000c00041c0101603605a010b094415264241900c0400c036410100400b60000d03512452540c02115503544030b524450740c82800291f040715400010301c00308910a08000a6018040c1000307500381440c82c40b0b84001000a0041d181d0700c5000034800c25400c4103002501514000c01124280008030141c4011a0011011a551441c0c0d506c2c060341d440600301c078041d06d41c1c524035004004800d090b9004054414040c01c107426000010000940a00b800381c0210001603000206010340d10980030480000c0c10302100c80300403184542d52030a603203111b8145000c542c1440c26401210f00b50720350300500711481d403240240303854000070031004010740d50074481c4940b15a0742800c006001c0200014106503150000e40c071000c080d007400d0064503031521105c013200c4a66a1550000003041629403004841c03031080c00513024505000b850f1040012001c6800010103408009001c040ca07001030001c05038920f204100e581c004030340e07a4242d0401d0022035003243c006040400001c0030a910 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 720017778 1250 720016528 720016537
    0x3020d020f210f06190513052a04090e0309120c010f11030301060c080d0608010c03061e090b060403081204020906011d19182403030207090e120403200d030206042003030c03 76
    0x7a00e00c1070094400049d84c00501c1103c0710140103001908000508c89620f56421001c11100b040040364500b21400303012075070700518203003042625000341560b01081c0d83d1200c0324600b0158185803a1075107425050f10309459100621411040c401c640c0e040d001046840800d4030407040302c2d01001c010b003643d00d0080301c1c060807500c042500041e18201010403683e45401c42c071840444204810f644140c200f42c0700200030040380c03e0007540500288000800100c0325802020300220102c142c1e2014105441070012516010701098140154000c0b1041d013261003e904103c201c03030403a00c111002d00b2882c03501c071482d80c5981142070b4800f0b080110b506412003d410141c0c80807242a07601d2169665186c02a00715245400000c1c0140c100c41800c20448843d17800c44440102c2c60419105100d031038602c1c0041d550b000ba403040300c840424625412130790380000100e04a0718000e44c1c07a2040c0140980e0001c3d11040000d000504515044241007003280280689035a00b20026085070b540c0c3c0601084a55a40c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 720019028 1250 720017778 720017791
    0x50f010e0105180a0311010e0703030e100305040b2a210117070b071103010203010608010314030a120c0c12020a0611250303020d020f210f0619051305 66
    0x306008210082c041c3c0128801c2606240050000801950f800300d44200c151070b4032500c50741d00d400810648002c180307d0800110f12a89031030100c201103070300b0301c1a84890742a80e0000c0c0b47c5840100000300e0a94559990705c2030301c0643c1d0302844c40c5000340f41c86c1407000314000034400b2000400c01e03070b0310401210700304030a688040807440020f81e6a41c0503500380000f0280300e1080c2c2c0c0c00c62102001545000c4000d00380c114030601a485900450310023007401c98100741e000c1000142e07000d0040003030040e4814054451004c1002951511302104409030650300c01210b003849040c0d66200000c1c015201d142c0c5a159241d004035404400c86411100035034071008601306407111840c00900358120031281c030481d180f020b020058801c4200d4020440715003410800030030b40074941c0130040040c0c807100e1840104840c10a40b42c101d5103889884081c4032203000490591803051145200b401001c50707080c5106036021400700c400758447c1c140401c00311a84a046d51100e5000f00400007642d8041c3c9450308201d20807603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 720020278 1250 720019028 720019031
    0x51512010906231c02030a12020c010809012a0c0f08030a1503110609060c0d1d090417220e0a1b0806271602100c050f0306030a050f010e01 61
    0x100c400c401d881d83c500c461000d03030300200d20310212078020340900880c0d00a5000809440c0001015250283c9400f045e103138080041c0c00c0204409519a00403d805400a00b40d00c000c204545080c0e00014050951001c49071401601e9010004220b10480f40071401ca548801c81c910801c801f4544522075070416500608082e05019800403c0c0c2a0b500140c81102d4220700559400712012090140540c404030b88241c014504000909a00d44204018240243e19503142111802400c0034414180c000d00f0035244544000b9040c00045001300e017200c078504d01e480b602c07540d036417106103142e0307001e80441422200400072281000070080c8045003102d20a1001030400d1006e0702c02840408201c0613090441004661041c000c41d4150610581d050352524017502d0f103031011281d4080010290500b00c034410451262004034040300359051000b448103280c1080107115080301c200000e40140205140541c1c0043c000c070005009540404c61215096084800d440e145100d08520310f000e081e45042e20746103036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 720021528 1250 720020278 720020309
    0x9020c07050a12080d24080a03020d0801140906061905030f0a05060d170702040603150c050c0a0f060212040b1b16200a151704020a051512010906 64
    0x1807002c00c054a0f4080c0e0f01488039440d040c0308241c820001d180445690a00c020440d0121010200204185020300142c4006200300c20130f6180080c60310122039105010400342500401c080d008515902460190844914031540d503200d0200d849806810055106070000c0c1c3d6052020355040001140900721030001e81000340c0d2440d00c045d065441c2500d015400c000c601e43c003c40403a450754451610360b220103406070715107103050f000501a58140e42095a0744200d1121110848010344120100c001c62070500c142010741d001f21041c0c03240c41c4600040c00003c44000a03504110b8107504607800080c10401261032070a1a051000200f141140c0498100032801096213a401d19003040d18034250f00300e90441024061a500c0102009040b168540b8079014000d00c55034568a80302004082d082484c034160700001e1000d001082400295651160f5059080500c030158458540800940d5400da820201c22420080c03000d006109810741c2000c0c980c6200e0002c04c0100c000e800c40412075103242590a00e6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 720022778 1250 720021528 720021539
    0x70c050d050912010603050703020d03050408100e010c0f09060c060e0102040b220e04030507210302090f0f030a020d3011030901120f0207060207050d1e0503040602031009020c07050a 80
    0x2c941081c003014003d0761040408000525040001c03500542c400d23700241025929401d80d46411202880b5081d0740d41ca0b2803409540c00310074840c4e81840380c0c161600070982e0118480c041c144000d00d0113a24101303c0210303660814000786400c10504141680021955284d031902c01c03011030f801ca903107c841c601c2a449008114900001080c0042e5403680702422002d850f80e84d0b00741c84d40c0e1301c960702c1101c210490001c25066042650303082500781c00c1648000d65201d2101c07003084082c1009410f81d5100d02034030f80000c130a44d200000d071002c0541e8141c071b020300040351a081031151200c0105000c020031418060070310b00f510307841145c9060148180caa580c1d414891524241d10703800745a81090003da1050401400310060f41c00c0f0300390580f440d010040c03600c4442d032030b41d6044ea40005802d94a80d0300c4161004800355001c10100c80c40c880c03d03c3d130512841110503000b4003621025001400c002d8003c004560001e49a0901500808511a00315564010044015100c119603c02c6034403a00321a21300145 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 720024028 1250 720022778 720022781
    0x30f040f1401020d021903030b0904030c1106040f0e090a0f110102101a04110d09030305150303071e3f0f0e0108091e030c0123040605070c050d05091201 67
    0x1132002d06500030340049004200e0848480d500d005040c0d0401d40c9545112642d52103d9900502031802076a4000041c101400d01110b0b0564003880341d401003804000c200300c00f0304607052400541d050461208078549401d08542e1030a4800c080c00360004000042680401c03000301c40403641e6038003c0e0280e500b50510340b00c80c941252040350041c54040102c1502c843c50703103417076030241194005003018503090a8901d459003080340c0d000c510880220f81d4501c240b01c100754002110600700386045000f0b42c5070085503902c040814520030540b02c20f16451951160402284080100250b40700d110788920810404a03607070300340701115502c008150300b40404003d60a2152527080e201c42170903200e10b0790718081030004590100703000340080b016000d1488004030b10103003c0c00082c000c46682005684800c2800800e5084455500e801000b410251012911405242103100c2c3e1058111130009000d5444000c10b80c0c6480310944010b1a42c011410307041182a0050b0240c001014143ca035203d220380b4010340e160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 720025278 1250 720024028 720024043
    0x16060c20150705070614010b040f05030109080f07060204030506130b0f010f05010f050c0a030c02152a01020717040603060501090e0f101836021002030f040f140102 72
    0x3911507800001840b883e02510042466521503680062003c40c1d0300e001c650219400c0e000900d1580c00006c01708507540ca68607180c006054114020441c3c0400340c0c5c2c950041b4402c45030710b90108a0085581420302c040c0d903054400454010069070800c2c5007640030702d00900803001007290a80d010b940885c000d040c0030351035541650440d031070100d15103081c200150b803a403501c036443c1c201b000020080a405048140403105a0521948404884505a1040000c1c581d03c040a107102c0c003006000c00246100c508001c0c0d1460a480c0580c0c114a0340411070b05400382c03003034803409080b0b101603048640703401d0f102500070300c12078200d5941040b115413594011191203940340305884000310ac0a01148040780c0725078540e80c003c4d4041c0400d15120b40d9a4032082c110b0842d0b58600d490a603030b1400d080c005092854241d07030110015a0381200604500d04206211500d075540c0a4014908941d004c815a402001282c9038240040c5d0381548603503489241039254510342c02144801d4002c1000c0d40595400080c800d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 720026528 1250 720025278 720025303
    0x21030e0c0d08090d1b0302010908150a1d031c0b0414060f0a080703050f0615011e121107120c0b1f0506040b0a0306050f0f040216060c20 60
    0x76240c185a488000803500101d09599100028040d110300141d608080c080d203456003e444140901d156000140c200020f0b6808008150442122140052034018034030b6406400711500182aa00c002c6030000c0100e540c03a4112114440042c0507840904408909125901081800d2007107035181400d02040d5450306044800021811020503110300d041c542c2c4075081400680188086580c802d1410b150203000d60080c0c8807500f0141345030b44102020700129500c60082c84038400019920705c00241400e0403040740c2858452080e440c10030300c62040201821036002444180422544c0d4114a2034513032051200311030410258200d85109806202c508860a80021443c41203540303a41d0003880349840b4000013204401c5036100030521765603000160020f0718100e81843d450b40000700740941112600c0c2c0103188165054151007a0f03541e075148404c1045002560050b0321000441c1e0503240ca609041802003003103041c40c101c119450303401a01982c2d0142d410030b0004245401080141d154115100e90 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 720027778 1250 720026528 720026539
    0x50312040b18030a0308180606181005090702101a0d0b0a1b05041d0f01062109121403010b040b07031803140f03040e010504150321030e0c 61
    0x10448010448040d0082d04840074901c00001100741c0000c0c14014951411408102c0103000d10480005041d005074000780094010001402d056000860301c0e1154a44511f10560100020300726034240c200d400014000500088003a051003e8003a440c2c0c03110901e4507400314507060300c510f0b011f807009000070662000607154001e00455510742010f200002491908140e171901c24000c2c40030b4142c081e83c140580c26580303103038940d820032102e80c8645450b442880001d0b0002070501504500451409044901c0c0e410164141d0052a1074000e003d10010500c0070020b1400710034606004003c081204204501d69a40160b54004c103120340c41400203000b086407840c400d0200340f20525401000700710031402405e0042444801c0040080d000303107240c104952000760481c0f080c9494004015030111031030603402a50525003080812100c901c0148102071166403070758800440c1142601c0107502440d0440b5005c40000814108038070070202e046031990000e860403507603412696000c2007118200800411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 720029028 1250 720027778 720027787
    0x11070510030e0316084504090803010b0717040602030708072d0c09020f250506070807091a07021e040e0a0204050901020c12130b04170106050312 64
    0x110010200030400301401c0c0300400c481c040c0898061520f00e44240301e022a90b6442e481003c0c403903d0f401d40280700200b044c10311005d4030480d6503440301c8040c011007012006c041802a040005020b003000e0000070700540400400462030030682001041064024044101071450011101045102e01d00c112401a007042c80700c10002150304000709007041c00b80020b4083c0100d01d00b0b8a4216440c0c00080720546001c41014408020350028914001c00c2c0c55041142443c0310951101c01511412a18486180031030030107115404e03207504030b00a15500403040701c3d014988654058a040030540b641400300300250f0b40055088101d403481d41c085100c100c0c16a041c500c182d8240100b20500340314110028880c0c09668055490301c1c4101c9000f940001d0080680710858014071040b5480070b086008640d004214980111800054034044d4291540300c041c1e48203090005455841007035000201044d0000400040000440034600103220010008002d04d6560b0002c150390391070100c7c848800c2c06000d20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 720030278 1250 720029028 720029059
    0x140909060f040f170a02010c030b0a050109051504170303220210030c030b1203070c0e0609040b0c1614060703060e0105060a11121309140a02160501110a110705 70
    0x409406409106451015619041e00c61136180e54002a9540b40180c3d510100442e009034140113041030500c3c292145000306051400080c00b15245d40915401752022144031052000c17003070304683c01001c6459020003068501c84c4015180d0b80b0940725001c10a012000b0301c085031a00c000d0102181754018010581c60405402c19409030910700e8040d41413695410542d88580c44a0041e09840490200955518102407030501200c0c6880d421201c030481d5030008225054035004091070300640c02402d0880159112195070740389200750b62800403d4a0140c40f010f0410180a550341d00544540c1c0a55600380d49248007103003216554851b6011540303400c401003100d802d000d4000c101880b002d190071014003032240011441c01840100d11100400001a0300c80102c50901d006405070090010a205410f10040c00a00340710024000140c180e60018803103210304000070f2802212a803050083c82600c03840301c11542c01d5000305403c8400300c4c0444106118420340820380300c0aa4a0080c034440422400c10f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 720031528 1250 720030278 720030293
    0x9030607080a23010602010608160e0408040b0706050115020610032006030907051c050a060c0516141015120c030804080607030c030608060417090a140909060f04 71
    0x342c15080703883d60b10b03020052208074400407000c0d11045102c0c0742d5a25458010000d00310742c00d6520410080d00306024100000c1a00d1266008840d1988001302e00e03a1201c0c141280780d0b114591140440d1480010b000b4200b241a41103d812a40e40b01c880310101442804181d80350350044900c11030501c0a4441400020001010085c0d404c4c3c01c0302c3c61840c05031101010400751303031094075406029448404e00f0820b0346082301d6160403500072029075107500d00c5140d990350f9403040324020040c0030075152100d00b451a403107076040c1d0300560308994010190081600b00406140c1103450550074501a0601e5100150060301036034128101d82d01182d81024a00344200740200d03c2401d084510b0304071440000042089003000c3c10244c00788030081d10603414010409400c8440c0380300420140343c1000c1c4200700c0444085030041e4403580041102101064803001d43d01248108002e542d8001090b03440440c458045c030000d08401c0b1005e480c00102911425911a075a4508407070300054500e11030001000100300c07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 720032778 1250 720031528 720031531
    0x5041e050424050114011e0302301005060421052401060801080114060103090606030602030c070b0f092e05040f02090718050105161209030b0a020903060708 69
    0x310308507100c4410b080384030000015242050000b003a1200f0040c884e5a11003c4100e010f039109003442030410b0008807031010b0940c1c01d41006c1042c16404501300c000340c003403400048011050142c82e004501d0000355000398400b0262000300d1035050300c4001281070300b0014100c60660f024030b4150b51016040d0804a8008046150200c0301c9000b510820544150004525183c0580c440401c01c3c082d810600000c01c0c085e016441703950280e050503c0c5a40805004003c507420440c02c1c82c020030001e0140c00c1c510b020f089240d1000700150310000420104401d003002402c846403107158078081c60744070411601c80450040d036010f001500300c1c84801540c0c0d0a1440440008034808101c4c810009444107010100c60f01101e055a00050560403a0118940081d04d99403203009820444680310381c0b00c440000d182c1180c050036046c403900013460040b440300540c5030074850b0b40c0509045a8200b480f480102084c2d094402101c80402c0700f000704402581038001e90f4006a805030060403180d07540342003103a03000340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 720034028 1250 720032778 720032783
    0x40b0c06060d1e0c050406080106060f050906090409022e020d0203040e0a020310031b03140a0c0b0f120c090a0509040b041e080c01150816050d051e010b010905041e0504 74
    0x213201e5002070180c40d607000705401008020000101c403890000064480d0f442c194525017040070030082c82d14180d54903015a00002020f60f000103418000d840419034241c1e540808142e10054103041552172040f9010701d49041c801b9500795492200c2d000703003d80e5640641d028054103a0040000180280000e501450b801380782c10f604040ea07980d50b13845400d0903900400d000044c0058510040c0144001c50b404240700e0b6030074000401c0b08040030f0b1215840300c1082e00178004096000901032401018000c10341d820400280b060080c14105500480706591110100a0080d022214001410702e09414018451508482c2c06e60240d51140d407440c940350040c1c1ca0303400c850020342d4030040100c0e042c41e018103041c04035080009401e1014030400f07000380156034801d04403540300a0342503684805403a9038008442c020340f42aa1b1555880c0792982c1481c2100c01000c0ca503591107510400604815046010b4080c004e0701c07403041150701c0d08280002da03005006294100c040e8032034800182080da43c80306030b03c10b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 720035278 1250 720034028 720034043
    0xf0a03110406030c09020409060605090607121e0206040210030507080c0304080d060605030a05010b04060207030807020f030d050a090f12030c060f050a020705070510080c130308040b0c06060d1e 85
    0x9883ea50340c0701d00790360184c0188900c19030119050126068602c03841000e4a9141811818501c11341c000424a10506000900c001c05a403485d080c154000c1c140140c4404e4480042c3c0c1e00002c04400003540d03100f003120709a200d00d032032012003400140030384034490080c540d9a4614001e40c4d50100d2a0b6415400900220340014041010103410001071180c030001c0c10086e45c4d10740d56801d004440d00250b0318107820814a07044200410080f0580005481d03044a0303201c0e110380e444008500001d4252107000c002d2a42601400c0641ba801e507074440000c08604056881e403c42282d112000185605024014000c04000351074a500c086400b560301411404c5c4510004103400b610842c0080c02e070352060710a0181c99401241000c02c00070207100800107814183d469000c502c600b100c004100d85000707801c040001100080c00c0035031020040d1b0700409190080e621507a21a52a60300700b041d50303c40106481240580800300b5031900d02000d00345203a03a0030100800718010391005604090000301c20455011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 720036528 1250 720035278 720035291
    0xb0103121b0b0a0b1516060608031317060610080c130e06030f03160f0503040e0c0310150905010f02070806010f090e150112020d06090506090c0f0a031104 68
    0x1000341c00032a1011510a070030345202070401005a40507507011300e160501c280340700c8504c4000c21007003c0c26039000c0d585110320903070880c0007401c100000300381c01c0e0882c004134000015007103994184107498004444ea000c9440044003a00c608a64507018190f43c002da000d00500700d61440b80d407054042680040081992900d440300800701644d44401b154419070034040560b08004d120f10b01804a410000c2801010b11714218110080b6007501c080060010a068082000c403024000e080042da400303403280c9070f01c60341982410704128820760411120403c3c0c6000040c400701d40c0d0211401c00783e01c1d2100e00d440e0100c005050030010b48240300c40d408034900b1072255000001303414804100e842e0003441c9016010b5906400c142105080c0e4004a07414003141e8802e1111103021502d9840640c110361244d803946600c10405c0c400a6170040710088050412810410360300b060050100d6944d01a594201c104e940e02c0c0301110a10481d02188002154401104503003040842c2c039118441050f0800184002a034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 720037778 1250 720036528 720036557
    0x402040b01110f061b0f0d24030c05150901050d0b04180f15020901050d200a05090a080105070c150e0303091c0e0a05010e152d070b010312 61
    0x1024007211003000f41d07502180a209000111110710403460f40c0740300b1110302e08a480c040c00b482900c240f074454030708aa907900309450102d1481c20002c0000da02500d41d101e4503503032030405105501003405890b1040340e05d44013811114a2550894a00c0c07401a144c1500b084284620000100500005a0b401c0307500e82c00b071010401250301812030f07414421700c03801101840504001c0e03148540309294181c0288100804200f50382c001c0141d8102c602ca560300801c4013a4601c0f043c51100c103079021542c014620109038402c285400002a1036005400e03070700410000e503100d070098240d43d0140c6090700854a4004010003180302d01009411601100902103591510307414024a0350b84204d8100d8002c0d0842c7c05403482c284151014400d0486042c50460300ca10505400900c2207205441058142308400389807883c0d5840311040b0803540c041190406490f0001c102107044050880244210030b1403071504440380072080642920002074008c4080324a580c00c541d1244074410b20000c0d154188001c3c802040d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 720039028 1250 720037778 720037783
    0x50913060513150b03120705100507122f160f12120510051315090209010e03071208030601051903060509060f011409011202070b040515040b0402040b0111 68
    0x340c10803000c006000340e42d9060000101800851a0501a090440300c00c801d80c1c000034aa210090503201050741d80c1c200d86082494040d00c8040304512a0500042180c00c42e0040c800c0c0544920940060144c00f09074201a005603a4000e0200c0c0c0c0360364510505001e0180311000381800c0d020b5142c903001d200080d911010040581064215403540040d0030000d84558031840c1c040c1c2e02d051040c41400b150401c0c580320854981c00b40a0503004242005c0c41f2076080c02190084400c3c0c0290b5424003036000c1d101c18179100698400c54845000c207810600000c1c003030a0002d9030130b040310510740c8111401c2a0a6498a6440d0b001411503810010180200600a40f1400031034080c4409500d0010f401340c5040c082c002c182c0380c0280f00c10300c6075403804644101a60014090745403100110300c50b66403200040010b031030b01c2c641044034121551006c1000710800c0b011007e1140203034014001c841010b514040840b0004408440c01070124855401040c01402d09030030403080c50b10141099030940c138401f1071407131 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 720040278 1250 720039028 720039031
    0xb0a1a060c0102030601090f0b1903061508070908031314060403021507021806010f2007080730081606020f030a0b060f1b0709050c0a0306050402130509130605 70
    0x40745960000900c006503800c00c00f400018109641600585407801d805100580942403401c10704e08403140348442c6141c480c1d0312601c082d280302c00c8480d020003070000f401003408804462a0010480c03e0001180d28540001510010b10f0341110058503542801001d81d10007410182c046d400680030f0002000603601d020303070446010111342c1c0706501c842860041140c449440c200070030140c0480c40034031080340d902c45951031000c0b000d82000b40d4100c940710f9924000c6404401e84810602400902103000a4042000c0701120180ba05a00c509440c0d4a202c1c0201c410b409452001c0f40d1081489600081085014204400880d005a000c1c9541a124241070380c2c0701510104500600100700a41c8022620034107180142c16940700b428900d00030b65148961048504011072603e075400652246801000f41e60b024080003801800b003402c080c90300040d10b4203d0082c03c0c004c241050700204480c140780c401c2d51285140b604212030100c3c90302c024000c1c0f5520151220440480b1118400041107050080e81d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 720041528 1250 720040278 720040297
    0x19050301081b211605151602030f34060e090c13090b281202060415020f0f03120711030c07080d0f08040c2c01030b0618040b0a1a06 58
    0x20f0007003500000c2c42150011031071704454804c0d1041000c8043e0f901c0307030383e040e240d18800880b402c00d19443c0a00020b80b40040010140300e0310310903030504c0640c40c240c1302c00e00c0001109902500981c070001114444c40007009018050000700411015203491404221107508200c1c03e5a200d4601a22412200780403502d03130b000680136640364000902c4500f480e841c2c200c05d080030060704840c8641e82d41e103200791540091068003c624100b0004000707555503442181d0080a00381090803040035080d802a48803c0d24106100e02801134100704803a1880202c211942c212502c40c5030011591500c83c05e40790101d104104c007031544000d2001c6a8071000402014020301442001042c1250007507a009100d943c01c2c0c541380d01001803140c02c0c000060340030703c00c400903618a03585d601540d403d0f0349100c624240c004240c2c980306a100400000c103009030100214020442030f03807a54944024130301d01d404000000d4400521281d80ca00004514002513030041034180c041d00c60140760015410300061080d0403850341d6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 720042778 1250 720041528 720041533
    0x3030c070804170d0809010c080a0e010b031605101706041d100e0106061b06050912040e0603190803060d03050c07030c0f060e181e0106030219050301081b21 69
    0xc2600c0d80c01c40c045c0360344840e540c07009020724009004010040407015204a420035118041150008820b4110000c402c03070150484140701021255002408082d1086900691003d81c005400502c600200300c0c005070303c2036109074151558030030300000740b0164664005281191001c0f100601d02808000f221041000001c1085581d015180e400c440d0540d2010060042107000703514011103003900380c81125080640000c0580e208124035040c42c1c40c8111500c0003800004020425464108549006410039800c444980f5401080098441003401010b4251402440000c6c014504000101255840b80c034001d41040f504401c414508001500212051142d901050001c0340c0c08000c0e110090006140c5000c480e0100c4020683c0303414030550800072441508002240302034070340d00c40400410072410200d00c641e5500401002500641000307021540c01400306169144184240c0741070311004c0700500f0304405035002c2c40410703000003460580c11022303032034913580b41c60720b0300700c41c62a6480140017 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 720044028 1250 720042778 720042793
    0x11091e01170603011d0c19060221090a0305030d05010b03060612090f010219080606040501051903090f0b070221090103090318121205031b03090a0f0507050f0607020303030c07080417 80
    0x100001070240c0311458002c0303000e0080411010754001a9001e24a102e5130100d01d540c840405540300ae4031550310f1440d00286000400020400000014802c01850100801c02030b602e03107a0310011440301b41d51480d4002c0f4180280c4200d800d40d200d01c0d68101d000041290005608030100c2030980e08003107090305803840c2d0a012951115082104558840700484240c0d15013800c090001c1c026000e42d9180c54540081c021100341a98004c1c0c0c00f030917642c0c2e0000c52100718100360b403510910f680d0007140c40e00014011001400072a100c00c0c002179001d414050300e002e040c44520b100440050822690135820000c41c00116a21100c14000d400040c102510790030400c1080340c00c0840c04406103516050821104000b004008440103105004001c0100d215964a85540b500545007180b080405041c0c8c00011021100f0400e00241c118100c42d02541c10000350b0301803008001d242d015882d806034164001300000b4882084040c01406024070410740e2070300701612881c40144000c5461003011582d8000c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 720045278 1250 720044028 720044053
    0x1e050a1214061203030402090c070302120403080a1e12050a0f15030209090d1d0d240506010e06030402280f0e0a061203081911091e01170603011d 64
    0x21040503101103c01c011032a504141d804601100401010303c2800c010116942d01094030902948a10044140c44181c5840e01c908080d0302d56405521a40b020400748109140c1074554038031542407509071a200c036003000810365000005070500130301c0160000e03610008003120180e40d00c51024100400c0745003207005401c0d44184406584043c18618180d401501602003090b40b0001034000c061404035040780c071540600125804c9100d103c4010f18403024280009110701000c00c0d008081280d0349414801900c0e000015242140d207420456084802000000c02509014035507284880e280c11f4030201c904072580141c032000c1c20030341000034410191113003040000c1100d0710498000078401030420049107041c00e8080d200d000d00c00000d00741308660340015220b046a40401c00c0070748074028244021300510b0580343c1030b07520680c0341c03d01c940b04460f210320840400820203081114180c4608424417601e8079a6120554000c0c4601c0e032642d241c8800303400c041c3d145012034001c14114001040d040c01c3d40c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 720046528 1250 720045278 720045289
    0xc0905090a020d060207060912050a02070b0301050307060e0d170406020601090203010f051011030c070302010909021318060819060f110322301e050a121406 69
    0x6030030051240d11910305400035a48800c060718141d0340c0480e0060f0f0b950350510308080604607091000c0c01402340541100000c60304403006100c8880643d0943e0100e0f61240c90f00000b5010a01a042d0907074010b46c02841030900030013000040350720007015400b00803200c2d51040c05620008240b50018580494100f100d540c0401c480760140250080a40c11907041403161700d8031000340c2c4142841013005251210310f480c050b0500c0c8601145200039259540c403034400c2c1e5541c0c2c40452004900046001200091040281c4291140c2d05c80d00c0b1010f082d0341d4a01240680b01210700030390250482c1c0d90b1100042d40c00f404004000049840194503012680b140c20700800301c0f0b141000c41c4000504040c1c000c07080c075a034502100c1d03200c880641d4560001101a5960913004038805009011f80c1603814980000c91a0a413400b190700140050103141d08292030003100c000800c0203614100c0b507030813100c42d08640c1c0910098290071211b480e25103400d501d1070700384038155640400d2100316a00c88405002250812 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 720047778 1250 720046528 720046531
    0x90301140c0c0d0f0c0605061314011d04080307031d070e160e10051303020409080714070608010b07060e150105100302040303021f090b0702030c1605060d05220c0905 73
    0x744c103100840a600070805041034001c0400107020760358400001d2410340d2181c003208280b103100302081040a81140441c04620828068030000c200215005c25000c8482c450b800d01c5030ba4000791440c115201c3d4070703095000e45040220301452286207030300d003e907446040203410f00138000d0b0003d00ca454102032002c40d24112070000103504200c0b07030506000080d1908440c4200420a03460183d43d04c9141c00e0221007000b5080d0002980203003080307024014400703540e014218040c020b04020803030340541045507690344014814034020034075020041107012060000741c40701500440000c14441240c801441c01c0074203001c1aa50052050380040c441414048042d544c002c2050a04620385405e544019503900c4425a25810f10104240a4401e89005800c00355043d68031244001d05400c207140c001e9103c0e04501c0340106d9521400c00c6062a10324028100c504898006c0c10481c5000c0c0b441707903c10042c003001052001c0c075000c580e4900c942c50028003d80d02c03207131f4028011210366905001550058460 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 720049028 1250 720047778 720047803
    0xb010f151718010c09090c050c07171e0105041b06140315060a20011107021c0209010b09092a0705010b0904060b040f0e060c090301140c0c 61
    0x405000e5080d81e8000360000480c02072041110515600c010203a082d400c078910082007594200304819030700981200859060f5458040c06000103c1e04010442c0d1a0049a4501c0004c0d07000794020401c8501c0c0941d0642007081203000c3c3e40d86098400e90358050b160b403000c0781c0401c81e07641d002000180108031808210070603103000d40b0f0b03150615200c0010141c2203482c0d0b0b0b80e400b5610020204504044280e401c51005a0161103036442c1c901d86a006024480301142c2c0c1a10004032600101201d4010710640e04000743d40308805041ca031840d000d010b800300503950404000721024403590007681e20f2a20083c0286a0980010f40d502c080c5824810794641c041d040d40b10301d241c00642288000ca4404141400460700c3e292a86c84007a04e0a106000d0322074042801d801a45007030600041c070078590001c8802900940d403c1c00f0b82d41580d0441c1e001c40340790202900c40c940120010a05014002d0001c02560386c0050011402004800803040b442d0010750f40074015030707000038500c8400402400541120764 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 720050278 1250 720049028 720049049
    0x123f0405131e0e0724180e15040209090a1b020604021c020a0312020d1d090604050c0c0f030d0b01140a0c031718060a0209011704110d0b010f 62
    0x149448900a0707080454402d1000641d214804080e41c3e900801601d00205007418041c0b541451000c210407031100700040e940b000034070000002c2c40385e50180460350201c480d9540100225a14180780c0c442c0c100c162903d06a0040e004c0010003820350700c00480a005036484c2c0800180d2044035112100d003c200e600d03d0509541220f0100b001580d104c4145000d01740c860400c0c90042c083d644000756001342d081c0c100811114088200c10710441d40040c465070501e4070f9403200780060440d94041180c0104103420254080440d10000d40c0c1420f10780c10180c1c205482c40303055824442c60020b02400e1058038501c0804a0b880403500c011090402d0051035240344003824410132040300100390401903c40c1060304001e101c1200b0842041510615049580740f443d054100c080307007030440c440d4030044010300851016104450100c0c0ca540340c64802c0b10074942c0141c4075548038030409100d100940e98020800d0300d0003008040a1100d0762070782c0760110707203882c41042540f02d2076041031110340706900241c12903009031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 720051528 1250 720050278 720050291
    0x2d01030b0f121606021c08041e051002040602030904060b0f071e02100810091505190b04060c06050703060b182806030605123f040513 59
    0x140c507540c644001c01601074604418010040380340900c0c20382c1d107410b1040f940c2c0f0b0240e000140c4079408074101c400144610800f10a94504c00c004030750544c01550054225440d003500f0807841caa41c200c81c000c800b441034082c3c07041300c02d501d1081c2040740c0090740b10340701680002800c4102460941324200103000d170103807030768240010162070346a00e0203060401890080b0816030305040c813580503407400c0c0095000f05800e402c041c0c0f40700700401031102074031000da08018000c80410320000030b0003840745900e030308502409920f10708000c000c0c087c04009084110102d10700008224101e9460080000d0078154592641404407445c080c41110b10003420702003090b181490900020000b401103a0543c42c00c03081110300c4500072000100700d013004000c055804074209220200c1c215282c130504040741c04079102004625510003e1280c81c49402044441c0b5401586020080146250142d8859003080d10601c0e40d100e060b00400002259035000e42c0701c034400c081000c01c12850450400303a000350b0f14402c2131012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 720052778 1250 720051528 720051551
    0xa0305030f0406090b0106030204060806030601240918020304020102160e010e06180a05060a050a0323031603030902100f1713020301140906090708150a0b2d0103 71
    0x640c0409010741500703149010114040c00001d4202c2890309400c081d001189583d1424040c0081d0311034070509001c10108c10000d209807802044407412107050750190680341c0386e00c042000c9070050380c8901e9400d015050741c1c0442c0440316401c14000030003607034200580c1c80c100344c000645483c05a44040384001c1c00c11805001070507030148200c1c119401c8000380022a1100b02c00035680b161141600b00d130712402d010030841030310344680100e80142420341e1480d82041c0c895007400b80018040c0005000c403040c82600c620200c01214640300724251841c207807410414103a9485800e003032240c0003038000a4a0340040415446e10f40d51055011074541000d000c08180150003038104202c0c0742200c000065180c4c0080d0030301580c0c4440105144d4001c00800542c04d141341c40b240c00110644800c81c6a1207103100080415200150f10f4081d1521783e8000c110902c0a01c081c45041d80009002080154944000d20040c2d102d03c90a69031104200902d080030301c003040c452140540d082c035021410103003040203003001c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 720054028 1250 720052778 720052787
    0x170a2f1509030a030207030302120403080103020f03010c14070f0203071202040f0b210c0a0b030405070b0403051506040b1c0b1014040f0603020a0b041706102c0a0b0a080a03 76
    0x34a903c507420f003d6107a81950505900a006049408040b9a001810003007096403011019050720f108542c2d01e00c100340c4802c2030601301d588021103e40452000112143c0800c04030b00907000f0248510007100b41462241e001c2410001158086000016908441e10440c07034140140c020b8484a210200b10003031080c000520f0406522160019541d074408005a104c141400701d11b128841c0986650f0340690742d801d0a908035030081300c0c1994240076801010410402c4041241d04403500100204803ea0444402690904000e0440c40d802562844500c100351107603085500044c0c01c0280d80d5030914070a082c0200404001400c0c2c1c0c5e240b68202c43c085c4404680101017070740b030090541d40014180300255502000f4205a0006035114455400019405010f00c000b0410350b80d011103500600f40000c040140c2e2080c060341c5d80ca01d038903400d02c410b01030701c00d9400001145280145020010115a4604003c0e05d0360669881c11507076251030888200c0c0c1000704485004100440090480c180980c030000c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 720055278 1250 720054028 720054037
    0xf020c0a0501051e0309100f020910080a0e0a0f1e0c06030c090801061e12030509040e0307060f06060f08040b0403181508041707170a2f150903 63
    0x241400f00c0812100c00e83d5280506a000c40102d42140d41e659060294034940d032a656000c070918846d0406440d003050803424000c1d82c441d16006040000344404c100303001da8403480700500703902082da031740c864940125000b000380050441c0550740e2260201058102280341c200c0d1400703080d91b0209100300340b00004002d02000001c645442c07400003030140c2196021602d205e800d43c4941910360815101084841030100100c1c40300446982c1d65100d40d9503031411024901040101801180d81440301d9101410203809c0030b0500c1c5408001e40e0311300b5440382c4d61502110a10040c485e1035655510042c40801c0d00b083d10144184a54200400145400c0d6640018140c004100900308100c101c014002003d1900b40403024007140c2a0940760380b5a04c003001815450104c900346c07500c81440c58071103c49030341c1a04940c0c800390440003141c0040d11980164000c2c0d40651340140411101080525050307011451440d01d9001c0403091300e2004844126180c81c0c80034203134504c00030200d00700c00d1003d034842c004100c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 720056528 1250 720055278 720055289
    0x2120f090601090e070e0114281406070203190203010c0309082d22150e0111100f020c010506060306061206031603030806030d110a06110403060c0801060f020c0a 71
    0x821643d100f002c011742011010350003078030b49481c004008100480c0c41c4203200c5023100241c480c4c0f2a4030064820000f8080d50f0265500c4501307030700c11404e002d1354541d0300744618228400751000380b4043c4d9544c0442c0c941030454050200b2007600c1c00c040ba04510b02030049030700d8100c2c0c1c0e00d01441004900d40b075070b80b02131103044485d0f40522425203043e280c1c01003007002d030809000118011510392520424541c80d60840280e1642c0f1a00200d2011800a0241101c03851801140e60b031b60014100800056139240d1061044461601c41c003010500140c03030318003d0f440c0c4140c42d0f003000360700c0e805486001825508042c1040d480381205004102a50b2104016100540120a00020982c90700404a810141c11040886011445031001b105040d00181d026001d924140c044030340c03100c02ca880840350301680043d00c8500e45c008102103400300303c0340d410030300e86908080740881c0b8180c0c0d00e61b95841203901c1d0b807c0900c0825400700041000540103514500d400f02c0d10300280030807400075000206071130713840e0041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 720057778 1250 720056528 720056531
    0xd020c0603060a0e04030507060f090b010b030411060316030608010b0616030918091b1a09060f0d09120908060612101517120313030c050105070302120f09060109 71
    0x3640c2d036940d0b404800080c2102d0580346540e0906080003410365000050507101d650500500000340450751007018905900880b1901ca245d080c544d040303503151320240c42940c1040400d03540340070070f0741c4010085001301c02680c10103401d00c80003000502170743c2c4c15a010b0141a4905070301b4801c0c84c0c4034003089410702c8048200d010320141043c903050b10200850380110410380e0094103104a1410b0603880703100d000340600d00395000c4c403142e01d4600d0f0f81c4465070b0281da0300017024210440d40152454018010b420001090581024013202242c0303e80d03009002c1c02c0c0d060a803500035503000d21103000084800680302d49044403501e41441499541c44002500c0c45008509605002c0c10014050100d0320105d03103405814801c0c035032040c0724402007030301d5030007104540036000b0701040b43c2401c0003074540b40d001c014119540c11a903d18946056007203d0000680c2404408402d03800010300a00c1074030711a8a003600d006840b680c1034000d14170418401040310f8162690710007072200031b50b0001141811500381000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 720059028 1250 720057778 720057781
    0x9060403030209030f0a0305040e0f04050a0627121b03020c06090a180b090a0b0d0f03051c050f060604030201051222110315040b04110316080607030e0d020c0603 71
    0x1007490801c00611511160040744400410148d004000344129090211030702d18070348070185907824104c0256030007031544d841490403000148540c4c03c82070b0394848031203030b0302c100542c05400c55010012051040701c42c40b1104000c407081d01d0300600400448002d040c40003183c850305640195540c814080d140344a81c81c04070310700c14a695280020005040d1340310380e10840c0f140301c000010207005e0124a0504c00d0800e0f100080b4056100d02c2b5000e84802c004050141522403601c230086402d00341a415404c024040140c001e00e44d98462240c1842c0c009e2040007c0c20f8580b200c0c2e5241c0341000a007440d0b1055000704020000f50303a029060700d40100c40040000c0894481080f50b008014060140503d00c40305000b42030b0600610710106c210600b82901600c4149520401420356201d00719001024000f09902240106501c001c5503070700328201504460304140d14000f0f20a00d0402507104038510b13407281d020800c00715410701958135060401b20081c20030981c1d01030701946504481c40d41a004420100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 720060278 1250 720059028 720059047
    0x4090e100e100c0e18100506070b04033b0f043305060a120b03010f0605031e06180c060a090f08070303050304032f0705130203090604030302 62
    0x180040450401004100080c201400340d03845030010701108a070b0901e89060900254081d010143e024500200750780c514204044000c01c0070f840217480346140060004001c11182ca48400174104540030342c00e44141407516140084c000002c12801c0c5c0380408845030014054420301d8908402c1c0d00d41c0514041d180081400880c51307421950800300d131300c14100301c800c240c000303e11810811409082101102505803080c1e4046c1800706500c0341c61f420070f804110807441a4494240280c60603061800440d0009242000a00b500d0340001c0550034281e40300410400340c94100804d184c00516151050745680c050754100e80c580e20000d0098005082c200c101e458140c000380007613543c90310004c000c20b4541e0082d10005014505034020310628445c80c442c08151380c20f00152400459900d40e0301d803455030351603a80031502c0c19200700d4042030184400040c200640d00d6044810060a8820002d01300c0b24178003402c1003020300c03001c02c03040c080302e204205100b040c940c003081031603101e0b8060601607912400b21 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 720061528 1250 720060278 720060283
    0xd02040e07030b090d0e150f041a091021110c07030803070f090e04150204080f0a110103020a1d060f0301080604061d0303130c0510020f0d0804020604090e 68
    0xaa110032903400303041c80c04410008281c0145008a14110440301d000392055420340d88400c911030190f501183e01e10403d41051241c1c8003c005151203c03054900342580c071f12121003c0c1d645100c0b544000c1201040f10041800c1c50304580c00b01d07100314035104450001602d0803984103035001c4120204992588511000d809040c030884015180d14000c0765106c2d035403410100c0c0d070f40e0801d49040f4002050705072003c3c1d2076841303040e0a505960001203040d10540b11070392050803002080c0712a0030050f40902c0001601042801a4849801c60001074400c011051604c807086044241d041c03414540305000c0e044509a1105000c1c2c2030100010341406c0e20040c031b0000400c90b0140d02e02880e18040d000001181c514000700e090360240f42b241d9024442000f800000d001c902d10001c00f0810107030b00500001d400301b00c0c0c4142d043c3c00340d8040c100c0500244d444802050364580c0140312a03000d40c4c0101a003091200b070801228428010500d0303d2102401d02d940060b9080c82148104484181c5890f05218943c005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 720062778 1250 720061528 720061541
    0x806040c051603020604051606120e0a060903020d12150e1308030112030e030d05180d15020414040603020a030f1b0f0302130b03101805060a0213080307030e0d0204 72
    0xc54030b18840410541c40c1c0290380c0c0200311421206801803010114100100700900d200303461094580010083c0e445005500400c2c0d0300080b90030704d1040f41b138400042030461061005050180d80686203548140e4009080400c000800a003880d29005550200805c06072020007903c001c44400c0c03482d40c441955204240c1641c840180c08008004000544040c2548440544905c240c0f161604942c0d900101900d41c0684444000425020018202195a100f0351001c03000c0d001014892070004c140c5130140d54000000300504e003e54000360500c4801140b0900102000342110103114075400d59020848005051000901c0c01e5441c002d400100956441c0c04c42c0c1503515820001c5240eaa25207010303002c0c0c4031030300c000d034003a1480da4130503500d01c00580186403600030042d00510b02d240c08404504020014091010303003007844c40c0c0b1000c0004405014803800380840c010007513160014412040b41c40c417059480744c0541da004004080000c0d03041259040107280882c1c401010003141c0c004030b00500794 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 720064028 1250 720062778 720062797
    0x708100f1116170322080d0f02041701180b180a0b0117190b0c0705030415090b0a0e150c01020c01090c0f0f03023f060a020301060806040c05 62
    0x4002c01c604030041d004250311481c0c240110300640c40c0c41d0a030002c0c2c0f20188420383c2c0000c181082625140158082604c3c1d00344810b104070f0001e45001010303031101013260701c0c0c00e504401e45038000a00300104c558a100302c000d0031030424000c1040c400100c100250305820020010040c000100000d48180b043c0318142c0c003201a504140d540d904c0c0c0e54a0100c0c00f40030b090142d2100d0181d1800484000701001400e02d4a0300280c0c40598100181d135200d40f150300200801c1500300010410811000075000d201038001003d007400b203400380c00c4810754060403c11181e0000910004144818401507034401982800a5402e4600c40c443c00445900102e40c3d100703103d040c04003580001944803400c2015806000e8243c041c14012034095110064500e0100851042c0c1800602a100c10b00149ca410a580442501c00c402e81c212003c0810901c1504610303034101050700307000c0c00007103040d000300c1c103100c403079845070501c0b804510719070501c8000b0f80102c4018040a01641e03072610414401d50190040751000304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 720065278 1250 720064028 720064061
    0xa0f0605030f030a0201060902030f060906300d030903021222060f030b040218040f0b040507020d1202030f130c05030303101a04050f100c120519020708100f 69
    0xd12000b9640d2a801039041e04019032800700000396010300d0344241d9015209a001d0b21907a070705c8120030030000ca0760182c8413a500112070407500c40c0c401800c585103280010780080c00307542c50500c81503250802c0c01c440081018275040c069148006580460000c030071080c01002d054445c1d081a5800c480441c80c0ca1401e031081c0071406020900076003003698111103c9003503400b44840010202804281d000d503543d83c9000b09610965400a440d040d00509500721240ca00058030360313024000902a640e05485150158103e545820001c076800f030944441801407060a52075424407683d180c03502c060080000c0c44010a41000038100200344103100001c06000702100d4890a15100900b0700e41114441c180d9114030340300070740085402c00801c0d035007100c0009040000c200000700038071001c03003079204034002041030154480300090071b07540d12848140c85030795030b40340c0b6444518805645c1c001401c2c0075005551240904102c48800003490f4024403900001c0454032003140e0720b2160140101d54035002162 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 720066528 1250 720065278 720065293
    0x904030926030f0c0c0a14041e1d0d02030a0f050306060c061602011d0a080c03130b09010e010c0c03080a090902030a14010e070806061309051509011d0a0f060503 71
    0x31800c0f4001d0500e8800003800d449000a116007003081d840443e106624030107510400000d61403805602c058040c0c440040e0080e603040048000780d04590f94908014808601400c41424152081116a541e5080c40c0001c0d072415551020107008039a040003540108003000000817202d44038001590490400c1d0004c903501030400c03075480381d00c02e40c40c120024019864451005050b01c3d10509100c04511620060036004c089522000040d40c42080300c030303850344400c1050041200c1000410b90007030410b136001d40d40f183d1148000614513600050304034100109401404085004410b05004407a4404225603a80360842400c3d80c9010444d80500c03806d074804402c0048844c403075000800248188001401c3c02d80e00c4800c0040c0210342a80d042e40000c1080000900702e041400007403c045088031048005039540d00e0310b0b0b80035540100c9aa11180800040c030084500780040d07240e0140c0030940034075010271005d41c1e5018061900a103407090068850348906003094196101d003000d0600541901d40c1c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 720067778 1250 720066528 720066547
    0x1210210080f16051803010905060901050f060603010302130e01060801111210080604080901090b03180c01030b061215060a090e01090b130504021302130303020c090403092603 77
    0x405600701c0340302e00a9001d100001d14090000000c0302e854400b540c41d240e003045a4400c01900c620710300b48815405650b03811100380420b40c10010288540ca000c4004030b80b81c507020900003282c0002825460245800340014401039454440c5014081940b60b00001c4080c841400c150240103564855000b42d4641300300c4080c040e00174402081070484408214100ba1500e8000c1e080191040c031901c10581c00034004200000c054100400707210005261402d1160740302d5207190b28a074010349880310400c1300c890803c1c940d4117050000c1810001d00b401d0030824442c144010410750320406030070b003a01140450000e000040190054008010003070503560300c0301700403100904841113601401e50740d80a810300009000f03003107010320341e001c2070054145400e010060840354080c22020380b040b1781c0880081031081c91024544083c01c44240350203c8045170500c0d60602904007000d0a4489005e0b4000c4020031001ca500b0541050484520320311540c007480420a0744469509051206251400b0002d0603052 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 720069028 1250 720067778 720067787
    0x3090f0f0e15010e12030f0d060518060f0f04140a0902011709190809030d020309040c0e0a1712030903030402040c0e2b0f0503121305030301210210 65
    0x507150454090809925400c9410030742c1801008810700140c5103440c071030101e0801e12485421190007400700c1c0e052020400140b485a00b0180518003480e6861400304110710b402c41034107560200907190b09809040503008074001c1180d194485001c0d241d8818281000d44035036000300e010305107460ba00c060394204440800c000d1302d0051001d80c00252006a0b04412115111820380124110360040c21581c14a099410503080300c29000e075007104003404803a0550304d06100034061b240031980650750b2007503070404020458124000002c2000380c406103100c0d698031180918801d403045100d0011002c2e070080740483c94009605003210140c0c10110a200e00400004091800b85100312000d01c5074045241c8216040350103294201da20090b030450300031021503c00c51500045081c1051a000318545440e0211311151508040751240d10004103c502d000c0000c00c40d540004042000005454071500d030b03e640c900042c09001003100d0001c20580013a000482212a0030b40d0141a594000c0c171410f074040c0c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 720070278 1250 720069028 720069059
    0x11030d020d1409070306050c190207031b05010806060c07180e060703020c0a062c0a14010b030d1b0209010305011a040e03040e060303070c03051f180201030903090f 72
    0x80c0294182082c1120a016450450380f10791000d4009004051554455801601c030250100218800c02c01803404021a0300c0c042c4004040b0f00c4d00203050403455482c1c40d04418031400c81081440c58a40b1041c00960b81c801d01c1da0fa08400102c4085449014004507d81001040e13030000d60902000320710444000c1d416044440d07000c0c42407041c4c90099854030001e0f016841041d50b0701c485500000941000155994003800c036991801090100c400c41c0c140e0703080740c441d004d01011a000ea0140d4803280800600b1214000003180b0140213100f0078480710003003a40c9420f02441c01d0b0a10006070300000100c0c800c2d0380f40e854102c0d0000d22011040d652810458020020700f0201d11200387c1c00d60041c541400d05016400e4105401c1000750715103880c11240d05400c420203806180d060008024100c00300b20b2082403800036500402c050031b014642c002011200502c5040d800000318140340b00f01100036400c1d0700d400401034080c2404281102c031843c0c103d40750306864010200c403801c200c10104070154501d0604 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 720071528 1250 720070278 720070297
    0x60328060b0607030c030c0c0b0a11071d0609090f030d06031101021209040905070e0703020a020d0806011d06070507170c1909090f0602070b0f012705060111030d02 72
    0x41154042103002c1c00030503c100900a00410684148213001a128240c1368800300d000c6d25040810503195421548650303c004d104c3c4002032120380c40c4000c8054107201000080040e41c4051190300403038541e00d100c3c040d0050407e807080c801d0f00c0000d16002c0c0c0034018000c0c81c2c5900c0d8103681d9500c3da020607500080005000580b02d410340c54041c03503219400002c1d00380c00c580c01c042c03410342000702000401000d01301c4624110754a000c0e1034000603d44002c3c0c00e0403030058a81d52400742e02d4050780380009103403110000d208070030403204000b4442640d81115184001c0d4044000d5481c0080d00c00d00070500500c20108010804d01c140c03800000c03007032054000008840961000d43d03640706001c40412218000320780340c11b44e001c80b00000801105110364030600c02d4510030070740c00d44a07000544035030040741c00c052400d81e0310161850401030140c001c829034502400c4040d01400050b520b410f0203060f25007410701040c00c150f6a6102056840e070007482e501064035901c10803282d80d18034401454000e508421940c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 720072778 1250 720071528 720071531
    0xd060603081908060a170c04020f04330c0303110d0509060112081b160803030907050d0f20040c0905270c211806070504060c02060306032806 62
    0x24641d140b040300e04034000d4000a00e0000c41c1406d02440c146003110b54900d44016102d08a200400c6440e103001505041108248031600e076880c0c254a02c3d4000d111072585000c640310201000102240d6078100948181149040310340c00040e8901600284a5200c44c0b00900d200400e01c5807064078940c2140f8030940c55442660301c0e59030783d401045c1c0807001100c001407072604180a9410302000349103020703001c2c540800172190900c0d82d950841d0308070300350b0341c00ca02c1d00394200000b0080400b004004042c011f1006030741c504510303185502c80845400e03200740002d00c604a84007015583e041c0c81c6e64213400806009000300300c2d85034074130b00213040c0f80d541e48240c5010303040c0b009045542502d1078200d6810310b81051050076403aa20300ba400003190b8041e80c00d07000420b6000c0c3d444045511295100303031044000081a40b081c2081d180c4aa2034103c0084c480000c207c820442800143d0344002e9031461503905558454881c0c544070300003400c01281d2b45846000c01100c0790b5550380480c16401e4200c1680c0100c60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 720074028 1250 720072778 720072817
    0x905010308130812041701060e0c0c0105150112021c051303020f03120103121202040e040219030804090c050c0105042415060509030307060603050c01090506120a0203060d06060308 79
    0x11040e221300749640842039038201071104004886e404450000c60000400000442a44075200b4241541050ba03040c00440c038040b843c0704240009102e40c40c1c021651201604145000c3c10001b0301c041c3c401051852156004031348400c01007622101d080b441c0e00d40240500482c540310600502a506021040d0010320a1000010a0043c08002c4800c00b000900702c03003009030700756241d031000f01c02405030710420000d00204ca01c0c1c00350403600c080c0000d813513040c0c403c9100c0d082a004100e524440300706500d1812180480400008a908040310211811001c000c20074075002d1206445900810018410750350908080101300328a10b196815010485090b425003506002c0044089420103180744560301c01d45242404500c1c06840503004070400201280d15107007156031010103840c0719070300807940c9a200c800c01202d01d681150f042400b0345003c4d5071990800042238400e803c91007024005e202d54a6000000c141152100320842d99500d0300070030f041c01583d5482c907140441d03510054271a40d041840c1c89 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 720075278 1250 720074028 720074039
    0x311120c1902030a0204021303170310050108070c120306031b0609061704030e060d020c150c1c02030c071209060807110d1215120215030601120213090501030813 71
    0x40030700c1a05801800030180a060359003031100035405007240c805007005d10740c030000000e105500f180c520081380060150b140e05003524120403112450300490305101a003070401c2145a070180707051503a20f030812100c0c402c61070300382c1c4190001c01036504040c0c10030804200c080079408800c0c07030800441c0d08941d0b8005140e555480300310340c44e844440b4600780d103403404004100404e1007130303901085040700140403901e0b10507144003110480e4444680c2d55100d402c41001050902281c40f042e84e442058540030501d40f807680c80554000070540f02003900e07000e5012000c02c00304182d0764182d501080d0300a00d000c1c80c07621700344806401d4501324801e5100245041f0001940c0710700c6040302403500c14940004003446c480300d402c00e0f00e03012072140011208a03655000c04080ca159030380c2103c002c0030800c5528070a0740e03190061001d42d86112003084a08101001848616644515045010006014010389640c1c0700b405440302119254440c44071f081c00c1c14008420f01c08144000c0680c408a015070f40c008030340d6030b0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 720076528 1250 720075278 720075313
    0x4140a050a0303081603110a08040507080c0d1506080708060f1302060f0706090b0a141806070807110109060f0f110d020a12050103030f110102090a0b070311120c 71
    0x41c00b00900007800400410840848041d603001e00543d0b074240401d5484c51080d2884003500011820b40004181c401070105001041c8050005415104c003e03082c850b1544011800420a005004040280190b03903a0a0888a03038403c10280c543d070401d41d0b88003940c0d800510707070f04c400c29146002841c55100c007285100c01c0c0321503c52540c59000e4101410265404104800d54000150585034136481d100904002040c00ca1094801d88980314000740c01c06e290310f060803da0400605110802c80c450404071840c21b0300280f4590305c140140351a000c01d0750741e200c3c01c07600c00780b41c00d0200a443d070824456008000c80d5801c804100c8c0c0e10480b08000c1c0d00c4580403058103444d01020440580102000360401007000740d0020104d80065061844c03000d96a014141e0131500c00f6441600026007075100800e91640c4168101e170860f880000035410900680d0004400038030034400c0c0d000040d4009562002c150003007031090424213148040d1868103150b4940d81069901603105a142c90141d9441c2c1650f001c00e2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 720077778 1250 720076528 720076549
    0x6020303060a0308030411090a1d0307150507111209040b1009060807031d010b0411030f070e13180c0503071404090f0215120a05061003050c090604140a05 68
    0x14980350503503185407984130980d030029001762100401700d5000c00860700d5903481030b4000d401001c0005039a0542480f56000a44195070700351141c5c000304811000318040d194000d0031411280c1c400a816126840c06499808201d07450040a00880200c0d410ba4810706001c1c001020301030744c0510540f9015810008141440b07000742d004180c420382d040c0002482090400c0d40429a03007400607201603565401c034040c640402c005605a074403010380158606150040c41840002120214203508084060f440580b030004c4c2504108906058940081c1d07a50909d0b10001c481001d070100540768014804041d0400350f64400e0f10202002c120024190030005204011103003510810311078850000200f00103407204401c00d0b13074401407141c0340ea0050b07503810720985100d005030880c169580b140300008008110b8000c042420080c03502007000a213448035102403504842e00c1c50001071a55400c07000b0b950034060306060300d0b00084081000315a4404480d000b900302c1c02c4c1214000c1590381d44000304041d0740107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 720079028 1250 720077778 720077791
    0x7030219151101060b130518040f11010311030906060901062109060902150307080a0c0c0303050a24061413170c030a030314060901050102120d110d060e0106020303 72
    0x50341c080781d0305042d1150200216245900001107030352665411050540c3c0c0005000e43d01e40600420104100e2030b15902e018034441065401d0b0b022450140c071181c000e44030200703018000390034100071056a80c0c401d6211944201450191589078105100303226640c8404407803072405000040d001103a41800340740d50b0600b404243c207044201c0410522208080d010005c4216822925500760704010303562214400031500203030800c141c4a00e40028018041c88000e400c941280d4a020803101326154042d100c0e0b05001e40500f000708454075100000c000074121144111108842d540c011010080d103810031104551a0ba0760310340e07080350b6a50380080c286c0700e04a00f003034411408550030460386d22509a151051040c2100380e030380c10051000030900705403c0020490001b540c03024100d10440f14580c0c0e0076000301050f80c0480882d07040c400080c0d619402c182000300710070404a80411038800541003070141a24107150b0b16100c001c900e8090020344a540202e450601071200081740103440002520320581 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 720080278 1250 720079028 720079049
    0x1101020a12030905030d060e091c0512070c0b0901060626041e06020a03020403150c0c0305090d081b19120810080a1b3606051207030219 60
    0x50744020980041c020036200301d0b6280014803c0c40e4a09505115000007007801c1c0b030f400d000c1072428091490403d5a85c0080c82410742180e848480460b62010aa8200004070310544555881e90102614940040e0b039000784440d65a03c2004150708043d00170f801101c559450704804004400341031141c0c490307a0f0030210308011070b002c00a00410b00c0785151155410140d030170003400817001c0c7c17980000da900500d180c0003c80d03000202001005202c10141105128041080080038184030005040f40003802c0003800300140400c42089603a0703042645080366a102c20030030b40c0e44400c125070210340c000003070400030302c3c1c0100d4000542c68020071010102c80e6911064100c040d4150304000d5403c6c003405000c5103980110014007040c1e424041040c2d0684901405030804401d0100d00c05aa00702c6042e044607420070200400c0804822503000318000c5039401401c02104841c1d8843c0f00c00c01464a64001a4449400c11445000250109208059038000c0d03074220b9001d000108107c195130201d00c030386000395 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 720081528 1250 720080278 720080303
    0x12050c0a051f0b130209010c020d050a051207081b03090d11150f04090f060f03081306022a03030909191a06180f1216080a0f0b0702070e040b041101020a 67
    0x11340e101c0d4024103a1302c05c1410088803401485d004a503804402e007030300b102d07a544001407610502004115008081c40c181300344900e05046070b51104254003030345000340d0584000e4111907807003813418002d840300d9440c040e1061b10b4100030f42c205040c0d1000030a07203690140d03610051180c000c44622040f00d54500c4600280e500e084e00d4030403408000d00c401c1c0c6059401647d982004900003d80004650080d8081c2c00d68507250450b4400500600002e58451001e541c041c4148041c00394040c4401c0314070a0403140d01031018104100801d0a40c0708012140d0b900260a00070020100d91107404450441400b9008100c07400d0700c40104100b040b074504006501400900c0f05150700881545070700d0340035002404080900c44410f01060f030780410081e154145411400c101514844562aa14000c004030001402c260f64280c40d12090381c01079030340181031000780c080004c030018001c0045038014840c29074001d80500d0541002e215441c1c0c183c8080710003941004520b0790943c8001502a8925005941040c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 720082778 1250 720081528 720081559
    0x10b0304080706020703091d010e13030207090c08011a040501080f09010b2d0d0c1e2d3c08060a02040f0518010312050c0a051f0b 57
    0x164100800c1103480e404204402d10000d49280090100c00340700b5190141c10b541411400d1440c00340050b4021001690b1030700400c0b010000c4241540c00901114030120301c1421428220f083c851540c00c1903c40b503040004c0580740c141e201c006030307040386ca00c000e100690010441c0f842c83d070f81c440c920032540011810408201032a00240440c3d0300604200c00008040b0030b0307080840d14400b01c01e004042102401c0007000011108118114580e80d011262600b1650681d51040421211800b507104131660702c184000c42210480ca0301009840d00a41c40c005107200300080e0694406142906081841c0d241c00c00100751390604414851500300c00c11070090950340d900c60f224000440030984141000740301d80065001014401d00f030180350745c104003603a100c9c1800320030404400603522441c0904035510300d8404031036203903e40505580d44a0381c01e04400420341001c50b01c0f0300507150742e80002e0251055603001c01400041034101a0040100f100b03841d00d00b44071000486440c0034055400542c1820111038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 720084028 1250 720082778 720082799
    0x405030315010c06050a06050108090d0512060307030c0f03050d14191e0c050c150304060b1f0c051b060405040e0102070c081011130302210303072309030601 69
    0x810041c185000502c00c41c00d81c641405a407402c0d90840c05496881d081401556408004c095018038168005c20a051491308007d20510a4283c040c89803000a00403880c2039800384400d03402590451140c0c130030701e900c402e08902d040550344400c8500703108005203060311130b0060305a5114050340b10011400c01c40c0044c1c09800c1c500081c2001d0b8200806d0002070702e034015050422417410001a502d03280035035458a8217500d0079451112891240e03c0c0704088a030568100021650302540c4114085141201d5002094405a090445150841e00e5405079101d81d64000c5121150502500413581c6940840c0a00c008200302241d0035904901c0400c8207020a04103900011051075071000010328111039034840324540c0045806c00d0340366401c19800701040c005240202d01e100300040a4091404684000406003914035102c000e0040d5980c00040c26011010814900c202c03c200c41540d03a6840d00400c01811b00c02c20400c4808114030110310b0803c030064040a5071280f52002c1c00034070300c0ba401c0c03461401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 720085278 1250 720084028 720084061
    0x80f0a0c051921050c0306010b031f1511100b0603011e051906090801060f030b04081605060105040c180e22030206010e01090911010e0411270904050303 67
    0x20802c54000c4000503090309814a0000400c861006040c01d4212842c010b82011034281c14035110381e014034014002c0f40b00300404c9917004190b040100b280000d105110483c4106035510000c00704525031918000303c3d41040b818076101882d001a20700c58503c24200c10222031004c86440d82010090005210142c2030344113040403c0d11071080c0100055072803001501851085c1c10100c04003180c0c420400c16150401100343c003030040d1000920000e0b05001c1000030002c21844003404160842d40401d081c022010100d40b00e14800e00d0345503110720707254140b069a440c4c0c20321580b4007407440d0a4101d0185442100c6a80300208500201d4680ca0b1408442c170310a440c003d440d14180125410300d80d036140e4a0b40d0401425103201340c02408070382d85081c0414000c544141e01940100342000281000904000403e074081311090800c1c0740c6200703d0101190040002c80e84000046500007648a6440d11125042100601071a02c0d070424100900a100e42c0324001d85008105034018000708029101240240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 720086528 1250 720085278 720085309
    0x309180917130803120a1d1005040c080c01020303130302070e19060e091f0609021c060501031404030e062a060a0b06040501030f1d07080f0a0c05 64
    0x800c0400361511441040c000e00c5400030804840042c8001e40d821007504480014500305028608100805140701c05880c4002c041112107650b89011002c0507103400000380c5818200001c54182c81a00b120413402000207860030f8a5182c12580001a070781e04c0002ca403a1030040c103901960450f02c030080101d400111013030301103003075010701c080124902070600d070f410344903000000c51110b07036a0700400d0000494040760003030309030303040c500080101d0007a0002e80d03d04440c1c0c00001c40220809038508910040c61a07030042c601c0c49000141010f050111920507228580d03541c40300b0010b07265908015001c507000c0e80b001c861001007540000780071074054085840c02c82c001416262821440903907044203d800d00308040e810603090740c2e44504484d0b003004803070303809402c112080004015500001d4034070f006602c5021b0406440f42062512301132507070004000e00d40302091a045415040da1203d854503494002c140441c414407040b920200d50020340a86016045040302818904000030701c800b08640c85440c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 720087778 1250 720086528 720086531
    0x60c170403021503040606050d1109100807060f14070b011a040317030106030b0307180b04090c0906031a3309070e030c040510090e0f0607020d031404030918 69
    0x242e1100c100c00040b54035803141540c4e032450a4034103441260516080640504040d003e03807000103000c81e100f40406402201e4180555541c080090f034a019103801c244a28050b10b00001005900000d915070190003039154128840e2000100f00e0844c092100d0203842460544010072800d181000c0304111380d02c0c07481c1d0729480c050300c2c0d44800d20318248240310642e60540000041141541c140b0858010210441c00307000b81a10704415036080240d031030b0b0707a00c60903546c906144010ba07440313900070b04426520041d651602c2c0da0b98089a40105011310013a00d00105002c030100242002011251040109038112550341c210417400c52017103048c0149500c141d1803442c0f12140150759004099100d41469511031020f881d1001c14142425442401c860280e803c02d024400105544c4c2003040030f071200584001001c05c3c14090161034000504049049409110140010264080307031940c1c0300703103043d01c0500051032040c00c1148800700440d800b40001e614100d051018040e5181b12808a92100c82c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 720089028 1250 720087778 720087787
    0xa06140403081201031e050d181a0a08060907020d080402010c02120c101115040503090d060c030b010c0f030c1b0801060e10031e05120c06070216060c17 67
    0x3076840b4294058800c86000901100c010000c108212030291a404d001c2c101045280303881f0343da01d0b0368448401c0300e4007040c00405010070303510381591010b010052030800385400b00f102140701ca04201e42d0001c01800001502a000901103042c081d480c140262282d50090034480710201c4101c81c2031101520490400c8084041d203005a600e0003124000008506c02400042c01982c04208a0300f54841c001c130700303102e00c010003218681e20105550310110740800308210f0075900c070310305070341544a05114150f21000070403c003001e000d444c0c0e114020070605901c0801403081500015200e2055000c00100b030180d03400c180d40c00081c80303078020b44506c520520204a02d00741d21000d013103c1c07015030303004210140c2d0359010422201d041040c500341c06c2540c00601c03058442c2140c0f00c080114150f180b2504903101c07c00e080d14100482003102c18190805003607001d0719030145989140d10f1300d4040c1c0b00d003801440b07160100403d008031a40c081d4100c071216200e080701088581c3e0b58101015815203800c80d00d000500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 720090278 1250 720089028 720089033
    0x6080702010f110c07090501060c0b0618041406092b030b0a090b0f090405031603050706150e0a050106050318030d050a0b120111180d050106080d0f02010b0a06140403 73
    0x350005183c00180100d4075400310107203007807810035580c1c012115503003040010040d60750031900d035540c4c207500a00c160041e9551403012074483d8801c80f0100c090b0301040001c0000b800302c1c420014401d0342c1c0c140b080d03e00a40b01c0b0710b8801c1e512060f10b18000043c144074202c0001420064900403003811147c1808618814444001112486d203580255485a02c50210900c146000000c1e80308400c000c6a25500a00b010303101c080c0c6d24000d41d05844072405500285500b89070042c401d45503481d503c01028080c00007880031800720a00e06210310581020020045400f81070a070091a041c0c443c241d4403941581c0d40c81000340c40c3c0c41910106c40740305000c00c203d101c081e079109000c1c0a102c0c40c0900004140000030405120011405118003540390349480c42c0b039040088404111501c4014074000b4842d10816800002d5403185c4882004000350f01e40100012549404968150540584d4550320086418200c0680c00c3e2485032070810703845800008280702d82d502440e8400a80400424000d00341758896 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 720091528 1250 720090278 720090281
    0x10905060405100e060103150b03031b160510020c1c060501090e120a05030402010e041820040606091802040b1803070909020607060504050102093106060906080702010f 74
    0x240e8040c1d8194120901c406103c04080c054007640d2040349006007020b6141d526988a012036800c110011161100c550849030740d410800d403148040d8246212915404035500c6030740d50307265150403521904c152000050a494624004c0d041c10000c0e03009002e501000d141000894003103032241801800208080c10080750945c8103085c003816005c02c0002d0b5010000000514001c05000b2485204104014040015a0000549411590a09107020f040600000280c050083d0551580010f180441e06009122030b10b840301041d2401d15032022107040030230083c04117545060050740041080000100440d421407200500c412a200000506142d10741e80b4914055101348032440b000581030010050500d01030113104001e005c99141082107180d07d0b80860f140b4001c881d8040c1006544100013018004290100d900c0050003c2c100e0304801c808001c4000030100080c00c82c8400d4206d50180810140188030700401e0f01c50b6a118100030a203403410071526400014090401c654030788410001c12101c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 720092778 1250 720091528 720091531
    0x1060e120319030204090b090405030a0f0201110c06040c0501051813090813030c05220b03122106030d0c080a230406020d0807140a41190e0301090506 66
    0xba80e9000d681c80d0720780305440d02070f6a40f2103802c6100700142001d1000103403001003140c05441060408004144100c074050b40100388101421840010004034510a1080400c0c0706105501c81c510b070b54400750302d03000111054026074250841c95000c4000003c1507151070854018410030723121010881240980c1c0741c40741c1d900102e16007a04200d0030070080c400c210031007a00102602d02a9046860f000014004000100071400380030707a056034135a040e040b2900c1c20300c44070210301202506183c0d036400e45141044128420034003011142c0740308003c214240f40100b0181d0340c03d01540c0e0742660611040d15881c1155201448800500160901c84100e00c07035100d0310882022101d88031252101d02c0d040c400b17814a07420402d48010000f07550200000740f50801c40c1c0d0410380c1c000c84003164461500b000f007526540032810000e01081c0c10400c4041c03160030361029011030410494041da808141d1082621064040c503807254501302c03101d03002080450f100304211444590010008a01c4960648036141098030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 720094028 1250 720092778 720092827
    0x314030301030b0a0b090a09030509031c0f02030c030405010e010c0f030e040e0d08271002030402120a05030d02030c07061a030610060c080d0e071d06060301060e1203 73
    0x48010001c1c842d41c1c085140e4029001d110a00005c445035001499070701004161215844c0c1e210700d00b40505110754190345203030f90041c00b20b40000d9030031100c0d08420445103030050000340f00c05c2d680e40d91443c4040240c0d0401a080c10041d030509081500550310f140c096911f041c1008400064140410341408220840d1401303601c544101a10b5a01030106851354035610701010b07408010f40700007403540072091590101010071074580018030142004403031102d000084085129480340d14901855641c011400342d807003222101442030802102980302e02803004e0141c69070b00288094803503001a600110b6014141141c032600d480d11a65800c0d084800511380e40000300581c0c121070703419090400c01c05070852200461490424a40400244038524880c030050070408080b4440132441403d8020300b01d0850b40e002550601502d0300031944051550400d01e6010005c000085805800c0c80400c4905075800340d55000055203082d41480f00c0711138641d514400900c0100b0070400c01c0c0800c48144002d216 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 720095278 1250 720094028 720094033
    0x3031c0c03050709082109040c0207240504170c0621010e090a0201110f0d02060a0c0509010c110307050622050f030a0201120618020c1608250314 64
    0x5500840101282c000414140900224201c02d0144402c006440046201c550813500504440464101214002c0801850704035040585151486401066400540e0280400d503100e6801c503a140301c3c01d20f040c42c01c4410110b00e007000240309078003030000003440303020019040b500d8034a00d0101007100c07684022031164110400c1449078a8500180d401603004180c515445034480c00c0502c11561a120602c50090500c240340f044004c24442c00e05c07924140414140a0b2501070020300006500c0700811200c00820034a80040d21030406c0c00f076003d4410b407840c10394079024890301780ea030f0b00035a6881c0090344681c9442501070000f110380c0c962009200c00c4804130070b00183c1c10440344254940c90042d81110340700b08440c0845d4541034070009a165a02a024640710703107061750300c3c100d650003070950b03802503041c440e480d01a120203c4495002807240326a807904558404e0000505000c0e44c80c89802903202c640c01a0b1841e011b4890f00841e2101901649070b40d045071556256614081003640b10071450064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 720096528 1250 720095278 720095291
    0xc090918160e060301090309051e0a090603140f19050a122012070809130903020a0b090d140d1103090c1203340b04200105130e0603031c 60
    0x258101800ba0b4002c40150000d000c07020b03441d94003412086503402460701602c140002c01c66508800ea01245403020064405045943c80d015110003030701460200782e403206568074031f00012803400254480d0f00343c180c03c041c2c0300c181103040c0542d1400c05040e40550b1a031050321484004030741d1405180c40d46048a40768400340400141150848000c1c601c00e001868012181c2d6000500c45403084840c0c0341c0c3d0040140da52008054001070460350142c20150070649005160020144c00188400140340540d140b40ca0701e41d50f401105039540c42d07003441d0700001129030041c8010300030000003500301340f11a00004106041c20b41c42141084e00100d41d11030856025801030031850a102608041c2c60b8002d8016502e41400010a00c840e58180802a0110401c0000b0f40d0140d40301424400030b0640d00c00d0004079941032a003880a80d802165500c04000c904026030f0140a46c0110112000110300d0440900442e140101707900b0101c0004002e40c0c3c150108111403051280c20103450701c0340440c01100051b20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 720097778 1250 720096528 720096539
    0xc0210030905030f030c04030b070c0c0e01050315070504091e050106020f0303070e030715030213210f0c030506072c1320131d0c09091816 61
    0x4449a5000000d15240c10007a0703011038008400ca071324081420124a507291282c0c0c905000c51b215a51010b0101038620040c4507280e03603c5440c039420280514107418450307840c2c0b0301440c12a2028800d49038194401440101c0320b50389000010350000c940d00b0801e00f400d40e240d00170000d6445500c031010300302c030711b050b050301d5842040e1140c00d025105501c0181030321800544040c2d520b01c0058800414004400b18000303180d501044200083d00303440d4155440c0e10f00b1030303070042c02940010001c0c400590301c403480400c0070b200c100e00c19003c003da01c2000003000d0940c1d85441808840d14442171f1440d200035000480860800c000c143e02801c540c3d5900404100c2213458040880d810442c0501c0342d002150b64010941c0c0c03071202050f21202500b1300041c4c12a1007600e580c000b803009a5164003244c0000c50081981c80c04e1101090483d046032031903510081040004031480f003c112111b041581d0140f0450080e0305012100560211800300855160160344d442d040c68588141c04401294103040d605010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 720099028 1250 720097778 720097789
    0x20090906040f111e0a0e06070c5402090d12020d08100302150c19081804051b090d0b04060b0f0102060402031b0f040e0a020306060a03050706030b04110a0c02 69
    0x4000300d030324104605103a00c5c03940041224100341e00240c450701000c038105003407004400d0b92030001e21100c040110880d40719442929220005040c800040000d140b90076a121940c500001c05140960521203448118402101c000d400120881e40c00400341c0b007500c40026800c482d40c1e40d201300c0580040003400b1110348010045840240366142c00740390b40d5801c00040e11408111403840948000145d2101442034865180c030485c50460861600c5440030441030005020049c403020180c04070760304400c094481400181d5100760f4400c420b44141034050313109030023804064640b01070000c2c400c00801440d0340320000c00400985041e10f019650342502082072a00c820038100100c0c080c0003030240ca2a00c1e0300040c4d01c03401c20000785109809080009091541c49122800c60124018003c10080d048407241c0c50b07440c40e0a400881c0648203031b50104540340380c40d02d501000c0365031140c001c00080d410920110050428950281d030002e4a5201e00040c0b89006800b405c8070024559840c0f0b00303400710b4010001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 720100278 1250 720099028 720099067
    0x3091513020a0503190204091401140f011508130303090c06050d0b0a03030c140705100201020310051212090a0b030112030311090a030f0503161520090906040f11 71
    0x6100b98005d682010103140c0302c00d02c0408a50f01210f0014540901c0c1c00e000e2804503100100c02003079440c043c59006668481c4844901840300d202a4105581c2c881469040304181401030f64007042d91000000c6004800003c060291842031a000c103080e600390ba508500d583d01c6810400100700f010508084003800361041c108010000c64540a603985161005084003581c00e4000e403a62075215400340507107100304100c2d8000c00f40545410100340500070024001e42003580c080300051040f0600107441d15116001010300c1c0c500c2c00c007505001c04840d8001280d58002401d49401207010380c0000745c0c204480780914002c1000c10101241c0e135500e0b14000b800c4404079041c2d9103030300d0301c00d0020b541d5a4503602a1141600c1d03218030704030600350507800c00030f185024800c3c8540e01e10304025030b0b01c17081080394800c901d80b80104080c00d11000003074100a411086454841d0446004144822032040c41c058030000d4105501400000300b090800b01c09034181c40502e1010600c0e42400904280905807030006c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 720101528 1250 720100278 720100289
    0xc04090e03090a050105372003090120120903240a090201120207110319120813050d1d0901081507050c0604120908060f0c03091513020a 60
    0xc42c502151100050f078948030034054981003044c0131603620680a401c007100c12107009048503802c45040c80c0c00a0840907150480300300005091060810141610496030281c1c0011080c091401d041c110401120f01407018804554208600e41d00d80030741e20400d0040d0050b00d141c10450955400542c000e151900c00101600c03c40041400205509a160380d00026003020811802103002021400101c50400f40300d60014080c43c0700007608801c120f2036440c14403407641e0640586151644008194154000d2040701811301c101401008810720711603c4031503030090a00400d0310340624142c03295481c010305800701401141d01071908035041c0040d410001c0d07400d141182e20300059810280c69a40f28020f2213070f011700901f600004141c009000714159540201003a0413a011440e182c20710809242c00c09290ba40400d581c3c0d4400700d141003011401c2d0b8420300c11200b10b0304450312454035400302a0700c01441c804080c02070000a03013052160010340c0d0700070080e10325601e010034814010041d9400c581c0e40030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 720102778 1250 720101528 720101533
    0x40204110c070501030c03020d1406091014130612030201060905010803040305071415030a02030a20070f1118060a0503070602190201210507030e0c0a0b030a0f050c04090e 75
    0x3601c0404100066100550302e00b840d020a1038800040c080d800b9002e0009881e2006041946104840c0c84258200c1d00c522411110446241c5810044202c26081401003040072403080368068150b051400342c0303441d022030185001400540e1000d81c0c608002080d0400c1340140d441d401c080040704802e0280c02e004d07105a501941c5864550750701c49070780d01d480d0310034404100c104400f2607107660b603611180d038042884090032036030780d190071800080258411604458000e16000d0300440020050058241781c000d0410510314007405a2141c8600d01803134601100d68401c6022030404039140c800741d810480d030010040800f14100b0000b003058901c40b642000340242c1c4000e0b810428164006551401c810014901381c0c030b81d1403140012211400203511014402103c20841e8040301d50541c400342c410051580d040048404080b251a100c1c1800081ca40d8001a001c070b0600941450600441e00009120400691020095044819039004840000c444070010504104092060050b403000c198420003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 720104028 1250 720102778 720102787
    0xc080d200d020901022a1504150504060311030112020906040914010f110307020d18092a0e03030a0e030a05060901090512040b0a08060613140a08070e040f0c030b090604020411 77
    0x208002c020741c68442c1c403442401601c0050047c00c0181c02160007070441108000c040c04885030f406411036000c2d100d0040003a01e00011501140e00c00800e59050307c0e0295503010001c03d0a4013045031422003d40440c0e413041e80e9002c000000b403445d2400216220300d13339001050380321404c2e0344042110a103180c1c000c04288104100b0442940c0801e00d50301419083c100744440120014601c8269070080c0c1040d8401490200d69160300b0340ca07021000708100308a815807500e2048094126854601d5100e0240c0550040c40210031290040100f0315402101034220790302e5402c84c3d101c42d450840d00340c1c3c80140c1a5905c03000a0240305c018040e10340c10400070100545854030701440a03125125249448040204550224503d0347e034120842d04503229010000300c4450f1650072050650b0241c00d941c1d4424841c1c07000024a841010410303104895040d203a0403056541c5484034001c00ea401c0a04548000c2c03007000100006216840450180c0c1664000341450314041c4140000c4070048980080000030522 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 720105278 1250 720104028 720104083
    0xe0d0207180203040f0f030201050a0b04020a141606020d021201050d050d260403090905100308090d11090c04150903023d03050402100c080d200d02090102 68
    0x40090007290714851005a0f07a80e19400c0030315041460980c0149903403907001101c0c00f41541504914015910403004025403445141044100d11441a08801103148280030091805844c805040b0f03820303151029010684141d600e580490740302070f82b4800e11a9000c06c0054102d00010509030242c442901c0e8014040da4940b1016a02c0c000c1c11000070800011700c0d100e041c6103101151011918150721040740240c2824136015001031103600414840380c3c82d080002c2d030603445022404003100c1d0070442e840e15107014407007031011074844540c0640300081101440400b41e103404994034410200e08290544840c20000c0d400100c2e1040c00b600810041110814009030b42d45462001a020000c03035280800301c400f100126490f01c482d00c11100700d40c3d803000c88140385030305074000c00e00c1107200300c03410600e5003140c500c2603c503002410b40c041d048050030310206005510980c0189401c0d02d20480c58400c0481c4900c41c0004c0340e00260064088a0300814201c0d01035804112204005070800c0c00003003150702d1030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 720106528 1250 720105278 720105299
    0x60f06030408030c09060a0f0305070503061008090c0a060503040c0e012417070e03060c070c05011d03030d0902040e010b09070513031208010f081209101209060e0d0207 74
    0x2501c0500a080c00101055104550750126900c040c4050021601d0348069140541040c1c0b2040000300880d05040c002031403a441241100e00c100e1b4002c10240300c50888050444203550001c0c0311a14510415424410b50341e6407690f050010483c959550350380349410f01d03140c811a4180e0b404400d101200c00b005004071040c2201d10b50401080101640c241d0b24500303030450b1807805502502d1804002c120074041d1243c2d03c161610b0340b41c00141e00f100c005032100c0c6030215031440340050240100e21540340510040d0b116010b90000c0801360b0101c030310580d0140d40060f055902c15119212907130b958000010860500380101005400c1d010000c01c42d18502001003485042c000300b4500420000040c002107072005100094055504104541480745111002505848080c001c0a031500300410300050b044030005003041d07041c140c01e07102e03e0900140704144040d41c107035a10303003405001883e056400401028450a81c025000c1c14012881032800306111703061400b90081141150048070043c000750b4601d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 720107778 1250 720106528 720106531
    0xd05040302101701080c0a0e09100c052b0c0302090916050408070306090b0f01031e0201050d0c020106090605040b060418061508040201030b0d050a02010804031116030506060f0603 79
    0x641d88041011030021048541d201040d18003e0220900c0c1d00200d640840000c000c514560705584001e2040c3d12040550f6002908072148803032a03000e248500c0050342549c0000006103610700f002400c240c011801c0c03e060310000240c40402c18011081041d80140e1400b8084001020707080c214944410348010079100b40004014492000c800920704012500c128200e03001404000c086e9a80d8640780d18100b00507200c00706007a83c500c000900070413140d060f1103001c00e04995105040001c84c0e0051514801c0e01345003401c0c1a41400814800211040e605010386103808a6940c00080e415041421110444d101034201c0d501036442c05071840030035262501202c0648280804908009900c10300e00c102500c0c40b904003040004124100e8803a00c0d400496150007540300362414080090008248104403180c2c100143c4150301c0818007002550146c082241c02c00d010f45015a0301c0c115a00c9014a80074500b80e254078002d400035010001c1c01020703c500c6d900080101d40040400d08101c00290307007800b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 720109028 1250 720107778 720107783
    0x307060c150b0a08070e060910050604030b0402030c06030a1e0c0203090103050603030c010603031d0904020a0312090302030d050426030304140c090703050a0c030606081305011e1b020d050403 84
    0xd40704071102c129540d00307078210020400c0c1800c54808640310b10404180f820242c0d6001e0182d03c1b02000724407202441ea13559401c1c0c44c0080e1406003800e00e951120850705c1d070b02800c240e030507001c1d90150450030f44601c401140318160340c100c0840c80724000c000c0c155201805c100590402c516180d0f07c1c1d08101d5003c41151050502443d011480b62031703180000c1e0551155a142c4007840d0f05c2e2060000030141c1000ca10029240c2c10007a521740030740300c0c1051140b404400c8030029880050302e0000d100007564145d185110b5034a61618000303d549030f9000ca031a103801d2141040c0030490206080243d516000700e00241302c180c01c59858104101c50890682ea0302018000500c580c4e85412030910462040140383d4001c4001042c00705281019600130b402804280c5503450b000741840410f1040303e00a015201c126986070b9030301070103139031100440200e80f0072194048400303540381d403405d0f084452000c0c824000d07840c810b60001001c51250480311800310300810b00c5419500484415040b450f080300039a4200d98 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 720110278 1250 720109028 720109031
    0x822180509100911040905030904060f0e15010f141314130911010f050c0607180806090c0f15070b070306170d1d030109061a0402070c09091e0b060307060c15 69
    0x400600d000ea0031030040000d659000350be410800104d034210b146000c1c0445201d40402c100c2038503044140e41204030159031950105411120b08441544203d80752881540c000e8581c1e030078210310041c40c0100b83e001ba44603c21a0700ba801262400d40340074000d00320075844600c41000a1a6240d880c1e034186082903031500d0601c108107511042841c000e0040b140c06214120640e40e4520b072a117800380c0111085a40c00d041600003082c045a0000d0008140d801034140800038801c80101104219681d005d80f0401500848020203203030f014408000505041d40c0301d050b400c200d5182c1441c0050465801e648504030801c4400c8e817400b49035001080764040e00d203540c83c0440c5100119030300059400d000381049a0958a03101403101400082e0b40024289494207000c1100d118807102000280d0180c0c02c0c0c00b60801e01c40d01c004000c90700a5074891400e140c0718102a00d0b080d940e026480010300c1c0c0300303117003640c28030f000e802080981e24081c0a210040d0250341402d4034040714507120403c0060b408a9000072070b6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 720111528 1250 720110278 720110291
    0x12306090301090c0312080703110306040c1209030201200405060a1202041d090106060801080d0c0c0803070b010e070f050d0f06030804060c06050c07082218050910091104 75
    0x1500c0a400c0312610b950814404d0498590b20320f04080d180410b407008a0000e941d1002107800b140c0309018034503641301c01d042c800b420b549030281000024a890310400061112001f0410341210750342c0180300045009400000c0d81d40b00c4400108c141c41c0c04130070881c100410422080c001583c41c40d054400061892506501c0869a030000000134802c80d0070104072541800306081052208201040c0b107951500020301076190307200f038140c072000c1c1c0a00640c9040e402075041c02c2c00140c0318001340b81e03040e4061000303e08615503d0f4a10b9056500124040c0c826044a000612803c080d804909805c00d83d18540300d5042d00b0084001007013400340044005005480c0c0702c410b00160082d4028101441d000104c10303907101d41d948005407507a190103e08460342d9040100041001d000c03c4140d404031500086c00e24a800e41803210125a80e806e42000c40102c4400d003000700340d0309800114525146900795001465007040700343c142c44c1081070046907444900303121100002920840c44075014280a840c081180c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 720112778 1250 720111528 720111547
    0x60501050a08100f170d08072307061802010f0203070f0609110a06020309030c12030f0c070b030a1e1a12030403080c030d060b03160e0f03010c030e0105012306 70
    0x19030f15550141042103402040882c1100011407018800050f0300103c440b0b00c1d4000e001980d041204981500c007141c41c0c140503041d428101c0e50000594103813170b03d070189032641580e100f00071581c82e60248900e4a12100e10308045580140d030306c01050280e80011810100d90b40d0703c00c1c066290014004003400c1c0c4488000c4100440a032000e944490028410041e80b600c64400a5681e0000f041042c468858038000c10b5250074030b0021021200c5000002e0b40c540100e1321030b510f6065100c0800044903101d160400260200700501443c0030703100b48240410f4a800541070540710007804400c1d840303418030708101500300a85840c00c0705d03010402030316250440384c0603200c8582140110750000d0081200003802c0c080c3d001d030120080c4543c003440f180030041c20f515202d944200d40011030741e81e0204440754800ac8442402010b0003101d29600600c01070140810308080382c01d4510205010b130100f900d584503016094428006d4a0240880780c3c030712507007040004556120311400d02e8596015141c0003e40182c0e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 720114028 1250 720112778 720112801
    0x90a1e053c1002060411060423120f0304060f2a0804150918021918030c120302010636062c0903090f04051e090c0310060501050a08 58
    0x2801c40c0080000a091070715110103034680710b0844080360040a1080301181e42c4c40c201c0140ca040c2c450780c001e2010781a80c10203040d644040c0500b0b241d540414921240703036080c042084418040440e09001d142c603107140401c0641640c20700c43e180000d2204240c070220901c10f0024a040c0050803442c0c500200001030700748210310380b00301d4000003050141c000c00f441d181900320b1180d108881e40f1035115499012081c0c4000708070301601c1580440c8140c41158002500c1c0310b000c0e481c4200c42080c1200202c5a90782c1c2d5517a6041704c00b0750054280c51041c007602c100b41a020b206e020000c00303030a4282013070381030fa5214a44055160b210081c0244810805984603c90703240c2c0b005000d03205100284034545001c01030400704c02d031000c0b040380441ca101400200394040200507220011005407081244582d01c40401026200043c1450103242c4003041560901c0c5180f001e86010b980391001403c8404500380c24107040c100c0b42e40c6112045030410400300210307640b140c00ca403510340c003c2c9880e42140c1c840ca1800b24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 720115278 1250 720114028 720114139
    0x1a040b0f0403030f050a0c090b12010308030a060906120210030b13091103030a020703052509050a020d09030906030e0f10021608130504060e1501030b06090a1e05 71
    0x3681178542002c0066041d140d0f032004118100a40301c5200ea43d45c3c4801118040c0300300562800301e003403400c004100240295001d5034200c4a1184049001a107420381401100d45660162159054100c0a903007581002808000f008440d843e0600030b903000b005c00324640b215108400a000d5645031000b8041c001340080c1030150000060a4079a54158080000c1d6074200c14001a04c50707009514110000c001400040b400d801d145603c4415140d10344603070381004040c010191510280c003080303a5860503125100d43c41c0e4080c424bc84410340e490800750014121070b890300e00c500241c0d00041202c05045000101c5a582e0b544800000da690b400c000b44c212030150300c1c00001000801c021408808c900b440c0e8003400152203042e10100500c0d03640c0c098004103904103884840c1040c8a0003000a071952007a00850b00240c009070041c0d10300b0040c6404a04021015400740d0b007001185010700000c410200758000040c0300c1240c4800782d03040c1d1b04802201c80020740c174142090a10300c50f009400710074042d0b0300c40c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 720116528 1250 720115278 720115301
    0xc05180601081504060806010608090303250302040803070f0c0f030f02060901090302031203150108130f0215121503030c150615070b0f0a1e02090f0406030f1a040b0f040303 76
    0xd019440c0c1d1000020f50311f00c000e00400300452010000600c0c0b400c800800c2d2441240140300591349400310401742c07880301043c0800d2908141d020003020660000803c018030503035101d051401120710550518884c00d0003160400500100c2e219010008144600710341800070b03804a4005550710895070043c0c1d00c20607a0b501c02505802031504400c00401c2a0003d14402e6080c511070711000003c80b40111000c03c802c95645485011100314031000c50311000c0c4046840d4405072801c6102554a421441590096865880901106d5040001d04200544d0602002030306070010350400042c89501d6071140482da00d010990005100010100e03036038050276001c0811814400b0f580c6d030a079400c0a04101c001200d508545a04100c0444c0200700c0e240315022103148901d001c0d03a03151204000c844042e61111a10f80d034002e10000c003100340750340d862240c0d43c001d51145810004062071403520003800400890040680180f0f0b6013000040303045409184e0f0b01007050045410150b0b2585000d8000301881c03a0389 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 720117778 1250 720116528 720116531
    0xc04021803120a02060106020a02010c12120f060306060b0f041a0d020f07020906100207180e0f160e04020906101e0305060109080304080c09060a0e070c0c05180601081504 75
    0x10b40071a6036007009007a00400e80e425640e65a803908016665809003070b100900080120b060383c40868640c6400407442650b030b00e82240c0e0405150005400d80751910710504120356140b0007003003084258403544005011110005040804403c8400400e000c1d501c02c0408410004c400407451020303c808aa1040010110031511003078450000080f82c4c200303e904074081d0b110440130828502e04014507c2e00d03c5800d50042a070982421044c03084002c001d5821488652601400b02c010b200a0000010042c1510010008010b6680c030700f4901540b994401c210141d040c1040c8005a1200241e0341e500c6002501c030111800039114044800d203a44d660030610440c1102041602c85c1e40c9500214007500b4240e0300c9a0495460f000c949499200b24803a0056076801042c2179006800c00b42041540300344002d11803020150341c0d042c504c100c6031007104d40c7c80001d5030300c1e11420304100b841000207000e0701013612207895000740716918040c6180007420301c81c1131010b00e000054800030429049030120381c002c0c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 720119028 1250 720117778 720117793
    0x15140f0703050415030515100903080304050f010507081e040f1e0c140d0209130212032a101d07030f02030f0a030804080901050423130203090c04021803 67
    0x6000380b6540003400b504485501d0002000242c52290050710700070001d03d80749903c200c18440800c00c4140f200350380942401a600c60020200e000030015512a0b070289024180d0003100e04007207800c48800808241c24408110184881d00e07110304611094403049610207422511941400c2c0c1ca441c580740401000b80c11031459948070b0356581041e21508520842c90044941e803100424020074030250a1745812120014940000d40b500c0c0b00d00903040f0041c521504405122030300843d0707052020344406841c0382c0c00001c0c1c44800a06d14a8001880c1d5500c480e2880002d05459001d9100d641005045030f0880c0c48014141a80350400a00e00200a049044650740c035680d1030030244145d000c3d40103a22900a1071394110809102190505182c0d0713150751a0b403482d030f079640d840300481d801140b481d43c10840140000f1413601c0c0856000d0891000c86600c1c12480c90000301000542c0c420401c00c649940e0045c03050002200c40020790185810080b503000d6103500444034441190b03031070329442a07030601c6030b060b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 720120278 1250 720119028 720119033
    0xf0305010b090702032b09050d02070e100e041101021617060f0f13050f10092303040b0f09060d090b13020a0b0306060c0111041e15140f07 61
    0x60212800e4402982c0b0180b03107654000b0141c4c0c6a00402c4484a01031024a8a4100b601c1c6090107144102280030b0700000c001d8102c2d115175142c040840380c5080582c1c0a0710081c00443d03600861658041c85070b0548110890601c1c94058207148090002031410705c1c00008505603038002d0129000809007a82d41494203641d4030030022182c10707400048a580d005800201d040c08854001940c440c0242c41003600c015102c0d803101c3d000904100e40181c0d0280560365109103c40300a1000021081200001003840d4420f801c112060b006407410384280d00c03864050310034910340302106407001c0b11051b85032b035611408d0418208410b0710408400940c0f040000402e21019201903000304d01e11402448940c14651b650305030000d03240d129050103588076040d184100f10b9100510000d5500510240410f070425034209502e0742910907618001c4010300010070280a196039144441002c2d101410682010920303000c40e1821014890340310504100e4090000c00c20b281281c01103907621802d81958580c2d84a650 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 720121528 1250 720120278 720120281
    0x60c030e0a21090f050d020102100e1e010b011e12050f07020607050414090a02040806090a0215040501170603070b040909050106090b010e0108061302070f0b06010f050406030e070f030501 82
    0x40152140e4007404003950440b0350b21a04000040d9006103803c16212030419007000180302100344c04a0444c400c88001d00c07501c0d66140100000301c694174004146440300b0011700b001c046890b58545451382c0c0b4203c6000c1090303900c145181010702c01140c116009203407615040320585c0b40361804051060a020078013030320321501c404052180f0001c2e0300340d45894581c0c00c002c0f2114480e6128190100ca1980000748881c40c154031126001800418014901031b44e4001490800e0000c40f9050042d03003101c40d1480940c2001c0c401445d40b04a5841140d142038102000a0720110442481400c01c4280c140016815242081100301900c1d40c5101c4c40e0326990786204a00150054140480d150b500741000000c1e955441c2c0180c406800d016111758280306049401114551402032403030740e204d80901700d140e24084503440102625401000040b6040165091035220b160014280d1410803001041c461405da034040e00b5201941c51914000c191200322207000391410740503800540000244070b10010400905 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 720122778 1250 720121528 720121553
    0x2030309070e04020a060f1218050c09060328050a050d0908010911091902040b0a09050d03090b030c120f010305010f051504020d020d0203010b04050a08010203070c060c030e0a 77
    0x11041141c0410341c8809001034182d030261402034011444680500c51240240f225550303440207490101050b400c0b28a00c10700381c0b01e407a500080810001e03203440301800003c2c015001804003d03200b840b068148040407a03a035850005060400e074165424441c3c02800d04c1c15040f142a411204803903c80900e4144a9180c814141001022403a000b000288000060198612441d000810541051000300034040b02020060900c81c000c040c0c81c0c04901505c900b40301070b00107404c100e224562110407240001e80b0400d4107800c514072561003140f00c48002a403207202c0c1e4094801300c40e0748980b240c07900700c8403801c41d00910403096541e0700d950b4100444117010700411412079004100910650750140400000c581c0700b40e0b10304e000d03401c9210308011a414550000c0c0070101c0381d90401071501c60401800c034102d03002a000315840d608005020030180c80c044060707901821805001310303e1820040c201500001070100010f140a0b2a0b00117641080e01036401036145481500036195000c603a442d000d182440f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 720124028 1250 720122778 720122791
    0x90f0b1807081501120c020319080711030c0601051c0c080129010c08130b1803160602070905130209070f0f02121605031c09030e100c02040e0f0d020303 67
    0x8200140751520480c00d07040e1000f1068450800020752204000c000d4601d605415040d403008008150700004200c50b10f0640158a54a001e10790401c007000528a069a42180700c2c0d5520a02001c10755820202c2c02c2070445030300b290400c00008004001c9a888021140c01034042c00d002c1d08001080141900200804004444100991001d841002c40d0380c801009140b800512011000c80005003c14001d0052504080c00d1400740c0342c2d1107013208820750111509090000e4200106c20325424208101d254601a0050703455650f4100900259204000d100b165900c0d61a1030201708140c42d4545402c20454014121070854a031109019000c6018010b1000015401501e401007040c804240300003988007403001c1c0b529080498488101020b02010f0551700c80c0410400740000d0b200c0e051200c1650032440b907001c00c059855040180540e00031001c0c40340141106ca0070f84103110b50281c502882c00d0b9040720000703406040420007511346510440443e04501c54460380c0750103142c0000c00340d8400c49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 720125278 1250 720124028 720124037
    0xc03070e12061005040905030a2f1c0c03080a0207030302040b0a0201090309090b0607020f03010605220f11030403231611120a0f06090f032a0507090f0b1807 69
    0x3c1d51340c001c1c0421501c1c205000380c51030f00b0502100388894810851251104201e0740e10407007642720030380401d15148a101015805030f20107400504480c00100d49810480e58504103441040440c3c0c401070108400245190350075139000a407001010b02a9050314040e20080e0500c5840e50746018020b03000b0010340340142e01041c8404400204c107900d03400340351010300d00035011900b05106507092061202d443c20303d080e415500d60302d0111316501c0b9189a8101002c5c80050200718569000024080365200c10702110080c0c1071031114101000508100c03600281d040c900021078004c101c40125682c4030403280d680e01003100064000d41460303540e042c9030742e082c040d41010b040500000100164a031240c91201140e40042010f000420142c0540d00345960282e000440e5209565a529480400e9140103d0108404000e182c41c40c0011000b403a98050580300c25074451402c0b81c40e125901c0001b031203034528542e206c0c0c071068500032a41e08110b0b40107101070804074240c007202410303203205941113441c00c0004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 720126528 1250 720125278 720125311
    0xb040b030123030714150f1b0a0c050f04150f0503010c180b070812011d18120c150901020702090903030c16030c020909011d03040b030c03070e1206 65
    0x150508503200c03850b0400038000c0c0300351890589203c856504d0010f5055105041c11042d6032503000f000001c0103030301e407070f1004555584480c0d42d80400d00b1040c500c040c036071a4440ea4001c00000e408400502c00d64408031036400180d01d6041c002000b800e00700c80d100300342e42403120000030803001580c000410382d03408400030b0100114084044840103c00300b209001d08c0c400110030081070350390303400400449008038409407401801a8840c4400300080c1e1040340c01407842c074a84180b44140303940407600415003590b03202c07828189032649a40c41402451180880000103a603580070101006020105104600e41c8011440c0c00304280b4001e4200b40010b83c000c50710b0400050302c0280210443c2d1241d40341c1142142404c00c01e140e0b643d80d071004601d003101400304202e09200940d9814440343d11030761000c000410500d007802c601c4503940d040c1c6078250000758410301c000e0011464000503030b070780020780c41000c5440f030756001022210388600d0038405070002001e00c04a00101c10208105100da1126032002418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 720127778 1250 720126528 720126569
    0x1150b0d0522030305063d05040e070905240702011409031b090906011203030c0c020d0b09011118010c0228082b0503090703060e0703030201050a11040e09070b040b0301 74
    0x19130320103c0c0c8054500a04440d00350651410740844d400740c0c00d030345000c5040c12b85a02078072000e03480580303422010900c4803004021503d840094010000c4030320005334040d581c0084d003801c89000700701001341800307840f843c6602c036009013a05035140700800508868050000c0c00c02d1010002e00030b00164021290800054902800001c600e8120740602c0248010075546403011401081e070203451104001186003000f01580c0d40c00c20f8026210f004603010401401c080002a084444426a440c0142030030302255038206503c50000c050688207085c0585601042d200003048601e20740c1c0380e4484c200c0da0b501c1491102c1540c4034200141c45128084603d5644c0100e541101c1c000d05444440214540166598181e80b1480195402c0b0f41248111060142c40f83c0e02d003006e60780002490519540106410400d0560900440ba0019801201000602c00117190409984124040c005074075400201040080501f001000014018040d030382d0303141c50f02d583c4900800e5100307105000350055841d421500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 720129028 1250 720127778 720127819
    0xb06030115120f0203010e1f050f01050f0f0304050c0a1403070302100509030709022104020a0510020307050f060615090307030b2e060201150b0d052203030506 70
    0x1070700e071100d816041d40103184504460304015903014840541d00c826030039612039880d0000d103018014074510810246080091031070401244403284011000c00c4504000c203449500000030683c00a1030080c0e61800909a071988078480c00303025030030355000081088148000070880980b0200c0c00c4400404036995084100c007241c038001400350703040d00544000c00044c900322020446402250510f03a05150301d8000090501c001a841400d583e600020039400107095214101c050000c40340d2080520b00745500420441812401002e0040748203003180340c8014020010346140a0303102c8121003030507030b4a020640c0c0b150420340b2254001d026101c0590b00038113074103041d6503095802500801805103103880308a450007001e0055000301110309408400c1e0311440d40d001a40c0e59409100d00501454804000d08442072200905828000d0001c14040c3c929143c044815840140d00040341d1520f8581c003e81040c900d8041c01184584c1c0500003004064154000c1445044100c440e003580e50810408401d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 720130278 1250 720129028 720129031
    0x120810060e0415050910060201150803041e030803181506090a09020103150602010207050606060a0c06021809010305060901110a0c03110f030c0610050103090b01090b0d0506070f030b0603 82
    0x41040c04107903240740d051a030b005140903071401c410741001568802c0450020700e400d0724002104034080301c2c140401d5409008000001a1103100310080c10310b80480103032030780038501500090184280e490f40368403c48200b02000b454210600c155070b03040c0900c2d240000d004400c02c001442c000d0550044010500717105c2988030748009011909640e0318014400000c001020080341410b5840c1d01d1000e41d55450381c4507038094112038000581c0c49200b428200d1404500034040707803045104200d1101c4042d031144400510a91019025817a48078400300d91594018040780160008e030b2203000003040c4900011150f0050001000030031004000c0d0380c00100b540b0501017000c0100e9807020120740002c0c4541c1c00c00d130711896003a090302c8484126420303031401c40d4008004c29900c1d600c03074028040c03496a00105a001081300f42020404c084c0c440d9140c01e1101814071485007174903501c0c44851101e441e0131180c410304a83c004255540c900d045840503001694070020000040e00d046012002c0e81041012613 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 720131528 1250 720130278 720130289
    0x160503030301051e0a0f06030b0405060910060c03020f1c030b03060c04050f1f0906090b0307080408090d0609141002040f170a051b090705031e06010e0d120810 70
    0x342002d02d4100036001804c0c2c000100560481c0e45c074000000d0000b46001030101400807985d0204d5112609003c00040c0c80d0041c040030b105000d80c0040c403507165000c96000c811104a8100390a90b040c490600380c0c2040408400d81d8624054541840040100744151000459040e2820405407004009141c0e940e4001c451050a03880208014091032410301001e00d01c0707040007003c054081c12090322114410000440d4100415040d1b0414070881c2c0c2c00160310030190080044060852a0008004100401c0170384040c01c90800021200300c0d0303807600c0c4101d820760380c0c120405005200d85442c00c0701c86003444900c101000c0c080c2503100c05003401c3c0c5000315003c0b0703004020b28050b15800c10b0a103101c80c46854454852a200d060b0080380050340c10b010708400c0c6450b90b8075109901d203401003480241c41c0020040c0c0d0400801b00100501c140a1805030000c4111010055104d551881c00507102c40ea940540d0ba07510140c01d1b8020020010b5906c004200d001e41c0d0340e030302500f50311400c000e2484001c05010380f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 720132778 1250 720131528 720131539
    0x909070e0d0c03300c021903051209040b030d12180f1a010503030a140c0102091309030e090c031302060d060f090e070303080703050402010c060905032a0c090a1b0216050303030105 79
    0x2401514000401f110a0308a19450745aa2540c0396203039403401c44a080e000300b0f07880c03000c5078442c1e152a05102c0e080046105502600184640100c024400e1013510174020403548d40b24031107140345102c0850882c0072a4800e0350f0040101d200e0070000b45000c1c014080703410b4080d40400106e82410084160f900d4400070740c5460300d01c102070380350b440030580080307240c6c0070345660900140426035070300c410b018a071548a120004e03d004d028140103144040c2000c0b074034007070040c0c54180080c82c1051404c49a11820b501c0401e02d80e6042840080c3c107903c00d8008035a0b0300e6080c05004a111903e2120040403924206004c00076940c0b01c40810713494070003178440507000c42c01010000724000e000307401441d841881413402c0300030f242841e520307003040f594520f4040c1da41c0e5101107100080558964040c1c1c5101c40f060440d074a00513040d503030003031740d418a0f01c40d0b06d80101c040a0204480103490340000080e400b055410050190103a40000e5480580bd4030a241386c614081c1e000900d41004070850703042c8d4002900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 720134028 1250 720132778 720132797
    0x5030d090e091018032a0206071718121c210903050301030210030b060d0c0509060301090b030712050c0607050c030a050618030909070e0d0c0330 64
    0x401e80841c0101101c4450041e014007041460040c4500321941c3e00ca125081002d00d20b03410002c1284008004051171480350070350782410300300380e41c111303e00c5a039044400540d1082c580c40d080400f140341000c007800c1000302081c50102c180c004008905104426180b45c0c0010894106440e038918185501c6028100e0421a000b141842410341c0001082110801c1c040b038100c01c2411422030f40d142d0700c10703030000740d01100500c1180b40400d5003408008413031a00744545031118000034480d00c100f00000700c02c2542e80008040c12802071050f0b44e81c2c004010402d0b503d0b0740c1e407003281e07070040c01e0b4043c064ee200b03001d500380101e9545448a900394540d600900180109044001449150307440000c05803054400c44080d03841c195020061000c00521402c003030030103810000c0000f111a041c0c42c240e000340f034209018134442d68407841c44541d4000b50500c0d1503002091307004c02080c071000c02c401d000f5142d01c0d5102004401d000d0408980403203021005c2c00e408010b4403244c220101980c1d425007441c0010144903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 720135278 1250 720134028 720134039
    0x82a0409020114070609030906021c0318020904050106060f1d0405040317070914040e031c020c0304080c0f0105070b0402091b31030c030303090c0506040605120105030d09 75
    0x14003110034648107041143c002c842401850760715030030058003100d0198842102c04100b651006110700280200e0005041c810b0795800c8402d600c441d038140d40e00400da40c901103a10903c0b0b00c8590402030640107006900642050304003140a020750340151008148483d00d41d54445104031031041e55111001942e06140740074204001c041e040c00b2b4003e9042003e14142c450180020043d8240244c05613101c081c2483d1409400d4480001c03404442c0e4411f0b0f00d0721100300b10b080d034040100c1d51100e150354080c0c106907000c400808005c3c000c0000c155240d200c0450040350300b481c005084169180d003114500301100d011001101c1d244200c2c2c4005010842c4400810014241152540c2d00722041c0410a44170104140026009800082e44000b40031500707101048101c50142000b10b0401000c5100a2007a0450300d1b03d01c2c58802500c0000c040682d40c0b0208414002c0c980406c1001d031100500d019a2566242d000400d90303005400005607107840310000003000e260000307507011a4516525961610741c50700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 720136528 1250 720135278 720135281
    0xe090115120e0102070b1b040e10080313090b0409080a3b090f07021509012403020405090d1d0a050315010e0f060105071e0f030801082a04 61
    0x450403242441645900701c031001074140a28590440d034070000603160301950420100400010f00011054100b403840032001d074824008507019100441350141301e0740c0302c0c0c2ca0090301c001e0081c0c1c0081c00c0c3d40004106a20190300039440c06040b0fa84a00040c04a05a110304100449040c14001007850800300035900146020f036455400907840c603181d001c404540540f00c0e40e120a0703412031323110b15003c0d6400401c81d681740c088002d0303412600d0b00c01c4640d854606900007030b5990004a844500000081002940d0f0403402d403c1001642402402d40c0c0c100d200c52841c00e0856201070000701d10403400c140000e9048180011103070000c2c8855940c803800801510024194040702a00d065000360b010321011030552410081240306c0100c41c004c13401250700d080d416014095002d003140b4480c0d11000280311030303603034483c0907202540d401140e00d440c2400c207010103103c0c03c807401a00807c00440110300e10706043e006903555040300c0c0c60b04152164121020015054aa0022a003012030b101001108006041a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 720137778 1250 720136528 720136559
    0x40b0405040902061303110310090803011a0d0608031c1802041e020c0a050d0c0302061b07060507020c010f090e01030b0402030123040c1205190c0504020c030d0c0e0901 74
    0x34040c0d9107807049640c45d0030b43c8402190000c1c0c902004014841c005410104104581341c3e2901c0d00421000086946181c542e110600ca105000c41d14140461b145215440072504820200a001c00c038507551420f85603143d4001d6106002c03808804042d081c0704102e2400b03407c8a400c1c001488040c00d5050f6801c1000a2480e00100c0340b1044030280c0f80381014883c0d00c010402c0c20100001042850710902d071492412914030010020000d401c200000080d400142d001d030081209500c030b00c140c10400e00111081c1c042c11402070b01e86810403092242e800d80100b1147c18888003a6600f100342c01008905942041103403103900d035158610f03c01000030901c6031a240342c00c0703403004002080c00e000c0b80e804143c1c02264070584111404604083c44108052000b00000070b18854480c000c012040b038407080c1e11884008021311100d01d000c60040300308000e45121101822001b8400c40d110b80021551a651350002c00d120b01c0e0742032909440c07559003406820000c01c240402032012400d40e003072809d102403200d0b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 720139028 1250 720137778 720137783
    0x507081e0c0d09080915040b0703032d2003010b0a1803080a0206011403061003020d0212071707090605031207060b09010b09030d081b0901020f07030503120a02040b04050409 76
    0x101070201e00000500c0f8069100c60501603d84036071280c000701c040140400364040c0104480404001c10080c0a04000a0700c40594241c240080c81100c00714034400c02d04440c1c4640c0c20740309840f12407503010038119400340071030284201d0340e506081000450314103144001c0c0a1841c645106108004d4080e1044840003d01100d403014040c2007681c95848444a401210030700b40582c12000040c04010210100050320403001c600500850815101e0020801d01600019020b800a4541403041d500c0d400c14000303100402804072803155684122001030f0b2103a440c6000d02d14050040002850350a40c060241601c3c40103000c0e094500886101c03510310b901030310b42207171020f0f00c50484020342e50321600141e00819030080c120f61b464050008160424562031002d4089c84019400d01007404442c1c03520001100b40a141555a102c0c00f40060303203817000c51904e104040c803a203080070041000110151210100c006080c800a4440c01d0201007070b8040c03406000c200d03070024002001149400e400c082141030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 720140278 1250 720139028 720139051
    0x12030207030f050312070309240b090106020d021b031b19090606110d0e01200f030c060f01030809041a03240c04030f0609050c12010509010507081e 65
    0x941d01e60768640d41d998560b4040c2c501d0f80002c1202d40d40d507408104c1c403582c089002e00e010800d6100342c0c0d0781c3e003030704804461030307920340210f40942d2900250150b0700180120310001c05003c040c2d81d41e403400a545181c0f14181c10014015141c83c0986107100d48510007400c20b00400ad880741c6181d808010a56001da41801e6a01c54040204c101c800100001d83e9000b40c200d014010407580c0c14004c0181004604040404007944a958804c0000d0362000301094204003d10b4040d0006000d40d0514000640c00380c80720640c0d00030b2102d0015050760000003854500390030303801d5a00c0c9907298096200d45034424840684001700801404a0901d0035506c06421840d80c010000300410302d02020030301d0501c242502e041c402c980c1c8070801d0f0030b4010405266034080e5550000e80c2c40c0a003950380d00010082c941c4001001030351104840350420409001c0c0c045042005081864100440d069090180000340d59000e00743d464100031845a500c100c940501c5048001520103580750592100240540700400198252 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 720141528 1250 720140278 720140293
    0x150c090d03030c0810062106050a0e01090e030c1e031b060601030516090501050d020706020a1706030307030e0f04110f0408060105040b0109031203020f03010e040624120302 76
    0x196103080c45a0340d51406640c00180d0b05851070005040e00c81c0160500324588000041000496803000d1138542620b5250002c00b00c0384400103e500c041d1007950003d551081c08403c0124000580910b02d9040341c96800c0b05110100784070340e51907200c0c490207203541c02c00d800240c040c1c8040d0707501e122030f500c1811011003100d02d491540700052451100228080300341750001c00c03d05c0362070369040c000c80340c0142035205000022824000042d2504103244103c0d414814086200a006001541910403494000000359629103040f080201b041842421a003030403203501c0d000c10124200002aa19165815210810044104020400c40300544c4400c1607105442350f191103910000c100140050912403034107582c844d82015141c50611005801003070140f0324203652202981c0e4000e06000440350410810000e000d2410001c401a01c1100f0350001184000000024031aa9000f0130070301c55030003810301f0030164031000c8917005210f000c49011451800582400d0008625020006005501c280102c4120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 720142778 1250 720141528 720141547
    0x60c070c0305011b1d0a140102070306050705090312040f0b070f0606060e03010c020c091f150e040c03020304231504060510050a060c1523090c12150c 66
    0x2541c8001a0040500414a10b00381380b2a030880d00003002402c0800203400c4c01c030440804180455450300c10381414407030f1204a01450b900038460b410255801400c00e012504c4c1c440006440707a0712480016000748030b0100c407501b00700030440a0307500742d41c940c0ea44108550f15244040310b00f81c02c02c0388295120046049400000303019842044000d161584440341001303854020142184d0302d035080b02c015034010056000e09951007140259209944601c40381a00c84c070501c42c1c084a4007140c119401c04802d020712505466004141400740510840d402e10048034103000480c280e01080c0c400401c0b000400f101400c801701420201d55403220041c040740c5071403070420401500360800750781c10780d051543d91017805510038203140321b400078140c1524402805c0d450300c40c00401039100f80300b001e425807c01c41a0103a03103030041d0304000080d1014440c050340d4040300c1c80703005071030039025907404c50184100c0b02c440080382460504c1a64485a4801070500b0078403046175110a42d40c000c1181d48002010001d0300038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 720143884 1106 720142778 720142781
    0x4090f020d06480c030f1b03080a0e0604030c0605100e071d10170c040b03010e0a110f2d03090102090a050a0503060c070c030501 57
    0x3140c25040c07550082c403040302c40706125201466040c2403840c0d03c0c04064070804884210000c00148452200007442c2106500000300f0101c15010002ca801010114101d0046080400350304c2840b009074482d40030030020407000320b1000d40c140500c1a44034480c0050042c0384c01c008002605040d140a05102c4103d40010701c2c10303440700001030a2480e44640e16008100f00140d00f03400d03061010010b4201418100744484280c518a4403100c0c41c0340001c4806d0300c000c01502c030410018101400c04524010003803000103680410000000c400001100a50007007040d18242c40b041c0c01c00c0400241503604241500b42400c5090080404410103002100c868844180c6042d680000b941d041600303018201110420310400481080005d20040d00141001181200c180c0030413070b120000c1181c2e5074901d00509400d82c0c00b940002c1c09446001000380780c0b090140c0303402c464613035699442c40e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 719964028 720143884 := by
  have h0 := BRFrame.cov_init 719964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 719964028 ≤ n) (h2 : n < 720143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
