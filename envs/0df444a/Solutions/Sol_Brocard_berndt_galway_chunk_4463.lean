-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4463
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:42:06.570773+00:00
-- url     : https://prove2.me/submissions/56d3dfe4-b9e4-4565-826f-290d8fb02322

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 802517985 ≤ n < 802697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 802519235 1250 802517985 802517993
    0x10b16020f04020d0501150e04051005011b0501060b0a120c0c080306010210050c0405040e031813270605070e06091903120305070807110c010e03100e2803050406030e0c0d 75
    0xc61f050b5030b1240d496140c03c00032001032104803882075a223240c02c01101c00003044190f100e841400102c0b0460a922604174065656450075904141c100c000e101c1c0010131040980d80d4486006030190241400c1070140246122014040b44c0e07400c10041c211220020001e45164000c01ca0f4020904003003000300300525215070710003255000750248a11542c1070489221840000000b0307900d040004803c2c02d51646c0020341000708c11004da610540c201e40d210f4280d00c12845900300740c5c3c0340743d40a8444083c00f0b2900d520b0f001003203030802000101800442c101c10b041e151640c5081c0c030703100001a03401861890804500185031505603200030700203030941a5602600e981030b04200e004441070344440b00300d80ca0741c0000382c1c2e603607031460440e10702503101c4e0071564104d40c480e0003c03d0b030302d4030003030300752040d200c82400340600f500e401c082080f51544c0320240a1001001814110040030021000d101000b011980d004280e845644103400800d43c68400701c0768403000511210910342c1c1c006041010520042c90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 802520485 1250 802519235 802519259
    0x711040e0d050d141014010903060507050705070e0912090a0314030712020d080c0706150f14090609040b0709050907080405010c090303020d030c0e0a060314010b16020f04020d0501 79
    0x100201c101c40c280b0054001300c840007a8000e0003403080b2401091306604003443c0c400c0400181a80f141081540200000862014490340c0c0c003801e5666034990351900c450811a1918143e40d100036103800444040210401002c60182c03041080503040c4e542c3c0b1501100003540941c40c542001e8032224502144410b1068004001d2a08500c2840e1406000700f03082402d9844a40ca01e1f4100d0101d080304c400501001448c10080c0070161054800203481d03014408e85080450403504071010000700c040c424002c81c034040110350a0381100303c90400e43c0b031515601242c105000904000c0c05400204081230240b401481100050a40540700300d1141c602500700038100401a40c06803044d500c0d100402c40b0390b41c4600344000507aa0550000c0c480142851401c41c010303c2c041c5105c008124211000581c10341c0c81258000c0100000c0c0d45c0403c1c041d035485107443c0484010b0b07000e00b0b528041000040d10440c600000500d446030119403c0001c3e1806c1c0d8042400b0b8400d02c0e003924034035403906001245c0c81003a00c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 802521735 1250 802520485 802520497
    0x1b030606070809091317030103020d080705032101261e0a060c0c020a05040c020c06090d0506090a2a050114091921050a06150b0d2a050711040e0d05 65
    0x1610040c448007054101d1b036482c802800060b40001014807110040746010001740002031050044034600a070b4154104001c9070034540e0403808032402c0004112110380c86500c00f103c10381d400708402044040e8280d0968648200340644d03440c01d542c081d2000707048820f2151054164124074240070030f2500000080c07a0052404040307104000c8010049441d0425201c0c0091307560355a0000c05110303d0000c1084015004021051b600a00e01c488440014105100d09401154054018606066203140c0000e001c0c02c0c070303c42c0d040c1e2410700620a4801d10b806d201e50008492080c01e0600b2200490301c2e00210030700c18543c1554028a0359040100c050030f59060b00c0c0112400c0103072690740c0c80d80241514281e548800c00c040c1481e03100c441a040403a000d98881c2d000c0aa80c899418401643c0702c4407904c444d0008141001d52903540c003441c1000d0315420141c00c0340005c22a5854a44100044016145000d41c1d500917094a00802d003450882d1510392094a0034408807040b81c041c4601244021f0440c1d1180d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 802522985 1250 802521735 802521743
    0x12050f03070f141207033b010605042307050928050103020a091a04170303010608060a03020a1707051507050c0a050306040b07022407081b0306060708090913 69
    0x240942503d644249400d5a01e40c0d030800700a040746807155081200a01764030079039840da10580700c5446540e0200e07100f007214070702500b800c000400712814042c2401c4400d194080c078002c41c20140c0502c4040c3e5040b0a50071100a500c064038855102c085085500f03015000e070080d0058040c18070034030031140e0a1440000200072100c8160926101c00045050780a260b00c10004036940b0a0b05000043e607500101eaa51921940c0d4a030606555803482d01850741c81c000c4000003904000010b2002c9a80b10030701650104082da00c4500300d51860740800c6a5405611440c29988c00039004885d1101044c0856030041900901c2d9106110128962200c583e002c02c034103c41d01d12070851100810708014003e4411100010003030a00356840d61a07500c4800c6004001c4000c50084001401c600507402c0c9002001c208138000c0b104071441c2c03890015010b5a40a058031b12450301c842030100001d03850310120b0342e200a0944084d03441c1e0f0410329003010075000b588003442d440340c487c0d0200215600c00760740b2486000e0107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 802524235 1250 802522985 802522997
    0x10c0606050d2f01020c01050d0e01050c04030b22120e1807020705030129060d0f150b031618030203060412091706010302041a130903021b0d12050f03070f 68
    0xb0342c40c000f500810040350850150300001809041036008030090180e100500c400030481c503000030100d90844e242103c646003e400041414414850003603e213a0788a191500c854034400c1080460074040c81000e140284141e0b2110310580e600392280040c03501c60680235240d002c4000315904546000c180c103d900d4401845161000142e500e03050281d04042240000003e41108142203050030310b100c2c8504181c2c10034810042c02007001094403d070041510801c030009844090a402080b51800942c017545185a0500521003218000d010300d644400303082c20083e554030b00d84940c5e84040381c003a82c07002e541400b40b10100710074480c141031064400d001564810000d183c0311034210151004000c0d4900c0786502c018014801810650700c2640640c003401c00f94000305418500140c503285d04440c80c9001c8580f2040c0c2c105c20143c040107442c40c813800300104c07145242240c00c040740100c10101001341c011340e0103498510400e4003075811600524030140c138581d40c0c0c0ca03003e5005800c9002c3c4d4601e40000600e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 802525485 1250 802524235 802524293
    0x4021c0c2a0b060904050c0607030e0f010306060e0907020705060705060f090726070b0705010b041104050d060207060f062d14010c0c170a031e020a02010c0606050d 72
    0x5411040003607001d0340082101c0352a11000d040c4551001c005200b02c65511400110500079640e00f4060001548266a480c40ea07038499010f1124403d80d8044090615007801c1c0c0502c04960841c69910b845201500c10309529034503420200d1900b442c0d54880342d00124002030b4181440000b2941c6031162116803200c400c2625000107859031030295210340d800c011180d443d6503105120840168000d40041403c891070152240c1407483d2a0380004130031102695903640c4503440b42044d00640050005040c03d0038101890324012a02c10400703010020001399000910300308000c620303804980410089201048815211951501694200c461a8080b40202c1c0d41c0455a5072039510007000380c9008044c44550315040c9001562901c095540450310302804000128040500b0700080c10036000310030040124014908000d0610b40780c503100078005880c0c0780d42e4004510340008014503015030a286c010b07080c440e41d00b0040000c2049401c0540d100b45240c0c000700c1072180610381c0c650406804010005120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 802526735 1250 802525485 802525547
    0x5070b1c0b1212030907050a060305090c09010f05040905011103010b0912060c0a0e0d0212030d0b011b1212050907090b06160b1f0b03011e080303010504021c0c 70
    0x61030902d44658240e10441c1402d4001010201460b00401c2c02d104582c040c030745600004014030350740c0d00700400080e514030420001401c1085034480d8680107851600031541001031907424490140600340c011500c58803c0d04c20032500354440300e1240b12100005e900e07941c403224803407941c0e07000700d4049200d800500020a0349210201d080d81c0180c030240603580c80c0101c9640d0582e564410b20381c00a900a10011040000d40c0b10503034606151011000510b90310202540c0580803900d408240e1410850310201c01603a0243c01021000c0c4544c000148800c0c0c2d2140241c00c4603203c11241c46020301e18201814041c0e0004006003240c09c0c0c03085c00b84140900c04604041c064a800351003843c2404100001500c800f2528004046030003619900c0011002e140d058621150036086c1d41c01070a0602d000401003010401400700050170745208a080d001c02c51801c0206652070106004440c8110360003d0801040c0242c2452100005020710381400080000c010240c5440f800ca6001201c0840c078820f902e03080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 802527985 1250 802526735 802526749
    0x100c09260f03250303090203012c0c130b0d051e010b011142060910080618150103030e010e040e07140a1e080106240c05070b1c0b 57
    0x900c40c0320360000508000c08204020312500f0b0070030340a056841c410322004d41c4080c0114032200b691543c28525400b5401407000409a0180422420703800a43d251355441c0d468440c2d507090400da0600206118540c940010804000c1e128028500c0c4140300c0c00103030a001251108085040610007000000101d00c010b44415802c8214000039402030703020b43d11240c81c80b400c5028401241480701045c140d000d88080790b8580b800601200c0c90b2001300c2041860b1404800c1540e118540c04160342c1420315101c5115910b5801801c1c0095a00f840c0c114006035840030440d01400918144e03403030059503505d080c0502441e94424500340006c03400205400d05d41000d008008001c0050001070105901d4040040a506a902821032340551040400070f04800c10040f030100d0301d012481c400305031a28108020b0708541c0356030310090004c58a602c0300205c5102c55101001b0004140c21700f45079400851800c00c2c14540260020b281d2004003050615194142d072140c4030b29040c09890400080341c42d24100011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 802529235 1250 802527985 802527997
    0x5060a0908041806090e01020c071e030b090c1008010825060302160c260d08181501060503060f2209210302070204180203100c09260f03 60
    0x3260108001c010340003032815a42c04414816000084198540c2c0c5400e080c0e41c1050f41b8200b2681d00803a00340c00118040c403a0304000c1041a00c110052003a201900d540c40c21144400f4106882030b800049000d90309200c1d4078002d04000f810340c40300380d60801c40681b100000b801402034a10074802e00590100d0109103811b00c01c0c41c150344840c500c03443c001049020750301025a066640741031542910020724241c2040c4040c141500040c0621044625800b84032040401908d969600c4420781301196600003c5c12078100040040032000b10300503100c0280762201002e00215881c1d000c0000052a603444070245005642c202c980e200f02e681200c042200f402c100f90714500214444584a0081103010b41c081c1401901c600500900700544000c05004440404110710109400064401c11490300c1d101d06240d140c001054001d0354070864011940c4d076080010400d609560350103101ca112801801264014140d0148a88000c681c030100a19079001040f8829194450648458a110b42c0802a42c10b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 802530485 1250 802529235 802529243
    0x1903090327030b07090b120601020c010819022503030e0c060c100e0a1b0f0e01060c230f0307020306070311030c090f31050702102c06010305060a09 65
    0x81c01c0d4103548641c807034600080e00000521851610000e07200560303030b01920780d14801c00d100c0746841c40c0101c0060305140c004103c490404c0300705d80c10000d00c480f2a8104a0a0b1385500030300607207804040a000c504480110010741d81ea014081743c0c042015410b4200c84462100642641c1a419800e001e000081c090610040130680000c100d10003026017030f40c800420114840c2c11585204015101c1829200c1c56001c1c4522440074214207220b0800b5803002074000303012250409840390304d0890024080b81540800508018854400500c01118140343d2850700981c1c0c016079416501106220b40e503030f40280000c81c000d004d5000003e002c54040d200341d030403d001580e902499550741c484142c507242d115503100b41d40308220b4121004a6201e0800f500c1304403102512241c1c9103c4404e039a12196284403280759405401c0c0001c010f400d03a1302003201c0007669102341003c140494220703400c1040d55500c4009683d5401401ca43c441220300016a1074101d9000310292911902d61100f0f8000381e49a0910240c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 802531735 1250 802530485 802530557
    0x121d061b04121212140a0b12251d160507030c0b040c091b03050a060503060103030f03060801060e01180b0109051903061103040308010801051b030c120a020405030c0a0f090b01020319030903 83
    0x149d50700086034811081c5606c2401805651903c0301003a040e1030b101d1161101d0049004130802a0002280c0107142d02d00c151400d05034100525543c000708500c80109005204520b1880414104075842842d0809851040d81c1486081103140004580005001c40d180000e13007000c021600b4100700e88a03001c140c850150141015a08640701a01c09036a4115060304041d40c64a001592030002e120307200160403a1030035200c4651500400f954154041800d070303564140380c10580c410310b030303007107444a0110ba4042e2a261000e080b60301034000c40250f1036002504860034050320b91240e80b1444000c40c8124800d44500700316980720b4941078200e5070200d58407400c00800e020054002ca80c6c401c003456122440c1c004892400103803184e00700003880142c0d480c044554000c0f03810b210364030b828000c0d40f40601058403c00103c9281054840b0041d640d0712400004565940d9541c0c810792090044032181d4038561100d18000104483c020018100c0a03415000100c0c0040300d0448034540b08180500d181c510110342c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 802532985 1250 802531735 802531753
    0x4050307020f03150a1d010c090e0606070507080303041b06051204020609040c0e10030b01050706092f091e07121d061b04121212140a0b12 61
    0xc8000380d441c1c0c42e60160315104150304640481103113001688110300e000300100d40f00e0a1581c20b0500c184180c01e4941007a410000d10821003035000720300d20b044401d0301c01001e03045e46405022a52503c101d00c005040b600800d58049043c5500000640c081c0f031261800d00b080c46a5030100445140c00c1d03014a200151701041002d00a080c40e114080d08240014040b601e00400400002d080b01c040c0280350380441d80b4413100d990703c0d240090181d184c111680c01c040c4101e001c81c0780000c3c0603100d0719400801c5075554951540034000311000c6120008441480b00d8005440b040343d1900180540400324425020200019000008400d03a08403254030141304105a84414805842d0301d00c9003110340b11032555940c0e42601c4d500c50f0014004203403280341d02a100a090450004285d100c07442000c0b81c44110421003041019076905441d81c03105d030000c110006046195204840c0c80540c80d0f004911281443c060728583c0d0b0759681100d02800b110941000400041002c0c410420300710340a0301c000d900a0081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 802534235 1250 802532985 802532989
    0x2030a050708040b0304060f050a0e0703020904081e0409061211011d03120a0216030f0f1b0f05010806150904090f061104060f0809210712021c080405030702 69
    0xd0062540302d11403460400b900c80e010f0703c000d0303041110150741180d218285500303181001e00c00d003a01704000200170b10281d055062210b9a1348510302c00240580c000d0b200040510120000791041000c0d01e40720701d00c2c81c02c807804184107550040d0080c55046071410000185070f4140b040360320701d0b45a01c442c4d080000c07950f0382c1c01510700c59224a0501a504200804a1610f40c2c06110712149031031810790700c0d0344605108100901d0301c0e0800d041842d4071481d170130041c4040b9001d5162003010aa10220040c58070303a0703502d0f0080d51800d4121940b0820008000d01141304072445004e54141c950a81c3c0e0f91a240d82d8240400c00c1030301c0e680151003882c00c010800340505060581041c1c079214020b480562010032103644000c100da00d00e407540d0b4602136000c1414440b8030392010302c11000306010315100c0080c1c1802c150454036410022104188400d031045941071032030703042c01940c40e415002400c01460404402e0003a445410b45008000d421411001c4546800d00802c6018003072078008004600706040b56007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 802535485 1250 802534235 802534237
    0x10c050a031e022b0c0b040506101205061b0d0c05030a0f05160e01050c1501050a060906050307050d1409100f0911090a092001080109090209070c110a0303051e04050102030a05 77
    0x8020405c203c04141c0500102c5c0842c002c56004500c610010000380c5889200b070303000100c8a801406c1c00134503404021021850025129401403c14804a94a08104e18200219101e15031007101c14904001c2401d4250313030054051031040c0300c139440c28480200d1601c1c81d40c00715001110000031a1035441170000c5c07054428882c000001074107041c42d6240c0a00800d08a1411001d02509000c00110340014011810f0015034200140107505110a210b03041400c06401800000c3c181d10801c43c01244c0700c61809c0003074200c4180800302c0010b440341418004c6c44107803107c44203036820300d5082c2456030041d003a43c2984222002c054010040403c1240301c01c040004158024002c1030030710b625001c400d0f003ca04a01d83d07105030b501c41c84601c040542c04c1000050426441648014601e9141610303810158070380d480d840364042e1891624404c43c90306890001d001006e0301c0e90554000000d11008010190014010311030b600c140d01d2040010680c41d07840700114481c601455006820600c00110300034080e034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 802536735 1250 802535485 802535563
    0xa080a0605010801111908370c020a0b0f0a0f0603200a0b07062a051801170f0702070b0f0702030111030402031e010b03010c0f0f0c05071202010c050a031e02 69
    0x1103004e1a04240c03102344036543e02143c41031030705208149070a103ca882c0161045550701592030020704004c0d0a40c0e1a03441c40c0c0e00c00142824a003155540c00030b0321440032a1b2211101d0312006000f00042c541f2420011102d007d1010401803d24103080294600c0c68282c03803503421650000050751406c141070f5a410050320390b1403a90b4200d1000724500c6840c400380c2c0c0310802984a80b0b655610b84928203070640107856000c1200183c14015040f4160342400f098680315070344008c0e500a1840c06884024049191203115448511000c6c0b01240580e00405a00024611507000724000c3c0134080c1d084002c10228030056030002d606500c01c2d0720244050f18141140308035940e401d800041e5840b40e890100f8251811210141c00080c0200c050084458002d01c0c0c2070300410301841c204040e0350440d80d0315175a42403d030055900c18840c03902024216827090f03a0038614264008195412039406203000b070f00704804200030344040c2800042c44052103200050010070003600c0e40703864420010480144a490f0020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 802537985 1250 802536735 802536751
    0x120f1701080613110411190e010c1e050709051611030d0903020a1b030c090506131a0604030605070206060105070b04170705060916090209010507020f0a080a0605010801111908 77
    0x1040c130748420b60703114032449a041000034800b590300c604000b190144440903801903801d1004e80c1c0820340c81d90f6440190044100d50101d5281e4030a000e800360056401e5422400034240c2c4500e6401060310040d54005900880e141c4038030b07000d2000c51000961340c414809111082d05d81c0203004443c5c400300d04c0d4210b029114001d00540307202b003d240d00e445405000704c0030000d09400000108008114680403001e000b89807485003040f003400c1080c001643c0500032600c0f4410720340c5030440319188000e690f680306c80107400109283d0350381d947c1c0c3c40c020024250482c1c0f8840580a6100001e80c2c9501507402c403006d0075031100b0b07100000d0360b03166a81c00749001c01c0d0305204480a0b090203c800011003c205440c011030800b0700402126100054010311440c6d113401100740d0314014401c01071280d030000160b0300c5240d412a44080e41c5003211011070798900c4a948180d03054420042c15078244000c50b841a1b06a480210080c0241c6020624800d0303248203424100e0a59419140b034901241c1c0706860042d004264 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 802539235 1250 802537985 802538003
    0x120403020607080d060f03050309030d030b0105120c0405060705010906200d0203092406030105060a05030d03020c0a020307290306091302010e0301022a0d09050d060603120f1701080613 81
    0x290b8a8400503042d03a90421923543c1d0001484444500d010050404401038502c1e080c05002c0d1503c0000700349025040c005400d003ca0500414200c0c28081d0584d405800d010301842e881d00d001d420074a0181209400a890440c034241c2d6031900c0c020036041340c605071046d100d01c00d440e01440c400c480e0000d600c000e1008a05025442d007044003580b05c841c08000c2d0406002e100212410040205821540d01a05680c4a40e802c0001084035803400b00b8050040061818010f031100d4541c40076504010042da8000e5142c0125140400d240708450340e843d425120a030303100200520b29842944403071100b0f41e030361a030012140d00040c0740320114400a001c058418542a840001080042400d913000b4040f01daa11600b100d0652804425408c1400b8946440d4401030461152880d005041d150309405443e020351000c402050510120f07400071001590b002c443e10a901c50f810b0030080c240c010035000c1000203090002810011108250f00c24181c410300303005031049071103d4001c8a0820300130841103c180ca4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 802540485 1250 802539235 802539239
    0x9060d110301140105120d0f03020c1c0302030f0705070203071205101a040f11070b071e05091e03061617130605070504061b020a0b0318120403020607080d06 69
    0x1000e0203020705600c6a20743c00e1801c1e504240070021402103851400220740e2001d0340070109070342e008140c0100c44c44103050040e41c502c00780d07207401c1c113082d40004007100f1020b0701500c0c41025681a40254031980e000f0350501415107468208642d18440c1841c0039502d0752000500b800a0006000900d040e2403060007142c1c54a90f102458405482c2881010940222038a04c0c03400c850900340260410000c444c4030070000150140c41e40805400380c0000503000541007400541544e0003400f032100d07008181d02138000204404070004010b41e201c52160b034001c588031500c4030741c644059840f209034121f004024201d02d581c1c0d1014000000b003110200410071141040d48440c1c00d04079150309000d0078008411441074101070500c2020b41f240a03001008214081008004059004c01da40315095080088100145041e00004003003e449410464400390000284200401000e13a151804003010707043da9224040a41d5441d86406584000b0f900010104040d0740000d05500041030140b08408001500c15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 802541735 1250 802540485 802540489
    0x180f0608100902010207080705150a030204050306240a050102030304031202160b0a050f0c0301060c030e06030723040b0a180b03040c031e020d020d030e1009090e0c09060d11 76
    0x3146090780301207540740289030035540c1c1403090002420f0040010080c6600d0080443c043c055803103001068a00003085840d100d502c02d40441e0020400101240c2e454181101c3c1c81680340c205070440d00443d80311064068080c2071112a2500f1a03805030082c5080d641c1c0ca8401390b83c840c2c2c2e038143c04001c055081108002c029058100560114011243c1540524108003054100d4401030320080381588054100000c10880d401200c5c1500c9462400b4020301c5100d00e016294035144c4904d42da842040401084406940400e64000c030340b40400700b801031040060b01c0f2404511a5000b044d0f400b034001c109600300140250b408000c6000152056001d6903a1502c181805803c1078a04940f03419000c1c0b0100180040b1080c01006c01902c0d1b09040350f80c9a51b540001c011500c7d00d034000340141c19060600e0180750181d6104106620054104c1500c4204000002c0449e0707140c0c0500003950745010300b84007907c0000207070303074030604d00c0540948442c2d1102400c00107200c00c010802c480d01510344060341e02603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 802542985 1250 802541735 802541743
    0xf0f06060a140301170714030c010c05010b040f0b10030b0906190905040305032509090c120c08090f0f0a030809030f0f18190603470a180f0608 63
    0xe0844081980d00500c05c452114101100c03684401000d00300001044c08640d80841c0045600009080015130640781c0d2504c0fa001d400d206c03c029034094901050315044150b80d801041c003030b10045440943c20300c4d0b07410058040350768001d0b110b50001031200010700c0d1030404c1180c00404030100d14a0005249d075804215040d204120340490002c0c03801702c03e000700c40c50100300003268440b64a04004c3c9a5140b8040101303903550300c2c45030b0202141c5036150064214018400c200602c40e80310301c240440042400081c1801d034040d02c0074551031240c02c01d07070309141c1c00c0810141e003855601006808103000326202120181005004004540010050010380c407000800501004440880113070b101c001e4000b014800643c0d001030517000b04138203200f401c8812092030a00040d0740460500180c0700f03016045100c8070007a00c54036414074400007800000c81080502404001850388075000003d80003450511000b140f03584a60120560740001310711880d45940c10010500d5065200050200d541d100706601e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 802544235 1250 802542985 802542989
    0x145021c0b09030c1219030507050708130f0b0c211306031410080d030509010b0604031505010b0702060403140a0605040b330d020301020f0319050f0f06060a140301 72
    0x2c141e0000038207118041301400490704120b034074000c040c14844002010606c10400a460204055845000403031090041c01590b0f102da82185005171034094802c541c211701401401084c10003014460006044c0c03600d441103a0314000c00d48090007143c003100c020f07803d1414819561103540359017400007501e2050b00c4141000140582c1d40c01080c6014101d2004081c45800352202000040800b800c1c0001600011b50b807118040300c0c030f00007903160381c0d01c01e07401d00600c011251154440c400040020611050210001000303da500081007141d80e69000c0081612800300001c1d0421f00611003000401d0b1003d120501c0c09043d4800d80740340c1d001e1661601c043718022582101d81a0800b010302a041e1444640340d609078401140e14444084140016034461246a88062040082c24000380c1151800e40680e5082c010000c0b92517200d05100ba000441c19030050703207403074245181071300180d009100600703511302603000003681f0800c68807090b0500c0180d60000384d1203000e0005803015024074402000007940 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 802545485 1250 802544235 802544251
    0x90902060717042405070b25050903240103030503180a061b0f0207140a03080c0c150a08072604210e031c110145021c0b 53
    0x168541c00c0480d0350076040b0044c40101410300d00403040050a036000011100859008640316425603a1880450148068400c406041428003000440820b42120150540d40c02c124143d85580c0320922000d0141440b041850005100d4080104042809440156000084030058100a40c1c203c000d00b407408459907401c44000c1e58542d540e0601102140d4024a4030a95103002c018125084000a6591a15010b05140a03480103070514080d45c0d9844030000440d4000d034a56220707516001800d4482118a488a005400b10780c2c0300004502182c084401c415070903181c00d1a20784605030100c64008800c604103009078211500c0c03d40d0b014008083e00e215070b104101c0b141100422480314003950280c3c607144424041d03131984601c4a95808240e000c048920b0391510749041100b890704903200900d00004e000ca035403a000d01003151840c41080654030040c2c01005030304c004101d2155042c814101c4401c52200c00015181d0b2005260101101c1001544228031001e8107505441d084000e05003552446 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 802546735 1250 802545485 802545487
    0x6070c03080418090b060909010f0f05070206090a080f071403031513020703090e1f031101021c1b080c0106180b0105040b031f0f080d0e06090a090902060717 69
    0x3240284921403240400c20035000e21013900c4076a2000c4449102408852084621074006020307140250b010510007400c0d8201401980c8081e03200400800094401e000140100d40000782c1240340080d4900c26280d00a00851405402e50743c0d00010390450207003100c00401800800c900c1150804c00340d0b0052101c007600e220b081e06484104004001030f070000d4400a8018030025000c00d070807410007000c5418110090301203941c2d4107681c40d03040c680a40080c5c00000c01d00c2c4040180201c0362560484610203808442080d201212145a0000c035060040c8c0042d4005c3e07940b43c1001038141c1141c884030700c258a0310342840d025422103402c4d50b07003a4000f0070104584c42d5034420b0085260080100c4000203080080c90a4200941080070340300003080d0004290915400e201401014030412004205946c00381c4005910383d140780340c990340d010f0502c00000c1c4c1c03850510445840e140c0110b95880800a141d40445d614020204000e0407201d642664131000078040040030070600001d5440c0440a20b5000e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 802547985 1250 802546735 802546739
    0x30e0616050c0f010228110a030b0a051014010c170a1107170d05070f0510230c0d1a0d03050c070602030702130f1b030b0a1d041106070c030804 63
    0xc0b080105081c1d650a04641c070208006e40034241c01c2c15840f07030034070b120036030408421010f05150103408070240096070010900400007042c02901c2000ca4082c8030801d01c00c3c8240c0c6c0314400c400600410305e000c0d04840c0c1c280c0f80d0100103598024014001c22601c05c10000d003e070f40b03645404000541001d4200408500c140403481641d074002d10000300079000d40c2d9480f030172680a4100056940010403010810311a00060103024001c40b803158001142c2e004040700c4500000000820283c0301c40c51130615241c200c9940742c0e0036110fa00c1171061107150224101414244002c1384000035002841c0600c0c000c140b10781c0c500caa2500c1c1c0c60f8034480e440c0c2c001e80b100d95840c050005100d1034aa8140e2040c000c540080c84000016540c0d050794111080e181d06000c40d129542900301402040c1050701e04c0ba9003201c0580300d86005030075030006828507400711103003045140c1c1c1d14030000140c440498020748008514002a00051224001c503100900c044c00d511b04083d01940d0b54812094960016a02100301041c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 802549235 1250 802547985 802547989
    0x16030b041b1106010803040506070312020a0512010e06011e0c060e06090f060907031101030e0303104b21060b040c05122e091406010507030e0616050c 66
    0x102c0c0441d1a0480000c0c00d00d0340c580b0300b91586038040c901402e44140c1c0001079440504d441640043d50f1581226000c6580b1a9182805451640701b07141c0e18401400384400000c10042402103903104600603194910b1003500c0003040008540001880d000740300580d03840202084051140e9505251070a00402081c02c090400340e203040381940c00c0040c29402102004212070001c59290100c0764881403985080b00402e005801604480e101440244400301c2009590840501c030081100c03500f15903081649401101004031a003d0f078900040662001600e00f1442d22014141a110f02e0004083e8517a03900e480070314104a144c914000122922003a8107000e0001d00c3c8102d01e82c540c4110340404c1100015080586680600ea00300500c03080c52500242040c05401084140c070710030183d9544000f885445441c010f54075500441a8030b0f8a002504502c120001030300a009140c161030b0342d82024490340e0300302c6070f1801e03030403c00d0340044081c01008030501c1c2445004410901c198060300415520f21301b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 802550485 1250 802549235 802549247
    0x1080a0c030e0a060e061f0b03060a03080313110103060f051201020403020901030812070e010f12110a180e0402012102040b13031101090b03160507170c0610030b16030b041b 76
    0x44244205c0c4407c440040828100c0e00300c0004503142c56040c13945990343c5000240c4032030041d0b440a840f201c130003c100b1080c41c190a8000050602c2400c8600c040c001510046044410f5802410b5040781d85c4141032210f86405210400d07000c000304005454180c41e5408520180001c1c0d000703d0b040c540110300d0320a442d207900081644520245000c01400402c180000c1ca01101101c1c0d00b424000442146a20f103003654115280440c60511119500c00108030010035040f04800010021a40081d0201d03404070502c8541d8003070f5070141d45d150422059001c1e07090300d240c9410428460594200030004040300c460000d400040050125119401d00c0c50400150310503201e0003403410070041560610002c7c5446041e6034111005480c15032003a20606001c4d41c49100d1561f01412154201800e565040d5072200245240125001030768503589504480300c224100d41c0c00000c24031042030707000a540f402008200b80d484056072a0100380003007004041401c41d194038001d036000760b0070705c0919296503030401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 802551735 1250 802550485 802550491
    0x6090602030609010e152b08040603110301051e01050c011e0608061303030f0e0a0606060f0c05030901030b060403150b090c091c0c03150218060901080a0c030e0a060e06 74
    0xc44c0c0c1c41224030f8040d046c00c3c020600100d40600c85c6e0500c08808103e10400350180e48840410300f80320b0000b08043c01c0c401e01c560002e100d0540000e0418000740070405288082c3c90403260702401d0035100c8513564171500c0001d021008801d04000301031005c0701c3c507540c007400303420708400440c1d140103c0d59a2034081c04d1f041c0c40300c40e08a444180c1c050300c184015400443c3d6802045905850009030700c20341c42c110741000e000e4180780345820384201c80c030800c00d12440e0b90028003150f4064440303d04041000070203888140741c856001d0070715001803003c0c4076254006d0b008505180801056180ba180c1c8a98030704541902c05c0d0f080d81203e507950401000c4a080c840462604210208492400d0001e850700080304000350114400105c400340510b071040001100100015542c4201013042c5090151100c2d0000e400613141102400c60706401c000171824000c040700c01135030341a500c000c520b6880f001c000703001d4840e00c900c48040554400100b06076070f82c1405041d090314403584004c540100014503543c90b200003d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 802552985 1250 802551735 802551749
    0xc071b15030e031e13031a0609040209010b0703030209090c070512090a120503040905040f0507051c241a010210060803031b0c031b0f0a0c050f06070609060203060901 73
    0x1080a00300100c50010a4950b10500601c854448800c07401490915000705c0c8140707a0810001407010080045200c1c0d00d4902026082d0350140c01d1340c9202c03c21492a106075006500310b40140010b02102620302d00900c0100d00904000d468071140c0d20118070501c80c100d42c080c6645401081d8030080060a1141041c06507203130f40f040381410805000690000c4040c85403402881c1a081c101003000b40a0003510010003a44a042041345040e00b8000310141140004a0b03183c001c050011a0500d0400f421a50354801074003540204000d980d54012900040052840003481003c110341d140c41c0c00d4011407254030301c10340d68060002c0b000800179140084041e42034410a040210a000d0441c0003c02d89920a4698107503162110344000c10980034410540a0395240c04001410010800c600249050104011048a40740701c0b120310201e80380c9008040082045032554004c010514005020790748880008060915040d456560034048034121041100e1440d0003100700107092a041d12428010300003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 802554235 1250 802552985 802552991
    0x90102070c170f0705060d23010b09100f08130201020c19151422031b06120207020915030705060301080105060405071106041e02060307020703020f0105210c071b1503 73
    0x30310300006c465010785400d604c401583c0e01e41d0003803081c240c0c0c154a00d200c0030403000e074004c0c1d507101c40a134035095121020017809940c11008101116105018a41201c0501c1d0f41f000f6032030b200c80402c03105201e04504168114804d0318803211240c0e680d18404c2c0071003082490528a114a440500150702c0184442030040c0702c03504241c00c0b444c1d118a001c8402815402842c2c50125094540b100320704042604060061074012464000305614130000710306a13641c54032603c0001200c261008240d10411000035041442e00b4049105548100301d50b542085005050300d003000d80f11030200e04e05070000d80c0a00c149070345660030300031241024030555401c000280380c940b110004000849680f10030140c0020600b55080e90900c6545840d040180403c0e41d0042c003165681c140030b10000c0da183e904d0701069104a841084100c03039580501c044030000c540a40c02d040e8540540b200695607213100408102e00310340100301010009882050f410080107400c1b4580f100b280c10034818509281500e0510000d140c0307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 802555485 1250 802554235 802554239
    0x101106060319080307020322030203010f0612060e0309030d020c0f06031b03060105070c06030221060f0d1104240f03080904021308010c020a26040b03090102070c170f07 74
    0x50b000c0303140c0d1060342c2000d0440d940e5250650201c0ca03620684102c04070038135190100c2403140800d00640c1044030b000301d009204c10f035101c2d40260125144c5100708401c0c081d0080d407a40000740150080d100840d0004140c1c0c1c1031400a0740400d041902c0d0710352650050f00528900445d62419002001c401002039564034210701d450503100342c503a150010980302c100c501100282c0e03240e1050003100d8400364004400614030366901b0317000d406500a0000f06000301d16841813940380310b0005650328400c0100401c80b00c0304d4091f1000740716107046a000c050310135601440706041c41d9241c0303002d031104103003601c02c04000340329a14902c081e180c9010f812072454041a50380c1040810003007016145201c0c812140181c0da5890711a0303469030b4000941c03142940f9402c00c000b44200035004900c20440602400c18004910042e540300c1c0b049006100105090300800c3c4020b001c01c0490303401850780400c0940c0014580b0925807030384004011103a00c0728900c00024a00034081031418890840c0303035642d94000703000c0b041c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 802556735 1250 802555485 802555513
    0x92102331206010c0c03020303040303080115210903050919062303072d020304060e010309080d0b01271403061308030907091506021e07090b0f1011060603 68
    0x71000c1e16060401a40e002944148004024000000c1d5402400c89a45035620701e0301401e206401d12410b0481081209001e0049000b00c21152610901508142d0310880485c0c1183c0100103454003601000420301c1050072649a1540303000b6100c08103400072100da8a441c2005006007008910140445150450384c0c886440d154241d82e0400300c1800c155901c804254042b89042c800000301c1e11100411000300c00015401000400954905a4030304641d403100c00d00540076943c121000400c100002c00000c0c2941030303194070078a000b0105140043c18805501110102024202c40131110032003141d604012030b061512205115604c1940078280511b0450b02d010380c1e07000181409803e4000000008050300c0c014003128010340300c440820030042d0f250034010341400e1001d015203c094407662002c002c281c04121400452a0001c0000749035140c144141030300602514803c407908034110208030384080d0349000b05200c0f103018a0303888115203003160310118501140074100714005e4121a60200d554 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 802557985 1250 802556735 802556767
    0x2030f030114040f050f0a05070207050a0b1b030a08060f040905100b031e0a1101140a030209060f121b0c03070311070504181b0609210233 61
    0x120510b076048107000d150103022030041d16940c1ca40140031450282080f403c1500c40c1555402010039040c20401c42d9200141642e643d0100e0199950202c0101410030100034041c1c002c00501c2c0d08a9200410103008140103491a0403e805030400310321341004201d402c1c20029028280c1d0b00b0102c90901828000380c962640315044500c00c110310907160614640c45840c100000100c800726492002032070301c211030a81e611280c82490480c1d800c60300000b038042c1503100d040c502c0e07400d502100e1414034080d1820340aa0095200594454100300c00b448000e05c141103200c007070611802d1003840301c0020b1401d80300c000c0743c0354600858480f0300079081c030195520703000001c1501c1c1a135905050040b00ba1917031203901071610f503066002c1d603402400c01c0d50003030003040010f40c0c07041e80510032070240541c0d000144e4007902043e030a020300f41c0020032600007045030154689584500d11500307404c03040c1640301038021581011480d0410040040352680c940f00001d200014028078100226016042c8182a00f8001c40c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 802559235 1250 802557985 802557989
    0xe06060d0305130f0f080f030306010207060c0f0605100512010603050d0f030e120c06130506061003092f0d020f01140d0204060e090a09050d2709021902030f0301 71
    0x3000004a04000c0700c8140610b00c0001e0302d21000c0700c2d05080d0f13680170210010708250040319100d010300115500a51400800da0f0700400058000d0a10281040c50803154605140c0050352011030162001e0080340843c07058500500307400060522050800e414850b40002202000f0003d81c540081000880c3e008107003912643c000d40303000d1a10116070311081b000f62141d010036800a0041e25440241500c00d000246000030581051f102117558440d40e481400b110a54068155000b440018005180c08101d034800e0200e5424006502041a162603000c414804041e14500d40c000e00d6032201208168481000100e0450ba103c0c421039a0f44c3c0421500c0c422000b03101d06000703c0303410003000d5012040c1034659048109004546447c2d450340700038402100107000750b0080050101068100c240e9000e8075450b180c00400034150381c2e001e200215081c080e004403150b460100742c0241c580a000c0d0600c1e03100103108a4a01507115400c1c01d10417042103403404005415907004024072800b00840d0703019681 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 802560485 1250 802559235 802559237
    0x10411c050a0b0604080c180c030c0a030e0105090a020a0f0b0d05040302150408070201090b120411130e070e150306040f0f080708120702120f03100b1603030e06060d03 73
    0x44a0300ca008414018010030401254014801300b00455102d000084044110504640c442401040c03441100140c00341a5640ea48103002000003c071151a403000500c0c1d0003901d4600041c260500c070b24142d08450f810354002c10290412030b12141946000741580d8040e151103000012044d1804444150610a100c155550103444800003000d050003481080c060310884681440700c0d103400e150608095006d15412401b048010740c1c0841d1301c410301415204184109001180755407500e85810b543d050084000c1507000c0c540400964401c0c030f1354010390510a02c10130090034640d003010b0045000c0c040c0100307940e284024030008038041d0f90b00050495000fa402403019243d08080341440c41100801b0f25000d0824403002480ca4104600903000300702c404a0b0886c1d40c81d203030700d403d2000c83e00c803515201440202a02840740c084001c40b004000d58121030b1103148550403507a501c111081d81d41105e141054082400c031102e0040c140c060007004640070b44840500518a8640300082c0d5168180d07070050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 802561735 1250 802560485 802560491
    0xd0c06050405030702030f0d14070215071b15021c021f020f03180c101d060d0f020c0d1107091d0106030510110702060910411c 56
    0x1600b44281070044881c40d68016040c3c60049407402e030038a94400b075a0b0304507000070f06080c16060081403207005950710241d0082208011400c40d045520700d0303410071715050385d901c01d900c1500c00d50101504612001458801203441c05212092000303030500d4103c0640b045000e584800c1d021405501052004e100e0508500d02c80516100c608084002d00a101000000301000800e010440402e100000201a401c008655100c0001818420800e40704251080801d525800f44500d0003811a103515541c0d0016120f10304108900183d04281c8a1003070744559103d80c001143c41070380c00184a840b00d079a000b400d00700d0b034004a5000c4944c0d00d501601c80c207140980d442040c06014440c1040000380c420380d142c0248011516810219107400c00368020354203661802980c0c00d03220000c081130714a800c0e0002d100c41c2c10040404c0c00d00c48024a4140228108004102e8400c980e103a51035584210014660401104148401c03151440301c13030901c45ca004c0034074140280e00b4065040d610501c41400054008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 802562985 1250 802561735 802561741
    0x10309050705040914030703031d1c03180b1006091e0902030601030b0306150102011b050405060d060806070323040f02120c060d02120a0203010518280f0507020d0c0605 74
    0x800e0964003800c5d14140c00d000000e60b44040c958550003003162040880805401020803603041c2eaa20a181c4001c3c00c090410b900b00c0c015042e01940c00341018440183c0c0c0450214100e544120300c11900b01e44002514125034010711031140d1204244015040d000f20030100d018501e5401c0745014841c0c4118000c01e5000000680c0a0b40700f9000020318590140c05c50354941003004528511a0301c0b2400b060043d840e2500e40a00c40344040c004e55051070203500e900d0316141c14042807014680c0b0a20a10021365140c203000070700d14500b000707214440c04841d5000240d410003964090904401080c60001c4440b111040c040403980ca2a07404c4415a41155001501c069081005003084a818401a84504040f07000c2410100c5a0028050101c80d4200b60000307950307201c1114101e010a0248a410494020707032100020749c2c019020b034010301d0212100c031110b40031b250360180c64031541c03c0000c183c40e00c1d603020010307030a80c0d401015004175150015000b1441c0d041c1c0014071519813031401911064440f404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 802564235 1250 802562985 802562993
    0xc300f020a1203080603060f060f2e0203040312080f0c0304140706120b041b050310080a0c0504050723070c080d03060f0803041511010b18090c0103090507050409 71
    0x21050003042a0541020260b2481c00c0c050a0712100703d441038024010030f400200301c554410502845003600800d00f0f070701c442e111024031204035079410302980d81030701c24860001111a00c0d9120002d00b0210360055a443c5d05515000240c0c64030352070000d01344404841840184c59211521039406050500340359201c4c0d403503040c15601503150088040b12801480301c0492840e81c400354000700f40b9106241030044038107030b105210455050b0720405070f1f0305800036001c9503180e00c580000d44d0026480028207100548582c5180c0c1004000d8000b194541c0f40d42d0810006810b043c0a50340e813000a07820b280488020035914016200b1014400301c0c09040700040d25010001101e10740e0000e81146000c985039059184c2e07019008120600600e0800b9003c10703c001044000042100c0c19610294840d0002000c8503c05454080b012200645a5501e40a15029079141c0100100349a00c1e08982c002036400e11401180c10805481038540c105404c0c47c0e9802c0100d440060b0f10011984142c80c0002d0400c2d1300d040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 802565485 1250 802564235 802564249
    0x31109040303021c0f060e01030503030406091b060c031106161b06020d020909061c080a0c050307052a01020309060307030902272d070e0d0c300f02 65
    0x1400c9484c3d0700346692544826003203940140c0c060340b00c41c0b101300320043e11000d484003144424400205581d104000040c0011a80d801078501240b003640b6180b00d086440e42244018011030700640700048090343d0500a241d484a004a590b9050034090009814010300b441c544100500b0000c06000b4a0810a40e619000500610109800c00801c6485612105101c07020350f01c404411481990303502e01081d02c80c9010511140c00100300080d4004600340c1e66212400c5070000f840e11020f02400410b42c0021138001e01c0100380c06407113000644100c448692410500308007108809801c1c1010348155449641c00000310b800b00602201c1194680e51540703c120040e002010001f500041d0921841050415011604071940f11071010300401c2d40d03405640000801c805800c15691b012402e904803900d11042d4800e9810100d2842c10420300301a007800304801500035041100c181b80b8481c403c0008522004105501d202c1000c0074409000411308c01c844083c416220140a82d0455900e4a08641c1d80782 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 802566735 1250 802565485 802565497
    0x90319230102070c0504020f0318030d0606182108030405033c030f04020d0609021903020102010612240f1a0405061909020c01021c0509150103110904030302 69
    0x884103519000103000c00380d020b5008100d00300d60300c0d0705655001c0b0305c40c6030600079a5010304030260a241940c0d50003000580c05034115840070400c0c0020007103051381c0c10701806444068501034440c05151040b01d0031030320712280341e940018103d0606189821031664690400c3d02801d4000500c15240d0f1a00d0070000d08501c105003101b40d01091050940107803044500c02c00b46408071000344621254012080f011051208907424031241da000c0c0000380061030020b40784c201e940d00422001034121040d03400300e180c2da084541040401c18139070800301304641c2c1c240200c0000d04a04105100d40314229a54040f01d4040a079030894510421a840314822401d6800185003108410080c084194110030070b0b03080e2030030014070900440c10400011b0080c10040c0c00d10b034404051411290700e9516103148000207400040341d822141d5020031811100080c0c800c4030b20b0541c2c074100350000d0541403a1810382d26001218010740e00404541d401003000c12145a00c124109a060f030f4500c2107a41d5614086009100b44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 802567985 1250 802566735 802566773
    0x19050c0d08011d06090612010912031514090402041d060408030109110903120f0d150f0509070507032f01140a09080f07020a03021002060f0c090319 65
    0x580080031003168440d030201d0484220b04103600e000518150b1503280208200c4007a50002c00d00404a411760800112544081c01e9030b000001d601c40d500c2d034401519402d0304005000194550240381903140d00b1240e000d0090000041000c01c0c6004103010448010700180064440d590b10a41001e60f500c036020400c1c001d00450003615003a1925241c443e0840d0001c0c000d1280b0240b07041064240e40d2030720401c40c0d248205c014000c150a03050043d503440c65620694980b00086000d100d0040781c00c207280690358040100544d0010039605101310005c0070740a544c04030344a0900081440541500442100c450b81d416142091400c0e4400c02e48034102d8442840c1c0c4101d09081c1b1030001d542500651004461a40e000c8103513032240c40d242d0110b02a41c01c40c59010f03089400c00c00400341c40a05900091550510203480c2000f01ea50f25000941960807a607010409a08190200525088030040e256400003110703904500305079014000c01e42c0c40c813603010440481d003c2c0300d0100b0300740100200f03000b2a101c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 802569235 1250 802567985 802567993
    0x60d14010e0702160e2e060e1c4d090c030702070e130c03030c060522060203130b070c110909280602030f0f150619050c 53
    0xd00d10800c00706031000c4400500501800a8400741d0100300c0c0803160880d0302207002490680c840c8182026250300c18904a828081c03c00d8801721900a00c15100005014644031510700b204140d0900c18001030441c009080b080d051b07120000050100c080c4000c0701e5803007442c03070311145040700341885420884103000c004000b0310b500c542c2015025080300e101c000c034080d2141d00454440240e04c07030341030106481e848003680003040280800c0355103262241e8011403000d030b003c80a89040d2076101c4041d94640094002400c004400030a1002500070a6084841d0800e411036085440448180d00992210001c0a00c0c3d00080480d0340c802000c1a40c000294101d800a14070b82080403001d03104040340320088590708108505400765203891074003144260b010901070540c464540b4480740402d007050450b03407032032003180c80141c2c0410710501c043c1d4400c00000003189039504010b4840c41e604040144203082001b12411000f0761501c4100035107105030594450900c280400382400d0720f4501841c00003450900c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 802570485 1250 802569235 802569239
    0x1305040f0207050c03060c03060d020d150212070203040b0403020d0510060801020d0c11060103030324091a0d0c0b03100509041a061f0e041b0201050a0c0c03020c060d1401 75
    0x5080c0d8002e001c4503200d00d08407900c040003007050640707454003107440c1a0068424800280d00c2e040c04103188506500c01000c1c1c41030051566100b0b80c0b503200d40040c4408082d40030800e00a040805601260403600500003181480c0c5032494810a912640c04004e0080141c45070460410504000150036811400c500340031031501e90300d400f4000d41065090158241c240140c041e0400d026110040414540f170000c0c0c40c82d07a0030741d00c09601070648c010440d0300e801c001100100c42c0e0712012140c1800b0f4900110007003005030000d141c18401016603005c00744980681444440022408440a02254400b00764503880b5a51020403504201e43c1c0d42c00150054014000c0000700150f0801c145000c2c0b02d0b80380301c000d40da00c4071000e000e0000e18803400030f03416454943c80c5103141ca004070340c0303448961001880418070081b04040580049040303294480580e44500c1130010980e0b041c0544410648240b4010f0781c2504903440080d91612650107207401000c00040240c0b0000da00d41001003038103000417803100e942d6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 802571735 1250 802570485 802570511
    0x5030316120e0c040f0b130504050a020d060b03070b0a021518032209020c030f0f0f160c081f090c12080717090907120603060e0d030e010e060c130504 66
    0xb01220381070310907890304e03d007404000705e00d00c22540c40c010003a20140440103006448001008081c0080c0c5140c4541c0e003003140183d68488034409280d100d0200800d0400f025400c0c1880c00c1d015811090f03c5a46c03e000780006282c2c001103801d0820310b051102c2001e41c40304203404500300d03c5d400510000c0e004c0010082c44640742203100d0301c0007030500c240181015940d4a07580c01280981e52210145801c20080080307950107080107040c0c81550350312520318201d81c0301c03108106548481400b440384030006a0700c000b0301c00700c4407038500140482c40140403101c40c00d034401d9101041c0d00c00d8040b0810b030b4a40c903410a221018903002d014100440100d508400c00d8101a002070300310a00403500b4950100e00300c40d81c10800425140900c030040c3c410b82c082c0c1c403100c8040d2000c0b910100300019161392082d000000c9040ba00445829003114400340681e00031008000341520800c040c0b6134410707130503c28041d45c0b100c00056020740c452079483c2c445071180112031800e401e550096000d00c0d4841e007000c00603404d01e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 802572985 1250 802571735 802571743
    0x30d0c0506060306040321180c14150301060f0507020604080f19050703020108070c020307090608100b030a03050c07031505070e2d0a031e110a0305030316120e 70
    0x440c09003048600564a03542010341ea000200c07030080000c1c002ca0b0309010001500019601003c0741c2c03510104646403220180d000480b4201801d8940308a50f180811540001400080000300156810100b00d01c06100d03210940c4011b21502003003083e60010b090780e20b44503c0c261904107900030070352582e4581c0e90100d19502c01b040340d85910240036600384090110081840310000e030764400c0c05800c4132440c0d80c00549907640024120000d0107211002000140e0b428042c19014040100000038181d040090403490801c3c150301d203000c2c0514014000001d80d400144140000368103260203955410325008141c140401ca6000034240c43d506450b00110419581003d80305807090703a140718a0400f2a0b080091074424150b0705020b00c1a1a00700144080c0400801010100701521049499a80303654400d450a42c085140c11102c3c15445800c04000700040c1c1d07288401001c0b04c2c80c0d00d02c0c0741541c03a01070b164440608800303182820001442c6c05ca50103658011982d5030000e0080122842101649460b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 802574235 1250 802572985 802573007
    0x1d16020708012f070f0809060c0328050f120405010b090901091b0e0a15050d0507030c270506010e0a060806041d0d03020c01020d110705010b04020304030e010e040605030d 75
    0x446400e0381c03402410041d00c902540c541365007111034011413010740c2c3c43e254056400075094940200080010b051429020002400030f0b60280c590b1b40c44008048138600b030501c0136403084104205d02004020038541103001614401600e9000101940d100d5140c8a4014038262001640020005e001c100d41d2080c19408a55528010340c0000000400c20440e241803880d64001c1203400240100400c04a203169880042000c0485801d00c0303040b6169000100746101e40c2804a8199001e0b02e41440bc022030504c03514011f02000c01a40380c403a0780d04801001c2c040f4650300d260b010700e5854000a6282c0e1241005104440d4094000f46560340c0391b650040906c80100e43c400d000714284500c01e00d0300a040e0381044141078413007025140c40981d246084020f075000c1d040810466400748514007542180c0d00c1243c100c0d114800b24140e550880380752540c25918503904083c4a1403040c810040800e0700300c4407201c1c40242c00d06c3d0030381250424500207001030400360030264051150014009041d41c02c180d080c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 802575485 1250 802574235 802574291
    0x14030102071a070e03120d0e1e030c01180206041503020f0406051207021506130e030307020309030d030204050a030609021305040b09071a0d09050304081c08011d1602070801 76
    0xc036506054141039840d58070103e6500c1b1034004100480380e00e48144d01c01c4480310529401c0da0b14a1110003500d00c00c42000d140e804815400000c0c003001c4845091003002441c000c2408800c64131540e540015469025a101e1030096420520081c05050300c603504031107c052900305ca039a19540c540308003c000383c202eaa07a4440c0c150362907000c00d130168000680c2e480410600ca40c45130300d50f41c034a01403000048880c4180021641c4500440910a9003407010f10f01c9400b040e80110b4a81042c02e0405240075010729032002410310400090201c5d0301c1e0f1240c0c28054a801060114041d10309101080e10f2081c5c40160041d100d29202c288002c000341c8243c038a010b030b144682200e803116102c2c0c0040011507404101000d40c0b0a0030007401c01c062115400040d40103003c2c20949080c60341d24107a07541442048580c1400038440d240d01050b0300740e0050401405032160020402038841c00c10300c038004400000c1d0941c405a00941983c080e81842000707070401610108000744080d0048031541051807c585202e00d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 802576735 1250 802575485 802575497
    0xc0c0605030c130e071b0c090e150a0c02060c04140f0609100c020a1e03020904031b0503030a05011508060f13110903010b0609011205061c080c010608070f14030102071a07 75
    0x1242c0340c000b40c1c0740b483d4066000301c91400d01f1458502544020181055500150701070a003540b560144086d020b680704840da0303030011883d141c01034002414000b0003800340507103032030522061280606003080d80c0c42d6102c05844040c280d0031200d0000d151401a982c619500440304400750380c03000d43c4070381c0c03418496209407849500552035071140646100713a0b4589103100801004100003520f000b60760a03801a008e800e03d815135141009140505c00400c1000351600e41c000001e00c07911030251304c40d00340100b4a8035104200e5041c000b400034084038000e08454480c98a68000e2a442d6990010007411f442070720504000c4103d03010505203040c0c002c4001c052095181070040c07991420f24100300c0703082d00c10594a100c40502c400c00c080d001000041d1540340c10580f400080e070201e4550701d03e164440c0d4010746026491f01c01c04c0b09030380d013910810382042c65980c120b1001081265620303250704003030b0b824400d11f54801e0005d00c0003081c024010200e0240c9407c0503544a01a40c03c804e00d900c82c010601c0e40d84031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 802577985 1250 802576735 802576757
    0x15092102060a02160b2b090c080601060f0e090403110f1c0909150509090a05030a0c30110c060403030e0901082409010207120e040c0c0c0605030c130e07 67
    0x20183d074059a03482c1001102d02c11b50515005428101526500b8030340d000000e42c072001900d40c0682c0e41900d030003c101d80d6011308014003c080e004010180444214134105002c00e41d9103010980080707000d0802410310204203413100b40c00c041800102c0d40b541c0d42004850b5402c017040600d00c5650f1801c03a0000c04521828404240302c516401032a8181504002c2c03186442d1070541800785800c8028403540b050302507510780d6400200140024403905000b13580c0d0740c0700781296061500c1d8180691035218850460504040300b60034912101c50020072a50411101d0140b1400d03440342090016414242d20140c0000c01208041e00000324100c0070b50240d40b000703038681c2c94030809a5502c00086c1e110b08403603c0c04a1134a800c00c0b0046580364410000e0002501300146030380c5370004904550103580100700d64070041725140c201889804400415450810300e4400c89840c2ca8160701c0d52802210200030340000000c0010508034100c54500b40e4500c00c40308200d998880c03014201105071000e800254a00e042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 802579235 1250 802577985 802577999
    0x9040c0216090e060726041a011d0406111b070f0e10140a031514090309011d010c0c0321050414190f0308030402030715092102060a0216 60
    0xa407003c80090400400141c2c50300c0310281c6104040c0c00007401070704001c82003c121000e55442260190380f0401034143e500310f20384552481c0300b00c140c1015003d00030b1140c081e00360785a0000c5407500a9004140050b0413405599030759107034880d4085005150034111048804c4020003e02001110780b0a03407130f485542cad2200130b0101c4144003990f10341180900b40c0c00030f0007104400300e280c84d514000141040e03580d984c3c82e41d815520079000e40000740d103d59151320088a0041c81b21605a0085032600070f58585400031001802040c541100b114920b4040b003442101640078984144006400501821001d517803454017408243d0350700c03c0d105034842412500c00c0e5680c01101558142e0310980c0d0040c884d00d0800742441541c0c032498a014040d1500240005a52110942c81401450040700e41c01d50b43c0c5818010305150030001e500c092004d42d1184401d440e050b82c400d04083c01d540c044094000c1d03900102000b0b88410300358000296000703d0000b80028030760307000a50401181d135007070141d905044e502e5071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 802580485 1250 802579235 802579241
    0x20703170909150d061a010e060c0a2409081908060f091b0c0304051206040803010312020102040302040f0509060f070909020901120f02090118120b060609040c021609 73
    0x380c0740e000041c40000c01c8080d0826260080c0c00c81002e40115182440d81d00d80e2015511900c82d041c1c040030140180b100c080d40e00a907c00010441900c206d450950500c41c810b960b0100101e01030041e4070540c0d01c4140c02e4100c0c5d0915810040400c0050017018640c1c1402d081c90351202e15542040100c103508840174601644903284560401401450710808080c2805000100107200d80c2c200c0f07030001c1c00e01002d1030300f00c006006040d5800300113545503424481403041c0200000c6881c0580c0d4042000c00001071214802c4038192a4000e10a0461000d03010080e0f01901541d013009500500700040740b5640d1105d607000d148901c05001c00c0728150785414910b05081e01040d82c0003030001c4e07a100d50030300182c0d030103400034400284180361004410384034103001d800300d1b0070300700749030340b520350002400302d801e41e4009400540c14420707104011007949029001c46680f070604d02c0041c189560b1800140b02d560f174170001d8450800014000f48400030561800079190f0424200a2551080d000004510480e44e44 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 802581735 1250 802580485 802580497
    0x2901060203030109110c0601030302030d0606110c060c0304030506010909020405070c050607030213030219090605100c1b0e09060402040f09020307050415080d020d030b04020a1d0103060b070302070317 88
    0x18000e140b441e401c0200c4a0044d0200c14101069404204040c0d900200c00700705c0d240c000d43c00303603001e15242c5c1d4007450544261002580217404110030716400106180300422a048420b50444000303560703070740303a0202d2411401568005041406441b00019074a07038a41c0048054910840c2d0030449541c0f0148142c0d03081000c1034000d0a1a8030150010381014081d500400390810810719031500c090742e9500003640744291910301c245000844200b00601001c074000d1401810b070440d180d481001614200070520880070502904014801d40e14202d1141c072001010041d011801c40d94410303141140f40d00e584c9410640e4201d018070b180c00002e140503016882040007141c3d0040191540354500030400000d008039218060780020550340004280b0810440b06401c0307441d035006091317061152030340507003250200700050780034600401a51324896030100406143d1400d100880c1b03036003504400101c0c001c20207500b18080f081c80000e2590305041d00000c54400301c9108240d20540d1a000e10102c420310f000d08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 802582985 1250 802581735 802581737
    0xf080d110d0e0a050a060302090a06021c0807210903090602011a0607020a0e07080412080c0f2b021c11040b0706090b01060f0206180c0d02120604290106 67
    0x481145041c481c0306060101e10204010605051940ca45000070304101442d4419000700382c1c0050030f4442420030850004c000c0c002c0b80050451981c682031500c00e95030104d0305100411032504001190305014100340c900309982645080d605030303201c0c010300d001050f000000381e01040c000607002602074070501581301e440080040c0d4500844541060100316000300070b00700c3c0e100c240d82038082a0070f40d1500e40700348542e000b0782d14240141042c1c01c110038103038030310722104041164000030000ba10305284222043d40b91922900350f5904040c48281c5c07125400c481e40c1c40031780c581c910a10321007000303642c002e403038803211582d42d480240b60b040b042079040f50000d44800d5070060003440100500354040340940803642c02810081003c4a055440081c0c58a00340c0015010500080c440201254100900c0d0703407080080062044a0103c03030040707a690303001070b070009204201201c0d80d48115140d500400840e210088102c0740b480c141403418a542c03910150004c42c00c4a107101e40e881d510900c03070304450b049440c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 802584235 1250 802582985 802582993
    0xc16031b1209030311730201020307080d0e062401081302091009020d1a060901020c04271101140403080708160f1202060c0c120a0215010f080d11 64
    0x2c030440404100c0400410303031652003c03c1074801c416075106da00d0020b0040d040054a040031050303c00c0c00051072001d0500401401c0017101006036000401c076000e16401c641000d4a59146404490140600440a0301c0030f004110912280910318a02034282805800e0116030950200c4011640404215051080012040c501c4400f50a00318409030b04074480f25404000e16132105940da059900c421500c3c0807241ea0350201c1815070806065502c11000120b910702d14114041000039996201803003070700e100c1c03541c4041c0000020000303190401c000c018000c50409a98090030506115214800c2841c0407840a103000f2000255420440303040d00ea100d01d1840c00c20846484102c0b494204110361324400c1e00c011000d8020905000303560214a1041c8200503450300c555a000381070140151148842c01402e214410070130074007041c47d0050b0f480b12003070141c0310044000220b01c1c1c810081c0e0341203a403450000021030208103200046041c0c0340004200c0d003140c510070100b2201d1018000b4a0061a00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 802585485 1250 802584235 802584283
    0x1101140a0c03021308030405010f1412091009030801050f090417030a091401021903020414010e13020c0a17030709091e110a080c16031b1209030311 65
    0x41039118556540ea20301c2c0c01420b00001d81c0c08400302ca08540c00403c0e060384042810001036031b00152030205000c0034034042e00341000d100040c904034081c0c0108001043c695000085c0c0d0440f0400103038400c0102d9a000740b0000c0070b10700300a0002842809018007540c454400b0601a08100743e8440c0201e40c410034000028020300d40892282e00080d003041c14142d116403084001c0340d0540b03c0280c03c4401c100c00180d07901000c2e6002c84002c602c4400ca801410b0050104100c8447c2c0c25158511440013030a08503902c400760030010740034461290b0118089440400c03405007800f0300281c10359a881c80342d50701440b9a0050ba908080354041214203100080300300f0428400c01030603030000e00030a00d00302205048025030044103015500070b03410b024274501002c81d030342c88c086a1089005400107800c420b45440d04110030b54901c01020114005014813010a03d80350920380c44032603054016401c0000d40c1001c2804030740c020440102840240e00080c02c00f15a5290660041400103800c85049004004a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 802586735 1250 802585485 802585501
    0x618150305281505010e070f090b160b010b03181203060411070f03080601090f0b03040f17070606050f0616110d0c0801020904110f03010302190b0703020607110114 72
    0x31a4415580442d241c01046500050343c03940090302c81c0c01010310042000c1d0704013000207481000c0141407204110101c1103401a46400040c1c000503a00c010000c143c0e0b416a07500400254018108001c1c0b11840a400020b0002c2c40c54002e035000d0203907801e0605125800720f07142c0390707140f107007059001c0404010004520036160a0340810800c04d50340b01c1d1542040000d8807000c880b8103400b801070340442e140d54100007256a100448030060956107400c084140d007001c9000045010041005190b5480c1c5494030050003003441402c2411800121203d59442180c50510040c12241c82094040c01341c00301691220300d8180191460101c908042c000d800398152144618900da48101c56085070082ca0000013140440c8103120242200000140c0e8680c4100b0034002101e81003111459801c41c10300220350340002d920100c9045030f0b0100d0b201e01e804400386124035521607040d8850b00c00c0801c00161103041640201d103052045869803185446090b406101c14243c034010713200801d1803441600020400303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 802587985 1250 802586735 802586773
    0xd050f16140d03120c021509120d0f0902061306121e0504020613030f020918030d050601020c04050108061509090a02010c150903111b010906030b040f0618150305 71
    0x500e00a02e845807407a0307180f00d0b11300c0803900201711500041c0c11a4000d101c6a0070031140c801d07000055034000340320207180440451010b0042d00700c2109100d49500c94061400d52a812403000345400501003032fa035402002c2080c560000e14800e00000c00c041900d1481030319954440c03814940701548003456082000751100009100080080341c0c0028203000b0789166a001c0c8690070051841140d2480c034008081c01080701d004001886181c2045001d462042da0000c04800e45541250022000c1503c6e2500e10042c0e0401424041d00f03500300e0724090000402c01c000041290144500fa81494400f40111040c003058001c2101c014580c2c0c0e020315240001548074280c01407540d40908000e480d00c0700300303080410646038068000c1d400100b1145949901020500807042c00c0713007400700044460811040081c0c42458544500c8090540d00d00071100c003030f126900304045080c900c400420080380c46031000a480d00c10101501c01d030501d400100206c2500f8070a11000350788d009002000804019a41c801c20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 802589235 1250 802587985 802588009
    0x5070501140901090312020a0e1c02040908030a0e010902011413091b08070507050a020603040f0c0b0318030c0a141011031503011407030c0e0d050f1614 67
    0x65650715140d0340d10016140341014050b4074003600110f110b45050800601d40e100b080220504548100309040d00305402a60380d0322341500c255618072000101c8041024610640305019400604050100c0f04103c40c1400440c070860303400000300a0306080007099803c944655200a011921180f5004280d4405201400391903020794030021555445103014001d44140c040448280e2060b05841d40c5500e400003c0c03580e01c80620320700300e410255262140b60340c58030840000390181343c000020800340604003103101c0d1400d8010502e80c00709503a03035040114640c011038030b0001c040c003103038614083d01f9000300488003170041c503000414a40d2881d40780c440301640ea450f1407019500c80e0300360000c1c4c9100b450003610f00c040e04003c01d8685a1920700c15107580c035244910410301ca40d16280e0b80e5110500298a80e0780c010303000b4a400104080d998100b91002540600700c154403017a02c3d69070030b00b0401c0c00604600e01103d4201511006000e2603081141e0103041c0c0148481007024a00e1011107007402c1e401e21318 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 802590485 1250 802589235 802589243
    0x150f1312022b021c0204050c030c0d050c12090706021e060c131701020915040503060f0601260612010e030a0c060207080304060902041a060702011112040b031023010507 74
    0x500340c03060383e00281c41c0680c800c070921011512225800c007545010701c0b03441d40c400766007000c0382d245180c841c45903407a910a04091511840c2d03241c000c51211020301d0b050712510060400703409100d01340044c00784e40d50441c5204840c01072294100702841074400c400190400342402004000c591102000c8560a4101c541c9a01d6003a0780c0c401e00107403c0c04500da818000001d00c130001a62840010280241030058444101128100300410046503e00040c0c1680c803052248000581e0303280d400c01210882003030030303080ca14660003014011002400605440c012601100c5040c81c0b07005842c18603082c0c4a0003113194400d500140018400031740030700780e01116030380b0030100145402d145c3c0d42d9540322908150f4054070b07100d6a9562810860400c1c0c8a40c1030381104903007080210f0101100040c1c0c10f031207a050000e041001403c40400481410080002003c0340e41c20501d80360358591115290a41044541c0d0301c950001880010301d00b0000b9039102d94200d2482c0781001c0d810308000c0103680c40d61040310111 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 802591735 1250 802590485 802590559
    0x209011b080c010c080f010602150115110313091d060f1e0f06010318081c0212131208100e07050903010e1e0304140906150f131202 58
    0x400160030038890390052444176107a02c151401c02038050303450000140c0114095601c80341103400700c1d501118907241110001d01c1590010000e106040315015402c200d880c20740e200100d1103004c19803002d6010b20664091420420007140464030446c0000030b105c40c2c0c40602c0e0007100115511019101c0c0d13495005800a02202002d44500c059078003e0310104c4074040300c0300c8201d05101c100e680c14000c104120800000400100d0801e4840781403e2164261031030404001c03600704401004560141c40300000c648181c1403151825881c03005101c902c4400c2290394000c41129034045a00640c9458051030004400605090915020580c1202d0242c85401400380c01c0c46080c54541d0b0074001c1e2406d1044800c058002d88424106d4204100701d035136001c138215041480180400c00c1c148044c1907040500f1182400c09842e0702e000703c0d08074100d6180c88204003200044c1b001110381210001c141a071009014955032554030700c07000c6d000310510306000758025aa2003690f203131003404c04008518a51051403207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 802592985 1250 802591735 802591747
    0x904051203070206100608070905130f020c01050a05090d090e0601090819170406080a02072105130501110604143901030c1e020726070602010209011b08 67
    0x30010a030412968040103038450001c02042a03810300d0f13000c00911050a0800d19070420050140c00c95805009150049400f9480d03490342c10301076001120b0807007440c04111356680c80c03900154041e14046031601012400c02021540d44a0005040b0741d01d00b600f135445203005810401700340071001001d840e09041190021011804050500c408800190481d90071402003007039107041440e101d840700d549143c5001c00e0004002e080d400905130317544030758109001a6540c54514042c6900c030f0402d07400c1c9110107880950b003814260480014a21283c1c03806151009070b541b030004460900101ca03242d030545d003082c0c0114000841501d183e125146658090b00c44e559034030343c0048040440749500c058910214030462441603c10308014401420a19050002d04440c44002e020103006660350381424000808a400691080c04075501914a442110950070090602e1030740c54814846881100e0044910000360540144216041d891701078552441d4032241591040107542c103500281d904000030064 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 802594235 1250 802592985 802593013
    0xe010902071106181e01200319090915060e120a02030d0e010e0405040b06150f0301060f030507170c090102030403051005010e090a05100c030207020d140c09040b06090405 75
    0x25050140040f018a0010079044041045c203000c21403030b81801e40203d8100352181e0f41d2044d40e51103010141c00201c4a10300300260310038914400c4c1c801400761040542c5580c5c84451303102035003104803034500b541802024203032030001200c0020307803140c000880d1229603414680d04202c01c0c031014126105054800403896600460309003502035400398001a2a048a02c0c802d607000504400c0400c010f440402072440c0c69070b52100034940c0684454452a00c02c0d4221002105220480b5451203071403108540300e5a60301c5004e450111800d41020110b802c04002500c0c00d4400c0001d8040341104c1c2e18901103d455008076500240c3c0918411411800200030120201c0c01c00c001e0000c000009145c00105985410400074090001409034a202e4006403240b102060380046c189203801d56000e0006641e84141a00b41d0003071003038000007508050b260300709505202074080c0d000f00b106004016210301007025810480130031400c5800404945c52400810301600b002204968000d07c04c00840e00c01802c1102 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 802595485 1250 802594235 802594237
    0x906050406021906090b07031e062123070317030f06060d0f18020301050601050c102c0a0c290304050a08041806090b0303160302070f0905060f0105040e010902071106 73
    0x10361000840d40310040d8822780300c00040c80d143c01d0540315008200450030080c90f15003034801c2c1d03407500300e41d83c204100910510541c520030500311049011445001503038880c00d1a1900150b2000780e811181c5100a0040d1582d01001c8900c074401c9401c031414642d8400e401c0000d00e41100340b204110b260b8a0f8a20b4035004c1c000d114500d03410307641d0440115082c181d8810103007941c1d801441c0504201c401d20400d01c000390005800403540d11440c1d00880c4c030780d4000c0c1c0016082502d802050601b1a10705510003440800070485107032550140003290030a0b9160b0760950311100030784029800c216018030242035070b00703122009103800c0b40c03148055405882071600d9a071125002a00030115000c0340c400542d0122909200f514000c2c0001034041c0500c00074840081e0701d07402907403505610b03035903400d000b942094402d026110141c040e14240c00c2195071a40c8814006003401c55030b0500070042d80103044100d40c018020b403000c4440132031402e42d80d0307030900c510b01010350050102200d0242c0c0302c080c1190345550f840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 802596735 1250 802595485 802595491
    0x50717091c0903110604080a060b03032a0105070206011220030706052205090103081c020319060f0321141c0f09150218030a0b0105010906050406021906090b 69
    0x181e00c000b11141141040c0c18450300c0510402c3c407a0f0000c000800442c00c7c041451039030190440c8002030b184c0c50450200341544120840e501407501c98902c118010b0032880c00e8102c6414130f01008000135a20020166942c0b0001c4c0166441804014010070014171910032009519a85900b1503003240c141c00003092904606800090118501145400000310700010840c2d5a0303a0030000241c9261901002c60760540381808090012400040d841d4081c5c0d480c3d00c4141e0804c0340a00c011035803883d0000144a03000c0050446002c00e604003600060f180041d48140b4055a4101200003003100d07546400c3d07100c8039003060750541031154140304181200300314070103406051403211842c444032004500400c1100d2113840c4031071600b03203051b07401000b152064540486030300d031180300140d880c2d044000c03580003100c26940c8561305210301b030440002c10480c100b013281281e0081e00c81d459000d8640b0340680d10b038001c0c2e0081400584c0032407085003240d00fa012035650070340d019400c001a00202511100c003004822 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 802597985 1250 802596735 802596737
    0x1a0409060f150e132a050405042003060910120c060f0813020126162307020126270f0307020f1206010e040b0703050717091c 55
    0x10840c10845800391607400c2d80e070a900c1e45010840d280e080310015400507071414494521036940c00c1010100c1c0c043c41031002034030315140f0400418043d0550300401a60141c000c580c011070038450041c240b220600d1040300502114258039045030f40c2d2800b8000b41501c020040c00111503003110006862250613a50481d07140109110401d2904020300508100c3d000c6d01c00b030041010781c4c070400c51110b500b4a8401002c560919183e10704c412410400e20040301581c0e414011005d130481800301045141d903281c5070200484c6c60308da80d011030319417503100c4503000b1b42100c0b078420307030704001c00c5d40158407070500566140b140c100c40707078164107410281504c0c030f0804540302e02403040c0f041e00c000c020368103c999941b9036070010ba008004050039840d02c2512400ba0b518003c0c080c020900d001915130f03650741d07105d02010005104807242e542e561600f62141c0300003580e05840e0f02d805d4802281800e88640a024880c010300d869403e100d2400b08074084034844000c0c0044840d0140c00d0b0710f100101e0850602000001d5a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 802599235 1250 802597985 802598009
    0x40501020d05010e010302100c03090f06021b010516240e0a0b1b040608060432011a030708070c051917030709150201020c060112030e040908041a040906 67
    0x6410000c074210b400c103070070400704031603000010401641d036201c00f48a8402c0c0c034a050454122246829107503c0d4040d04180742e0b2045025020036895400150440b0745e075000607101c003c0480c80d800644861050841d800d51a0307031000f0b0104d010a5615084a520311240c90200240c41118152601113640004a032600d07034100d1801c20051101150350380da007000c80c000c0700540c05804442a40107912440c800c01c810b0041441c0002e146036110303408101c0e292089003821102d00303000d46402e15102e01c5c120701c0120301e4160200220f8000c280c40e0200780b01c200032804032484d54a542006650224008012804114046083c0000100140040500008410301d903070003c2c80545083c0048101001610a040e0401d02c2003104007940401500d04803042c035980c920a42501000407070192141c03c1c540b0003244188800003404010828004070103500941d40ca00006903a0010081611070000018084c8c10051000303225484070b444041201c1c1703070b000c8102813816550f032045000307580e081e5010040d2445 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 802600485 1250 802599235 802599247
    0x160b04060e2e09020f0303030109240501050d020d0b12010e0d170106180b04081608010902010e0603060402040302040615020c030304031707030323061507201804050102 74
    0xc4100300288540301500014140c220480344070480c0008110300e20480b8944031100c210942d126030103402181c04010301a6030f56980c4801d001c0c80a4280200d421460210202c4003a401e059812001010740304141d41d00c03860003c680c00000069002600360054541e42c0700c03400a0255580170340c4800c1c000d8542c00110b56201c04516941c00c05220448003000d01c00403002d6030170550f0a0351041c5041d26094103007805c01d9084440c84646000389034118407448800050702041c3c2200028820441050010040c400161583d0505090b030303001080090200d80e45004102180c505980138680c0907001030700050400c0e98940000301038800d03941c4166a1400d00c0c803100f440c078541c1448103070802d050940c002c5260074911390302c1c41030b4070f01c0c5428041740002c030104040042600c40e411040810a01c8407525900c2141030020005140c4140d03400740c41603c46500d00c0c0d01e6840d0b10780546800c160020654105003120030420040f4180c900306966100001d181190601d078203810605005600030400181c1301c032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 802601735 1250 802600485 802600511
    0xb030105160906020c0616110d03030e010c0504031a0702010b040c0c05070f0b0313020303090a030302012f0a183f0c06180f1514040506040506160b0406 67
    0x210035003200c01190401c10108071a030f00c846c81140c280c010b40312561001410281048110441d00c02c00541d48202082100000d05500d40c22500c0b029045100030002c4030070044040d6040e20031440000c00d20040500d0028604c00c0758100c1d00d41c402454000030442e404e83c0000141143c200c51040e6001c202824841d1003840070420104003d0410401e80c0031110341046241d03406370200404501d00c800108043e0011034034240241c514150380a4402203100e41ca03482c000c0d001c4d024402400c13213060002c00811100e8040d2901c50721468500019080c07805013014012580b440c291284054042044100083c0703100024142c4026a10301c0c1446115040006c17000c1d1082482c441101c00d07070191908480741c041090b862880044601c5424960342e010761444905c0d8030721020303501c00540f81e00d108400080c40001c0c98030480b08170409030b41d42d8005508132a180206030003030b8041c480c4c10503000d00041c002400c0110042001c030414000582850840e550342c1103c82004403411621341e0b4807074840c01000c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 802602985 1250 802601735 802601747
    0x5120c0a05070f0611031513090b0a1107210206150f0103050601170c09150301030f030503061f2c0108040b0a06080f0f0c0d0b0a050a0b03010516 64
    0x2200484105140925246008026015000024040001061001c0708200483e446070b802c1e1000d0030100750b140d01d85a040a04001078505486019101941810705065000e1251f05c031416405a000f4100c0c0d1600c904000c002d00d80d808400721060003c00141000c00e814003402c0c06881981c039022800f60510502c000d0030000d000c2e0002e0042c0300c01c40289201d0b9600e0b090490703100c010070320f400602d03a030b0740c00300484000764803800d0f100031100400140300707030340c800000200021601580c60300703a4040c41343c1c50081d1740d00c800d21020300441841506900080c0c4540c0080d84c01030030013460002c503040140b144054200b42042140701007150600320383d203101d2071040d507103d082166003c00001800324000207840e110000701b008140c1d60444d0009600d007110b550120b80a00781260848038441ca04c3d10206079103009414400b00307103101d0314480030300f5850521240780200381c3c000414035054036000c00d0140500b074081c00c070150a035161354044a0f0b0b40c9092081600c54000d040c14910705400e41070003e080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 802604235 1250 802602985 802602991
    0x1140424050f15031f031a10060c050703080a050c060711061308032e0905010e0c04050d0f030903021e01030501060801080a0f15050106180801140a091103030a0512 72
    0xc0c1120402500c10f4051507016280e0202000079141c10040c40b28060401454954000505580070701204818525002100c01c2c802c07070200c0c900c0001103842d044250f62804801400915aa012920a10005200a01030020a541c1d424003d0928003144441811b11a08803032100001c0da080302a1401d1100400040b0f401210702011f415040751036480f01d81030b40c803006150803541e00c29040f0b095074900340403c0f211047c681c035411149065480d1030000d0046d000c20f1203400203d1021501003105541c0c90802c803002c40314010024410750311680e8411144406075401503080c0000c4000000168030f800c407107254080724004085410410040014023111301c1038003c00f003000300000c0140882c600000d803c02d80b003130b0440c00d10b040c1c0b40c41d14600790800c01c504811401c1d225041000000300d03a0303049100b02460090714528401481e488221450881d0200082d2000d0322181c800480c0e110000d550160314400d0041d03034000080788400d00842c1c5150300a0442c60b00203480007030484240c0324441c0300250 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 802605485 1250 802604235 802604239
    0x10020f0f04030f06200d090507081e101b0c03050405100906080717010611010905100e25030605060609100809100e0a1403040806070306031109040b01140424050f 71
    0x140f0905c21410914035401440103072120203a4420000090080c10480310004200c000c081351141242c170346ca140c042000300e90303480d200d5110f8590b400d1014107050082000071149010a40d84510f0100c1c421120070031140380a8003030180800c404103141c2c440d0f02e1403801c118404c0c0c65a210b05490548000d02c1450000c240701c00304440c0c041c8070300316803050742101c80c119096440c0050300c0b41c0416000f01c5c010409900002c1c1503114080b44a10512043d4200c442c1010450050b62403030484540c1e00d480c14468032004501d0030014102c14070014105d03030310032600700d080030b400d43d814180618040b81005d03424200d80b0010030200c00c208156001c0c200226120108480c00601075071071840a03055403200000c5006200041d210441042c6401c1082620f0042144d03604492075402c18010250003002280002d0b02c0d000d0356103d04211780d0070310142d0203000310f40c4154070381d1a6a107010300140924030842044c542c8681c640c3c05140c100c8880c07810700040001042e0040843c14500300400001c003020000083c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 802606735 1250 802605485 802605521
    0x180114120712020d1e1a1002012a02060702030c151005090f06090c04030c050f0103021905070b010608090a03120e03070602040f0f150c0f0206160c0803090310020f0f04030f06 77
    0x5403048820f05140954028156611f20941c1c02043c000c1e400b5002e1007104000d42244074041051000700d440010500c4403081d02641c40986849900300d1320b038424100785890651080c2010311603409a0340c2010380c00007004d103103604629105c0001803401d5105445215103003002c1028001c1502e0061032085c6c0020101c4000b52600385140e4490200e0440e40c03207141d1003142444526411a40039804a6840c0b082c818000070040c03c006c2c1d0040e0540d044407206903002c141000010640d54005d0041034001c031024402008144130b02d6030b040380d0041e40c086803900940d03141e0044001d103040400107404218410300740540c440c1d0a0410369610210369031720400a113011f40404214a030804e0b12500550301c01403a1008651541d41444031284078240802500700b407000a1062445090303c100c0d040076442507510804280d5591501a900d00855503403c0d403542001c005640701244070340c0201400c41c0640b50706070426007030340c1d078100094015074030907607001080d0341a800c2048060302c00d1a8000364800209 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 802607985 1250 802606735 802606751
    0x1020a210f09060f03150e04050607020606030102040e0414100f0b0315100e1b0a0509090a05010f23060a03020a110a030e1e0411180114120712020d1e 66
    0x2041c2c3d2030119544802e06990706d908510081d07240c21900041d010500085699040030301c3e0107540c803c011200305005002c1c28020a001d0325060084604030b400801150782d864485032035980300c50b807035516900a01d00c140601010b034908070b4014410f005d43c881e0300004400460300d0038181040117141042e003c21040108100010391200c801c03e082d030703455000020040e5120002d070030211050900f401d0402501058034030640d0350180003480c481400b96904040781c0c0740d2407070420545000780224000c403040c502003030208402c42d001c000004070260a00081e40450b4401051030707640a1051940040d400040c08031119800800c94a0340d440f00074010040f0003c9a103000b41114130329018140700704540c40b850300c40001411012841000000c2c010003540000400400d0036034040c1003009546a40b20344801d59947c081c8502e0340002480411580c98a5200b000301c98240c84014040818402d406442c190758111b2403020b0f01c40002d00340e5001583c10281c2079503050340130307104e100c81030036609011203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 802609235 1250 802607985 802607987
    0x110405250e033a0c0b0907030c120b0705030c0922050f1902090105091908010e0a020108130201110601030f030212040320012001020301140102012901020a210f0906 72
    0x4420000c81c080ca410455403550030f011261090040710261942d020a0180303d552500481c00004480c4100980f6240c182d66041d906079440315241d01901c2503580f2400144694000d0005682c03100c901500f00d841d0000c8903000807504001401d40f000300c0035000780005128066072180e0b98000380104600d03100d624001e8050b21110010241a050346500801e07503d01690061041c1c0303d0840008210004400d5100708480341c800300340c4202c4030290700340144445280c80114040e2182601a95400c03400c1e80d60140460401501803412030400146825405010390b00340000e40c061407040303146140c011414100245000d00741c003100070552038100404c20004600d000d0342855103003403922544d18241010016982c40e003444000c1201e0004044040c00a0340040d03004505841a0702003110205904000481c22501600b403403501500162000c0c0c212000700684410510405104590424020340d540d402c1d55094005a07040340d994402c0d0341141150003005060500100c0d2401003203261402c24 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 802610485 1250 802609235 802609303
    0x41505031b0d1703060f0a0b04050603090c030111131401080f0a240306110a08040f060b03031c050601020d210b030f0c1903110405250e03 61
    0x9a55901507020400c0301120303450310040102c00e41d412148255900d4680c10207280181e0080315142e00c2a403111041480620300300d0f6280f41a0b07503080c4c10007400c0c03a041c03034180200343d4030242401e00d040c80380840142d00b0355000d02031006048a40040103071120400301c07034000b95583e80e8000e500302d8140d045019229903131000c00503600562000149a40f40c80780d140800003080543c0c203540c02c0d88640850703003481c556400d01d004d046901c1f500082210482c146021a1140202da00a01c001044c410100e400304d030003408660301071400f5800c0000c05420610001c1d10f5940312010404040401e000c541103e1102c5110b00e40e4410028006005800032030000105441c904007625020f03d0011003034489400c6c4140e01c4544954000b80807a4070a0300040240c40d0b0312404802d10034400d16990700c01d80f904d03070343d007040c08811039510121f00300c0001c100c0c004120280c18000c0051110201c0c5100c1c4040998644440800c811420b0321110000819941814100800c3d89004264262a01e840020600e0000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 802611735 1250 802610485 802610503
    0xb250f170705150c0705010905030a1106090a1115070609020a0503210a091e0e01050a0803070305070611120f1e0a110c0a0506100f060f0810210204150503 68
    0x199050f6030391442c0c60488540200c441c0070300590720f0b10300100100071000004110303030210f035250820313070350305c087c4800b542c130306c0102c44440007078019061101c001070342284000c0034401c0c000c03c0c201c01d4600c0801d00800702c1d080104243c4000b0745541d645019030800e505107101605066000d40184100040f03c2144800c14203081010450002580c50a507403040304018050034a074200503000b00b17060f603502c41000465019540d5071120781c1000040c20328110004504460b003540145003081a2134909952070b030040b580546090303855030702d54841102c41d0f100600040540021050580c1490200004866001040c12100d001619010801da164409082d540089001c00215403002c0341c26480c1c0c0180100d0b0a410054800c2c440d2500402ca07002ca60325100c0c4001c0c40500300001d13510190300308503003064030421300402d040e19008200030f0f100c0c3c03410542c4140000a4030622940d580c99000000140c40359020081c0c0d48406901c00718541030140344002c40e21140d122914134100400a62038034091 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 802612985 1250 802611735 802611763
    0x30812270c091b04120501060e1312180305011a010219021c02060a20060c0a110f1209011d03070b07030e0607030801030b0f010b040b250f170705 64
    0x180002421443c1030700d0800342880c0c0000e44152100e503580c090307110b40744201c0c408580c15401c00c41d0124902005110b080c0c410f0281583c01e5000c092980c0300c10005031000e038000810071909441d44220100058000d10045106130000150b002450a5650318083c804407002c1c11908140002100d488500c580601c0040d0100c0e11000014446008040c5094a0700c000a40000010544c6495203420921200a0040c5130390949500d1142c010b1180d2100300803140c00f0300760716003407010a1100e8483c1d0301c4e008801d501c101c01c550380307031039844000c40c6403c080c89003801c914140011030f1151544d024001c0c58405081c1003000c509824201d00081c1c607030302070b800340d001d58070030208240d07040c5803181d882d032900e004006d80301682c1d401060500402403502400140e40b42e0200b000400c00d20586040e85034101c441e1048401d040a08281d9801d02c503500ca0340084403400340090359607070072165885030010340f0740c4070b090280e8035482140b030030141c1c14400750005104a0400e008075000b243c404200d6200e01c1c800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 802614235 1250 802612985 802612999
    0x1006050f060a0207031703090d020a0b0a020d0b221a1f1413052b060c050403080d06060e030f0a0609030306080d0807120605031b0a030812270c 63
    0x201804a00d0080164406050506c07562108241c0c100c0640045004001c1d00e01514490740700d940003030346da5030398100c00240a403e4540004e4070680300e66010380040768140e0404101c0b40409000283c0303030480d59000e4100044c00740d400d00b04030312841c801c14001860386d4006120300080b603c00654640301c00388204500d098054000e4803400e01c41c081c006800c82c4680c0d030107611182403008030703000030384107001d40380c011224807540c40d4000345645040b403400911560040100e000319980d078405405c14807003140601c0028013001c0005400c50000d07110712132500200044251800000404c492403405510f4002c0c0c000c14128940098045407440b0703002e40240000c00e04100d0391a0440080084c3e0748040058011120750b0f140390795110032858007485c115550302044041d81c0614500725141441342c5c5a060b4000c801d10104134210040c0c43e0024080103050155090343e9807106101c96000e0070010b40b90f241d91000300511000c11124259000c110844900713500d00000f118659280e001c0525648110300f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 802615485 1250 802614235 802614247
    0x9070609050d05280501060e01030f17040504110d0b1005030103062406120b0111030a27030515010f03080a0c02131e0605270a0b090c03091006050f06 66
    0x2404004603030410441601400c0440f1440080d04c0f42000110002c0324103500309400040c100c207085880c03506803a0881d11030400d0340050340e129814a0640241d0000192051000061950f101d10903420311921002c0050f55400f010006901117504801543e0311038118480f0050516601405480c1500d9011400285c904950640e0360404081149011000340f0084c00115400b0303400a88140c1c0360f02202c0092201d84204001550440c41c40d10100f04641e1041c130078688000d104004651070260302031100d40c848402440d0145403150b094005841641c059a1b05025959041860b14010099404200c603842d04565983d031241c07051207115010020103d030000c00f51358030900c1d08907002e04031003020400c916a001c0d61490307001d130909080704200c0c588580051030f8248a80c525000030680d081900108161503200c0d0f4810178094070710350500b6941c100148058540f40d02c02030085410342d05441d224641194024504030940c006140c0d00b504059080141d0740f143c000303104c10071000300c0750640c03145 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 802616735 1250 802615485 802615493
    0xa020313300f020f01050108210d0921051c09140f0f010e0c060901051c020a0e150903150a020c120301091103100b07060b04020c0f010509070609050d 66
    0x10070340150244031540030801c60740d206070000b805210011180d020344145101c07001a942c00c071002445003614540100c00c0c41c1c407045024002165109081c000303280e0038140400a0241101e0701004220307090b0385c40c1e540400303c80204d6031382c00f10765031220f242031841e02e0040d030103194022280030f190030314481e181d00b00082040100004900051200780441d1410343d006074000da500d00b0003003410701d0f40b5442c29450030140c2e030300442c04144410028107441d103403050584c01103403950302214111103d0503000c040149548240d000a10b82e4005580d0351a000140940c10407420903c00c140c07445000004000038402500d02241528a2000f103000f800b003156074441d0010043e215426802c8258090210b201484600440146040ea0340801003080f40580c1c83d500d5220380c7c0f005642c0c904003400000c000300f020b5042100100255445913201090110110f0b02107000d0b40c102140b80740b19608842e060154428007407090540c4800501c008065072451715038060459075481c020706029501144d50312042c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 802617985 1250 802616735 802616783
    0x5150702040507020706110a0b01170a140d120209130c03110c0a050c04020c060a0f02040906230a06051b16030c031202033405240a020313 61
    0x2054015206001600e4085002525094180101800b0901e680c0b100074002e580000d6902c08507500c041c80180c0c59080801385000b40040321890310707141c0700f0009000700240d290701d001d00402c2c02c044000d001e44400140081c103c1c0380c4d010f01880d2418411711074a04141d8504554103001602131074006154000d13188100c0281407a0b80b44805c10203030000c0c03401500400000e0b0720b2038082c010020b0350854402602000103a108825103c86c0c40d5000e500401c0f500c80c615840326244000c0c0c0d0800501c0d159446001c7ca059517a0b503801404000881c6d00c2d40b85415408900c0e6404d414011181e07040344078109900542940903108989000b000c0244000c82e4504d401c12920304548400a04401e600f40d49140800b00d2183c580001c40d43d820400000003191800001230390340c00e01800f10500003003401001c81c0a000740d080f076521200140300400d4140403540600201140c048890180d5944d4504844c410106460240851034854410400c01072000b5895a1035030420b540724001c914541c0d15100c44152b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 802619235 1250 802617985 802617997
    0x507052d0310150302090903030c030402010f2102190201090507120f0b0405030307020f190305390f070311010305190c02010911010305070c0206250507031a0403090515 74
    0x10075140204081c0141489000780b41183d05c200c3d65900c00d9a40d480505891340000d4491001c41d00c41880071400540c002c007202d0f0800348961a008050310f4600c0c0d006200f0a51790030b07000320074640c009100c3c0d02c4001d1414010390000d0079400203210030a910b0383c4081e07882040344901d1501c0b880b10940d041c00c01c00e5109500e000c0e5508242c800c03005041500700302d80c80e6070090350000c0141c41044070b03018010a01242800200407910b001501080c41610155042c0d4418011001030f407050744910610500400700843e8400d00401d00d0744d14507400350003150301c0d2032034a02c2c8000040e44104020030000d50042940c000300302c020b00c0c0208607a2140d0405060b251b220000d0000268182a02c1d0fa0540e98154050b008880c054001d40d10005441001503003142e4090310341d0380000f8900b01c40000503041080050402d81545000c0000852000c203a684003200c0305002150550080303c802c000303001c1c0b128103080300350040da4500121410655400741482c0d611740701d0300d8000c1610b140c000006442d044d042e180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 802620485 1250 802619235 802619263
    0xb160302070c0807080606010c0b0f0a020702030a030c15290102190615050906010f0e190e06040608030f1605010603021302130906060c020103020309010b031203040507052d03 77
    0xc41c0343c0c4425085440780c2d00c9010303448483c401d03800050030a40c410025110a150041801c1106440b00b1001c0d4030040c00081079045855000c00642d001a1020462409598020303640d460007403503903103840ea05840225030b455003400d0400c0000411100c117420001c0c600e503080703a88015102da11200507400e000040d000b0000707403125a6403840c1413080340d80100c9583e03160806d13120f1303145441c0c0e000c224001d5410741d0754070300003030500c04002c0e501c0340555000802418014550414041010035000c4041c034180c100100c026201014810507041500070880038000c0740001d9801c00854036110701d502d0040d40401d01c0408040080b90051180070b602c145c02031070b000b8048429030b641c500c4075040a075101141e810750030804d144001a13815454482e610030b0320740503594206400c071140c00440c00703904058446545950b0301c01c04d1040c1da65040140c0c048020352a84100d0b200c1c40d1504000341000201d41c001402420000a040d115201c000c20210005840d05890f0854007410303000f2030310b002d200701c45000b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 802621735 1250 802620485 802620503
    0x3090f020d0812160801030609060b1e03060f01141003090b0c0714070302092806060e010f09030c15030b030703080d06060306052b0605040b04020114070b16030207 72
    0x5003440020350092204000d500c8030fa07401c07516030b402e0b01c0c1d00704100800c01d100012525001400040c42d1500190b460340e000f038101051013080800040c01d038090040202c0701d285104164080c00c1d040c00c0c000c040d400400c0c007100102c0d41d85031403007185010411130b00c40741c400c1051180c821505402940182034007500030700fa110040c035201c0c8a10080350312040065440d0303d0a80d051581700c820003c0c48501707a81d40501451225198071007034030b070b102410009440d42110b4424044904489a110309001002c40d55159100046408000351503104101112020060b01440600100e00d0729259070301202e8540c006504880c2006038120024010b40034043da05018044000091103c4c0c003010b8550046914401c0103240d6859074290103ca0062160325040443c5002d407041a01990b000103005007000507940022440c1e1750703296011180219400c0300c114200c0c1c4144015544d02030960580c2460154042e80341a00030388031410741e010002d00d07028800c440480604a914465010780318000c0d40b00c4001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 802622985 1250 802621735 802621759
    0x1c14040f03020901150e09060d080304060b150a080f0402060403051519140a0c0c0c030b19050c030a0510180509160303120b040204261b1003090f02 65
    0x40080d0a000e440180d21607405280042441ca600540d003c4901d265030300c40d205500b44202c10b128032002c00a1100307500408480b60000880d4600c0e005501c65031080000040350803081e0200044d002450f2160141c521050045e06210b42e0072012994104c800b64a03903403003590b51440010801d21640d00024403038040c62541d240740c11106002a4013901c0c00c00c90340301d0110440b03d0148111101611704400e607402c03d4022901c40c2d901c5900644007a442e501d000400c3c240c89455102c0703182d54680c0708076030124a03d81040284100f84200c0303503402a010b40b0038040e60030614200d80d407500001c0c2c0118641d03542c4402203030004017019041e000078600905810540903141300c02c00001c040880303808010b070080d020010805100c042e801c2007500c0d4980c407100c5914590044c0000100768007900715801c207508101c042800c00d481c0027188003001054102c50030800400c405c45040800c041c010344084024003100c10b0113079889910080500286140c0011809010b05058103c0d451480000c0c0d081980302901c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 802624235 1250 802622985 802622999
    0xf060402160821070e0105130902030712060506040506030105011b060e0307050105090105040c030f030207180606020f0607120b060f16020a1d07030b030a0203100606021e1c1404 78
    0x182c07504120188038500f00d9000000c2c00d59100c40c046030300000240c042d00040c16558051005005000e0030319111511040c2c0f00d810400c101da01c1503d01102244103810f04640d641618010a03014050682c1e80740d0500786000701003003141c001030150505014510081c0c18148092a08000b451a0002024450588a20701864803503020001c241c8055080200285405c041401000d000c0e0340c0c802d41e0900c015240d40c031420000001c04000306c0450040400000706c100401140804221019000280c504d15115001e40340c04002c101035036040d049402001000364120b54010300c500720003040411240030340030000e03000c1e10a100e601d2180c08004215044080d4419101600440c402d4441c244081d071108200340354003d280900001d012040000a4000da1081d00401e16914001c1c0c1150031a1a15900203030408610030000001665a62020072400b9410840081d01c400400c03c1c548030240b09030026611904244845405041040700c06600e8078403e24221010010307240d400d544458948003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 802625485 1250 802624235 802624237
    0x20c0715180e060a05030c0a0902070c0e0c04090c030b0904061e140f011706040f0f05060406050a06050f0303040506030705070f0f0201120c1704110a0815090a03080f0604021608 78
    0x1502c03401194190303c007045c0b030f0070001849012840d0007010034a00a00e0501c030301000c0c0d4409141207807440184032001602102030140c0d00d004011030b40c0c0143c3c90b5402c049140e400c452035480c89404060400030354404070784030f031802c0942140d0803a40214010302d60381e2840b01e00f40e00f55840d07005070920308414034405071201c0c101103005503c0440d0824a41c0d0340da02c83c0b00850128114001e4080e008507001c9000140c40c600d420286502c9048810840066030b00c40d18100502140d007587d4007a20398042155243e024403030305026000c101c0d04d0115210098011903035072b000e14061640182c80002c0480c00c03d0f030050090f034614642c046189008404203251000380c102c0500800c03404580d4201a2204898a0340a001d071400080c1c1c0c2e40c5543c10601100d440040507020b0010703243c845102e05d40612503103c01007082d015050180040c020000e0250752404c9a560041103422550000000d031000a50301142c180d811001041b0398041544540c03001034000d00c140c01e9983d580703080781a1a0810482140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 802626735 1250 802625485 802625491
    0xa0c0f3204030c0803040b0f0315060417061006020d05250f031403040201080604051003021002010c0806060a0203270d031d0f030c0d05011107051c0201020c0715180e 73
    0x70000f4071402e94038a1119134a0085018501c00b12400348000808140c011020790b40c03100c2c0d00d25014400c03291013404900c40f50b000d038000c412100380305152010f41c0c800800400d508940e160001c800702c1858144000e40714001190307a5004c10600180c062000c0340c0c000c803900c40f00301d0802c890b10744007000d40c60024070702103440c0d0040b008139a41c149a107540b0031a890a507841030360103031904803c543d510800c1100600f4001c00c4160140102c07240400075807150000703c500c501d1030743c00014200600c440041c151030b40051555104803020044e0f40711407a40402030301e54042e082c041e0701c00368101145005000c5541d0180c0d45400600e1340c1258014194008441c2c41090030701d01172160b00448140c14080220044401607406d80d1211392503030401d00f0111075a01e500c9014800014107a80d01001220581e84455000d80320b030f6001840b14200b41340c18070680f090b07e83c11070000b10326210303000d20400e03100d4145100b031031610a40396414140c00e40c02104d0803c1041e599810185040d900c1d00c03060000b605041d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 802627985 1250 802626735 802626743
    0x40e07050123030604020901020a0b0103150b0a233c01050a200a0b0c090901080a05060109050414010e10050612071404020c0709050a050a0c0f320403 66
    0xa0700245540c8002c1c050820111484030700741e5407444c1e0361082803001944c00310321032034110321070501c084001c1050706070964041c51160201031000d40d800d0001c802605c042d011141d00c20307041d0302c008000e0101203009090a881a0b03000c0701c4500540c1800140d03100c0d9406241144850340035500a0014041448648610b07580f9010064550700b107200445a5000e59031562001c100c00070304501c03944030402001508846c400f0110750410f41c140d51002c4070342d00c058840c210180404100360840740b802c003007105c5c050a040d000400f801d10942e243d1603981d21061043d6030358903690700301050a000e09114100c400309040002402080031243c003295590182140c00840e00d4a001c001c10061303d04284a19400010100200855804c040003034009105880790b440d8040d07420421034440603070501c9014010040d1400008251818540001c00c1d22001894048154070300b4413000d0110303800120550041c100b07460120f180200482d0390b08040c0c400008017807140d50060321b40c42c00c0b0480c2d140042040d40c0c81 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 802629235 1250 802627985 802627997
    0xb0c0114100b1c1b0c120f1b020f090903030a050106050a23040302030a050d021006030f08180a0915120c150516060207140708120d0605040e070501 65
    0x5016914450303031207901802180440c204000e01e030a005002591402004504000806507003e88240111428000c85030010a21400481060000716102086c10710040c0c01e180e070321a00713400d0008080ca11442c20842c40c2403c840c06500c25500c910285000c518401352510425007040b041c039582d0381c3c0046400d4001942818004140c442c800c200355034004036035481d01c0d40d0a220300101701c46603500441d0820408172082c800003000da9401c000713212071580210060013002480d000024148400c80508140113030406c0c60030800105000c0e00003a88a4000941c142c440e000c4100703051501c12294209075020382c0e4000d0201e6040021b5100300c1449141108525481d542d48000079414120907038040d0180d02d0080c010030030a628003082114940c00c07454141d1904540226625201d1540107090343c003070781c0c049881410081d4004030960b1a0306c003d03005080da5880c1c034001c16030b02d030723000c40b6000c85505000c64500c1408403941c04c01e90213010300820600c0450301081119944150324417a25002a035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 802630485 1250 802629235 802629241
    0x130b120402040b031c05090d0b010e0f0108010203064b010f1119050a05070801020d0b030c0d030e0609041b080709030302071208041e03030e0f06120a02040b0c0114 72
    0x190005440c01700d25800d40310380c2444210081d00781c0f03194006040207600202031000c07480000d018800510301074442c0c100c4e1b01d921030a2580300c900594505030010450742c0e1041050000541c0c400d240580c0785035040b80d001d007080001c6c2d0812441e44600c0340f18040b0742c114855a104042a01e00c1c1c0340c0d40c85449c00c0c0d0303e10071103069070442100c3e0585803000c6209030b6045555240c1a08085210801c0f040340564110703404801da41c0e49044c5881066480b8180595000c200c44800c05011b0003010702046003100100400010080041d12035046240001d0a0043d4040301d50340d16283c80b4140d40d00070394000e004110b0020243e440c0d10f0440548201c030702c0014607845c002a101400740c9014020341740c2503030080010a0030700f0320301c82e45441e8035207085c0c50b841810320001660041c45980c010751006507200030f05846103103140c0949072025002e60030b44110341c004070304160ba85a00d01602c0034107581e94003a904548070444e10300020f2081d0f4000d40255840098160100179054120303180c085601c46c28681540e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 802631735 1250 802630485 802630489
    0x102010c0212030105060d020f0f031b04151112040308090f1c0f08070b13030e0306190b0a1703040e0105041503020d03090e01080f1506030a08130b120402040b 70
    0x1540b101c0c0c212034464003400140310310f08041d0082c1003000e0708210014a8812007601e400250307009409d01800d481000020402465610603070441041c142000240c203081c2000c540c40e4500d030f46000703007004010034481e0744680d5280800031a9404010300c202c1e196619201e04190100ea0f100122850060031b5814589181c0d080c8081d00d004140c0384068040c0d0815443d40d0392544a800040040d505c140d4103005c100c0101f401c4030741c081e006e00190f100b40f6102101a1030040d01d401c488924051003031300314104000d000760304080fa0301c072695801000022403200a0000401c8107026400020009d010008081c0f488040000100160340d160300314010140e984404002c144d400108900861a0300001c0400060900910030710712076219040240e0085d460b5201119044d10036030100d0b4040d84141910b0320710003000d0100e1400d2040301d010502492a000010940d1410104001040e5401c0000d43c41e034280600031024020f4465540490f0741c91252036090410000d0654050b445589080a00403081c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 802632985 1250 802631735 802631743
    0x1b030506061005070209040c03021c060e0f1e030d05150120100504080d0504082a0a020d0c241706090c030a06270b010903080313080c03070309050102010c02 69
    0x740020f650705031034480b039076090000f50319024004550480f01c8150100041e41c035200040700c03018a007403245803001c1c92070400030140c030304455aa0040b0f0300104908a0361400225010307806010b400f004950b5029a51811031542c0f03d0002604440c03407402050254206120042e1298001e099903400f80ca42401d520205542e52030803407801540c1e000000024035000560050366000d03016103041c1c0d0800b03840f0442d8106440c001c03178046901810000d15041d100c4070304294200301218951810072400700700e051460b85e8404000c0060300c0750701070ec502c0c042009070441008003d06030310040604c002c0c807140c0c541410100c20f00d0040002c248050416100c200c045101584500c10003000e51106e40c803100009a00780d070001d0000c105403074407501d0120b544e008007a41c3c810004040701800d020459003a440800700d41c075010420381007142100703040010803044400d582d049804a00403114802c01c900d4a41854030804a80d55501c3c0804101c00c01070680040120040794420303002030045500d1110100c0e11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 802634235 1250 802632985 802633009
    0x120606030f0103030305060109050d030e10140403060e1c090302010f050304050c040c0e03010207080310080d02062d01080607080108010513140c06040f08100618181b03050606 77
    0x214641d084010408644240c100d10380016040c142071031056164000b0a200b8007070070400703401082e246c000c4034005003030048a4102c1d90000c6e1801e1610a0503a4081100c14451071201074280c41d111040042002d03010700801c80420940c58141d44407048119000d81140901c0c4003d030b012485101044092a000d00101c0e445240c0c004081c1940c3d0707008400300b100904416103500108200140544042e880900c004d210040c0110f03500c0f92030f0b19105521810100050300b00c0001c40e0861808484110b40000e08950854100240480350303200808584d035188900500b0b80000404403000041e20040202d41d480c050500b075070f102076107680c0b01c80d280c500303a440070703100c1c1d640d241c441201c144c002c1941410342801c0010010141c3e1000759100c40015420341090f0000000c00e12011010018805d0070012640c0d4608031300d0781448601d1a1000400700c000c0035000300c03404503869503400045c000b20302802e148000e500c465403d00324140c1004c40f60f18200c2e5400201c1e01c03171040c3d0b03011404600e48a000f05171 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 802635485 1250 802634235 802634251
    0x60705060f1f030b041511041410021203070e0a0e1503010507082d0a230402030604030324080610060e06031b0c0109050309100509211509010212060603 67
    0x180c29141d96a580810742d4010015162403001b4030003048110b1450040c3c481d0401403141090b21507040095200c00b540600203110720886002c03484d04a001d030040303040d8585070022042c3c0c6851b075442040640e00070300408400caa000320b440754080f0751060b0702042c0b24040d06903c11580c002e5150b403c1072508070b41c0280d80c103034045900e0500040c2d219008800d06204002010b04d5507188038490300c142c0050a400740c0c1c2c20742140761952088c030b41540b524049480c1c20ba0154880e40740d24102038000c651503480c041c001030105512940300350300d040800c10381703c07100155000139800840e80c3d81c01d80540310081610340c0c0c2d280d00c8030071200140051003460700c80440302e0010720075480e40e10b80081c064140780465800c00c54445007403141000d40300081c450203040c1c2e402080510b40d690150300402000ca0040810a01804000d0011a010780c40707840010003030a9102181c41d0454030030100c0c1c90320f00340032a04018440419501080580481034003d4101407041c00f112003426215001007100c0d0b0300086581003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 802636735 1250 802635485 802635541
    0xd0b04051504050c070203010e070e07021b0f2b060501080d1706040603050a080c1e06160e03030a090f120201021002090a0e090d0f05040f030b09010b060705060f 71
    0xc1e07491416a1009410141030950285030802d660302280c251041c55110a02d96040207400b0040500059045540140c462000c1c0040100300b0100c01c00030340c41c84514034003900d803419405009481d0910303904515403003505074500a00001c10100b0030300c106e8003000c590890600c2d00014050710000361b0b100b0058103503107c112640e42d2801c140c604114000b0031596009464400020100b001817240c0700905008800c000d9864603030030383c400d10b00410514250b0b00b0f45600b82c01c20310340d00740125a850308003100c0b40307141c080190b5103101140c880c600c0d40d641c2036040c000000c0540d88039820030184002c0300c01d0340c82c0141110f43c1d03c80d4615101441c0c40c1c4080c0c05a080fa00880c0d8800342264020300b0a1b81c070003441c0380c00040e203e9000200806080f261030700d065203c5000e0340e00325504180c21444040c551300d8011720782408c0c140e40b604900d00303502c00104405500008101c030ba02c42900101128540036108984807421420141d950704029540c5485510403180410755081b04007000c0e001990040c8503803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 802637985 1250 802636735 802636771
    0x307050a0807092a020f151e06030f0d020a060b0415120f05071508090f120a02030c240f0708060d05010207060e0102090414010f03170409020408030d0b0405 69
    0xc02c050a86030492041d2484112407a40219813807012480050b142e541c001d01d5503000c1950185e2415000182c0107040000c81030800107458801d080300107040341007a19110b035031f4481c20080f80c6043c803a0920001030b400340e0819800c1960b40080d4101003640204418070128803001d062004481100b90b654a405019001c2485081c00c2e81c402218164440e810040800031030303841c3c0b00e0034894039800484240c00080c10321a40759500c040030b2604588050003400010030841d0616943e01d0f4481c1c48250500400b207208600140244203880391124507901313130340000707940f101160014180f4000c017904a61100340810911450b01001601c5503296454001c416210700d02009904959410100da81d59002c200c2c1c1c1e40010454081e41012551a10000d0f8036510303010100026520036542040b0824a504010845210040440f104482d00060825003400d82d610249120340700c5c6402c1042c10500000c3e00040190000000701400008060100b001360700010800094480596181100c60032000e88 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 802639235 1250 802637985 802637999
    0x105041209090e2812030f0e010507081b25060617030d1a102c010203120402011103030f07030c090302010e010e01032d060909020d2402070602090307050a0807 70
    0x202c8001e80902181c18058030117503181c40404406405110000e52925007410101c20700380501d280d0352004200030f014628040710024000c0c0e0005002e035003004554146084503002e032008946003c1142c4d014821180b151190701c5c10b494010f9030086a001d0f14003880090505900c60203600c8044219001e036250a45443d17152020380341c03e01040c04510000300c08204a41c1d512013a04e100e8440325210700b21059901e0300e141c481f0760300c00e100804c8c100106190b441300e50385e404401c8440c00014001c88140b503032150b000407107400304880400c0540344400024404201480a00d861080361269005c1c4141c4e099610222280189440000c2c040703004050361038450744c0940031640b50908107240000b12011604400c4ea2031114010b07409a2443c1d01c04590b102250b060b000700400b03010f254400303000e540b00550214540c2e031b4403a0406040b2550301e6950100b111540400045298401d010640d150012414140000d60001184611a2190711400141030a29901718401c0340d0410014191103890148 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 802640485 1250 802639235 802639273
    0x12070510120f06060305270c0904050712140d180501031a090c0403060501150c0b0901020706020a20060c032802040b21010e070c0203030c0105041209090e 68
    0x30350300039403502d81c80c80058280c09807180c00010000e0340c4c0c000c505400c1414618264034160494052209030405910400341d00001d540c13522500c00380d50042455440741001c50070218160000c02c010592265036200b480f14a0316030031003420b0288140c5c0c815202d80c0005542c8040308803441c40203030120010402c4a907000750311850000c1402041d048401d10b01c080011010a0110380c00d40441001180a0052248030b20405002d8a031000359035030b01000820016185444205000708102c540c680040d2060758223406407403031164010001d644038220042d02800e4040c142e404541515174258800d082000000b81c80b07400345500c10099407458840038a01c81300c0707403040d080705940701c1c0030041545540b29561000b08010002c107110140c59284c2d07a00031a00c1c0d611052441c21582d40084c00510008100c15020307038100941c0c0c00c0c100851091440800d0540c0030b1855604500c0d4645800c0005002c3c00160030020200580c0c0c403100025102d0041c40e003211882113914010354044100e000d005100b0031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 802641735 1250 802640485 802640507
    0x3309160908010b0a15020a0f2114160305040f03031709150c03070c0804180606020d050f03040c1d0129160c0f06031b0c021806040b03031812070510 65
    0x2c41030b68454443c60300c80d02030000c82020110b50040d641034408041d072600c04a04e469a8170a4030b4104000078407802b110845001d00410011019403800c42101010301440c2142d004100078126059034179030f241009040084406125121504094000382c824900814003150082d04826210415242d4400c07449081c5c01c003c10450510014543d614086950200500010082c034900e5080341c425041d0b02d58140c400701d40c0032805560041400c1c0600e141c0040aa03401101c014000035165034407420506030803169030380200c40800c0b03900c40e40c001c650b092090140c16180240d4054165034014082108040605195941d40400034051000c0d6440c001c800303038444030300034a4a1017050340c5a00c80030200e102280c0c44880440e0ba00c082c03017030840e82c60f081c1c10345411015042491703130404641c02060012180c4040c559010040a002072102e90b1070350720010356120041c0842e6280c1d0300031960711001c00c0f5804422071044e00070f03080d26808a5000589801503d00c040c2c020a0001d00070314040d13846004034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 802642985 1250 802641735 802641737
    0x70302030411090c070f1b03060b040c020606100f09090203040609050f0d05070f081213030f0f08010915080f0c0301050c071101050d0b0d0c14093309160908010b0a15 73
    0x14074500d0041081f04540304040c1d0b006600000d042440c81040000301c40c0344842c0401550400d00401406030f0300c0380d21000040380c1d01c0c1425104101032400480700e404240d003120043c40e1012003800140151039102007a554030a604695a00c1ba03201c41042e910301214000d10001170013000300800007880103a580d074078607100704415420310350260000010302800315629400610b584c400182415444554143e9440345810281050700102d40003c01b2034a05016680401c2d480e06d40078101d48130000a0030f4028491003007070f5200d100c440d5881c1502c501c01c0c0c10000b4400e43c240030104084083c5102102c1e0b40c1680702c4c5000003211410001911240c10005111440e40d41d100340524058a481000701c0230303075100301c0d080078a1a00b01540c107080140f00d05612030040c009001080741c545409103150b180007038605c905100c00042c01c0594421402181400ca0f08461048280319941c41e01c0440c0c02d41d1286c01d0b8031a080e800342c581d80c85900b210348640d01150300420301e09041207140c0c01540050050701003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 802644235 1250 802642985 802643003
    0x4031823010c0c060e15043212070f05090c0406031e09050303060108150d020f060412060614120a0308180102031501020d030b0d0b0618070302030411090c070f 70
    0x42c40e11190702e8000c480d0300c00341c040390030088a41d0702450006400d58211401010702400c0c10705003a950384040c2140d54840d41c03007803c41180010100700c0400d1002d60448020103076100d006422116035100d4881e441501002881c824001c141850011505071041d1b0036010000c0c1050314000f41200540046034084150340707180c1c1c0300d104004889020702c8441c2d1b03005034001e603030b00d06100b0001400020300521444c819000c5440e009180d544240d01740e00b5031501200c2038128807103100d000494911075a48410f02a070300211024003040090340002e0201d44d8110304900d00380102a041c000200d140c20694080d5420041c161030009002e0b5100a4001103440310301c48482c5844849a801c80c1e1044c0c1e040c045400c0c1081a905040d070341000038a0101000d440d043c09810f03200301c080741c06c000ea1041c0c0103100300706a2000880f02d881c2d80010042802e0124192101030610140c0600294400c1d0f0303043d40e12080031401c1402c207007007900301c081c0161f0348502c4039880d12401e03480700c000f01c1d0160202260302c459 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 802645485 1250 802644235 802644257
    0x140a1e0b0d021005120c0c240604050403030204090c0206060f0102060112030503071206060309050c1504060e062a0c0105070c0b09040e160617010b0a08090f01140403182301 76
    0x24500c142e0300e12404042c407171030390740b4110304007d40e01d403c8082c42d41c140f0b40c81541c0d800c400e004a0032917945030040c0c030983d008076403900c6500d000e801174016038002e4060300d80f030106250b441e264000360307030b81c01020180c801c6045001d0750401262180303400d00424024a0a0101030350010344164002c5503c20364624180d44152000030304881551455030160b400170b5219407850302408028042c401c0705000031a10204240d8000303000d1191401648540803e01400400d6860252942001c13108007444924642e6030548001c3d110b115030b0b000440580419125444241c01154024030031a20350399004001060b0180c03410400c903040b644907004181d0801d48a20391048219000c021864140684903041c400b003904280d40103204030654459124504213a9004211198026049584827070b024500b500640c0e4810002c146451884010006550721b81b986050b4215180507055009500c00da0303a540c08001d802c800042101094082c58800c2121890361264880c1c94809018481c04181001c3d82501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 802646735 1250 802645485 802645507
    0xc050417121c1e02030f0f04020307090b0f0901090219030903020312180d050d0b04020f0f070219030f20100809071a090f0907080601030906140a1e0b0d021005 70
    0xf11007100804003160f0040180409603d80000d0300b40d12212240c40c10b05c441c986500040d550b040390b0b10840300320a680b8071030b5980c075448034a8811100e0501400594403541d413000302e90001d41c445040c0e0200e1030824103808003030342c1c46402103188841d003507802507003408020320055511103000ba1003200c2c0040c0501c4e00121641c0c1c18071070344807007840b0790304c0d0325844000000155003618801c12401c8e11036403042107203000c04009901910f0340200380000c6580c903420144041f8146185000d010080d0441461000003040410104000c10502c240008515250448011740d0304101426450341d0090340b80d10345010140c401c158140c1d01800360011640c4ae25668043c0341070800c0e603440d0300c8110302c4001562045070300304840b00d06070f035020540d40300c03400c2d2a00020082c07144e500500541e0401d030702c40040d4424000280c110003c2e210081c48450154200030028100402c24501018089140415194504080b51090078824070015040e400c2501e00c507130070041588212011001030000500c0542100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 802647985 1250 802646735 802646771
    0x402090117090709060b0909010e070203130305030d06050d02060d050c0d060320090403020709020a05070c23040b0d03030b27072c01031d010c050417121c 68
    0xb4000c000141500d14103240c101c000b5661560004021040104140c480c29240e4441990440c0d8a1803464451500d030060124110704c5000401d07011815029008030600402000819030b0501e452800c00c074a982e00d0301805030005400d00041d610001c103011000644059401481d4060101020207280c405000020011280c0c140c00c103a541000140280100e07501c040d880030514901182c0c2101a03203025070b002580e4032514050600095004906080c0c0c040c01242a101b0b0317907a12450220000348c6500a0740007101c8100207114110750500a0800c850400348a40700c1d00143c0030740481c1003910582c80a802400d88408500d40024681c010705c0b540c40d12030f404000340111f40f035070600c03010304008000800103e82002c03011088172490307100000c0500d154590800401082c00d000c15045c405600003104c0880c03840f180502c0c1c1d42041c0983c003c0580c80f00040c01a1158034140700280c0e1140c0305603503603624020340ba000c40c4a0003000104071700f90030840075084004201c02e010500a80c181d40700404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 802649235 1250 802647985 802647991
    0x603080d0f0e010b0904140a080d0c081006021c050c160e090c0d120c050d020120040b070305030c16151b02060f07050409060b07020406060516020402090117 69
    0xd500d5403840c242540614a000704008000720400a01c00c1820031400100c0c82a030182c4010034071242404044001c080500440c910700c1d40140b0070729190034a9140010141c807084817540c00140741500090066101401c0b4901a0f41c00c6034010080c0340c0e0201104100701000803510300c00c0c0b180034000ba00240b40200520019407030b26800b410100c0745081002152403102400404107600400d001c0e4500d51203045400c224240c1113803101c0c107040c4420500b912482c20000e0060b056014180c0c40014280c0c054000b1201d8014107419005000520000102039000d0f50045060f400810008500864841c0b0003541c0c2001c100010549003052000c0000d420110b001c03c2255141c800c2100c0d812059034511031651030f032401500b105c031940a0038100070f480d000b00a080075403454031600440d04140c07241d400d07240946141c0000704406616503092520f981c01c1040201e1040c1c0c1031060200d02c0c24428000d80d1042c2a103054444800903890b400c01002e0b4100984141c1001007551140d07000606007e58640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 802650485 1250 802649235 802649257
    0xa06020a05100b152701390b042004060e0c0c030c06150901152c0301090809030111040e0103060b150a081005030615270709170703110405060103060308 67
    0x44041960004640c01d0f00410180e2414405d003088a0110700e2943e00528042503c580324951f10221b29013000301c83e4203180800034140755500ea007080104500800908104508041907907940400780041001b80e40c600e0148042410f10f00011900542c0034401401046a485081c0c4e82003060f0828600d142075422903030b074039071600d000f10307800303000d090018205001d09800c202c0f807500b0300c00810001d061200000c8580c2066200c840c1d40780040c1008001d40d001f00c007001002032061040505003804950009504140300e94070b0064007440040e17810040b241240d414015541d05686180c561900520000032030a80041c400e1081200a040078001049c481c100c03603c0c2d02c0018100b000402c070024105401450080e0321000500103100382003140621800d40032102c0b07140291303020750890000c0d6113070748180c8800304040040c010440e80104403501035466074032a2202c8a81801c95440d624a0288005082c1c0064070659460909040c0c0045920683c1810041025552540c1d82c008980c0007403c203071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 802651735 1250 802650485 802650517
    0x230f130c080114010309020604030b07030b060f12090f06070c060e010507030c120c1202090f031c0210090b010b071e0303020c10090206090d0f0f060b0a06020a05100b15 74
    0x30001d020080b00c000f842c404203107000c1140c5400f603804940c0d0ba200342c2c0000340a02452800094205d44246c00454032003202410954440e14160421242c903081110528504007900000130100000003078420360603100709000b00030702d854040099030703003c4004009407501c80e1500c0d100c245941d000d0103070f140141459600090a10000c060040000681c1041c031955207003460007081085a02c0401044820704001c0010313030b500c1940000540300b00c0003030180c80d094061450f1002048200100d1441c40405503020b80d100600c40320141c81c01c64600d18401004240c035034005202c131850890180c420503101e403482e10a94107480710001030492901c01e04400003600060003441c03c030410301161902082450090010211560009046009072000103000300b14031541407050100500c10038029a8204410144501c09030030004082c0c2080b283c0b440c028184000d0000b4241d01c0094419512030b0407070b002d850820441410706000d02039000003d507100600754030310402d10762414000e00c0e0f0000e51010407 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 802652985 1250 802651735 802651739
    0x18350c0c0a06021c0e010203040305060408090405011a0a0302090a05092511031b0a2406050a0e040f02011404080f010b0316090905120c16230f130c0801 67
    0x2603640140d08000b04541190345241462804034103100003805950a040e041e00d00c101c0700413803441c001d0f54030242080c4242c030300303000601500a000741201c000989040c40710360b8a880c0c02c20041d20081417250f0303640d4010443c2002c040d200368090010b0110040407001513565039000105550030540d880032034140b0000d01884150000640404a829075080405d10170f164044240d03164061061980700311550904180e0900e2000c2c05200ba0b003590110a5100c074000d014403254250342400100440c02c0d140460120781031071300d032400b0303011206500c4441e4120b641d550f0340d000c0d21b1260820200d040c051080310304d60340c1c01c54460151004d0188175004000e00d1851712001401d4440c4003e5050090f0000e003504114807641c02201419a803103a03030085104516841c00c14506030340881c000345071480118601036120804500e00c14404000c0d44031030440f580b209622607000d030310360016640030400c1108528660400f0010b441030000300502186a41801b0b020030303c1034440c540441e00000c0c07040401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 802654235 1250 802652985 802652989
    0x2040e010620161802071406010f0504060e060d0f060c050c070f030f0f14160e10060806210a0b0403020601060e03030f090f150306010318350c0c 64
    0x90180b0b035024410040088112036282c000140d24035001c0c20f201e9001c1007403910407050094040320f4600c0e03480180201782e81c41d401e95160300c03110f00f8000d0440800f02007200080503d00b90007001d096807100300140943b070302e0f02d10402510b100542d508440c0345d42540e40080c042101481461002c050720f44030181e03501d40002d84c2c14104007058026182d051104802480070800d128602220705a114010840d5000181482c403404000303003807541c0403071061a54450780442c03207480380d0b41100e002c508481c1131078541c40c1c03032800700c400103000750230004902200280c00c80c503180001d0440c00404c1c0756440c5443c0040e46000d810030440c031009803800110707281400205a41006071500410b05440d0080d1111400c0000a44074032a0390713181451b00d00041200b414907a91280000310041000b400b1f50421031103c0411145500212241070201c1d00e881d440300100c40c044400789400b580e010380003902c072005455107a5070b0191940440c411008032100f041a03507403900001004c465941d00d005211502511007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 802655485 1250 802654235 802654277
    0x813050a020a03030e3309010c0506011203030501091e0c18030602030103140a2001031107060e0118020a0306090305040b0c0606040516170402060c1b03010513020109120602040e0106 80
    0x540312101608013010388000d842103003ca500404800101287c1e00c2c91082c004031010551450042d050780203e100000c0c0208a040341940482d11a440902940c1c1e030300c1c080d200480390104d05030900f42855442c005822011540300300c00c01402400d00d070003103910041c030301c010b900c3d00e94004035a003da00000500501445451040a414800008008480c0c40390707503400740c0340e094140030341c00da18659466034117a0b03020390032504c20580c802c6c4440340c03125103a040c003002801007800451803030f501e40070300c1400300c14082d040380340c410343c0103130800c483c1d0380c6140d40300c00080202e00d000f40c0404c541448049800e920b85002401107101490003081d650400b0400c11044030340c0030f806d815101d14100c0e1540324486c0c000038180c100740d49803405a190f990712070010844510543c1c0007031420340a5802480b6125031141340309140600140d00070451a515a640044400600d03040a0301003000080200001d00c00402842c94952088030050700302541c8201700300d07941c4400c3c0c001e24082002c0754195101009915 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 802656735 1250 802655485 802655509
    0xd020f04090b04110a110106030b070816031a13020d05090304150c0c12050c03030d09110906031e0a050318042d0e0f03070f030807020601060813050a020a03030e 71
    0x88080102c07139900744980c41640b2410000c070041c0b201448103100d03040820741c000e0002707503000922004207160a0200410305002198040e022111105002407024800c2c030490b02c40070007500500c42c1c900780f40350802c07080d030005020f01e2a0302c0740c0801c680d0040841e28040c4602410b0b1100c011603c1364140050103d104544a4040c01040390b40500c14010419222507401214072908546400b01c801341000c80c1843c02038206030360184000141e50690b02080d0380420280c034000c40b40920092400380802101c00c41c1920941d034580e02c0000034840c082103803000041104800310403103450400c00c2d034499055030490280b281301407070100b4544809040c240114904800c8684c00400300500072400040f04442c2d00d509003032956a1a40c501040d03890800440091413186c0080760707192500380c5050106004c40c0c1d0340c110005040c840c04141c4082c000107455050320307410f84400c50b1a43d100020100d075010540d900f40e90a01c03e83c0000d002503100e268054010f0b50003030380c5d401c1190b407500f01807040c00b50b00340f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 802657985 1250 802656735 802656739
    0xc0c03170909070314060103092f10020a0803180f16060f0206040f06020c0a0c03050106320904021503270703030c1214041409060d0b15060d020f04090b 67
    0x807511481c1c2d5905500005c3c0c1d13000c0024200001c503100a401d190b68240c2483c1d41c0301c43c82440c8908000017401101080b2480c403d4212150404245041e208903101c1c1c1081d84018848207084c0040340982e0211450100040c51040c2216003000c19182140e18101500140740326031b200003441405019400f00110710481400e00041c4428141540c50400d1356442c1c203009444c181d4041074482c40a031003400030300d12464124010108a41d00c03070074824001d100c41e11400140240e400581c801d400803402e038801da411195074110840030b80c010140030011400070030032039014400c0c00c5070107070314010000511b0144540f04512142600032901180d250068000c1c0c03500607501140c1e04200003540b0a50141c0010340c4100c58140c40d6600d80c2d07041e03d0522940040807400500801d010403100b07828664402e0700c28040710201c141d41c56010038070001d0099440050f000c003000c80001040000f42089030340e06c501c0c0c041c020614112000505c0c030708030313001030304404454040003030704100410550288440b16401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 802659235 1250 802657985 802657991
    0x20705070603060506030a05100b0c0c120a0c03120e0402192d05090f0301061502070b030f180a0804090b03070906060509011d0d030807081311010c0c031709090703 72
    0x10300300005c9107404000c1603c0e4100d43c80e80d00003195444103d0402000b011660390791a100c2e00005d14190302d035200460042d0286084540c1002c01c00000511070a60300d030090030901e011130460f195017003c03491041d242e00600c8400341007083c00381c5451008080c5008c1c0c0810740d032600c04021a00420700c0c4640078450340a10843e0360f502c80c110300e94160440400350203060481c1d030f030400e81d4041242e01c50341c280115459440c25100185000c8101c2d015070b1410720590139540a0354440c040140e11313000a60b00000b421100a000801180382d841c40c961500001800b100c02c0e0030319680c0c3e002501e6200b500200034242c2c0301e0b0714000c910b080c00c01180000c0d1081ea0400d01510b0b08118006141c0c3c0900030050b030410916149414601c5403940305200104005881c00e0110100b0f030a024000c0341043e200303100007030f80301000286880d200c0014051215030041c01c410307a81100900446a2200300c8005848030194003400200151010740b8880e00b200e0007008a03515044150300f0407010540c028005400c1c982 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 802660485 1250 802659235 802659239
    0x30902040b0103140a0c0306050a08070f0611070b0c10090804060908060f041b030b040c06080a090b190e19050f0a050616110d0305090106140904110f031002070507060306 75
    0x840509280d000344000d20000c3c500d507180b0021006400281c9c080c1c0c0c0c016126680100308003001059100948a03109070700c030b8410366696000c40e00e48210051588040e000414140806114a0010440f110008084a8085214401749411a60321240444400c5000501001030b590030025280003400c082c0054285480d00300280d0b514030600400042099805401080700c00502031400000795400203008030703075444c0900e026605542c0707a004010104901c80001a1515454000c01203170952184044031180c070380c907040343c0c03130074090351803480580f912031200c015144402c200c103480e41c00b00d100102c012007403103081460804611064101c0c50fa000b00502c080882c8000610941041030901e0500c2401514041214401e43d090340280c20340c0a030700d2601410980c140c0195020394141c0c802048001d80e103658007525400d0070b00c1e80c03581007641900008c01080c8118032200c50714078007900e02c4820702090030029007400802c042c03517010298080303240f405000c401c00030f800181c181030404000142c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 802661735 1250 802660485 802660511
    0x2010e03070b0f181203060f0a05031f18030306090605040b060f1608040e0609061002101116052b080c0c0a020a060e150405010906230307030902040b0103 68
    0x1002449030a0720a640c0d0003044083c0390a03540302101d00c04c8202641c04040301400c0d5514640e10030707251035105e10a42841e0340c2140c5403d0b0b14a01c2183d6000700180483c50781d580003926031142184950009a59884410045c00c05491000e200c0c14489e9800095260510703000c00e08481241e040140142c0c904040c001c06510ba00d001c403800c100c000918142c0b51303858164400c66030079503c0c20040c400d21020500141e196220030540d8050340d82200c02507680e645140c140010b505440d000d9500580c8030390150b100b00103450b03019010807030100300118589040d40908030b50b22800010220350b10f5004001c0a00c4200800004d103c140c01e05809011813683c2050009040c41d01c00f8150304890b010004014035040c42c10030102840a074007501603182140d0f16180a8000c01c0548840346c00395201c03100402c0c0b001250402c540503503005031141442c01e81409400c40fa1a0800e52081c2e065107400001c844040e0107c402851017028160340102d00c0c9805841440300395525000d403681407500b00442c6041c0d00d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 802662985 1250 802661735 802661753
    0x30c010e01050417070c091517010b13090f0c03030809070b0f0703050306180f06030d020a0c0e07090e0c03070f0c0c18020f12041103070b03060d1104180302010e0307 73
    0x201e034031340901a212403682c10501c690110329400203001c140382c2403800c031084030381940400c101c2c0c0c1320321002c0640d4071001f11100d003a5040300000e1a4007505050174481410402d074400c0500354090402c0c3c03140e03200340d540c0f10310300c0e042660019400314500c1000c20110081c10888000502003184240341031203c1b690550700c03140511880202846804000600940c44800324481c0102088510000f00d061030540100072480c10b0382c80c24082d004032030002203100c0c00010004400e603404032404590300d103031036801742c54050050100340c200010004000303040c0c20350072400c2c0c2c0140e20740361080c0c0d968182150046c02c005003481145091110029003400403d480400c8034049070040074040504a107100a020f009120f5034400090302c6401003070280306800c80c1e8a046128520a00d5800004d0307105c241050741c0d4030b5040c883c1803a440000c00000315641002055844030921030350105d01c031000f6643c00101030301c0d4210030009043e008104040c00781513090007101031201d11070b0003071351030020181c8404c010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 802664235 1250 802662985 802663013
    0x602030a1506050a09180b030a1407091406040f0e0f0601050a0501080c120712060b040302040e0f120702030115080c010930080903250e06060a030b0109080f030c010e010504 76
    0x150303110106c03204000403203410034076903d5402010b91714208480e281c890141c60281c110240c4074811000d0209003c9030a1240240900c5018840800d41c2e503601c2c100006020703164039040c03819403149960441c0300d601b000010741c02070740c290142000398100001c0c03205118036503000d181048000300500c400c00b02c4100c210382c1542c68124400c3c0c6542d81c3c3c0a0252442c45108003a501c070149041c40c001007541001d800789c403c3e680700300c8083c800c04085001241e950306a604882589800450805901800707200c024003030184090004101181c0f00102d4490404c002d40c0001105d80001c1c02c00311156900030350300c41c0505243d1a04071601c11f1802d080d01d8201402d800d02400e4051042c00c13100a02c2040030688688881c0201199a00d00c0f2400700b00721003140d03200240f00b1800038200e01240300c20f01c0200061050002800b0b00b0306204103890200c000d0580301d290941808002000803030221403d04c40e554280c210700008582e1100540c08c264211898502d82150303d2740b400d0240302c005450314842c4a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 802665485 1250 802664235 802664249
    0x9050901180201081f140f0411090120010c0903050c0103200f0f040b0a12020a020d21090308091b06040302060a11030706140a0b0d06180602030a1506050a09 69
    0x1116907030301549461042d400812000c03040c1c03103414001401540741c00c15401b542800c0c0c550b05010800340b000d000030707246a042002c0350b001c2c041c07020020551151f2031510304110a085002810581c5041c198210340700305800000068074100e080c0144141040400c0b01d4078028a004c20410000c60304840c4c41c0c00000010075070009002400c0e07003180701c20f20103441800450803e2155626601c100f0342c2140e40c4858185008600390404940d826180c0d4401c1e0703100300b01d66401034805988220800c07140748588602e100041030b108086030b199a40c0c1442580b0720300b4401d40300c2050300d0800f1006903241c1051218441c0c01613130303a60800b40594a402062350b0403039030b040c1c0d5400d8464021000940308250043e1581000f44004a121360a000f001e422901c00034041030314440d140d03281c0304980000d464200d80ca05410030f5003000b4240008010b03a00c0201a90050100c180c40d0292666030340040ea8825117000707042c02e450b809102c0c0307440c11352150b400044c4020700340245488264a00030340071924900c2400303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 802666735 1250 802665485 802665497
    0x501050d12030506040e03180a0605031009050a0e100b040501050303090312090319030c060606052703010b1503040203070f1203030f110309030c010b0108070905120a0c0305030409050901180201 85
    0x100313951541e800800400ca020410340e600c0e83c6480c21024075210b0750040c00c40c03145000c0300c0000740d002e001f00c084900074402403da002e40c0a04101d0707610302808000d010340f4804d6540e41100740001c6410310000010082c1c000c004241d000d003e10801080d204181c002c588660420003480100c3d5500052003c1520703272402000d03403150000c0000a052054402207143e0340030401c0000c2081503444103060712024480c600401c2070301e46442d8111814000c8800003100342804613100301702a404003440d003014000c0203001040081c2454081511001d414120f01d4680300044184800c6190500403100544510302010060078a06040c030201703814040c00103020f2503610f00c074400e1130103026001409038203148609550707207050a014040c0d0303036403000944038520752070000014941d41c406e8429a009074071a079103a40305281000c040012490611141007000d00c191691000080d00e80721112000b1801100030390b86035494082c45c48161180149940180e900d0402500f454500d00d42044100c29028a010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 802667985 1250 802666735 802666741
    0x405060406030209160f030218010813050129031209060f040b07080306010314010e2d130302100c1e0c050f03130f03050601171f0501090501050d120305 67
    0x1240003404035402c081c0d00301c05100c0400131804103000301824105000d946804890400000171000c90141c1e001c2c40726802540f1007101100d612070346005800600d11700015610604a55495086a00c8032418000301c40ca1142e4070440314986030242604d02800742d0240825450a41003604c20b4423442140c1e5210341c40c049148403890250070141c5024290b5181072a50fa07003480c5c1841086500220345c450b000034200500b0540010203004400d0488500c5005202d05849007d10f0395401e10072200c840c000c1d4079581c04440c644010f24048a4003420342c0005440d00c0c0c9802c3c0c14028100b900c0f80c010a814142424803c41090758002000c03034400805c0551002d401070740d01c20884000b0704028018160b131040d03041d1400c80c0200480100201c5480701d81085209585400000114849100141154014000400c103c18042c0044e0205140d41019180d101901040562014041c80c01010b511903691005110000c81751103914013418084034440c0f030400c03603940e9115410302d42044103c01c00d0385030404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 802669235 1250 802667985 802667989
    0x30c06130f08040807050a12111002010f1b140309032a010f0e0607111203090118030207060806120d030c020709021204051908041505040302040c11101a040506 70
    0x2003801e240b588015034940c1c6580d83e14026648213194040c591040800e03102c00244503450009584100d54012840e11310180210708004083c0c800000c07401c107654039240390041c0404644204080110440c50400201d400c00200402d4400800d07203000d4a0b88003007041c401e500c00000240c0e505084010302050300b075440c14441c9101d440000c0b4010381d8a6083c448145c540c12004c0c2c110012031a0703070408a41440e503c582003200c004420307035585942031f0020039040025006a900850340144004004030741700d410755090a1001038100000d07001038100c2c85046c041c580d40811403079080701d81181d64241c801c0c40501041c1d20740c20b8000340c000c24941c6e110503240646000b40000d000030038954400715211110010040d08024007142d0440d00d601620301243c0200b141c1054120b40907030032004a90516040209840c142540043c0080c1800000c1c0000030050b03646010f400d5111205603507500c02ca50803003503141d14120200500c400c00d142400f040300ca8082038603000d062184001c540201d01c40d165400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 802670485 1250 802669235 802669253
    0x703080409140112260c0a050d090b09151b100b03240403090b0a050c0f0d0801030b0901023f0403053705070b18030403020103020a17090d020708030c0613 68
    0x1140091100000c1b0f00d1030141000880c0020070203005400380e0341d403540c0c0a6422280c1c1ca6442c0510705c81c80005100244440c100301881c01d1140070207034112031901007038402c613082038050005040340f190b0110b00001c0d07144070140149a9100403d800070301092148402d141001c03e40c484020b840c0f02c01c040700040a040c8140540360007070006214080d524058044001c11640c03060b0104a4184a2010390310381c150390028000c51405c6096580030002e90a5035603ca0034101d02400b8921a59002d02032080c1c0c200d20300014036012410401d0403119804141e412030b0319001f05150002031103071540200001b082d0401c080b240b019010000030071500907003104042070410240c1e400d201d811900c0780700d0040c0b00e42050003801280e0049000040d1950b400301c1d200900142d0003042c4050f81c1041c8401c200550090f000303010400d40b181072044042148003820301030342d0302c111468051548850341820016405105d6003014100d00b40165240c8820810881d940b01009031150740c1207a03241000b881440001c107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 802671735 1250 802670485 802670543
    0x509010314040b1e091905070b0d0f0e0a0203151e010b120f010b04030b070e09040606051201090c1502120f0a0306140306160509030703080409140112 66
    0x241c0d04044070305180c03c068401620031905401840c1344d1400c5890411500008284185c844c04010404d540c0c0c440400345042150800c1218580f180c10400b14003a144032001d0a1110304280001807110048010380054035a0b900211040c1d82180d9051030150301c02087c0310b50712000e4506a00002c0d110112200b0381664806121401803107034070004030742980404024402402e001c0071960035904c581841d186031100a01c00c54010a901300402c10020300c00316002d59100c480703130070301040d603c072041c02290710600e0443c0d045400b182c1d40c040078040d030300e813400742c0c035841c044000c5c000c01c500407050382c51310002207507802071241c03c90036a5503280310340e0f10030441140e410000c103d409880b0801c2d40303a001e0b801d400050441c00880d0a16101007000401016500d0103c000200100b0032501d80390110001c41d10109265010800c04025403691510204860801144036800c0c82e40d0780e61410019401722201d90607080b810440c80e0700100036855200300070705005500815120681d2146000f220001c033205 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 802672985 1250 802671735 802671761
    0x507020411160b1806010608130809131d031c1d0f0a050f060f0a02220b07110a0f03020105250f051c020706051b1606090f0506030705090103 62
    0x98440801c1000000f00c3d00500c1502604219041d0f203241a94892100740035503c0007440c1c54000400c0105209903c480c0b99000714021031908075480003090114007041101207080b81c548600c0610a148054540079045c0542c2c081c505050b031403800140766070010002c0c450003036202d0303180c400200f60114641080f004031008560401090b02e0200d900c80703803e0300086d078030780c02141c522030307480c0d4800700d80d46214090302c2c00c500d1783d1951440d5802c1c0003034110400c01c00c2000d90480842604403091012031010f40580703607205464040520301100700070640f40c5041d01451110004020045540c4090800e036542401c0883c1c903490060300c504882c02da101101008954080c0489051100010380e1610440c0281e0a8400c40d4009000726405402440c84100041c0d01404041144c03500c2071014000c81c620010f0440c030503000760400d003443c0281840d400900721070300d03040400c22203030040e0811005221003410864403516200010f0102d000c010140d038184074000651341c074142e10a600c031410030803507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 802674235 1250 802672985 802673017
    0x10b040906140a140601030f1b0306080c0402160f08161b080a020a05040c1701080114060109060203030f04141501060807020c0319030c0c06030e011a010507020411 72
    0x6050001c003600255035003040c488140d1003c00c0116107a4002d034a8015a048611886500d5490045004000e21140075a840c0e981c0c1d078515203212000510041180c00e03550300441d4150030443c40c1420440111040d9200314410004541540c900c6100c6503860b0f500050724100706540c9081a40b40f610070703101000c04400c0044414400c1000203603640c82c1d0b02007007007000e60314152540310b16035070350111043c0130303600c840e00030002c01041c58250400e001440152400280102240304001c400030707030070f0300004096512842d08242100c0c5c03506589521400918040c1052450040041d44a220280000254481d00c100107014000c8081130012602c6200c001c45881f03041c880304001c00d000c820300422000402c054003240409100042c4111035240040c06840980d000030885a6400c403507680031000e008011070007002107000100880000d01007928082f84000c145a041400c40304e1102200c0800da1200d00031036000d903031160558920310760650700021001c80140c0403504a008030704c01801440c0c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 802675485 1250 802674235 802674251
    0xc0e060f160c0e0604050421020705100806041b0512060d12030b041d030405010c0519050a030e0102010c081f0312030207021309050331031208150907050705010b04 72
    0x192440c150840c1c40d50f0010441a8680c1c00400c01520b4060328081c28210b00116141c46801150000c824148410700444100e01e507100b0209881000e01200200810010750400071a41414014440202d1409840a003150403010010f8414098149044602c1460340000746050322030345150181250031a401c03801c44003110400901410002004501517424081d0241d80e008400100c0c80d018000b44002e54105424200111415003000c40d06071244d21515641800c81c00d0742401c5100c0242c001c1d005030907519100c1c10041c2050b000c090006045a03d01007840740425800b581903608941d00c6031801502460f00c542c500c61030500c5d130b00060300c15109136a00e032101d1a01503004000440c070a40d000351a505480c00c1d00b400711403c40002030a41d4004100d0176a803c03603c000c1078a0200420100c4c51b040f0554480c81e044400442c3c1c200702c600181005195004039013196001c2c0c1e201031072601002c00b014990021901e040c4026201c2d205104d0041012000c000c801c2d00145812070b07018100b0408a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 802676735 1250 802675485 802675493
    0x1c0c050709020c0c0d150b040b09040c05100c030903030806060c06190b061204020105030c070c12060e0d1e170c0d0b01052b020d1418010c0e060f16 65
    0x260081541020034894060505054100001c20101ea02e406c4140d68484090203003120015000c1e445000740d0040d0340f00f00c2c401c1a0381d04c0741412030040340030b5102425428209010700c01d0f0500801c1880003407042c0980038500199010300c2480507254140b5044031252140c1010522502600003560a140592420054908040141c40061045023032003849400803581c140203076445801e0b000140c1c1c04000740020007650081e40116042179000389168504112915039805940d51500050031202c85071940c0b0083c04964000c404039461400040c0c1820a10700201505140201c910901d002c4c2c100d030035102c9568050f44083c1904088a201c0308924a084407605c07884c0e5220000d02c0d00520b1510014107940d511a5013591010082c481c45142040001900c112003000140c4440c61015000c001151038180d480c0100a0060b1280a01c546903041c80304c501c00300e0b00f0b60ad4a1603030740c9030f240c010a4603003258010000500000d066860340e5a40d01e07940c00030503803880303480e040d810481d00030000301e0108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 802677985 1250 802676735 802676737
    0xf0d0b06030f1b162006070c181a01030f0e010204060819090b180c06120f012103051c1b020706090b07060b0a2c011203021c0c05070902 60
    0x3110301c82c8070124044004522003645018200302d9070503100c054050100000c400d1030420742400c160b101c61321001c0f9403400010707a55900c00702c03085601000d1190304114040c03c6540400907111000c00034440ac0b40701665101c00100d43d440d1907410107407140301c081801d0b012030340041c2482e08054000e554031511020040d11400040d14900c102e01030182d0f10b614808a10300c25280800c0d0310400c0d00da115180c280400904101039054088680903484c000109030340c0d03c2d0000c0a1881c000e900168161800b00b0308a10003550590101c0026201c00700c042c411008460948005940d050401c03545422800c001e036400b18107a8004005c080d07161004840c04200318051440300c0c1103565086036601d680b280030444540205100c0e0b0303000603100b03100c5600007407029040030054074406040d036035800f69180989069281c01c101ca082a604c0154041c0c080000c14501c080d024104842040121120664000390360756040e005121041e40c64902c5401e01130320807880c2d030030f82c0c0c0e8010080b604c040b515041500d000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 802679235 1250 802677985 802677991
    0x403021507410109031718030a0801240206190b06030109141302151c06060e03100e0604141203010b090103061202130f140405030c010605150f0d0b06030f 68
    0x450341e503288410848005020b1303030a5999240d0740d85440003111648a2414100280103010058105020800b046008002928102213595035480315545842c0ca02c40b420300c1101c1c8000e107652169564000c3c0b1503000500c4680140048201c0040d01ca03021849100506c4a206d40a0388248004000940020560801159015681d030451081e4490b60440013a11544c084c0080d04400c540c1c0c01480d000310030134050a61203140442c1c501500000c8800300080b52080e400010200d00548a01c010604007007155401d0002104400c102c081242d8080f5959440000c000420722482400d00204070034040c003028100080c140c600795100e5071250180d03080e40d0424025180041d18015001401051000c02e108285802821141d50200c04c445010080e0000d81c5154810035200c0a04005660001c5a8944694011030145444154080c4a5070039512954000c1e07116244001c1242d82e2661960215076140d410040c3d000e5549200c092074201500001000a034010400300800906503818074040d44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 802680485 1250 802679235 802679333
    0x306050a1113060807030207020301020a0f08130c05120c06030f1e071b050c0d0b01030605100e011509030c0303180501050c0a02120a12050406080a020403021507 71
    0x400141c0d00c5950079941d0040300c0b9954105281c02e10704008403030182c1c41503a000032440c50003600c0c20002e500441d003607070300242083c000503800c0c04e985000150700c1728445801400442d0041c4907a00d140e104e0b8a000c010781d0191901c01e0641c0c03c4000700d20117080003000c581c02030280c559900d034503004900514420080b030f10f040f1440c461004403401c0d560102c5581c0e00c60b08560700c55082c2882509c14540003040414000c6441d031003100202c04480d902d000500d4a014031561405030203605524202e800d554010348a8903410510a60611464107201092410341d8041070011417610000c071803ca600c54229400500401c004490120902d50711201185a030b10001b909006d050381c0c2d0301c00454240c41072105200064020345003440051500248000c046a0400d048801d0b05d03407940c0f9450030304a68199141c01044c00080c0c100308081c4c1012007140d0001c1c03840c0301103052030719580214600c0381c02c4036640b8090f6000024001c04000c5d010181080d4031110f803a042440c0d2000400c860b050313030203100b1a50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 802681735 1250 802680485 802680491
    0x2f042402010c03020703081909020913060b100f1115010e0106110a050d03090501020712021e0705092d0711010b0d080403020d0305040b07050714030f280206040306050a 74
    0x440b0500900031250280c0d8981e864060581e03400c151942d0030030300d900070136061070f85031074504000d80d0355440380f503000d002c2c0e4480090300400a03260100440d003c41d55014082c1095103805100140c1116860402454a007098900c0580c0c5500d0300d420819001c01080d4490410800841d4442c40144154180c49007611000081030300d8044065960310b031220001d00551002400707910b500e101e40c00150a651040c0c00240c01d1071150743d03d61070f681c40aa282e060040c3d00008000d988050144010030181d410000036214840c2840c01080c01240010648884610540380d11031090320240310320410b215081c1000e201c0c50030540c1004014081c6010b03000041c1d0308106c61014103261004c41002020741c40301d0050b2501d8a19400e01c410f1101104c001d0b014440e05000025104030084010703c030462044014108841c01d1121010105404c0242103000380d0103800c0c06e020801c0e00181300300200008a164840001401280e80d4488400c1a0300941108c0040303000010040c803500070b1401020b006030f00b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 802682985 1250 802681735 802681751
    0x31606031d1617030d0e0105060103110f0406081e07020f1b030307150207052509060b09130e1e0706030504020a030f020112020412050d032f04240201 66
    0x10b54074004805880328405000104020704205025500d106a1040080c0c90070f003a032000c1d00750100c44114582c00301c2a5118002c000c030560f454460aa90f104d035a1042e070b800d18400c0320312220341d030050f030080009025540c80480c02134000440140748060070141d05030b80300c1c601040c00030b441ea6540d030112101449101c100ca9111508607180b44030b00f00000d801181800c48a840300c0980504141e0356203001a400c10100c004180d00b4001500c10301c0f2404180b07180c0302482101205d015502c7d611140c0c000c1e24281c400c1c8104510700048821103001151a824171041c0700d8100d01c001d1170b59407900040c030b1290900c100c0e04201880c5000000190400642d10460794039001503054940881d4025070024807000180005003810080c0c84072207006141c040c080041c02c01614049a105c4c1e0001125035640d0400c2e0f40070424200030000341e4140c6442c00713000d103500d090002c8080d4420f01c14080c070145800303a540c006071003500080c1c0c1c00520390310085c02042038042d0071040320325174100c03442030042d404c08050b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 802684235 1250 802682985 802683041
    0xa080601050309191b0806090f16062001051302010306150e06030405280203010b0a030b0621161e05150306010201090c0b0d1d07090b03160603 63
    0x540303104412090240020403480f0300070b11390800400000715189a05082c010042840304078a50000c0d00400c0020310090501c10388042c9030280c440c00c040d40b83d901c202504c100c400c124694500c12514941841400c07200c1c84404418102d6032400b1401c0650710740700410142c0301014900b080440d000f0307202000380c07170b03103c1c40400c211000c002031850105d908448148a9418414015540280560306840340007518182e0700009281d0004520b01c0035000c8080b4409514080c420254120b000700d0340c1c40c851a107140e0392500781580007800a4406c54150f51030706401c0c2c40e1001e184136280c0d6084280c800c15198800400000d013405d00441071040d1841186284101c0000c80b00da098500060840541c07c121107402c444075032009003941e04654807a90424001032810700e0036005099a0341c00309480b17900311008001107581080780404041c0c0d5200509a4401d00072034042d06607440c1c0c040201c0c0041da0800407910b0001070041103c0b1100440c100012070700d926900481c10308000e02e810201e07500302241 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 802685485 1250 802684235 802684237
    0x30c091a19030f0f0c14030624040f06080a0e0c0f15040503060c070c05090f0c0310180c110a080f0f041a0c0c0603061e130c02070521100b01050714030a08060105 71
    0x50440d001520700c0002710314021703103030401e4032441c461541c90340c41c00f42c450000e005001d00c168404404541d07444240000300609020742c0315101480c0c0002d1001410541c0003030348014290300450b01a10711b980c0030419102201085601911001c0c0807640c25051910110700305a002070025243c071000582d01159524000c94054054071040d0f0400311191603001c0c4840d130700da202624032035020070600400a01210004030080c101e001d41c06000542c1900c0d0710b03003c4c00e142007180403003426804c0410ac80d030000311300f0400d03180b031450b0315042c142d01d400c400180c0a14038800d0303401801500c411510303180c4600c01040002d03c3c1e803240140a0320f0315040c40000384070141c0805d44800f81d10100c00345641295100490003030f020400010540c0040c1d085140404080b10240303507a010050700001414440b45c2080306101d00711a64407032070803442043c020741681d190100e00400480aa031150786070919680310340d05032500f05030407c241e9801640e031b50b113020b0740c0c99101c5ca06610106600c1c00c0000c0c52580258 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 802686735 1250 802685485 802685491
    0x3130e040c08190314040909050c01020105070e01020304171603150e03211009110a1805060406080c07050709051f0311040905030d0903030c091a19030f0f0c1403 71
    0x8250f00040d51416079041c5e888102d40d904140d18120144000505e804c918080d0130b00a5015201078806424600d00081c00e41d1001021001031194144603616566800030454044411869808442c020400b616030f00700100325414415810444801100740414408407001d41306402901300721048c0050303005a124000d200d81b84881d14a00d801d01350141c100300b007500354416508500003684a40302d18182d070803a010f100f41068a0320004c41c000481c1c0703400072801510251244405482030f440d000c0080d0700361055001d00e0781080198404106114501c5e03007901d0111b64480180d0700b44540712034180000301b0342252045151820183c1d0407640711510820312040d1390f00004440e40703c1403034070b00780f002628550303034111032500c810000b0a00460061181c180e10910030358003c11002ca240e900180031038801d4101c00460315040303001840446d01c00040311282108203401901003161072740154001c0801024a0070841d0034012120080d8a45a21400e04030020f41c94a08a070b803000c0080001c14003080b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 802687985 1250 802686735 802686763
    0x901110609030a05070501140a0605040b0604080d0c140a0f2a0e0709180c080603030a23040b070b0a061d040b250201290d120203130e040c08 62
    0x200064600244551300a1a0280c010070000c40c00c01c1c0d1030a8031244250048400c25101b981d119024000c5141a002c2c000d0706220840c0d145040c581400c80483d110582800008203110010400108003d156406040c3c0070003414250380300f40c43da9051803590005900383c21100c201155442030a510f61100c94214015400008041d5940c10a070340c5084401014200c03006210b1000000a4a4a000050980b10810381803001c60415480000a002507502400c2c40c4c0c0309800900002d0101c561000b044182105a10140070410444107000326030381c8580c0d04010000800052604240504c40800c031780140c04040e8104010303a540d409110321003443c13603052259914020042004204207034806900301d078040a48000000d01d008240c1c03201041c034240c010141c1d44441001580c51881c0c0c0c104640082401c1d002044440d6410018610180144004000000713115440b03a19620800644110044247d410110a074a5244e2044c1404040f14100e0701d0000000e00450110408943c0401603260 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 802689235 1250 802687985 802687987
    0x30e030306010c1718040f090305070f060603021c0317070f120b19081b0f040203090a02030102040f0e0c04030c0b0f09041509201801030e0a08090111060903 69
    0x80d00d401114011025081a144c91303501d00c00d8a100d0700d62820040025459081c400141e4044000a0000759919240410801464108180c000c41d82040490340d595900502d81c40010b1368034540440182074541001e504211844044500c1000e41070015403c9070082c1c651015800300c60100d0b00300f01e00100c0c1c03400c000035441e24200806d03d000e040150802c1716034507004078002800c0d8000c40c0b1058100220b6030480344440504120050045c80000d01004000700100c099400322408944c000c100c3c0e610040c0520740c00000a40d0401c4284200c1c403515500030b0003950780c0c50742c40309800d0140800d400f03103a00155001c404101101d44402c00c072401c890303110040a888601e800c243c68a5500503c03000c0c3c5043c00e040101032000e59a074428449540ca0320000c010850b410080050126141c110b0900c1a1038024107030341004a1050013911103540d031000140c0600c0303034084012000f4120b070040301c80140c03003242100010841034601808010b01d007a600c6c0040001c43c940456541c82003600c1901803508 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 802690485 1250 802689235 802689241
    0x905130b1c23070326030f0f130221071e0f0f083c21120609060a0308070b011401050a081b04180207020306060319020f06070506102103082208030412030c030e0303 72
    0x441c0712f5604042040d07140540d8601036803040c1d100d4900c003100000341c2d40104180001d02030324000040410250421108002409051609541e914091420b40241d08541640d003420040c440c080715202004060b088200b8140d1124442e0755564061214060f0740304000310100c003000400780555806032480744001d0055102c020601800d040080e00e904d80107040001c0100201d40301c3c0700100103451250040110315898043d10440102c0a0340301c8604101042283c4410345a1007040d540e00020303000c0d1102c90a076a012240101441280d02c09485455203044100100312160b002d480c01038000d030240c542d0b81ea24401015250350400c140e08100406051001c400350070308016071480c03040c01604051400c005512030504d071203000c0300d560100c0d04034540306001800007050404c40c40f014140c101000780328196000743c4071140007003d07075400058080d40000c0d0a080c0c007242c0c514841d00005123545e0b905040c05d00c2440c1840044003e40031900300a401a0114820320400e4120065140910b0440e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 802691735 1250 802690485 802690519
    0x507050f070f050f0604030503061c020d061e110d2a0c0305090d1b0501020d090e0c04030b010323060105010905130b1c23070326030f0f1302 62
    0x10009542903c0c14400d0100412102408202e044e0156010340c5840e030302c03890018200704940209550002d81c00c0b845102400042c1c0f2440d0140d00256031140c404201022070b4892402c58808423a211a20182060104464150000001d0118054404003031000050b001640c1501003000031190200042811800864074415150707490041c2c880e10b0194540f55180000901c0040011030603030390300c134005400c20f550944116283c40101420f002901c1c030000008005000c0d0f118901c0380080a241c60030000b01c0b00801d240c1120b0145920103600b06195840c2c0c24002c05903007000d40500d180c507502c0111f041e0303012800280300b4100c62050351841182401c0c40300f8404258200d12251142a0700d0ba01a484c0650320b155645103c940d0780e00e1852100015810803380500503000519807601c420a080c19080001103a4001035a411801170040c1034041c00f042641200c5203042410b2104000c4280070950309003120140c091309041c1018541512801490108003c80d102d0080d840702190145a40c22 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 802692985 1250 802691735 802691753
    0x130b1006050a0f0c0606030c1502060405060105221a0a06051e1b2a0f09011a07050111070303060b09090a150306050a09030906080c0304061521060507050f07 69
    0x4140f03d02e0f10000c603412070758070501980d00b075410854580000303a005014208101d240240f140d00341f8030061409007072036110b042c0c0750756060203040d00a400f4819a01c030341c0d413042d0160b890107180c120410010000d843e21030b49105008170040740e00c00d16146c0ca002903000c0c81201660100c1c1007660303040c4602040c801c100704076079100017090003000002140011030404240403011107900992000c12081c0094004070071080d120000207481441b100303541c0c1d94243c03540c4262505541c1d2444000500200312119414a401582e500034a0345d82032101c001040c606c04805440010b209860600a007a150bc425170414000c18259079003214808001420050700c0d43c12410036004401d18045547c0d46946502042c0d0300211528010640ca6500310400c042d071000307e61b0300800e40d51034100c040b400d062040180c42d20002e030000c0e0405403160020519403000b0f650300c0b0010310b40b140c030440c0c0301251160707150710500341d406003581c0d0b03945480001610b4a0082c400c680441005220581c54020130f5030350a058 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 802694235 1250 802692985 802693007
    0x80d1706040902310212010905150d0303060f050103090b07031109040e070e0604020301050a090b032a1302040f0b0d0204030816110a14010804030e0603130b1006050a 73
    0x401a10342800b0070141e26148840141c020b42110b15080d2031040030b0304540b102e01840b01c40d030581441044000030301001d509600d81075540003400810280c03101084035100620844203a42d000070f440b00386804042d0540d001c4011601d078001c61036920744ea2540154200d60b50180d0140c03540e034134040080c0034603110364440c207001c403001c004040c03d0a1050300450304a491a004070841944890030520031003025802095000204580075403866047c0030116400d029103206007004540c55000c83c0d5030030b5130103105c142242d654410168150342040650003108a05805041d80109144215040720040900032a029103000780041c900892800b2074441c0d050340051003030040c0f19420301012002545080003410305840d540f40007003020005007401000309607441c4440f4800c40344200c042146845004011100c5502424944015030b80c50405075182c40d04000c029502220000411a206c0780305091448a24042c035401030a40d5100104070304035850500608011070014412603004034800e001f0022 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 802695485 1250 802694235 802694239
    0x110f0d020d03140408070806010803040609060807050d020f0301030b090a0c060f0c0c1202010908030405030a110f360405030f031b16120f0905090603010e190309080d1706 75
    0x43c070410104074410182c10540210210f600300c00702c2000340000c104051405040c0c0031002c0c0d407415241c881d001d00005104d00c160740c04c2c05041030000f2074550040c03055600d42d1041210079555044c1c001e1644e02941d109002c120b441d044c0420108880d624001003000e0703d02c0e4002c10320401c580c208502598441050203541c03041203000c400c91000160703454101c900070a24079560701d41008851001410baa00c4030f40000d48030380d100f4001080903590000d00c584425802c1a4100c000c959040d020400f03480000b15016008200a4400076200130196118100380349800000386e1074845500f64040b000c58103a402800c20b41c07007405044400c4001c03c00a41c0c000c5060551080c0c51403881c610020a41c00c070a00c600d181402510298061000350655660300f9141444c00d481c140d0f60b030300c0003d40320603080d018060041d83c44a00050140c0c400f58005200d1a0740d40003207440c8114038801901c1c6402c0d42c444110001140c0e0600003a1401c3e002603c0e00c000320141d1103103840c1032843c400750030082070014503c0b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 802696735 1250 802695485 802695497
    0x110c0111030c0313030203430803070b010509150618030a050d051306050f072004020f07110427060603080f030a050606030108150a060f080a110f0d020d03 68
    0xd601560403c010903102c0030203e040c0385154550700425060480c14403040c6a85084008142c3c2c2608083c03095140000450108921a4100d0b200d08015501d50350000480f922000407500148203e56035603038100e0307508941c1d001682d078030600d0f0030319141090503000303030400c20a200c01c0c00d00129080d94040214000f40c01c5034940a901d07240c0c0340ca0715074206044000b007040020224400d040140518003c1d01c1c15003842498651540e954a502d407084c0740c001b501510310420034400d00203403003003500000c0300001c0095440340e045034440302d51948020030880790f4002c00c4100d4410742c1046d001d01d0301e94118408402c1110281d1101080f90400b8011003151100e40e80e440120007e000320740544048a58104816268036000d0700000440b40050307c002c0c4140ba0034801003201c9180020401300c602c0b0310700b8000b0000d0701e60004880c00b6110300e0700801a121009100410760550000d00c042c00d1a010351200548041e07050280128000100510f81e005403140021f0700c007505206840d03403800c0380300386044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 802697841 1106 802696735 802696747
    0x1608150f150d08030a0f0b0a12030804050c0d110108060405010f0915050915090f060f0f0d02090c0306030705030c060a180306090803070807110c011103 67
    0x240e0700c110a180c810700d09600d4000442034580d5000a550762039040450811000d8107441a5112010f80f90a40b10101440c22110b5201103905c400c0120042000e90340b002c89070a803008005031400d00c10302450401540b1b9461003c4c2c2618003401c101ca8020410300001488110040d00e0103126600781401401032801c030150740f400700c030002040021410360f22010f11200010541c041940038078450704205035824131080042c03d0410803150b40c20281d98030101400b03014002d4401d90341082c030250b8110298107000e20700c0140074900030040b021040d0664001260f90100302c8010f01407800c0801444200e04041003140e0142608901401500f22403501041c0c00e8000c0020010400854a111240c00c0180c180700b000a190440800c3c000c910070307410103900e998420f9681000080c080d10009035820300ca0f0f400c1c620010b484c43c02420b01c540d00d100044541c112261104c55040c0010011 = true := by decide +kernel

theorem cover : BRFrame.Cov 802517985 802697841 := by
  have h0 := BRFrame.cov_init 802517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 802517985 ≤ n) (h2 : n < 802697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
