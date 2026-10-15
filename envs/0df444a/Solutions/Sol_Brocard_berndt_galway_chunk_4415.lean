-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4415
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:32:52.571416+00:00
-- url     : https://prove2.me/submissions/bdb6fdbc-2622-41b4-8f7f-e3a317e92941

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 793884892 ≤ n < 794064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 793886142 1250 793884892 793884899
    0x60b010c050a210e0a050915090f010e010b090303030a0905030c070e090706030b01050f2214030c060c0c090a090b0f070f02010c05030106110a0b0c120a0603030e060f0d06 75
    0x70101e400e0309401c1c001c1c80c80d61400340543c54052911850302020007010701802c10303d05400e003e24010f004051018803203003808540241da5601b01aa4054007032005080025030400d13100c2c0c1d4501c101a0050079078101e081c0115402543d0002c1100c0d400541d0200100d01819a0301d4601d2850040c00f1240205005070711707020510181e036600c02840351030300d00111042141c0d144410340c21901c1070b665840c009641041724031440c4140d40020510030745000c3c40001d50b000060481e900140032a08000380b0a40d840c850908589010400811808800c41d0142c1c41c00c0301d600a99640da0240d82d07001401801c2201c00a4024805640000203094000c1c2c00c5003094a05030b90b800300d120000b103d5030000b081180901c04202d0348144034000316004c0ba40c851a00d143d00b054010358200350500c046107002d00c03a01610000240d5003460080c00f44400101d9251900d0720482d42d1008200020450b42e1a14684001000400e5015444500b0040142c0d2019600c0e0b0442504900c50b119101c201c0c0c103184d0a190300007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 793887392 1250 793886142 793886153
    0xa0309170a02060f04020315070525050d08012601150305011508070b090906130c080105040f050c0409022101030c03060e060603100e10091407080a05030304060b010c050a 75
    0x184426000c50b030030b542240e51064484030b41d801040d20040d42546c0541480d20382d41009007809030f04100782d0f0802c20f050101001c03030030703031040b5100c03901044040c00c4490440401000b04031162892100e810003191700d6050410702e2401c140210160000758a220209140b10034080d131042400120b030024003c80d0315101d00384280030b003810f03c9104d084503030a602c002501c0c0b68041000015540d0144c1c04034600704107130040003011072000e020103900540c503510b207000403075140c0314191030b499460700c4e50b075015032504080000300c1d09080c10f046101c0c0d041c602004244112030701160706a4107100e900607151206c0c425200340a402400032841c82e10400070011042c064000c62a0007100d00c2901c01344054850880d0540d10b40405445a030f030180c0c44080c0c541c1101c0c0068102419050404040300c030503846c1e035000e80c07041e5000e00809840c0041d0301100032031829414000f250180c005000144503040140d642c55070380c0d01c00108050311082e920582a442d6a1142c00c0d2105001e400004072145400c1e1070608 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 793888642 1250 793887392 793887397
    0x3040608070206150108060a0b13140105040602030412030c02090c190f0f0f140a050414041803030e01060504050103061e060b0706110f0a09090e030702060f0a030917 73
    0x22100030942010000d01d0941c03000a40510072140c40a1304d5907032580e0f8000549035030501400050748280d100d03001189030486400a4400b22058041c8007903030320300d0b04040c1c0c08410324025150381003000401042c800941c0000456007240c06a1a40407981c2c441410211001c00503464025840005d020601642c90b0b9100054044090030390703103901102d00080416250340c03c2c41449800031400340f091030a9a40e009a4101c0c148644030304040303094880e02100b01409038030030481c1c1c0c40400c0e0f020605100840080c861030051903402e0385d080000d1100340b12051422140940020101903e8014081100d4402e4010100818001d801408656144e1510300050801000b03540603d407032145600b03001c601c1c1401680304807840f028165241400d02d4075184c01904a02300484004181040b240d0660081c03000108269040b95582c00704881c00c0c1103e10050301c00c4584a00e030039074028004240983e03038400c01c8030b0400c40300555866603203d0203107040c2c0244c0b0102c94041c0000115224904c1100d9200c0700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 793889892 1250 793888642 793888649
    0xd09080a0c03030b040b0d0618060608070e01091104151b0309141f0e010509091e0906010819020f0a03030302090406050406030b0c09150c0307060c0815042c0304 71
    0x40600130b424012080c002280c6146011540c071410703819060001c207a40760300210010050001c00c2182c10080d446a500b40c0b80c903a80901d10315030045000f0403280c00d01c50302003400741085076001d01034103010001c04c4040d801940a245040419420000d106070f000391221400149014050360f10a4450f08000d07102d680d1031b00c101400c040b00300c01c84c0141031030700314540a0b10303010740003464085513480c0c5421920001324144681c10700c44104040c0e07100d5901d401c029407041100500400c0540c4803113904200101c0041d000c030040b0f50080300180010b6101151a0b0720b00c4030505051040304580740001256400d64030500c5d0340104850702c004c014154103800034000c2ea10301b5901801102c1d80c40c0140021101c0790300c80030342208614000300d940600707628010800303200004c10348101c034007a140302ca41d041c0d0f014813001c0c5015440020904c0070440c0f0fa005140b81d00e143e9040100e0a49409101d481c16805034200a80c46503684900704022102120440306602c0340b03421b003a01c2502d04444a181e43e0340e22900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 793891142 1250 793889892 793889897
    0x110d05160603180f1b03060623010c05120f04090203150a060c0c05360a0b180a1d0d02030409140c0f0f0415020d170105030a080d09080a0c03 62
    0x180f050090445400350703007115072251880c03000c00843d031950002202500c0c101101e003103800c000040841d909005880141c40ca170084c117034060010b85004e034000450303050540c0c1030001d030103003641c013141e408a60b14551280c1c0d0807416035a0510464510710601c12078205103500f034808001d0150b0000c0035441403852840c02e40b01c1c01c0e110f40d10b82030306441006044800902c41603484409000504000c070092422100f2810014902054a0010070052492084c464901400d0400b0000d04100c24041d500d08541c09a60703081403e42404130340c01001100400f8a4101c545a50810344c4d2040e11500c01d004280919050300d02244841310003c0d100d074044e03c6908089070505d07010b51170700d103400d0301441e0160b4aa03600c040c2c6000d0b00040c9203944c1e604070007003045072940244000100b40d1414913281c0301d4400e20b94090a0203000018001d0002c4400140a10070501108014062603c1c00a00d01503102d4000343d8154a5011000038600944407040005205040208801081340c0d080294052454400d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 793892392 1250 793891142 793891151
    0x6070908012d0b030a08070605220303020c07050306011412070509181011070b0a06050319061b02010912110c060705211b1603110d05160603 62
    0x5610380360a036810014400d02e06203401448508400600b0114120324000c030740085014059000000e082c18450303e02550000000aa40d2080050502c100c13540410444449040c0052000e0310040c17581002c0001801d256002424404038202088020000d04004080720029a1216142c11640d1003107a12640200b02030307402c40b1003503030002c1015025203c024001d04065940c003615039070540d1510090305450301980e0010040f4614a0081c00c2980f8580325039039542c0c102074030f80000030410003041850103070315040d405d00c4140e801091108000a143c8140000c00c206420a000202040418400c0c820030b8001c51644c0d8a8064104205050250303512a08900da00982039a140b000d540d034100e0540c01000482c0308034a040c0000c2c10402d4010b02c2100e48110f0204480780700039002e05421298603001040c10811008140d5525441e81d0414014000002e0280101b00c40782c5624040180740541c511045845516880c05d2110000d41000c110f9081131446c03440c410401486000342c01c0000d081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 793893642 1250 793892392 793892399
    0x12090c180103260f040b192609030c01051323060103061505101809020a05030c0c1903110d050903030a18050d0809090a090b04080307030b12060709 65
    0x21aa140d0480e60040f14031a41807071440802c0000000307100703401030f00f801c0c103100d6852003100c03100c0500064840c134850940e82c1c400d82c11501d08503095104420040182c1041c0010010210317100c11186504200914081c0d601c5003030b5480c0c11402003410064031503103030034104140c0c1c1c600c2c0500c4941e030500503030b9400721b900810401c0e0321503005c45400a0038140c2c401001080050401c0c0d00506050101d03103019120240c6a0300062140c40200300014006890100722900710707205945042c0c010290307600210700d880141000904503000052644880750000b08074003003444018000b224010149084201c81c1c10424540a800c1c6003040c032001a03c4e100c2d294265660500a000b01c0d00554002401103082c402050801c8400c0b84948004022080e0544000941030710388525000e9064480d503100c40e10b401e001e006208443c0d40003410b203110642060003c401188103425104c1c4c00c40e81080300d090303680c0d481e080194080c0036034020b8603030009285d0796003040e4040041102401801310703503640300207213a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 793894892 1250 793893642 793893679
    0x5040c0507110405090d0c0c1d040c060e0f04180501020301030311010b0103050c070f03021509030a02010b061801110114040f0227062b0c050901090c0c0209060612090c 74
    0x4100ca55201c298400c0304d00d001030340c1c015060001101c1c41000c8c028292a02c2e0522200000590142e05101c0700c200002c0c00301b000510f440a8002d8400c0d450014950000e21000803628010343d04680e000310b07503503860340b12181d444200c80d03d4041c0c2c010700203650383e503500d02c0c00502e03204e50411100c1203035281c0518800f003580f0a000d03141c02040d43d00841428a80c2544070080b0070b840080084082d4480c102c4100c00300c85140c00d905108810400c040d6440c2c02003440068251080607400c1d5209000420441e02140ca100c405004070010a00c1c4c5041010303680c215082c01000d14100894249a50720204000c00070030644444281e44203480400222890b058802240003042c80c07601d81e07180c000350001e5002d0506201212010105e42c00350650a51035060100490301a030006644400b00003c050000342000e85d945401130103100710801c0240034000005040c0a5008002485107042d1008154241d844800703803641111800c1d2601e16070f0400010942e0341d0103400308054001c1c1c8004646980040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 793896142 1250 793894892 793894901
    0x150709080c0904060f0207021305070e0d020907030e030f180a0806060f131107061a0907050403030f11030c06070201060b090901050d06021c0c0806090103081b0705040c05071104 78
    0x1d02901d03210154035550f8078039029010188030620080d5083c026940982c2d03c00111000e40c100480001400742080100103210451005410b801920031040410060f2241c01c006c13a4450200d14001401000442e96141142300c0c036203c200104c01c021604900c03800c0c2030003d06151160480e903803030701c01340d4a00360b0740c3c0c582808440c407d0b0702c4518200d00b0182c0c1d04184a001ca2154800c100018088140c0340031001140c000d400e06030360f40c3c0d5030781c04d481e220022000d00000c558a0308031049203070351070702e00300c0205144a580070040400c850b003400c248125010b5016010700c011170005403505c82c19030000d00e5540d00411030302c81c0015801c1c90300002e51046940100d480e15a0060140c54041e1b0a080512161055000080310a90b0782080b00e2000640c0c0c2e000c0e05205804180c6002c40c00300c8005030000c0c19013601418091080c905480100005884c84003160051103001c4603803046074407402041c0b03007041c060783c1c80140c020b41429102c0902c59484402808100d2041c2c1d182101428810148000c44 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 793897392 1250 793896142 793896163
    0x7020f0f0301020c16060f0f08060118120f0b063703080f2d04062303041b05030d050301050d0201121a03011a090103032015061c030206061201090515070908 69
    0x40c4040b00ac01c145508c00c40114130215284402e07079110a560b6144183d481410750750956210b043c070001c410400441d40d0406411000c05c441c0c0c19424605070362401d00c2283d248404030400103800308401c1501100c00000781c0150381100589456100700c40c4070a285500c44ca4004910080036603c0e144c1c05031403001681017490100d010a820302d42099000d81c2c403202c2e03091400c41060040c9a440c048403408d1002544030310700c08e08a120302c07400c000c03a010f000d0340d805802052098000c00c000050b00d55010b0290b81c1190800c48416282c0c62090005940030440004410245410302c9141c0e0311900464180d8070721400250020420f8015005a540300702454004203540900ca440042022078442c2049880402c4174000c0c1c4403444001005a0b0315140341560444400740b070810410500385408140250580c44100818081000e44c1e03400a49500f001442113114004240b070742850034100b588a454903e50107400c840a480314150913492085040f550100010750100300807814060210b4406103c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 793898642 1250 793897392 793897397
    0x6020d050709080c01050c1e010e060c0a080a020306010c12020714030309091b0c0d0e010f1d040c03140a050f07180e0c0706021201140607020f0f0301020c16060f0f 72
    0x2c090803500110750345d034072a447c07840782403081c0c4400d0b28400380541003410f02d00700114000a000045d29443c1400d040008048440034001030284036403a5400c6900343d5848200c00800581d41e5850b41c0050300c0110301e480c03000d00105440030120140039000035440003600e5820a5101c0080c40c1182017594a208017450190000c0d07039000402c80e40d01c1443c107070700000500001d6280c10510b00f8840680f8001c1500e0b0b1080c009140f00b002d814403544c2140900c4030300c405c40d2401c94415110304000034054400a2a40c9000719500c40b00105104d209512218045441c68100303030a0b070800d044014042d00c0b09030795004006002c1008035400c18050b80c10302201c180c0e02215024803901e0040300011404004191501c10407042000d000001d001e8802001403c50112894405504200b82140c1d0700b5a201d440500680702007082d02d0142c1d50740c2c502540d40398411a0701f41d010300500130109000e801a45007011641c421602081d03414041c6245c0c0800380c680940c0e9004c0100c0c100d41003115584c2d1500c152001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 793899892 1250 793898642 793898653
    0x3060117030f18030a1203060b03060136090609060504050402090a0c020a080a18050111210c0102161104060e060d06110d15170607200a06020d05070908 67
    0x202c680741c00050514044100010fa081c0c080394400b013030a1011820007141c000a42461b14401c03250144551006450428121410342c90070000103171500450640400345051000240e8001c00c92401800d580b0924442c0110415507407008024041c010502907100c000b820302101041606261048503c11a0028240c00454440b00c44080c001d1079116202000c5006003101c0002040c1c1c1d4200401e11200030341d49550041200c000801c1c030300042500550704110642c0e0301d160100e80d00182d00604211a1803c03108981003100017a040791141d03145904055002080d112001c9056000c5442e00900495a041c0040d1076002048122540ea020305869114440080f44460502062010b2424841c50b0002401c0304c1c0d010000d0340c0d83c0c0004c0180441540c03142624046001c601c01e40340700400c0e4080da17481c103041c4200c0381c25454060090582c4c00f0403602c010070490705900c0003403050f60414020203440041099007440b50107503000d074201da01e0042c00c2001091650340302d4000072040301e4440c000b51a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 793901142 1250 793899892 793899907
    0x10e060114071103030a090504050906040302030307050a120c05030603300319050a0e0d02031c0b0d0803010e150f0a14010203071e0c0b0a0504030f02120610050306011703 75
    0x1d4000303950039100003e4595588003141c50420051441c0f000e170703032603440b440d0740b4003400c00c130075684000c01a0b422508544280000250008203036034124440b42415a0bd8000c400da040f03031000381e0f0380e8209980307904180384910320b1500040114000d400c00d4080c0e54091301d41d119509110041e40c138888800d40707490903042003455482d10165030000407046002141c40460800c20042c0c0d4003daa00000c0d441d511160341101070f01c02c100700340c00300505002460505201010117211050000ba50b110318a4440c0503200d11a528001e00c44c0b07072907900078803d82d2a9612031214504035a000c4515104581c0c40943d6010340d4901502c2c807135040c200c001e08510103103003009003190344480441c0c03a03141948000d0011400080d028401d00200c10003545840051840038100100080583d52009010b4002000100d1a282d40402107030700b80d981090501400c0e0718107101190300c4c00c25440c0f01d60542d0181e4001d001d07644240c091282e0807640100c0403118103980341c1240ba543c01000d01038401c0c1540c01001501c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 793902392 1250 793901142 793901177
    0xe092a0a0c060b0f090f0106020601061b02090601090503070305010605042304030309060b06070609020906010305040515041a1f0e070914120307151506080c0717040906030b010e0601 80
    0x3c941080380a000c030800c20107124003044120f802a00c15080c082080c0300140704107681000458014113861404461548126204490b940c09070000a8000d622031030000300540d0007504400002d00300542180d401039528100240206668001c1c24466800d14043c44100010410300c809280000c00756500180c45540e000da00500e821031003100c10541310040701d240c44c0e550350082d1100d240034910100d05188180b04015040f10000c010314141880c08040c080854400520721001c2e1000d07030011445500c072401d201c0c00f0810382580c10901411240100804843c00030b401464813054100980c0b01d80f0b072038007200c1400741012a0170b6400103010220800084c091407010b520804405046495405e8452030f00720f0030b542c0034510a80e00420780300350342d4407155800c0c814906111895803101d0803103030800c5001070142c0c00c05405100f541d40f0200e061024000b14040300b072403500200654546e5182c1d641c503070201901e00f510040e5500c4034000000200d06814202c1c013446074905079071b125000107490101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 793903642 1250 793902392 793902401
    0x2f1003050702010902031606170c0a0f02010e19031128080409020313021f0e01051c0e06010513021617070b01090f06060e010c020f010e092a0a0c06 65
    0x2807411507403554481c602584043c00000181c0e40a0f6074079652142c00c010010300508801d000d044100407500701006016040130301525001040f5150800310140d010030206d02402c17501003111801e0050740034042c0100f074032050783c0d12054440d4888cc60094607a170400c1d078030340e4004600800b48480601480e00203504c1900d0107022980f003070f2215402c041d181e60342c40f0103c0e001100c5c9011800c0c1c0507407415041d171600303010895204004e00c0b0b4076444040d892000400302943c40f140f0700d06220300400c9802142a00c415440c007450f0f008101000315000ca01030442e81c400007032040b0380c010244135800401c00d81680c02210320500c000a8409241c00c65503881d059030007080641c6003680c105c14814440054240e140d0325000305020359020540907183c0d0400c0c411113030a0380c8000144100c000800c0c0715a604101b00003442901100c038000c4210350100180c80d01400c4181d615400351002c820040764848c09880c941000c0c000103240d15448030b1000b02c0e803030940321f04080403011038100451000001c42d1a0403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 793904892 1250 793903642 793903651
    0x6040506071416050606030c1c02060f0403060905010b12010212010b030408070c12030e060924131221050f0307021504200f0a12020f030a2f100305 65
    0x9442c1d2604000071a6856004400d03003044600b9040344051001a207400c0140d01c15984c4121250800c201b0403040d15078100c103800d0b08c024021003000c03030001ca1000c0c1c0d81c01650000c513085501441800504d10f001070003009200742c2c96105000e001601d401c9100f0500c01e5400c0d102e0440c80340c0c0380303590030314140041e00c2d00024130031a03d000040054900255525180d903006207038a101010040780945001307400b40030208445801a00103000304c02c40c5036103400c9580d03620640c0344100e00d01140d2a59000856225120aa00180780e50100c00984940f07241d010481442c011034603075240000310440c4441c0c003c07024108000040e018815a200035080000a542101e220300443c0d0039004504190301e9907140c02c403010f0381c00e4502c401c014101c014400c0140c5008035001c444a12415829030009400041240200710850f082001c0040031500d880e1850304481400500700d910400e00e07440e00d18507040b82c526a100c41e0000241e020074030760454034240c80b0484002800480d017810301c0d80040300104001032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 793906142 1250 793904892 793904927
    0xc070302060906090a060c0309091505040b12031c051308071203020d0c200f28050a060501080708030909070f0e0901090e0f0f0a120228020f030604050607 68
    0x100c8154130340d4030300940750010002a2036502260096040141080302c8a03401401250705007410101540034076000750f004d8a40031640050010081c2e400301c1e11800890b41141e000703100c002205e03c080380c2602500b60803c0a40071081c8040d0b0f40300c44d00d04081011060008040c50b4041c0b0461740007954049030f411100d001c07450014200504002c03079000380d415005032100410500300f02025041d0000c41904400c107500c130014100d2010340c400c003503580d8200d00d440901e4413803507885010071400703032840302c0c81a42d81100031901c8504c820b06013400101000e121f40f0707407184245800040e0081012090302c000c1c440c010041505d40d038401000381d81071800410558204020414400ca065a9040240e0f000e0140904005007500b105500e140c40d080c0301c604a02c00c59403080b071181c07002c907400003000c0300240e9002c4400840c0c0d1048000503031800d9050b01e2410315492060300407200700304803560142981402180c4c09580e00c0e040c041803680303c800546003d00f0076000800041e000b20302400c40d820b2203c2120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 793907392 1250 793906142 793906147
    0xa06180303080c0c060f06100804050705120304031704051f08070507020d0206030405060601110a08070f110d14010f06290c1b03010c0801050d030f0c0204021606050c0c070302060906 80
    0xb1011358103042003140d10003401c0d941202400040c1c10526200b034014940e40c207095003682000d03128036550f001117210b594460403420003007000164003801620001e5600c82c0c122140112a1400611540c009004031801003481160b0000a05085c0d016800c41443e40d0f1a07070a942d40b030718542141e00b980326100980e08540d080101c0e50040c0c41d04801544103600070703000303050305052070000146601c0300198108000c0c0d01025a0902140c07800d03003182c412690103458100d003100c0350b1038413100841c44000325560200045081c142442041405a424495908003c1042c07065090011085031207500400c205041d1445d44004402c1d0091404003910031402d43d000c0c145144204058030709054070b01100d04009090301b18a8050a09004048254429051901c1c1d598100f002142c295444043c024041107840c40c0b00c181d030390740104020369000d40c014006554440c0103144010400f0401d04c01207400c1440c0c0340004d80d103503401405481c01120540050114240b468003086000d0b04141c81903603014104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 793908642 1250 793907392 793907407
    0xe1002030403090b130b0a360b25050307031e08010b1338070f020d1e030302120a0c0e1509040609200a0503010302042705010b0a06180303080c 63
    0xc00c0c0252152074400e03500c140700103d550391700030a21281d030040f20f440c1854160441d842401001001c2013030b2440300380c50762b880d80181100f00c82e450070140c44a000c2e83c140117500006000b004401030849a0180e125540b10aa418152524160360801c0c0400000e050800600030109003000400c040c806404a540110782c481c0000140c0c0708d101517000c1c8802443c4400307a06d26a50160441a821151036401401c05106032621100c400d6481c10087c40791031190003403410401c0420600103664400c5400095003951890040c000754054028005010b400d1400544811811300800d020344640760344071035901004c00c2c00d00075540600d002480d1108004d01c07582103152628840c0340001c000c01140841d00d48861050f6a40c3c42d01110500c03110844104680b100c45500842202d04403a81a58001083c0340394044000740c02240c0b5900030003201600c41040c05108054000c0c00002078103c8070b262034940d50b4541518004c0415a0400c2d0b0b0f2207141c2800c10119000303514040c0d006482600c1145407000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 793909892 1250 793908642 793908659
    0x40803040f1406060117010f03030513150804151a040c02010b120106050117010e06150c0d09060311040503100c0207052d040b090610021009060e1002030403090b13 72
    0x403502e20456100404000045d07900c9450516440d503400d4440c030480d41002a040200c00c02404060301b071201c0090101d24440000000c080101000b18100385003501889006011a5055030103460440d001500b50317480644c144070f0098502400340702c0e11120441541404040e080c00110352042d035507100e40b090066219150034800c5c00748480c0001690600780400549030500b0074a5042d0031100403001805a01000060b040d0000022200083c3e03038507064940003150302c41c41d000a140ca01844065150300c0390410810400d40d196600c0c1070008010b03076182004c45000324403c00c2d9040d40312010780680000e69500260061400b0320685244c15200c1c0e000c070b003082c2040001c66842a285400c030b8440584a14401c4ca0502e000700d5050048070f021b0400600481809800d16100d01120205e80c4810750081081010340b0601c81b505018242180c00c1c407400a100e00004084503015106d80103980350170314400c8034429a4507844900d01141807000006075030300456000e054500800c4400b0a0110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 793911142 1250 793909892 793909913
    0x307020f01090923151021020a11010609020f0a110f0a150e070f0302010f0c02130f0b040e0a0f033e07030302120f04030c0609030524040803040f 64
    0x419800d402e20728603040700003d5440c80c0000e1540b000c0300030a04400050317036a1510041d0045075540b61015802c080c0c0100316000201050080782c2c0c46100080c1320310310a402000710f20a102070700008204090f990b9110dc0140d12551b4074141040e01c003007218500380c5000d604100340100359001100e1000c0c030500262440c3c240180401d961030001d80403c510030448a00900c800080700303202801e8640d01d000381c045080041800f0084c103000f40c840000605520814804940741c0c0c005201205e44902810303084001c2c80c8010580b40e81c2410082031101ca81000e00440e10700e44141001450003004546610b03010340c8908030110100301012100411840542103020300700381c030800024a800484107000030300c1c81608160005250000202080440e402050840407000b00303808580e81d9000038030181d0071034411600003d045c0100c0210120301030360700007220402d882c13052080b83c1c2082e0505000407105080c0440d0442408c00c01c10000b0005983e8002a54004d81319004242c0190200d540c1c884849 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 793912392 1250 793911142 793911161
    0x50c030c01020315030f0109020a0b07084f0909080705060f0708010e070c0b100308040b0405100512070e010c0b070e0f042c0a0807030e01030614030307020f010909 72
    0x4441d440491100d440c0512071409450740350300081023001c103c1c3e400b203041e9200910a81c440030300f01069400a0101c0d000855114465581c603503051038580d074001410841c230303c510903504400c440c0386800824480400309a444c2d102c03401200c040d540341c005200c1c080c0401c0b81c800c4550034004d002500000b902041141d004524890b840200fa1524400c01480c0010507400007000714200760a02c43c0580e00440b08107005500044890016070300d03100c9410b030000e242c0e84001d0035090001800920092410060002d0703076422205e47e0405543d0b10400c682038001e0640b00c0e406890800080303020203000b4071210034000700605150040c10b165858000401d403040b50014023140000104011f01d01d0110320091540004507410030000258280740d544c6608180211120807032201c0103c60b44440070000e4025a03644945502d42da10010b24000345000d0840c409240400c1c1440380114031621004000c030038000c4081c00031030274a81e144c0c08010306c114016044505004804c800030804c04014084c50154 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 793913642 1250 793912392 793912411
    0x303040b09060c07080d050723030a050105030304030c060c0303061d04050601081935040801050903070206031906050316261f15060c060f1b050c030c010203 69
    0x41c5072144000e801c1c0b40d0003d0011031298001c000d640001515102640d0850300c840034005201d503500441a2008443d0107500c00d6604541c0c00c540c00381c2507241c00114442c020010782840030b030360f0321024959a401240401020b1100301c0034140201e07881084544421130091501040d81c9550712442906400c010340c542c2400040c3d00c0030081031101c10000d40e40106207400043c03c40342c11400c88210341e41c541c03160003050798a9080c103802da5103101050507102a0103504a0400c80803040701010324991161007211007a5081c82d00040035608080255101990058442480d513603500303918040f116640c40b82c4a42407582c40314007003940d27102002070300c0940c124590b020b03115604000c42164001031a100040004c0800d041603d40500045400b0304400301140d09c00840d5400650900080c100400e010715148020070070006449034000f404580380c074000c200070800c044c4590b90407415604400c841202c41d440f4100c1c1c81442905c500010a0740c0f608100c00d0702e040026002034642664000e4aa8000303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 793914892 1250 793913642 793913663
    0x170f25030e03070e0c0904110a02030705150c04090b0d06060e011809081803030d020304031e0f0e131e0207111002070509070c02030105130314180d03030e030304 71
    0xc0641044010310710407011401480c00301c2c500103180d2803076040103101c65199540403032000b0503a2038607004200501c0c4809825611400ca800d002541c80e04803150a40701c5109400007a85400c1d21244c125005a840d0310440d0310301818a51400c014103030243d81d43c0c1d00700803462110004a05544640400390800d815104c010b0b501d80302c40106200800959080e24520f0710f8004000a401f1400315425405a0688034900040d00c40000b4158010f4111403c1da003800041044101075006040c40099008038000d07030307003141072030804850114001030802e001c00d0b40c9001015151a1010100d008881e600001080b5014140001482c0c1180080e59018040d0041651400c0000910b2010b01c42e20040d504c201c030703640e0a240002d42d200000e01c589400bc0301108017048015104424103c99160003900038084e5040810030000c900304001c0003a40081c440031001940119488211200d107400c600590b0301d08043e000401c1481545560110145503440042030440e8209201451203103000d41c58582 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 793916142 1250 793914892 793914967
    0x180a180e060105010311070f02040212010308040302100309021e0307050301020423120a030c03200307020f0915060d0621030905030111041202120f010b0418170f 71
    0x2841c140307040c2c10250506040031103000c040e9001c8010b03922816044128000c1342201c9001242c000c3c41608031806034085078000110070300c21060001d00c1224801d40742c004a4040140c001c404036014030030021351002c6025401a2444050004802410801001c2e91031041d6130300f000a08a174480e91104c0004050200c0148510444080111401505691201caa504030301d69094039841c00d04c00c02000c1c0000c036524503080c90f01c99811800d01520907480d0140314001c09049503503d4110f2030b42203114007042103484d01181030520089002c0c080c02c400b00a00d43c8911410801c0b03d030000e42c0d418130099503e02c00081c401c00740c506410f0401c0d2101600d050001003904000b0f240c02e0590304214001c0e0304041d51820940208812642100c0004100035944c0f01544000340002408035001c0b003540c40f89281902605c181940f140501c00000c4030200001301003000000040c11003044050803801c0d00510100515102e00c0060160882d415400d81c580b480e215600d800c200c6480c1c440c0d00c040d0071303050f42c281c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 793917392 1250 793916142 793916171
    0x16060201060b030103210201021908060306071e05070302150a0617010606020304121406010b030a2009040510031a0627010303050c0f0a060209040506060a05180a18 72
    0x1500580040b080c540e195604641740c441314020481268074403d00e0900802404a1007075041d560544100c00340c000d107034040032100803d4401e043d40c0c041c1c4607001c0d1501140300d6501a0394400d111310809250b00503801c00750301055910b6040301c0340c1a0250f00441910300b20403e0070300407092056503074036000100141000e5001004100401f40d07000c00f6171400b1000e00001c0d40000556007121f1146107000d030314450038601450b408450501204092107080004512066a900a1441aa0300c19405c0100448061385040c1a40b074040740421001c1080000c6050303414541c0105501c010000e40300511142e0701c0c1c1d10102ca034602812481c1c4001030420500420f807074410108035406d20080c01b0201c1000210019048440041c8002018030000051901d50341c0e006001e9062000710042c152450505203052035400703503111001803885903103482d000031018641102500d501030740540e40c0d141085510074041c1c0e8000c1e24040c640da440000407400049100744c80242d001e07001c4444001003610390075054078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 793918642 1250 793917392 793917401
    0x80304030b06060c0337020f0d02070317030c040e04050a05151e071e0305151017090109020405072f0c01080a2a0207050a0e0112031116060201 63
    0x2024030402e0300f000400d2030300d100041550004800303000481d0801b00c800e88001c005111024110901d08030501d04088119008070700d100c28000c80c1001d403007002414060885e1505502d00008010315180000c811001000344095540904402986c41c5040e80f116098900c40c0c504031000c5541d17030f000d07070320400c100482881801008080d101000c881741c14003000441299510303070390404210808100149503e88079101240440c0c4807018046000f044411004002c0d040480c0c2d0161001d140c40507401ca42d0070300031041c0a0300041d5a8440442040510f081221380401130650402503494919450150782c0758401e16002d0115912a01c00e100c40e070600030401280c4801560042d0b004848100940c0300000c0744e0380f10804c20919003400241d940e40e06080061800d0300c20b2813481c1040c9141ea0741d100d918400c900c0b907042c1c0c4903005ca41415540740d080042d18005801091210341d8404010840d0140c1d200ea001310951083c2000f000425075001901d2422075103044080030f040e90410100b049940a108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 793919892 1250 793918642 793918651
    0xf040b070314120a0f0b090a0e2b08070e0a121407080709020a05160c05030708030310150e19320f03070f180b0607120f0207050a080304030b 62
    0x4903414010850549043c0d440d000744540142511202952804505a8030120764003030010300b6040e46040000554000300188032064106114a840c2841150901c2d50708601e502d0050080288542c071841040f0380485e40684801c0c1807091904c02e404040d6950000217029041803400c4409c01d200c40d0822080a1101100302446900224801d0007117200102e418000c2e50315580016940d0b5090f40000c031002c0c0306095000c40900b0040040b00100460412814106c032030403801c5524664564000315107a2206540011140c10005070412200d08901c1d0400d510501c07038200450401044404104000841e03800c1d91180007400c0c4040c01164004c4800d0160350100048030840c0c1310702c0f517050710400100c14040e0b5100390344590400e4400d170380400407500540340c4140d800b03400303a0f982d8038481d09400c00030b007030420701505003481c00c05641042411359801c1504400b000c00510301140781a1480c0d00701804220841c010317070001040c2a140c1100400081409000440d561071441c208204480c4c0040c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 793921142 1250 793919892 793919927
    0x80a0b060a090306021b010609050a0b09010f050d03170709050109060309030c0602030a060308040308070b0106030507020307170906161b050603190f050403020303040501050603030427020f040b0703 87
    0x14807040240c2c00312448059a5010b800183d44400400050031461070720b00c84081558205000030846a00b144c00c0180152030a103018060500d10300200010502e00b40110f601d0340c600110208044d10386441004100c5000f0301705042c802c00c900c07090f020300c803004903518400302d90120010001560b103c80c05c40300800d543d103400c00c040b05c82c0340d034010400c664904001d008160084041600400207600c15401140d1000142e42d44070b6807450510070b142c0108200740c45003500da00000460602902800c1c1c450501c0d540035600c1c0210715511580e0b094040c0e400c840c81d400d030910050300d40351590303001415410040407002c0c0494601c2d02e4000340c0300d420729011400402005004010a469003801d80e90400040d01208610020710f004281c010401c0310081400c0604002c140428150003100560055010b040240581d9551100380342e0340303228600c80c8001000942025103070854440016100c8a48a8400549002d1000701c581c02241c02641250494280000c0c40303500300358000003000019031189 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 793922392 1250 793921142 793921147
    0x910060329011805360d2303040516080a170306010e0d0c0302040e030c0f2e18030c020913030e0f030a0b09031216050d1a04560102071203080a0b06 65
    0x1000ca1f5090030560808a035a4041c000c03004c941044010703c0b169801019021a00d501107075a40012640ca02e121201a00c000040b0704080f0346401510303084920613070041e140c0d51500125642403140c1c00c040c9840640c1c5000c0480380120040c0e80318060556a0400d280003141c139880c14001c21810000c41242011003a4000402d00c503143d52040c406409a004954030502c800011141c0c0601409101210040e5902c0f200704d0b0354205500321000203103c2e4003e4402406aa8840c3e891044241c1c200350090f0120b04941d5660a00745421940c041480401405031400a0b0302a5111b11110400362a040c440340c10214207100704540e0403104c15844806040c02080701050000054418840d079003102600c0c94444401d82c5100800022285603c04e019004100c40030608402a80150940c041c40c07400094014410400310342032605034401c40006040c101e51001c804084032040e0a03030714000c80c1940240040000d00700508694111824003d031a1303085589000034001d401c03a04010421031003035805 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 793923642 1250 793922392 793922417
    0x911040e030c0d0e01021c091701022a03070b011403060618040807080f0310050a05030d05160302010b060a0c050601060504031a0910060329011805360d 67
    0x30380c00d05440b843c2d04200340c020204000403800c012601d88800540301103866040b04943d400034920b0101c0b0340f03115142109410b00b9035014240d00c1070340c5900540403c2074500c04020304448400c0000f0381c01800c1200d1030480a0b41d070322071080800760b210341d82441c4416000101824103011a40d8400e0040322031032080d03080a540d05801c40c8010304040c2840c079004c16564104014a4103c40700d241011700c0a0303032646020200c0c2080040e2901804d030060014000000e01810b00144405502c2503d40342c00f03052000701c0c0748180c01c03d1610f0301d00b81c04564036030010090356240d000040048071066655000c103800c66050240c61300c42e06034014070420604110810108090b5502c00d000000088040e401030788609440500d003403412002004010702c1c2443c00403c1110b2803008100a0000411f1029941070807603103621032900034840c1142400090010705000c041a038401c5070b1103032440d105c040580d034108582001240e800c41c0305a13290729001d0070b4148204010030042803103203000d01e82103035031680 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 793924892 1250 793923642 793923667
    0x5010f080604031206050405130302070e13063c1b1713050f030d0e03040303050a0f090f03060f0f05041e080409150e100806010e060f040911040e03 65
    0xc0100040c0c104041c4d40c40c4200c0107482604000000c01009000340a50308016480c1d4003400034003507088000d4071500d08002050b00015111502c9540302490754807152170641c80c0c400240c4040641d00e481c1c05006065140082140381804801c0d40381d5444e12101402d540a01008681020403000c0307080e07100d0401000c866611825214510100b4034898406840388511954211a03c142c000d0031801944040e0142c04400400b07024488cc803510706014019402d01042d4603442a03010150000b04c08000c081c7d5818020700031020b10a04c945080d40c51a55510b82c10b0120b850140c00450314641c84005030b02122451b4040c10040720a181d80801003814255100144c84540008004002540d041070b001406140001d0368010810303d00305003c20034034240600140134460055100c4503c540001c940c4200f016110002514640c0e8000c3c40d459081800c0d8210040000f0481a40301c500c074861f03e21281c585016290501f0f11520b0004030704070080c0100019221840040d03a040c5d80f00380441703c0501da = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 793926142 1250 793924892 793924903
    0x81605210a02030a080919120222090c1a0909040605101703030a1803140d060b120613090b0a0507020c180402030c060c150601052b05010f08 62
    0x41460311411000c5800030512810100c1080d03010703600d4019145000140400d8000500c040c1e0012034607501c80c1d042400c0c00708801d054900030f65989082c58122040182801244000094540d904007885244015084810323500040c42c00c40f0b2100f0781003010400381c50034030940d15141000000881c01c00c480300c4041224010010b0001d08407a0320343d00450071010b48010442c02505540356110254215620301c03a9480d8016100c0002444c80c020880c2a0040b040442c2c4100950580c2c1d1521860551082007009400a011107004240d45d00c40001e69050b0090007012407005d006080002e510f085001c000000716900d2482d060f50303040102200000703400d0165075600c13500000c00080e441d152100200e1030078191710b030b09a4004a4400c0f901410b1651260040d00c5144214219803a042880e030038000c05001d00c91b02d40741d40340c1c040704040d00c0c00c00303400c00b005500c90b0307041c5056410301c1031813003204a42030700030010058942c900c260492860b9031203001d00c0c0d0144c0080100105a6441d0103441540c4c0c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 793927392 1250 793926142 793926169
    0x1407020a1208160c1113020403120503040203030d091703011203030c021c03090512031e1b0910021606120e0a0206041806050603071115010303020d11010f020d0204081605 75
    0x1000000406003045550405d0000d030801c0548450100000d10b61a04000c0d0b05c45d00003542d804880b0410050b01c18881c3c400c507481941d001e8040d60a04840c0d50504c006407031000d80c11101501d08900d40d100a0101c2c0740950300070504240218401000c500700501224001302c2c1200442d0803403543c440720000c1054107611801030511b4001a20f0700c1c182480c0b4141700100100c0c001c80d51000003880640200d240802030764400801c00f450090f111611910988804e61508102d81d10040c041035940e49800c02c402c143c5001140140d401c42c5000005151090040360400004202042401a00f50801d03200d1044022600401403140e40da994000071858055407203800010b20042694040381006508400e000301006411151070b401d0000015242c1c800500341f081c400c0c4200000460040d0072403134868100e070381540150500403080c60003114401d044503000640c2d50340714614601c8800c031074401040c0304111820010384550a084181c0d007001d02c09501e0030410001040f0501040e990b900c00400c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 793928642 1250 793927392 793927397
    0xc061b050406230307090501110304060903151d160503211c0606050d0c051801033201080616021f0e030c0a0204052211041407020a120816 61
    0x520440d03c0b2402c2070a180702d40b046507030358004004d0040103500103007030a0950304241c0b0307a6032041301019462541d85c050782c0310b2a40001d18100007000800c90071a500098071500e240d0104243c40840c031400c219040c00070141d59640c1c030480004003169000c1403c040030b494200c01910000f00040440c15009119103000794010703c0015442c82c00354603078401d42181c01c40408051100d0f9545100c0501580c025105964440781404510000d00348610b04139050540310b0070340041d1024240c0011001408901891000c1400c440360100e4103000300c0c1101c0408402c00e165142c815070416802504220f405003020807150803205c0c58028154004c111403103250350341d0f8580460320803040040c04c06801100d03103003126030100040801c2440408618400010b009a0341440306480780138056003851080c0400c0d642e0000040f2071140052591000b0700c041007801030005c2000101040345a91000082e2801005030b81300103501030401c400070807089010083ca0900f070405140c51403941e1400444c0d500315a04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 793929892 1250 793928642 793928657
    0x81305280819140c03060f09071505120603010f06080f0106060804030512090703140c01080c1608030c0909010b030f07023d050c07020307090b0319060605030604030c061b050406 78
    0x48502c00c001d10f0b18413000041c11981c082c2004031121480103019107054006004102021030200045038900020b042d040c0d44061502d026020320004000000d480c00d0742c9552940e81066842011b4000c5d440544005005880304001445925085071010b0340710030144004202000b01207500207058030000c003a0304e41c0845041c0d0b44d4481e12070811003980c1000380001102080409550000903485066520a0325005004e1b140c0840f00c4d805030107509214401c105180031120000f90020028580218643d1946800d0003403c50005007074000907007028441704030101c200815418141c0400c0e801a410707001030300340e40002c0350079049070010750b400b481c001c82d0403840c5c20a202205160307042041220071500300000d0912000510060380a404103070f00c24400d81601140e4007640d807080e001d8030b400c0140100400001603d04454546a4030416030320240d40f03023000103050300c040c400c1d030b48160320a95038407201c452645002011103030080c2d03030b00002000320441c00709150b402c03508403410343c0c540b818040c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 793931142 1250 793929892 793929923
    0x6010302060403021225152f010204030812042a14030a0b070207260709050c040305060108010c11030c0a02090613090803010303141303081305280819 66
    0x241ba0141d1501520f0322809418009003c2c1c2c28003c10560980c2c54640b100b0307066000d09841100c100762011a0002c0c41280320503480d402c014012804000040c14000140c10a41d4a8039801c800fa0012036040c849250000100010441c0503986c01d035240c80000740356a500c05400b405842c004146004622030004d0003e8941c0c943c2d0703820008000455484098891140340c1240c0094548c4201e02c03030305144200e07010f085003c441c2e142405040c2c403460000281105440d00c1241e00260001a0224810800402020010420621105018100c203000100f900c44000e00b006000841d100c02042d91504103201c0d04a94000c0401c1030740645404884400307154951100145400e02c009619402070f07403800c0c0e40c0600f0031160700059030482e1300984030030004c500107203001ca102d4414032401b1400c1d107170304240c240000b0789d410026180c150a4055412070440e203400218511000f903021180b00c1d054500c0c2340d200c0044042074001c002d0002d40d0040c2980101840000f50420100c10700100281e0317000c0c1c15207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 793932392 1250 793931142 793931179
    0x1081b0f040216060e07062111070b09061012020907080601031d010b0312090108040803041b06020c031608101812080708060915010309060b0a080106060905030601030206040302 78
    0x840c00101010b20070383d4080e55500c3e040300100b4918070380304814012039600184041c000d15401145601200788000382409480000d0000c040380d182c440c16451050020902050301c480c0c5c1e140c420900390300240511b003071850344203440c1c20030b0390b000d03913524a910014400140c6070003903030039004403090505101c26151400180c024207022074800340c01074103000c100d90b91000150844501c0303000650a6603036403186422130035035038880c461101c1d01152403000440c001442002c01903a1083c001c07a10052000c1380584001031f80e41c020780c058001684840050a01460148400c400e2422172540c207000052a03c40310580304d181c40b00280e0140c55035141c1c000892a40e900d5a001c000380d000105a1081c54400c0380030780700d00d009844800002e04414001100c50030b10020040c0600c3c070313410280194010380c200450180000308400c94172551a040441d0301501d0308020b401c007030303e49000046481400d001c401000e0a125030f108600c6907000c0c200400160700e400003103500344d030b406540b101159821480c40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 793933642 1250 793932392 793932397
    0xb090708010213030b13020901170f010603030908190b06010509030a080a1817071211030601140310050126190c090606020c0f040203180a06060e01081b0f0402 70
    0x3a40c000d500025036112450059108102640e218848501c80d90710342d0b01501d4500a01004002c0d0080c1410b00180b01c0010154000d40c5408054421540b43c030005440c1e05003034038800d038012004170301d13110341c00d0003184c1c002d0042050030040c81d4000b60f0038400503144c04810540280100d818003000203100b0000303032400d11900c0a810b81120741203030358a0800c18010580c0e42c05c0c40801d21038000c855004154001d4041e41340c205101c008000700b01260034140c5104a410b0000c0d012100c00520303404696440d1002e116090007041c0c03100007007244040f03a2050600301501181e81005c01844c10005201c044610f0034031081c22000a950321100c55603114809203880c5c0740300d00126444110552803070800412003a03507002e541948205005042e900e44083c1d07601c1d5907402c2300302d0784036012034030403a52810280d0155074481c5001103044980540d103102281801c10714141940c60b941c07035510500c50055184280d030300503c0f00c10300920300c0c160800d030401810000e245076144221001e22940b5182e9445406 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 793934892 1250 793933642 793933649
    0x16060e1c081306052401020d0801060e0d0213090b070e031c11030c01061a09130504110d1a101d09030f0a03090309060305060117040c1a21130b0907 65
    0xc0030130090030000d01000d620000c04a07a4480e5134564406883c0a51003c103078003a8040180d10b82c0e80c09a424101d065031401500f07100b40c2e822107101c20020001d0380e2541c420300541040460300103090207186c00c1944160900600c081c1c148410002e0440c91038500098000180401c00b810607425044500221502803031000c2e051400d04c00030032080314005066200700300302c0e56084006542c00510240c980014041e00c0c65242d8401c0c070380480040c01800c5034000c02e40c4184100c05081c6900d90020000384090321140c400d98405018a500c03c903402e5040f2411600300b0028a90110201d1034151502803002c00340381507181b041c2c030110101d031a9400070030680d15202c400120070354a4005a48009005010724001034001911800e030000340035001e031140500411041c0e40d0388070807108513810b001901201910854941e0080c6e400040c2484006034060800000c200c07855540b02003201c005a00e45804200070422124100305100718504d4101d44c881200d648003001201a075140c014031810500300f0750 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 793936142 1250 793934892 793934903
    0xa0603021b010615020c010311030106080403030902030d0201090215070b06120a0203013210140d0c0308090a06030b37060f02010e0106140d08070816060e1c0813 71
    0x74404200c4901c460009213048096074200c0e4000c22a040044003682c0300380c000b4001c045d10400060240358456014203038002d00a00380458480d085c0c1d808a4903046902c400180182d540300d04520842c0780102030301910b5404603080500305600c40d2504500c3c0030000d4a410310801f540300441d010094140b240444068004000300007500c4401c12192039003003002442c4d0704c2c0c41c60903850070901c0040c424805008149000c2c1c00b15040b405c1182d17203040803003000300095201c020341080d41c0004030007030058009540300e030808a80360380c42d80c03084c0001c08041c1d800400034582031440c01e1502e5101c00150240340c03d980c1e10000511051038950003a010640300030511080c0030450007040060700500b84074807000455001304610041c00d400c1c2401c8910703e0261101841c803980104406150a00f07281c2080fa01828542d440c040b0345a8510b04582e05c5440d4504032204104540000e210703103807041354041000740010f440995600c02147e0307054102040315609004000d4086405082e191110002166200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 793937392 1250 793936142 793936151
    0x100c051b1c060f0b010203130b090102100609091a22020609040216050705030c060906180a1203081b1204030917010603050d020f06012d0e0403021b0a0603021b01 71
    0x3824150b0150110410085541c1d08010b00560b00f54800011107604804141c4415001400e04d102c099556101044803811403069915403070050b03130a0322030380d0000c054181001405d081240361407042c00f8010710301070404d6180b900801c031a100c00040f07011048000c0e0214180e08000300d1000a859010781e40c00c064015201144545801c0c4da070390021203201d80107008403050380d5030f908201a030b41c140c0381c03041d00c0d00305409000102e51401d005014040300207620a1440c0c1147e84100440c555139001da2081484042d40d0080109150300f020f51640c018054400e102400800001c01b04075a109500400400040c20000101454840c0c1460000b81c8116801008030b400301003540c0d0b001e0034107404103640a0140c4801c910b2540e0000401c89100710300d46004d0800d41e0301e400710382100c62081c00c820f0700c090024a0a0b114411501060b41340207410b400310b000280341041c2c28001d1510788120f00ea4216102015403202c00756a600c50048100c4085282c0580d85110003404410309007074032808005190b090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 793938642 1250 793937392 793937449
    0xb0a090b03070e041b021209030304090e0d11031602100c0503040f1a030402010f0c0c05060d0c020d02010e100c02010b090901060302100314152706100c051b 69
    0x2614202684000300c070280000d004070059002d03510300017000000560b0241e00324401c0c900b0700b0760180c03000030001026642042e82c1c5d01e80c00c4059448100555903a600300b803601000940c4c00191600c2c1000c2c90200550903d900342140c590f0240450301c0281c4942c0440c03605000c4140300d2010900b074140d00c0400c0d6510f0b00da40b000c1d00003010200703000e08038907080784400000c03480054005481c851034050352040707400c4000040599803540442411b4601d480c0c00280459603880d46001031807112401ca0f000244440c3d90030009090081c94404841164180032800314040c10000c0d04030410040d9040001b03004a14030700503401000000842e507001484181000241d000640c40380381168001d032114101d4401e071100031021611000144410030300700c40003040510710841880d01d80d07064003a0040d429074440b50180c07080441660340c200e50594050f8108010350401d500e50130701c0150316003040b00240300165140c41e140d038040e9031602007068049010301d0b25603842d13072078039522a007010595440c0d0703520 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 793939892 1250 793938642 793938647
    0x406090c06031b14070318030b07051306020a02010215070e0306091b09070504031b0b030405060a11090a03121e0809011401120b3d0f0803040b0a090b0307 68
    0x310706072007001a00028902070b60040c003a520349641140740802c55031805c0000c1c1c2e01510000c95814081c0c0c51a41000800700004040354502c90003038142e0744545840b1f00b0381200c061038000e0250000300842d00001113100c0140d80010345000c0c0031a462036103606a81e82c0c0300c4225020040d0b40e036082d502d80300790700a22403d0400440d1010640410056240714155102c003444170805066a1010000d0310403c0200003041c45821404042060b407a101d10140b80e507000a2002900103440a03641c030380048042c0710aa1100d84501e04038000900714507800c05c55034000080001c5038501c4040c04072040c400c0d600c0c00007485010121410f910b80c6030922a140170410000348141030454001c409503203404540c0d921040c0d4110400c2c103c452510070003840580a83c0c0c0c07002041e601400318074007140e00102543c3e03150a1420810310b042001d00e444001d0740000c40c85071200000b40e61240340c40020000c424446800c0c0401120141c441120419907104800c0000f00c40e01240340d4810711510341e020040c03011059 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 793941142 1250 793939892 793939901
    0xc030c11031509011b09090b03150f5b0605040e0f192319061e060f1115070806011830210c0b010e0406090c0603 50
    0x1003020000c00510103040c0801440c003035640c0c00030b0081b074800e080810603c4c031542c200c03031445600075064540003c0b2070307260141081c2c2d00703131001302082c2c43c1c0318108040107080c00507030308801401c800d450b2004000f40383c00c03042a10400b00100c11103070303010526050185800b018603038211003031050722440036902d81005280c0d400c94050f00d040e400c4650045a00701c60072100c603500501780e03112a458180010a161401009000c025030b0720361140c0d01c1c008100c60300040c940f6124009402d40304480e01c100440f404200c40c0031b9009030700b01c0610f88010215103100d508a400580b07925041c14035203d41100300a075140e880b41c800d45c0000d40701c1d045011540e46042e00c91a4001d415a8541318842d48400300151800c80f040c000c1c8500402d031400e010451819401c41d8110f18a018030b911002c01c9103000c0884550100800042c1c0d000c0e8490340d454614482e0444402e20501010f281842402071283d507020b10400041c818041040c1c03604c0089014444103520001c0c0c880d90003206c080d01680ea8013170240140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 793942392 1250 793941142 793941151
    0x203070801091e1203020a120e0708160b070f0c030611090f0108090d0e0f030f06041214030f1e040c06020c040e06010b070819030b090a0b010c030c110315 68
    0x411560b48010030040120400c0c038201a40044d80300c0001c1d08030b082c02c030000d40085000354100702400c15201c1c800e064034425100b82ca92180042c00d4014181800245040310718107460b50031885800d030400075201c41006071a00e1070744c403081141c40300189045c00890050701d50006422a454040000b80032040500100401e18060702c800620004900055650000032200c0119603001008003402c5c00744541a503101e080401021031500c401301c803020030316191007600010b25681c40b13a000c1c07005004c00c142e044020350f10f43d4a0a4030115000042c000c0b040c1c040a001d9100754090305001c1040c841c548038446554480c8080494503505e000c0c00e00b9510f0811a1042d94007500800a0942d41c1e41028090a035400a4000082c60b10740d01e4105601c40960110706c09840203c028083c00a407506100c0b41d200a000c401e0340c020401142410400070f2000002e81803400f0030307241c089800380b6a41c0003201d40c15983d806040c900503001d00c0381031641e000040600360990601402c031070012031308000803006000307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 793943642 1250 793942392 793942403
    0x220902040507030c05090d051903020604061d031207020106030b0c120601020f070302120c0306010f182a17180f031e0313150207110108040309140a03020307080109 72
    0x764407102810780c00c0320f4080c4420800110200300050709400e0070080b805480d4032aa04454509688018503200d407281000c0460060b040a820f100602c0002d010741c0810355414569506070aa031400465504d02c941008122501c1200d0f0000700c0c01d0b4002e40c040c6000356001400503d461a0009454541e50b100b1450807041c2c0e41800085101e5500c00290132440c103607040300500245045400300400c40702000e100f60b120340700303208603c0899182400348074020301d405400c1061a074140802d0040d0340c42c84008110403140b42002d171000460340440d0341c010289000004684800305103004481e880103603001540c000d9144000c0c0204a58192010450a038450701900d0240c1c0b100c810007907c81c450205403242d000303201601e24000780e5a040081d60010a50110910100d00c82d5039901041aa42805084a184d02007181002c0c0301090000f00180d081c2442c000d0000d10741681c014050741110b0050380202040036020350303441d481e00101000910740040031225219030700c288007400b030b1642a400703c0340b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 793944892 1250 793943642 793943651
    0x903030714090301051e0f060a260a0c211709010e10050c070b1606110c0703050d09080d0f03180b09010902040e1c0c08190f091d130222090204 63
    0x10049411281e401807000030032480d9154980b01341e25141c040c64040721401d2504018032902c1e030940400c4990082d901c12440522864a04680de001d010000c400290003411074030702070300018846451038002c0320210385601d91610480d0004803052036a40d481180c01c85115400e1040d8580c03c40064204001c5c82400c94a03c039442d020700b01214020100d850b08407040301680240001d9190704103502482d00280c000e07050a04413555985000000c0e4810340340c641040c00e081181c90b5001d090840a081c0036070042940c400500c83c0103282464a010701d004140e40c0358030f10002c4d030040c0c22030b08291035000360313070049642011078445000704510f0300c08903c550b00e0f00b00d020b0100040424514400003400144100040f0605c0040e01c044d001c0880132151024108440d10804210200440c0d800e070860352100c02c0312002c4d0b14050071042c519000244560b040045aa008406102506602c01d401e10192980d02d41684085450741032a901c4009c0ca072814050340c182020700542c05002c0c1207000316418003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 793946142 1250 793944892 793944901
    0x80a02060f011202150a17010312120c05030708090705060c10060906060203120c0d06030819022a0a0801020a050d0c03060f14030a1205210903030714090301051e 71
    0x10003d9000025004031900c42c45070020102c900103410b00519034109504411081c60000030300a0098100f1202100310321080c800d0168801160415009101c40410200200c0f14000d000c0f804014581410808a80c00146c2d58003400d0140d00c000b4200034100340d4442c00704100607501c550b401049110000e02c2e1110000d10b81496001d10300460300903070080c41c80c0c80e20f04440301c03048400c000c00c07c10328101d0401c8504400450744c41000015406800283e44900c01c80407900401301c0031001103001c41d804103a00c008104c14090015070303102560803184a00c501880d0100e002c94203a07903c00147e6510202e1071440700c98008008044940d85d03040304008031498144250100d0741e0702e001d12400504048028098a00a5981842003490040c2200c2c81400c7d140d50f03200c00403402680f510001140840c0703200018205113448001c0300002c08080c0402d150058402ea90307800f0080c0820100241c000c030350551501000112120f4a0028000340440d00e0070281d42e50301100c07460501f8030480d01180009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 793947392 1250 793946142 793946159
    0x50d30030204090e190b071b061e090803010909060b060c071503091a1317040f090e1209010c050607023a030b0a08011505090708070f0c0f080a02060f01 67
    0x45d500c0f10900400441030303409503240c950105a00030030200900203d009000390b518801c445006070b9610500003c41c0a40c4125640e080c2c0000194100520a06080543c40054201002e407415a400000001440401c2d41842405040300c6200b00da0000d10025800b00340c0c80000c95960305442080e00c292074039a088040031011900c00020161100d03582c0d48000b00c00001484a030b0307411000d01d030b90f01030102c44542c582c0807884403003001c46401000d00040c10044580f4400b1940010484a4410481e5980c100103c82e1144121000c00f0041d600004a0540980c001c40d0301c02a030a400c4003c8503c0792404000103952654841721200039030303101c0110a0070395904d210800a8541403442900c920700041d1409a020780050302c2640d500c10041c0b000810b10481c2403064110042c9d03243c02020900e0b1030b000600400000251522007002a210100804940c20002021000245140540c1036520505101c090008111b074010a100c078009411864507a0005450f4020601460217440c1c5036607030b00350b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 793948642 1250 793947392 793947403
    0x108010b09160815030102030916091107150e03040f0612020c0c09071e180506040302060703050c0709060909050f160e0a1103090a03021006050d30030204090e 70
    0x22000d0002e840400d00d84040c0c4100d458a8001341d08038001680d4040c0c080000c1d080e81c0017285c40a6940e8040c2d00410036420303241c07070b18038000c112100f004c002c02c400b8850036030722074803c0f6040a800480302040c8656803c01e541c2c8241f41070450101580d80352034a030504002c2244c03035031207210001340e034100c54100740c6e036000e201300e4100c1c030f14000080003004405001d1001c2c3c0c400040c291024404000c410b4036040b101101c3d00102101c25648125082e0031050350384200c074049030490b50207410700f44424030041c0c60303034400c488500340c041c2441900e60941e2074505181424a0b00403000f8035041038000103600c0f00c16044500d40510031002c5e105403c5100c40c4013540c0701d04035040c103212840e600b5400c102401c50420300541090801c4404200c0c0c1488041500311035100f40d4640d00702d6803040b00340e5014107034180b2130004691b00c0d03640113000da41d00d4500025034603400f809010b40404500058003c0007843e002808040c2e00184001c0e40c1410301e0311074060001c0d00b00b4403c20a80c41d04007080071211600c045207 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 793949892 1250 793948642 793948651
    0x60f140906070201110a0204021b061e060d0c0f06051b06100b0706020c0d0521071d01030b0306190c030204080d030e1e0714031605011d13050108010b09 67
    0x1260b070400e22690011034240d4003411300810316000b030303980e8140581c88500040a030001d00342c0d42400d01e2800180c40c07608d402d100030814440e00f5001007801e0401828042c0468000e403086901180744916810912041c503e19804045018036004000072100e030810050b1100d44601082c901c000c04071182c0154903100c085414040911074440c040c0218104035001d80791560207000c006090256000c10b1038540310008110f600810b00204904c401c5902100c0402e0040c5c3c481c1c0c801e00b0071404d20074400307012021140909009000c86500341003259100354000750700500020304444890404208075100e541e440742c004115071f8103142050f142603000f4001c4400712a0208010725000c00f8171031040b0024103000e8900f060300c0c0200d000c909082544d03a504070441c5540b00c009000514a4542c680394480001682540603400c061651a6004108140001114002c0c209480449005089403007601c00400c1c21680c4640e0b0030380c2d40c00c010403903503000034144c1e02030100810a205440080205101080700d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 793951142 1250 793949892 793949899
    0x50f060711040f020c1e0c0d050a0816060516030c020f0604080705120301090e0c27190213080c1503041b0308220b03010503030a08060f0307060f1409 66
    0x1c01071901800d02d90301822410714010001401e1943ca90301050030800c080c0b80010551030b5403400348681d03450070300a29038441d0040360280d80040980d600c103605e8510481000d44010f80c003040080b4268814880b1058840e03002c0c40402c2140f03031070030b034550103080024065000240b80240703481e44030f03000041c0202c484c11481c004080d503941d2955022450351107400308070f603540101d00134802d919282d50040e60180c0319031000801c42e00e00e1224070600c2d01e800120002d20414200d01040307070400c04054114a0868203d11101445c2d44801d8064003029070200c8140c040380c1300080d00796021040801800903074001d1010744803070000c104100b00c00340b08014214880c1070001c2001c180028400c07100e02c0d0074035400b02500e8108690300d4503181031b150460b81c80301b03600f03c20304400100b00e450030007851005409010ba040c1d04650414000c41d03568044c4000780000d204d0003502250596807103990607000208004c04891b8401c0e21100018103619003000040c2c0030549990216000c41f4908013603407218071024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 793952392 1250 793951142 793951163
    0x30f0305071205060607021503070e04060b1903090506130c0803090927070e090f010504111903080a050403030908031611010e040504051608030903060601030e030f0a0801050f0607 79
    0x4034a5600140000382038103605c200100f0a0310010b0300d444c1c1c100316a828480e81d14680302c4c684881e02030f005485c442c03805881980390541c1070001d180c00009448050800c4040440111f010b803005170000c2041c02c802401903c9046c08000d0040d8070318001c1031040d48580450000b584e607071900255603008040348070b40d100c0c3c80c42000a82c021444186c0c2042c184045010420002601351401d0400c1d0085c0c201c0c0340345e01d440e041000702c0050704014030f1101c80b00e100020002450581c0394444212207100740c0500c10200310301c0940c1c10100d54407200c0c001e55000007240da81c803840346502811507031203440202c000c0386c500100025810008800e5800b42151078005942d594003a68400364440d01075060141401603682e0108025101c51143d01d200341d11403030040c062240005801060180aa0302240280d80100503012568074045500d540006080c2000301d441c10541503541d0650060b507910303202d440004140c2c412203c0d4010600ca04a03a025a101540000d0304020b01c2020302c17a5650242125001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 793953642 1250 793952392 793952417
    0x604020108100b130906120308010b03180114070207060f08060603040c08100605010219021503101211010e0d031e18030b06040606030203060d06020a0c020616030f030507 75
    0x1854916500c40001d20b020107119440340150a400e400c804001545543d44200500c440190307442648003130240c04408102040e06903900800e0141c0500803140d84040100200c1e0844540000c0d1000300982c40c402413160a5982e008030000040c04c0310b4107070051280590001e5420b01461240507043e2544d0382e0400313140e946009000841e1b0002d403044603006102e84c80021888000d1089110804030b03040d001c00c4040c5000002440c0107030f212444182008804d9580c801aa070b0300d440850b065030303071100d900d440396180000c00e46100200d0340000581d00300d402c056400c001004031400843c0300240c0342c0f08000c0c100350090054107100214002c002c83c080e82052050980e9034010070b0105819841c00e04500c0e03203820250341021002c2d50003110644c49980501c049803405001e0040907020781e00d8114218a401c03000181c0c0b101a40c2d9002d46200e5002546020240c8600c1c00076000c3d40d0050007040d079803030201812180350441d5800c02c0c2c002410301c5c40c2d640001c40c0309004981c0038100c213079640342d0555107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 793954892 1250 793953642 793953647
    0x1080406020715050408070b0901020301060f0e0a0f030312181703060d1b17010912051305040213080f0d0f140c010504030e13060b1c18061a0405010806040201 70
    0x5a002c3c0c0303400074120070800b1065440e0241c04d101c1c2e0700c14468540c1b2400e0910700303618105805441094203900510050003156031050000302c4c42c0c1c406150003003c2062540104240c03038850307001400d10a0110501206140e082140032a07810504a4200160740e005001a804031031895401440b00310b02d41c580f140b0500f2000f0141d50403901c0100032400f28007490380c4002908035228454040502c28480030800341c4503450301024440310480091200844554400c120035010302c3c2090f007480382c0421446140b056011403031000d094082e00c1155100c64502030000e600600c1c2c40743c15150b20a40c0c2c00d0003024074020582000d1408103485031801d4410003a019128607441c190200c40c4040d05214003018501c0034011030f07014901070b884040880c244c61040c000d0384140311a80300c030101e042c90000c00c02802038070200d84103101c0d00d5480c683c03000c0d40c5881450103000941d8800882c016510041d0050100c41d07482603546003052000c011460f40c0980502c02590000d11500b900d41d004107000601550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 793956142 1250 793954892 793954897
    0x60301060e030102120108100b032d0f2409012c010f0510060e03030a0203030406050a0e0a150c0315050d030c0506010e01080606040e1917040b18090103020108040602 73
    0x10341c000c0000d800d01c9070f480e8941380d0f583c60982c80f03030545034082c84032107a00343c0142c416001e4044043c0e02428a051210850340071564003005481882e0280d102180010641401105040c0006c0713401d40e809121100e96525400d03034024121142200d810010070039140f01441855240f54007000c0c4155810b51301c0c618140b06880b04804c0300b07555520303942039408081d403031712031584165401560550780c03c0c00e24100078446070710700300d109002e94000c0010320031a40d000000c0c1c90340591705c03020104142c0e43e800d810002801002c0c8945400c0d2140b901071904000114142e00300c4c4081d001c3e0104500343c0740c080101c05541021003510002007400d24117100c1402e008060819080c000e090200c20380c507199489a242c004242e003c030300f2010f008c8005100f00c1106000c1e0540102781103c1c00d000c490b90700c4c2051510b85981000703220028020b05030803c00c0140340804104030000351030206468541e18410a8425803281761510300044c1881071004039032411220b410706a98069403895150342c3c2c0d0b0340e641c80096 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 793957392 1250 793956142 793956167
    0xe070305270309041e0b0603070c140111030109050a110301062007050604080a06060b3a0f0b03010605060703022a191d0615071403030a061e030206030106 68
    0x3804100500e2202d134a41e80141e035503012104002c040003001c800e40300802c40d000001141d204140800500a0095100d100c1024044d02b0441c0034440003142d48005004000002c40d0045803a804400065001e0080d44020f1080c0b40ca2902801607401c1d81e80703a42030703a1000f405030b5408500b001e0305200442c886540000079040c004402c4806858440d4005059900264006d80300e40d0f0028040000b040118007501e402443c50801141c14001d000000146c002d01040c41d0041214035010302546000702c05540050700c1441c0202044104004101c00000e07100b104143c070300941c246200003505050000840f403e890f015405044011035141000c6055040ca001000c044c010303c0a4000c1d1030ba0b038403091241089025404554070318508903c40301080185521030b4154008032040103079584039400315a11700885004220740d034070858640391000280c03044e100ea10501c808000c005d40700c80d140d4070031410b0305e130381c801003002504080c07071096240501400000c5d0444001d00c0104481030080103c050b44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 793958642 1250 793957392 793957471
    0x2010209030709091b0f09020d020d0911040e0a21090815161e050309031b0109020f0303130b0702130c09061209020915030304030c0f0e070305 63
    0x1030845540000e0714010b42d64100c0081c1d036036502110402c000d1141d81403800e40807400c0c1000007462074041d02580c0a0a54402d17849400d800180c881d2040d10f0590458a00924040c400c0210600314200385038820a8808400c2c0200e180240c622380341e00001075021a01e541c000c10350901071080b034100e581c001c9424040c41c4248000c81c0f502040501c001c0c4001001500c0460440040d031409032400800f10385040c0c00c440a0007814a070200d00102d5413401d05c0c1c80c900e07443c1001d135986d07125800c041c0e19611507507041100d0680c920500100c0c2c440c040d00714444403402115020900b41850081503200d11507081c5507503209a410b00208003949800004e17181c0640020009840c60388070790200d070261000d0401c00f0001548240b070910510b0380054415076000e01381c090411000780a0750200d403004030054100c582e000d482c90720f012019501041260050766020f2041c140c0199903c071031030a10b54180c01601200441c1400040ca082e1080c441c2c01c7c4102144207000009001d64441310034110781002c0d50501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 793959892 1250 793958642 793958647
    0x106030b091801140405010c140403050309011107050a0801090b0f0907030314190503070f030b03030904020d020705030a02101a0d0b061f0e0a0503191e060504030806030c121903020102 81
    0x205913080d07890091042d0301482c0081030002041074000e007440b03200b030101003185100b07000900205400100f40c1300b02e45000e082440d2001000769031079181414a5000c40ea00003400c05004c501c104040d049035019510881c1d02d02c0003074a0b814905400c52604460310750499011500420100e07200c0c12402d109400304145003840c0030004558004d442540d0f000400101d44000140684554400d80e40c3d140d0491a04e010000e9424640019403240301c0c554009128640119081052030040e604880f200c0313520a003201c1d03031104200710107521175020040030020245040c85002d521030708442102d0318080000d00341c50740d428060f540c40c5081034024041c1d075004280d4403d0041d9071240e07016090304070003868407001c01d03082c05142003144000d4039810590003a0414500071786101c01c01c0c1c0003100000c4d032080c2d80000075024118891a140c04142003e42070781d050406100174140c120700f401e806603c0c2a4141c400081c407031410300009074810031409000790f004c4105842d440d01320109210f00c082c0301c1d100151 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 793961142 1250 793959892 793959911
    0x909060f0e060918011803081509010611100c020708060f0907033810090e030406200a060b09150f040b061b07060f110c010c0f02091306050106030b091801 68
    0x1801c440c6c00c5104c41da40070b100301140c02c06040d005580c8a5004030b5400c80e0080c05841200820f896003030621404050000d0701d00d01051003c8103112070340180800c403000b00015004c0440c000c0d13940c18103104045040c0100000b1030507904014405a10804c44c22004090052440e0b4610308c540110110007204860060105490417074032108003009a261001c082d0014103041144600c1c0d550b01da480ba030711551404800886030705000c0180c0e400c9909505102080b4080000401d0710403031421140020350140075403c03001c102603940894620201a601c10b62250b5402122411064500b41d038140d00c5101c03014604aa880d043c0c0010307000342000f60840f8103000d241d421064040c61034141066558000880900140307504c0703c030701c00d0b026100345401c2d41c02040507503100351290400e96266040081120310082480508008010b000750701401a5900d1300c1c10380d50001c4040441c0c2c0048441038104000042c50300e11a0040c4d0992009c000c01440f0b240d02c8160340781600d40b0f18422100520354849d20b481 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 793962392 1250 793961142 793961191
    0xf08130f11010201050c07020a0302041d0d03020a080711062410080915060114070320030702180702190f0b0702101404030804021315060909060f0e0609 67
    0x180c00d264840d109030850003005000280c2035a1005090b440d000c041405500d000d680c91440c0c030012031360159400200c01211248000d004c403810134804065219414110020541c19030044c1202041c1c3c0d640d8000c141c4480d9000c0b502c1904003903805645070700c1b08000c101c100714418070903401d84050111000c0d2042004010441c4859003103903010100301305108000e1002c00600440d007005101c22440141031034403400281603515000942e421500d0085401400c0502a0086d0051500c0889040e0469010700317103ca0350740c0d407080340102d006401d0b044188008038101d2190038011801500a04040300604441848000c4421829101c603042c000341440843d0a00540c240100850340c041c01001c0000220341003518480c140c486414a2080108000700c1d500c0601180c000307038100e4003010b000501800400140485101025411003005000a4400c1d00182044e00720751082c101881803e82c2c0780c03200c0c20b0340e80c1c8520411120903140d800040d12482c0403050a9845040180300c0d50850405400c507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 793963642 1250 793962392 793962413
    0x302031209010215130f110603010f060e0d080a03020a021501060827150601030f0e070f0602120d0908070c030f170c1e0a0f0c1d070f0813 61
    0x66103103400007041c4441c2d5034140403ea40483c201c504c0d00d4454200020607618101c06a04058020503035036402c1e10810081201c00c2140034002441261a0b50311030b00365800d0300f0247c1c402d640c0402e120040d180ca5508100f212410a0307904008214202191720000343e01030741c0304034100411030003241da8810795000e004642d0385c003902d51a601c41c1c223549404080c1001041c0e07070f07010041030103101140c02000004005010103081c02000b00740c0c0207640300c420058000d40100320130a0b038404c1c1000400c3d4038030301340042d55100715504a000c5401850b0350f29030581e00e4520141d2101d007020001c1029040c880c5090300105104c40c898410b0078a017265586840c01000d810382c2048a00f4070b0180d004d401485180c8030350940120598946525000366400035070390707a201d016079103c1e089060140d0190202c0062014115180e000b034005683d250691070200c0c0c11848d1405000d204050341c03c140c29900b06091a0395106607995284ca81014504074401c4d289850000c1c41003044088c000340c07240000b03114051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 793964892 1250 793963642 793963663
    0x1e010308030601081b040312090e0a0b0f01181a1201060e040c0305090604021207080f011b020d0813050106090f0f05090d09091109120d090b0306061b07030203 70
    0x2510340d101d04102000600040c0050415076049040303504402e442d90800c03040b5000c5a0f449000405500e1781148280c50451160b403040c8400ca08440421039142842c0e0001e00b01080111915188082c941005607440320310317400401c0b8115905403041c8200341810860b00d405101c0f40d000c242c182926401282c0004000b60403420025140140c8501c0c241003d01481e11101c40364102072180e03280000e010b03503917010014030203441030342d54280e200400c580c14841803000c4d00d00030054070303103d2040c540307020b000e004020f03070006542c0c4000d00b081401c1440420b0790559401036079100111522490403005407002505c0d0155041e55031000009210805403250a40d202140e06001c180101d00c3c4404c04210350005100703041540149041c3d000700342e808100300c001d80d41907820010700b02074500078140c0e1740d02402080700d401c5855502210401940019849400922640c0e5280e00640311080c01c0070710300090325078980280041c0600c0c490080c0300c82e210311281c100d0500304e402041c1c0e00d03000a0304d441c80408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 793966142 1250 793964892 793964903
    0x12030b211e03120106020703050d0c0b061009030c0902130905091c110109211806210203010b12010b040302010c060b041506050c070501020f0c04050606070605010e07030b0f0109030b1e0103 83
    0x1808004009e0b040c00040d40c41039035410074141e007034403603214402a40402030009214015001c800030381e0314040d842800c041c54120604200030b0b40ca9181c800020b41c04186902c0f6007178500100001c03505814040e80c1c2c40740304d000d405004692990120901d4408045080800b400000c4040941000342480b80ba81020702540003400c0b0180400066800c142d0b08213000d00400022180c94100001e4080c50748088070114900700000140745d03110050360206507405841000e000100000c1d540086402410030880c0d0003c0242c10303030340c1e1420294498130461000902103089440c41070301207200756024240707100000d4008219451419031404845105030801c0c4040350012032540c40155042000b040600000c1c0000c01e2561011810075035540e5244410b82d00c60303a164400074070300d41c07541002d8465071607001c0c0040c40103503140d06485012050840d1143c0c000391502013603807040d242a0102c144500c2040c2c544913138880c1540ca9000a5140c028a08407115091034114000c02150168580c02940075a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 793967392 1250 793966142 793966153
    0x1707020c011704111309050f0d030c0504080606060d0e010e060720032205060406021b0901030f0b060604080a1406060603161b12030b211e0312010602 66
    0x4002402c64200c50390075049100c0c0800400c00050140c40620076140c504403400e50350102c070b025100015050400d8014054098021090109117001500c0c10150350303107480620000c24a07143c1110079018174401c100407540144045034043c28410020301c084c0346920004036000b040e50f002c450a640d00c0358120011a8880300c01c0001040d0f2202c0050ba01449800d91114140d0340700e10503958a0050800f04030a442c0810080003400828445800003844003514507921542d64080c040c0d25040c42a5110303282c0c912500c0741e1400c600d003004080307060380d52002d034045181d99281c50704110040010461500810b0401000c2008402000241c8000344507801d02800216209101401e00002508032405540107009100c00c1c07100100c0900e40000703103481c2c50000f0f8084103850103865220b41c0e00103455403003a09003466020f54107400001d0881029613a0317000b0320400c1140d40003403208a0f54150b01c282c0050303420003a8950b00701c01c617a480d0368803402201c2c14242004101ca0b40c180c03083c0c1c014030243c1d121 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 793968642 1250 793967392 793967413
    0x50a0617090c0d060f020702090c0a02060a152711090a080106150f1b0b090d0c022107030c0b03010807061103030103030819092301060b041203170702 66
    0x406034000d501c0041200500440707100c00001c2a003e00d881c2c40c2c0140007135100c2042c42d42007041981035507071280d001011a10541000c9800b00b1301640100d00f5179005024180001d90070341c1c024040c2c0200b038582d82000c01c440e1880d003110b00c40e4410742410780b0103c50b0705141946100c1600d5004444001e81c003071140e241e54425150810088041a42c071200060341410800c0015007510320640b0b0599148c0d06000c507101d64864009c0710902e08445c00c2c0c030702440d5200036001c01d0024050080b84210b00c0813003101c1324800038000a9419504048000758402d107482210000140c4004001040760301c01812604107a8072560340c842c50f480d030764020342e80060b000b100400046204204150061586040c00418100c140c410071380c591205000140502c041d03800403445204500050845c4603400794800c0214036528a010007450a4400400c4e03182116002c2c0f900f8040c1d0188114801c58840300f0300c40f481c0c41e250090749000583c41c41400d4052000c2400d041000400d00c81445204030700a5020b071410404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 793969892 1250 793968642 793968677
    0x2011409100e0c0904032f0c0a05040519020c070b0f18061620030d0906031d0604200d0b1b0324060c0d200607080a0b0109050a06 57
    0x3407400b076004007540310100d0280766444284034a9000750305032412822140c501446410f20504040300c3d122240013036a80719a071881d011840f401c100208031203600d11581d0340c00401083da0403c1d10000d00304a030881900e0115042a802000007c0c0c141050700c04c16a518820315400b80c022400340000c0789000030b511100e005620390115860801110010b003413001da0500014090218480100b48182c5c1c6404816084001310400304081801412034201039140301b001006202c280c810100800d040c200181c0003100021000ba01003104136008003032070341e01d5444288a102280100d0024220b02220302c400d41c1c1c03034600c2d43c01d0005010346501003190502c507445401c141da031110b00c8001024203000b4019080440c002141c02c1030300c0c0381601410107803d00000f40c202d20803118035902c1c42c4603a010300016240c106100864540c0d280c12801c906400c0708c102d980e01c80004136034000c00200d050000075100078043e8048003c0000c1890001c5520303884201080e40c1e54481d400007004909410b82071210f80301d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 793971142 1250 793969892 793969901
    0x212241513080102130b070c091e0f0507021504060603020d050f0c0303030c0f09030106090213051f051b0321010e150f010c0f1506061b0c060804030201140910 70
    0x110b0b034000c40c038040c840c01c4206103584450140d000c0116000991505100168452034050701540c80e08001c00380b41e0200300c0e851026520a040c601d80d041c40e00c401000c140b188070b1a0310402207500a80706079424040403a0a46100400071140596035030004405a22030300d0908180601c40c0008160001a204e02c080c985104007030300912980c0100304012825501201791403814029582564540740a240064050700e680d030000040c0d603102183e00c0f1105039064030f000b0304071501603074641c100c83c075028017058480309041c104201140b410082e250f544078102202229000c0c1d175070252030030b091715110710000d6082c107075080355900c108240060080d1002c0505880d00021101040603d0121700750105810f0243c148480d410b0080001c040030901a0709421713490480d5001c06c0c4012035192216690703004210174020381c030010b80080ca85003c09a500210041b03007a0b0480c0c802902c0d103240c444100c401101c010421030455413101c81100004a0000070b0b41d0041070003001814417608034002c40300460f0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 793972392 1250 793971142 793971149
    0x40201090f0609030b0c1b071503201612120e19171303060207030206180a0602030a0e030307020c0f0103060e0a0e12070804050109090212241513 64
    0x70390000c804102807500f2520300000c981c2d21180c000d000f592068208121802921409881d200d0110343d2002140c50210b40382082d1600f0b0181012940e1f5890070480171900661100790300e2505c009003e05071151040c000e002c42c101d242d0004105e068050307641080c803c1182c820f40011034040100354640030902c0c092112250f60510040100603c0302480e00130b0080c1c0003401130481c40d0042d00c0341c002100c18104440d80c1501030358032210303c0c1d83d992038140000c1d4042c5000341c0041c0160408282035101140182d501a1520402801440007070b480303141c02544080c0c0031610b000c2d500e0700700f20001007042c400b5600c01c0481b60041c00007454820280b1180b0a11004024101440c091051003000740d1142429002180040001900050030710210b142400703010710a14583c10114402c02080424801001590000c0c0e0ba01001e035940da10f40d140a90003002420300e071312485900061309207100030449190b0000d0008950b10642114400305104100e00581980d103a00c0c00911099540403085080006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 793973642 1250 793972392 793972409
    0xa09031e081209010c0c11040c0212161104050105030304090f0228020c030f0d0804020f04090c1e06050a05130905101d04050d0c0602120a0b180403080105210f030304020109 76
    0xa6010b076544400047c0c1d4283c0805110310303628403e0600c00b034400c00800555524030070040744e0fa008020202c00481403645000c450b03000700b11907107045c1810305002c1e042c12280050004d43c2814240f6003030380003a1068841502c016542401803400b00c06e8990601c0c0e80c1c441811204800e0307074924641c000c0c20310038001f44050113136000d0b50300c802c031018000600d480d8a195625018419469a1000544907003aa10507240d001d810003d1603014003900054480859800039003216266404102c102c10003089480303405c0120380c041c0b00086003180198018210212070305031400b981c48d2510a140c00701c540984079542e0b8483e0546062202c484103110003084480841910b81181c5480c1d92800c2c1d58050000da03000030810700980c40300c104200c80c0c0650b4003c9001a426080914140031960018002403420307902c52020030b110107621042e5680300c240515059a00c1c07030300c40da0a00b03060154640c03020600580524010703007800910300c414881ca441100229024550380c2c101800014400c0300c0d1500310490 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 793974892 1250 793973642 793973657
    0x21010e072d03170a0206100f030b0712090c09060e0c191205091b0108070f0509030f1531031d10020f0708030a09031e081209010c 57
    0x24000e11409821085540181241801d8081071040e182190003607000800ca0960384030345006000380500507010004107a82110b00c0c40e0380e0a8081c040d071200c3c501c510414195000b0080c404110440f56490b0b010a041c140107020050b0803010b001283c600c1001610b9590b80d107141031052414500400d4024401707075000b6011410b002d007680c2024401d211244481007000c1d01145000c1c0d0094419000007d4009010049442c04404494035402105140186da060f4003502c24805e41c099404079000304210360781d15402c040d000a064031194400d04100b52b2510070324073f2041b000c62040024a850194066440805042048410b80180210100c400b5401c94840c10302210322840603c40d25081d07050310740b441803e09500b0b2090b504040c001c0b2283e4010204200034003429400003904d2480c0c04041e002c86240c85c0e513a60310583c803405002c840b00001a00c2c86400c1002c62001c03918401c1134440c04849030081407450ba14517480c0c0e4000e1130030541181c6010700f00440300c0028440c0710003903041b82c02c2408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 793976142 1250 793974892 793974899
    0x1050409030e0603072003030702122502030c030703060209120f0a0803100515071101111b031014150312093c040b0a0e0403120b21010e07 61
    0x2098116501d1802c2d01481001c40000d82c007070b1040d000040035280481100c07201c1007000c500e15449a000710f40c0c50016100700c210055003109588122040040580c0e501400604042d192078180903950609a0b458855012003060035582805060001c0d44141d80050f0748030541020700540154034440d0340041e40200c0702041404001148450006503c44c1c2002e0ba04ea907a83c400000004044d0805900f03c0f241d1030804444014000003000c1c1ca501030b40101119006040045402c10800324402c5c45540200c0540c0343c401001c401b00039980f51000301a180000e0481049008880f071f402081a030002466040c04a602480b800c0d10580300c030154054041400e4004e4049010b03c03914038194000c1c107110100c4410001290080d061030049000001010740c20320b4807d540742c08001e410745202e030f480d200c075150080ca41106048100c40302e00001050a030303501e8034141c031407209204078206a2502c513032500d119582d0300d10300c1101e48115000d80b6001c01040c4000750342102c0c03072590640466482081d0a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 793977392 1250 793976142 793976147
    0xe0708010312090b12190614040b030a0f0614010b040e070507230607030e01020c1207050304080d0503161d04020a0302041d061c12031d0a05070305060105040903 71
    0x14103403604400a0110010b405000720fa08292a0780710b20556131003c105a580c60000350100780c080c451401c0c4154080761a24015002c55500c2d01c00e940640d03c0001d842d6110f0304081d003000c4040280181640c3c0300400544034581003003a4640304607500c6135503c0707a100307103e45483c50315800b60000034032031414241401d844180604010b04410305100d0041041c800700803d28502440124881c40c0ba5101c030740403203014580c0c62500351a80d4000c00e0a00710103804480701442a01c1c40c03960803a00510003014440540b5869038407130b071020b42c1d07280002c02000c1401082000700010b42e0003e40d8806689103442200d0311719000c05001003a041061000c01d00a15401c00320103601144c804560040c2e4840108006074002d103c1d03a4040d400e00750400c40b40c20300305d0b00295003040c801e40b42640c404040034204101d1903031680d0401c40007425544030011004100f0300c2940541c0d040d80c40d184040040ca4144000d1603e040c012490403549030b80001020310800000344171842c01080d080d98103000c5036043e40c0d4013 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 793978642 1250 793977392 793977407
    0x1090510061137140709020a0915030b030607020a11010c030c15020d140103050d0503040b07080a020d020705060a0e01061a0c0106051215010b04030305030621010e10060e07 76
    0x1c8590344400e11040031061100d03904403091400d803c0c08001c0000102e00d00302c0400300340007402034014055600009290b40180c003c40c1e4803030429589203441d0b43d0400d0305018182103115890403c150b80c0c1c012039086501c04114035401660160004c10122016207000517502040703004542c104040c035620f02d00029046000405030b5640868500009140d0700541e00c02400f6410801c00c1c01d90400101402e9003103501c1c21641664092000c0e1442c903548103c05640318401528010300d156044e40005414a00c20003c0541103100c65401514003100040d10030103036005990300743c5154101006104110030180301e030310f685e11a450000c0c0a00e6203032209110844841c8400182e41c0c070400100254000020340c4244060140203001d12000c00128100b19034a1655100b032504021105001040303840c0d00106840481c2d40c1650b0741407465580d074050041c80308200b0300d0040303000e0107507420800f542800c0c001d0001300303070300c0000070702d901e1444131440420348449a003c1c001c3c0032080c070180448150b11141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 793979892 1250 793978642 793978663
    0x7062a140106052704140714030709060e010501050d060b0f22080c0d030203120106210e0d0c0f300c02030c040c2006100806090d08100b03010905100611 67
    0x70004142d17880f81406003a8100c048200da207140502c11011945000c040d1380c8130440038058088950154544425004840d0140a8440c00a01000040040e0b42c441c500030140703614107100205041303070f403480c0010950700010003801c0c504101003006500c442c1070101518160402551a60740d551411818503250310000301d455000322012900342040c9402041284c0382c2e4080300d0300540301c80d0ba582c0300041a051002200118161041003400342c0c0c40b07410b004002040d500031018103410303414280d05480da000113400803200c4502000c1c01d140400c20020211351540b0700304081e060710420844010950220b40c40c41d44061225100704c1d00050785001946007820a4142e8000581140041c000e481180400300407455003001c0c8000030300b10080200301c40e4040d2210b010071142c525160420951512402c6403008043d5200d880c1c001d42039031080c001c1ca900f01a145202c80469626031130280ea10b54800d8000d142072981f95802d100172800030700704150041100d86030480490458082c041c0d1038812110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 793981142 1250 793979892 793979959
    0xb0d060b01090806100303020f0303360d09031b0e130c05031e01270b04080421050d080712050615071109010b09010207062a14010605 59
    0x200140764000c001400c0501022421135181c4d10b03041618482d1024175000440c014011501c4901e09900000180d0b800b0301400c507482482106008444091164540700d8609000d18101d40707050f2140c014004502500c4141da52030114a08608005140c04410017900201c1132101c1000c0065202c1d8000c0306da000211950048800402810100c549070b0040e000039a1601031101d8a4103210540c103042c80304222004028001c10003c4001d00c1c5024407842c2a112800080034803410025a61500c40b507400f80c8141c03401400c00741c45207514400780342c5548001d403070f01c01c85038004014068100513281041300c652420180d185001030000b03104880f4900a2071070603032030380b02181080d692110021045c050144a8a4450905041180c1c50184440485000f14210000401c0e02c440000c22991810307410380042c110940740040c1251b13400051200c0740e48143d040043c0d00030b0040130307041076007a050280c08044003403213000340e201c0d00b10740160340160f2050140419031580001d1030604410640c4008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 793982392 1250 793981142 793981151
    0x3040506090f04051e100e0705030702012004090e0d0e0d0c1208070614060f100c0206120709060903020109090203040305160b011a0306180702070810060501030b03010b0d06 76
    0x1840460b5105840c8456a94082e003030104000c5401800d10200a1144049803440903e48032192050301c004a14012045620040c02c0090a0039014600568212a151000261444030300e004402c03038100502e6040d00c040b030005000c00001002d03018400110792040e001e465882c01b00c05014001c00c504049541c007924072110f07000280288480d50a0090040c2410540b40303202074030f003014440c1d02802c0c040361003616003500310700f95800e400741180c851040a0110324841da0700d0f008101410030011440410405180e44070401a101d400181402107010000d00d441420000c1b4050080c1c1082e8102800b0010007103000c02c0580c0c0d000300050100c0f0081c110040c0c0d40c0d00d030307420b00312560701c02c0f200c1c0d10283d0740710500c0b43c50401080300031541c100c0d03002802c01d52041c50700184140307182c441919110390020041d20700072203410142840541102c5940100c610342540c1d65240c0d4101030080800b089002d5580504119a513090301135044000c80c1203000300115903080c80041e40940d140040a810140e48 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 793983642 1250 793982392 793982407
    0x30a030e0f1c1112010e2b0207060818120909130807080703090b0a0c022d10021c02010504060506151c062105070609031a0c0f0409050f010f0803040506 67
    0xd8044103125141161300910840c00d2414002d591100400b030802ca804408100e000c203c02c519107654113800d00e841e40682202d40c6426000c480d0b00001030040310390308449503080c000c44003081180341068004a107145882d40c10040412202ca034004112417140c103001c00d60710340060803000c100c1e00000d911101841c0c540da180e00b4216104521604000100c0360b000074460410b54000050031042c034800c9812140b4443e00e102d03421064100c0750301c1340c8a0407004a0790040e1a04e4501e0010101303122030310482e031004072030603402005000000f00700400f503550348081c072090260714001c2c503600401c00d84080861210044010141d4818400b50190780d4840411442c00e07440380d5040903004107500391096405401d01041c1007980b05060070220307103074814603100107646401354039001c003100c0d0451901420603140310380480402c1390003402240300d0b810030480f580417045444007a06c0940003400340060b491034807243c803108030380701a000245d50505118042054050010840342a29801d5035810340303469031b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 793984892 1250 793983642 793983649
    0x60503151302090c030f0a0218061e160c06032307030905102304020f060307030b190e0601182309181009020609091302030a030e0f1c11 60
    0x1603280020f6201c103c24092080c028242d0703015500030310046070440da064880480d1041248600320300100708070346400d000a15440c0400180c901100f58a143c0400414a800d090a190780031074485400004440c40ea841405403500d0f00318041c0660b13082c1004405928031110207910320300820308011015040008003524841c0d000323407610070340c031000b1251441031006040000d880520181068022088854016100a001a10f0045070060419a1450105010300c08070b5400102032405040e125440c005081e1100640c080228502c80400400a400c0c030b01003000703441740039101d41c3c100a006d00c1101400801c03103e11030111075041301058083c0000703900d40a4250409151641e02100a804008200468244911402030310700107440d00424620b1044045074550b41029400007800d2111070514244584040d4000c01c402186000010b82c1c0d6000a240c08000081140004d180400e0704016080c510000c007041ca20854981c00e1a442510a4000345034412001070810700d44041c0c040b0741e0b500d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 793986142 1250 793984892 793984921
    0x11060a180501050109020c0d09030b07050a140301060207090f1e0216080d0b01091a0a1b0f03020d030b010903050a170c0f070f090501080c100504120c0f05030106050315 74
    0x9901c1802402150707540c0c030404009402039103403003034180110071f01202041e10622164080d030354480440700e41a1202401213841d42c00000111060003a84c0d80d05149840342e4602a5000b085640d0080040c0340c01c100454068640d1030000ca216503043c9120764118008890b00c400d0401004840107844a58004260740701108078030010300f801ca0001a240711012658200e4940c1d00d038203885104a00350740d42d110450301d0032658045000743c01d09000820505228240022649421200310088054562540c5040310602502100960301200d081c0004079014002c003130350724000342840c40c401031070354903855100e44d0b685100800c09004181c80c43c0042e42141c05039881f22800500700c0f50130031040c0481c1503444089014400c20000d21100010387c810f854010307107050301d00400260203003030703100381c14010780035440c09000c0c0a00c001030001280958901c000c81d01d13894026014518414a09031444c0c0215176076800c0f460003641003c1081c88a070300c002588405003110b003150030241d61341c0e5165800055 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 793987392 1250 793986142 793986191
    0xe010e0f061608030105100807050d0203150907050c0f0309030d080c120c07050f0a02010c030c1502130512010c02192f030c01080105010e12070f0602010c0f11060a 72
    0x3001c8000d41c2c1c909100e0040301940c113072407080d100000d4140c122001581c645070211400000200c00308851003801000e0340182d5080781403003a40c80a480d034400e001a011100c01c8030b45500051021a907000e041e24100281d41072a2040302c0554549040400800e407205221002d0302d05018501000c5010741c02c950081350343d0301501400d503005c1c0e8207110300c5100107507004400030781c0e03180704d40c21045480400101d0341b4070800754141c6403407540c900d00d03980503941c80d002040305450844d18115180e4019030f050004124040840001c40c0d031880c2000204000320000c00e4501c2c0c41c0d40e14200180100a0300000c201c030002d03410b9100301407960501d1611441c14212548016600c03607070000b08404500710311501e10050380b0110709a400d20203150004443c111000d01c034090006007000c9100f07801d8213080001c9000038210905a68000e5119413918480101c16401100183c1d9110420034509520080640d280d0b080c91801c1a120511030040998951018056149903035450400d42c489448070b020710a40f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 793988642 1250 793987392 793987417
    0x1140103120c081b07050a08010212131e052d1b13020f03191506030c020a0203060405060f0108162c040f020f10200c0a170d0e010e0f06 60
    0x34055540c1041d1904046d2180c0342c003884070345e5030121b0008018004c1d150b0354900c0190b02006d665603841c000d14002600b140550321181c4041c454a060b01050324112802da005400a11159070401c0300780c640c0300c075034401240f00d109041c04101c60310440410000d5903100c0c0300064001e86002003000034100b503840f04052018620018001d01005541000340d0300c40c0d0704401c068070840034051150300c19a0030181c002868021304510a00c03031203000f41d0194400d00a9841259100b5600e039000c07900d400d5060b10199040e0303201004008001c44041c11141c0504030182c0905805c1e0f001e0900604d034440300e401140d000f0384101c9103014590801414242202c0692602a21030781407605103c011500759420036070003612900b980391400c0c10b000c6a10080e00815540b203000d4088481540d441925088000301c1c040c1c05410410015961848590750160031080071a031b04581014030b49914000360a90010103101030f901100c0c040e42e8000302e40e51080002070380c10609248011000981a10440100028 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 793989892 1250 793988642 793988677
    0x30203060a0203092407020d09080a06151a070b01060e0901060f051e03060a0501091206050a02041a0409050a1406060c0708010f0c02010e0105060d08130506040b0c01140103120c08 79
    0x605d24034088480380030b420143c00380c03555030b404000222803115080c02141960342c0048599400034035150f020f40c1c04001a010030181c2c41c0e490b4280a10755081010740d03200d036140085819004d100400c50718500410131030030105411a503041c0410001603051161906000d030107010503484c240188229580e409000903140316420819100340c800750010b0702c034940074060028012480f540680543e07401c0e80c0d100100702d844003e256440070064140102100310071070b001d000020380030412000c04040003200c900c80075102d50400c41c0102c206d031030003420712080604025540c070513200c8400d52540c02c00015110306549000c100000c83c5030000e01e600101466107404401085031100d6403200100c000580e009001072445101c08a0903214151052640080c1507c184000940424003c04100e10340c000354180f000d0b540d40001d02c030750b003003903101c0054540c00160081100e44284503296000390a4040102030754107648440c00f081c03002c0e400140c14400000a00d03014005031000b50b0391000c401c1c102180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 793991142 1250 793989892 793989943
    0x90807030309050c0d02090a020c0109060f0b190311040e01021207081608010f0509190603150509010c090b031009180203060c1c270309140109030203060a020309 71
    0x24028200b0302e40a4500380030301083d41d07a01d0b1a0107104500d2854008100d4403080d01d5002c3d04000070f50201d048881c1c03640d6101031420001d6610b000b03021000400c00000a0424840014051004610700705001c040910707040c284000b908281c80c0c3d170191101958001003180300001818024400d01050044c05004407007004800c682c8029564858140440070002c40940c2e500300384c1e400c00003802400c0b00440e1b103590620283c2004070034151300c1840b84069075419445618030b401180c52580095604c11410200c80ca140141402260303001114403008000c041d5000900412040d04c034061000700c600c00201007440c41e9010308145001d4a50002c04100700200d01c91038200754017291004a01a028038400100c0c5c6200204c1a036880c4089041d50380090400c0540b40002004180550524040e04182d0301c04189100d00c4840c0e20b00d40319440b40d200312414000c840440303d880c031203050304100e40e140f01440180c4000c1422a002404020302588030340b50f0390222424000391868450406256030020f4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 793992392 1250 793991142 793991147
    0x1a1210120f02031e06010e090a08030c0a02062d0a290f1918020d020f03040507090e15180d1e02010b090115110f0a03180f0b0d09080703 60
    0x1000741d4030860488601305801072800307030302d81843e8446210540242d40104000810340d070100364481006e4090307955800c40c2d5652900203030015a440741c0c1070480402c40c2c01005404002d19600142040d1103082d52600d10032403181c000402e20440b0049100503804585404030700e0b001001600d100c8024080c0852501210a5401cada40d202e00034824074400100780c4943c01c0684d03003aa001c24403900c288100d68181003e4131178801d5108030514a1560030040092000c04510261050146c0540820340e01d080c5428000e10b000790701c2e0446694146800e03200d04030440c002401c0e83d05402c06080c810881c0e6102c08012041040440c0881018050822081c103c5030744040c103e810020020140703101c60711605800ca08a07031214007030703a40020b445c03030062281a054000300d082c02e0340c003441e120380000505070426040040c0029001540d80c0240310311800c15400019200100300910300190b410303490a140440307802d5413441000c442d898001076600321480160000c80c48240c0280e0070310b5a420361480d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 793993642 1250 793992392 793992413
    0x10c02130c12060509061c0c030f1506080c100903050703030906200d03090501091a190536160f12240e060408131a121012 54
    0x1040001e004445660002c1c0d007038801c000039680b0241110089646002c2440b00130b801168403c05aa600e01c2a003d001908900d80e0700043d504ca4000325034281214901010713146c100c0c6014008081c20003409020381200054445c0700038130201e80312903100c042c1140564088000303810240c054000c5540100a00d034005041c1411542e0039079940301d60169400b00030b0f25440703000500780328980111803800d00d180d210360031581010380204c00008900529980d0b05030140030428205a10b0242e030410011614204451041d8202d844d060511051403d00510181c110b070034a0b400c1014000726504010301e0803200a10055000d107942200e214540c40d031040c94401070207210310081d0b100c4200000c101901102da8040c600c9a01c05804a02c11441c1070f0483d0210500000390032034640d80350762207214075004101c418081d0f4002c1aa05944492000e040b40c00842240c01c0354121070f01e621011003203a2118421108501ca13580c1c502a91516448011118184162f00c034022500c4d04541c41418032048440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 793994892 1250 793993642 793993661
    0xd020f12060a0c08010501110a0803040204060b030f0f0a140103080f1e040f0b071104111303060906051305060106271e05101b02030102040302030d0f020705061e09010c0213 76
    0x1106140c1d170b03a03035130f00448a20100816840c12600181d06050001d401013000d0340e04103100400c0400d0254487d080c100343c5810445aa0803484015014450000111040c0503040404c5040500000b0285031307620400d50380610005048420004039105030707d40c01d00a4a03a03503d00e100054145074800c0c0d0411219400034010240f99034070032240050402c4c4000d0484032116444020170200031030703034420000100303580c40e000b2484110821510b030b0f1100040001401a600c1030400044401c2c0f41d082503000c4840042c8000045020b00d0120404a800003d41c0350440c0c5051810700d154254451100c4001c01c0d01780f108000c00b410180000c1400004503112003101d40c241c42e0b140c8517140c1d0b2001008540080c140744035000c10030025014155008408000300c210340083e002515103a1f4a5000c03a1411020f0b2044100041440c1c80404440d641804808001c2400b1258036041014402c10b0400e5502420180f10b840c200000c1d085525900402c60420916002003400d06021b695506d14800b0b00300458 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 793996142 1250 793994892 793994897
    0x10503090a1a1915120c05120a06061509051e0306040804050907030606050906160c030c0e0714031501211b0203041212091e03060f0b0d020f12060a0c 66
    0x7039044600611307115407400d4000c9081d02c1c5201500d00010720808004281082c2d81000044e01c0c041001d813112984050360384035003801080b00704080e00340302040f0b91858118005110315250403090f041e612079800003c0d28011620003041816110200c0300e400c0c85010402e806000b08000c110500c40108003074400c82d0016104010b0030380e1203880840c100d51040c0199000f082d0103110030502800d22601603c0c03007801815021003280c000d611100071001c0281e1084a0082c1103e0060000340130350240260002264244201841f01581f001c0130a40002001c1302c44d2580d610444407a141c2c458840b015402250901c4400c40000c202d40260103001d4a4092003111910340c0d2006900910000031642201e0b0449045003849486680d07140d02c1c82c0b0b181c00c2000801c140d0b050080f44441d001400303107800101800280250710314515180080e9807501c4820560700f403504801c4500c40d00e400c101240703606c2c0d0445012080400c8100041c03c000c2c4c008800e4801d6100740810042c00e0882c0b6030018085008a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 793997392 1250 793996142 793996171
    0x20307170c0616120f0c031d0d14091f0207120302062710061404060509040f06061509080715090608071412060103060905090c010503090a1a 62
    0x2094080e05849100508581a03000d100020b4020050030300b0300100c8605858090100500d01c0401016280b0305d1200080c45603440c0074003102150140f19100300c02095002a08001d601c034085c1d81c2d1103502a69a017000d0102c0420b25040302200300d01180d01c0d80070b0042291f00001740e05088281d03096800c02c3d1752801741c17050410219031001405180701070a607240d4010201680c0300c4059000449442208800428000303007440f5000707a06010030240f801504c400011600e2500700d28204540c3c10242c014015442c01405000c69110f202d0f282e540203030017521243c8510b00c94507081000300201e078040900d06401c2807019464950207103080c8102c078242c108a81c4902e46800c042400c0c00c10b468450b00c003140c54039100f0440180604031140d4000d40900306440384000311883c0c802c480d40032000d442080005241041095a0103200710000741040e00001c028a18003e0526503a035014404000e060080110000340404001c00450000fa60300c00f610411981d81c0d03628504400c1e000390ba00c4c00d68485c95 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 793998642 1250 793997392 793997423
    0x515010917071202060705010e150a0501050a090b0a0305060106170c03090303070f1407031e09080c0103090c090e07030507060206090c0d0f140309010909110403120903060c020307 79
    0x1004201a82201d0300c0262180518010001a4a4070101c60032070b04102d060020764082070003031280c4154010050b01900401d44040d86401440e1001040040c100d07280900600054440704504010b4500108000a0940f0304d40c00003041444241c0c0010114440c0f4000800c10f186e100241203503101d40b0b13054940040e00e0780820540710f030100711001e0b0200d62091002561030752007080000003c2905040020140202c0d41320109135a102040036800300302d100c100d841c1c50354403a100d00110260103181000c00241001c1d06c2c5505c1e86049407000c0e04140e00c500d40c0409000307144401c480203101c000010480c3c60760381352050361901c2c0e50b44410f560a003c0c02c00002030702070000c980341d071080041c80f01030031021100382c040000d40c49411505444000070880706d4070009100c00905040380300e080c4e000f55154403000000505c16002030700820f10144c103186018041c081001d00783c030292a40700e840034180104800d01214404c2c010f510142c100c80c01d011110300040d80200042c00301500a6407108200c441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 793999892 1250 793998642 793998659
    0x7120e100314070e12060405030315010c02010c06110d0e0a030e0a06080f0c09040203071e051c2004090204050f01030504110d05030903070f1502010e060708040606050405150109 78
    0x102d09500400307081902c0009481d0f144141c0040e10841801040000e06090324200945804c00444044400d64000018010150180304008500c8403007440d1805100803035600080c5140350042c00100341c241c9554100039900f260740305030340c4005008113040000400d4400c5081c2c2d6100401d0090780810041d690098a50801c4c1c0140b00546031240c4401c1010344525000b0000084001c000c0d41d2281410302001e69140d4030740c00150300504980c3c1c0c40c0e003021407071050644012455031a00e102484001c1100b0081050510317000c0701141d40400f8002512607080003007010100714090514407680740040c000c01d1031551903001d0800c0c0c88050310300300c004150300e000560844502b5035000e00b01e90102e0021100c2460400d0400b6041403150701500e0401c4088004a4505010342d00324040499003000140001c010004051040110a02c001e203c00d2564900e85034a42001070044400c101c0f440b0009410700c5883d0b0070800003400054010000c510304042c0810b51108601c20030360000b0b124001c0000c0810707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 794001142 1250 793999892 793999901
    0x2103020319022a1c150204090212090d0c0813030b090a0303050901050c1c0f0204080c010e0301090819050c06010306050601120e2a04060f030203120c06060603040807120e1003 77
    0x40058501550041354806110030905901c8046449441a00244010000c6030025100400350924007684821045000141c811b20040014409900a55604208660102c80800029000541d295484400701c0c1300b0340304690b00b6080940140000414008620350004858018074081d550802554580481c22400e03650162581206440144201a01c440c0c904480ca40302c4001164001402d44c001e600520a0380c0140c0d2282490b50401418955070b960002e40142801c038040b0020084001030380c3e20031109008222803061600c0ad40c09618040d14000e40450b02010381a0080f50031641c1d513482c0110140008a50203400120070460181494602e4002c0903184c401d02d001504d106018504c3e040c89221100d01c49503865078000c043c2e85001c1e10303144a5107020f4040f20b41207800c0c84e81503005161401e0544209510711502c2013210480c400404141c403504054122000d59482e15281441d843d64060040060550740d18415a10500c58004190040c40e0b00b00b070f9421440c05201403020350440307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 794002392 1250 794001142 794001223
    0xa0603020d0201031d0a110103111c05070903170d0c02160b090a2d0501051c0207021206070c21120f020f03240901210302031902 57
    0x14907103005000640c000d030010905020f00c0a0702d000d6060041c0e501c685010a01c40f82a03600043c1000010451750b40340c01a1005600e81e0f004803481c2c5066011192540e0403c00802c0120a84d5000071400f560302c91a000c100075a0003880e4890301c40d464240b070380007940c40301c2030000312986400724403480c050000c101007040b409083c5d202082d07241350807007041c8560301c19150141d01c049506404a00c0c0c012444ca0004c071525441380510210340c0528102c1c01d40b54058000e070f03044c0001840f040c0b860200c4400c4540707401c1212400581c4071400d03480442c1c040b0231418052030b4580544010004220361040c031854403103002e501c1a490220076078850015410620f90500700280681c4031900c2110310390340001c0c8040c0b4408000518041c10744802c8405a00309a503a801c0d0078520f01d401e90441807a14101c150302443c212101c80d1a54509101d0210350420000c1c0c8140740240c04a028080c0350091040c0e5410285641100305200d4246000030f40714080424201d0785c2150603580002100031202903110360 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 794003642 1250 794002392 794002399
    0x2150f0a1710060e0f030c0d031101060803072d021201090b0c0309250b0408030d0b04021c09060b0402180117130b09160923160e0f060f070b0a060302 66
    0x180398420300a1006403061542e030503204155281ca02c9031203010008c08440e002c0d94138600007030418503005094401c5a80181b80c0d680c814030062000c103444400d00400800c46446c9800d4444e030030041501406011400a54080c600c41d03102c40c070264064205284292040c180e6462035919501265014041941c1e40203203640140341001a1075030081c005040103e0802c561107185a540d00c0500060340030750003610075a040892014401101800340d10264a400c640039400c0c40075403040004c8040b410445a001c036030322603105000b07008650f400749040600181042d961240c2e048172145045200700300041c0000c95480404202041c0d1000e598003a1500c520303500503a00050b03d660130100e60191a40119025481c51000315002140a80c80103040e0102c02084907448190b13202c3c1110034140c8269800318000b02000349100401d00b44248a40d010305240092071014404509903822180045801c400c1c001101c0030310354010405403a0151203600f907642c403640d41c00126401c1d00da440c44003e40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 794004892 1250 794003642 794003657
    0x20114040b010b070212010908072006030403030f0b0a03050f12120402091807030302010504030f18062604060501090b15030705090103020c15060108070e060702150f0a171006 77
    0x503c0c481140148030550004120600d016510304029003102d1103020304440000c130010300e140401c0002d6642001c100c0810545101c1180340001003441481f0040004003011b41e1409040622822131703005454209028241001707081d01c904d0f00543d28115050320908510408000c401c81c84105421034a0341e040c01070b0350504540362582444500c080140c607107500003000c0c0340300c050250f60400c00100118000da00109150802d81070141900c51080c0d0310100708800c410701c20702c200c1103690b1010101c402c03520f0000246260101064118160740204032000c40f903004c1800140111034002c0750695071844420002035403208204074442010001e480b21f8000144002841540658007901f4110018103003d0720b40302c01110610305210702602100e040c3c03841e031070178400c507560f2080c00c06504c4203a9062031001e44200034001001030080e02d00c0244a00d40c41d210b4401c280c0210815600c0c01c03502c9405058465459210103800400460482070483c2400c40000b49942c41007820390003240c00c10b0301c4020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 794006142 1250 794004892 794004899
    0x4060503100b01030204320d020607030f1e180501020102190305060d0f03050705160614030406060b03070c050c09070c060f150603020c1b01093602040501020114040b01 74
    0x34060701c4040b8006050640c00d00c000a8010078000311450b0745034030f1001c2c89103181401181040d00351042e41e82c140c00b03440b590b182a801038441208480a40381c060030003800780d0805507000c5910404000c13680a1840c42c44030501c90300e581280c25401400401d0407411011030310750004908078002c00354140c1e40d110140703c80c0b0b01c80310302a40c80150040406011107800610507214111900c6105404400241d0002901d005000301480064400c41090818801c90380c58600006d008005455403010542c0c3c0000120f8200b10065100400520742840942e0312450301140c050008926280180d4041c005e40c0310944440ca8240c07001407140c0f000d038070f440c0425040ca40350310f001015456611780f2034030782da00300b1101c001003561401001444690f50140c1d98000c0d400d883c505024000c611400300c03c0c00f81018016680c2c00608180a8402c0b0a9190b004035480d0441c0f10b0b40303185000e110300c9190454848081d2049095002881038800030b8000344140348200c5001c125044c0101c9000d452040400010f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 794007392 1250 794006142 794006173
    0x6150f24080c190e040b0a050307050127090b010f0311030f090c0a140f0919050c13030c09060e09061906030813030b0c07030c020f2106070e04060503 66
    0x41e0009807800344241028415800700c3c540030041210742020484500c44070005180c9400340806410080d94000038041c80c1c0000f096032100b050040301c5c140f0010100c02011501c41d071041903110b01808102800740703951148104010b00800740020b0019004e500140b847d6800ba010302005d0b10351005280e840e641d110a03030307800c2400c1d0150030505103003d002e801d81110707542c400c0018080c000d0016604060102c03401044a80040c101c0118000c1c5443e200b00000c501e10203490f10070100003690085625950b00c114500c0707600c500104004200c204060220501020520040c00d880f2480320421403035840c1c1c85840e05400007110f031803107036911410000c0c1d080640d003002c140100b846d100020402985a0391840841d42000c4250010f10903254405c0043c0201c80c04810303000744c0035010951400655460040aa070440000680201c814217042413003900d0b5032880108006207a007101c01002500c0b191746480d400180e038084006441ca000b071018038502489840c040701c0000303008240c61100250310b07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 794008642 1250 794007392 794007407
    0x3090f010905040e0607021e0a0b0c0c190204050f0f0711030d06120c05010c0302031b10051302040c0306260c060307050712020102090a090203090a06150f24 69
    0x40e040194030100010035403594040d2031100c081d001d0103085030349800000207140103082a08049480b49406240712319403008104000ca00d500700068482a98179040c80f08500d10408950103882d204920307100c12600d07411540c0a40d9548215424405c0340c6070ba0039004182101618956860002c01c1d01185226010b0300302c1400064403582680d0170006241171003070031100c20703502c001c5d003c2141e003e150042280c82010035011308400d007411019110540c4000713540b805950000c4801c0141141c8859625604001e40480741c2d082982c2070000d07203030400b6001810b20311288128022824480404603590007400351000355564681c1043e00d0541c46003008680606078044440e0038003888501e182c49032200001580b10300300c0782e10f0341a40c0d0441e501d021100a11200c1ca64011039105105070100d41c2d85020b600000c81d80e0034000540c4035260100042e043c0104008010f0046181c228506030004a40820764112944c07c004122074070f55589a400c0940010403407956000a0074005c1c08030b040c01010b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 794009892 1250 794008642 794008669
    0x606090d06090602040807170303090d050703110105190b49050c03070f2301020115091a0604080a030c0c0b0a03060f05120a06020306060702060d091e050309 69
    0x20104040e03419443c2c0804030b0340550030000f11074104560034015a50690b0000038810201401140345282001c041a11403241c220010304002001459406052141c080c10b54400c0b0324000810150a040c084040580741c00c482160455003407850070007031858914030491489080010854980f8200f5504440c8030341034614480700940ca100388540d5400403e1104205184200004c01b1026254020580703031030304541c4242c034000e0001c0800e00c00618910784502089010204440e55800201c005030b01610040b002174554100c009400225005650816105407400c0e40c008225025041c060042e14400e40c003d1581940c803e90f81c400000344191441410309014502c2181050b44500c071140035580986070758000a0344800c0b040c42000440d003880c0c00101000c0301d2003c8a48050b2400395180d0647c1c4c1406801558044001707143c2c0e03200c0000300c816040c0c1c018001c90f030300c005c6030682100401b0003002c20741e004050700105140c4050001c007002505038001d401582400700400810040c180b9100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 794011142 1250 794009892 794009903
    0x22051903022115010806091911060d0212060a1202151e0406030f0606080925050d051c020a021e06070b040b06100216090f060302060c061e0606090d 65
    0x800b01001e2400c1840990304102c030f8201c006030f055141509075460064090300e481201c0d08040c1d582c9120000e208200100e103640481d42403122080040050b5250040441e80c0b4074090000a209406180c0741c0e51044c4a80400c450a0070502d45030751780444441c248c072078000d40080d85803140e402074603244409011858284034041d580c04004421444050b0421751042d00400d484020721200000b1030300510700600198544a03656203007601c512503644001d031090b00c01c0d00e400c440c0c108031059220311652000d0503018061807514140d0b072601c0e40e40c800107d45102c02020804961421580c07000c44d0280b0003540007440c4a42140d0180f0b5148a41e02c103c1240e95880385080143c80e00042d191070800303100314090f4040c00c3c1a85881c40a11110980c40c500c1801150045640000c1100c1d0b80c00840307040d00e40c80e80d0005070b058122181c03503004240580020358070017804a88a1180d00b40001c100d8466207500c1015a100b4aa10104c903040030002d032503860303200038140504020b908103038403103c041c5c40c0101c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 794012392 1250 794011142 794011189
    0x10c110d030903030305010b1c0e0c04050c220501140a0c020901180b04090308070f090302031002071202010509030901051620010e120703031110022205190302 70
    0x8000208032458410085000c10140300080080c160140b149500420048581c60310f4403805c03034140101441c0700282070a000d990340380350b00704940b03003001403006485002d03000f0000742c10034012401304c40d000084250009411425103041c4480ca08860344222141038490a01c20b5660712480e1081350051480c0c00c0030030814a0052026944e040340300360003811000f80201071000101e1078041600c5003150241d02882c100032071030000a900c11072040e481010b52074a1106a0910072084a84040d81d40c0040e5040c422503101c0300c0602895401003a000b8440d21803c501541c907584140e00b60b5000701d910070010b4000b84000c021650060008054246410010300740101070750f5641c014840c4400a8101c000302e000c8481c0403513582200c000c40560800303e590b841c081030b00c11401c583d55100c50200608201a91000500c80703030042240d040f00e0748500c913080d03454083c000005288030490070005aa0403056140020381e41c100045000c2180001000c00b62690303041d502170103000d01445c3c83ca041c02e94402c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 794013642 1250 794012392 794012423
    0xf0f062205060f0a0c050c0d030f020c01020c24010b07021908010c0908190c1406160326040b0f191a0f090c0301090f0209090a0e1e0c010c 61
    0x62202c40c1c4243d00342142e0f4920381c18140740b48001c0794550543c1c1c50504c81d0800c0400f403401400035074214052540c1c40c0124414407048250030180c010039283e06429170000c15211001040030501d0803d0401c01401001d14610104003180826070a110758100d022082080f2800b608103c2d402e0401c42e03801c6006c61140c035981c6d5070403d003114040080000001d0b00e81c14144002101030200c110291405544111040140e8031a17000d0080d40d80300740d840341c0e40358000015082d251001500c0b40020f22040b20b00c031288942c00d000e05543c01401e11031512055801e51089000c902e10b150500454003da44482507a885030100b2030b80c1c1c5000303010109444c104042c04401c0302c5590103510692500caaa82196202c070381d800340001e00080c3d6080d01e02c14041101089941c00405040e2411500500f5020a46034009000c0100030312a20540e15000b50307007142084280c2e986508240007400920741203a6256410010103440040d09280c0098540c100f01d0000c081580308240c1c03410b00d240125a100d40d00c560 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 794014892 1250 794013642 794013653
    0x5060a03050907031e02011e05090f0301090c0329010b160303060302060a020f0c0406060221120f25080106181517090706090b160c0e090f0f0622 64
    0xb42036004040885d01290b242d003c550740840140c52110542280940a14131301002801e14051122140d014115406080c0015a0300b50440304a03d900007461a00e0a926828001450341c90b01c0c005040f5440122440708140640130841c0741290203e4411f603045c4903042c0c1e00480c000c480b5140035002c1588403000803000d41d940780010000013405400429095596410460510312200c0c0b0300751140b0b140c26000c01200b900852401d2000b1010070708200c00112481100b06c803805000100c08000000c042000480850040114000d4400d284010400b0002c103080e00050400c080c1c10800044140c40100076090042144d14540a60714090202558440f110080c035412844403007000103104903000000024000360f84c0e074001d07240d00050300e07846050600141041005200350031002c803001a0007a050325807c07101c07154056000b8140ca0503140d03681600c1e06110340c191881c20b454003903a0850b0003a031000040154030541a10040d24441e40d5001c50b0b4405044030089827403204e060720110000144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 794016142 1250 794014892 794014913
    0x91b06090909230f0c0d0503030604020f0d1e1a010c060b010e09040b0103120c0308010e0a0e03071101080c04030b04060908090a060206010e0a0905151005030a0b04060f0605060a0305090703 83
    0x90740c6100a001c140600b1003c545448140b1006a00a41b4a10b900b103011403004012240c0c0008191009030b650b24074507142d90007a01c6650750404140f445e000b048404001e184091a409500f11302c0180011031200d41748c6a04094640c2180c2e01180c0955a44400a25070b03400c60b1142900c1410450f80c0c0d0703c1650042500010129021a4407511a100600c06c05c01e0b04414840145018688408501e40c40c2e80c0150542006010b0020290011030006039480001c0d0054407039480c5840580c4d45134217030b5241c03968110841004180c041465240010041e035060003e8a0450350012498030280c2c8854481600902d1001d030280c62202040203140080c0d00c038078085800803c00d59004003280c0d0f02d840000074110001410000000d0305141d11200403410004080c482c40c0c091106e0550715480d101c010603240d0020794081901401940c07004030600c807a40c448948207500424088c0102a100a2030104486186c0107030b40d03100c00144000b00c0c105101c2d5100c3c540c0004501c0444904984a480d22401103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 794017392 1250 794016142 794016203
    0x160c0e070c0b07113a18060801031a09010b0a170d020c0d080913020301030c090f02070b04300f0e0a080a0f0c0801090b040311060405060c070c031203091b06090909 72
    0x14406d4120401c010a12804910051409141102465045585400c0c10021105041800c0d00c10040814500c00f400e40c00000c00b0301004019100490b52441c1d9907840640c0c540140346140181070312458480d0010950152483c0004c1000c8410007080c0c0c1c80f00000c0e000b00d541d064001c0d514083e24145003086100650182d40580c0c6142d0f00f5501d0301010b1030130744521059000700640140302c4400010305080005400540c01400040c40e20070803101e4190b048031f050703091300c9150100d10398012003d03008406c151103210542c0c0c1c1c484611461100b40101e5042600c80c4419075889034a00c4e001080d01e40c2c903d02502071080102d045980d036100485829980c0f070444c01d0310000e08980c140000c260b00031074074002d004080f10140c9003928007615502d4642800400c0c104005d00009010010400c1c1251504007540e400680300102e895103003c020024030320080101d440e4510a40c0300b45060b01c1d0b4800c404111005641c0b14400c1c1800c0420000c00f80c8602c1c0700445035810030200b82e0403030202c01000d8a010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 794018642 1250 794017392 794017397
    0x50409050a02100f0c14031608090a08030403020a090e192f0d06020309010b120f060105010503150f060d05040b0a06140303160c0e070c0b07113a 64
    0x101c248900402c4101403119401009005103512452041c03030300021040c04080d0420b110034036582603424494190700c1f610110607001c7d0b00c040f100f03400300680980680302484054500c00350007070300c400003280c0c0e910850001039401001408100107094403500301044081580c815618541407590400110100c40601115000e00c0c142d840c034030040c614131003081310307203c6038201c102c4031440d90021425014410310080c01c3d030b03900000085c00c10300e070940100d000198054a122503d554a030701c215224000c4016129450281000000d5158414030a40b4010300c00c040f05c50035904070780700802c4001854085402d400003020302c1089a6103d1912801e44a54003c0c61500300a142c030541d000c0480302560800500c41c030f40d4010325401620300009136007911984c0016240e202c84903040c011000d519507803114800c07402c51010800c0b065408100005102c0c4291850220350b1030303002c01502d9907050004400c8a541c00395914454156070072001c50917550400c0c0000c22049140540c044170310b20024500c401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 794019892 1250 794018642 794018653
    0x31203020a0f09180b0411040e0414030f180f040524011803031d0306011d060d030e060717030a020405011d090106120b04021809070c08091905040905 66
    0x752240c0000920071036085034504108000d041400000941402e07940e5080000d80e101d02d035145540740d952101a40d02d440c0b03100700f612032355241c0c03c1242d0803504590445135410328804542c2c941304000143d4104003040d1071581d0511051548240c2400c40705044079a1162541040c084203487c1c42c4070320f41c002c495540c40c0b503000c1c450f0340d040d11503543c00228529040207141c0385003690002100d0307070f001d0541c1c3c6c0c540fa000c0381c030350394040c401c000e852104210b040c0d1502410b03000040114550020149800c0300d984030621a60300c00003000410a64001c0180c04116076005d00340340c4c0c3c5400030080001034132801c00d4030f00c408212030604450750011610800c4039079001406026139a0444a12464442d452080d050b0400644022500b0070b00c061141c0801c0c401302c01c11041e44c1034604d41040d015800080c0085484188412455070360718a440340903030144800d10007117240c90384a480c1d0454019040414a80341c042c0c018280002d1000420040c011080000004600760361140501590103024000404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 794021142 1250 794019892 794019907
    0x6040e220308180a0506010911040801020412170c0601060c0318140f030328090e09010603290721051e180d12090803101a0c030d0b0a03120302 63
    0x40f5082c05440021540450307091400154001086819562280c4001c50b121101d014041103e0140d608034003060350001c10085100c81c1049101c900c2e40b0f00950680e86425510340b00da180e148100702e5a5a41c0d50040b50041c030406000724181ca1000e4482d16003060410041803543c04030070155040300b841d03d041103136070408602c0c01c0888030100241c201d0142d498080741e109000d0301d0402080d0b249402920f2100001116400ba190b190010903044402c0c8100c0d2402e0014240240b03507a000458043c0817175101121919040324048a204040500e00300a0b0385815009a41004441c440003400040c82e400b16000d9641e14040e15008510b5651409084404103494412400c0000d01c41e44056051815900199100061207850490705080c00d0130a000c2a81400b40500781c060300103071007414008107105150b41e44c00b1030b600445100e55030000c02c0c804d22a2104810340b151030980340e000d0b80305002d8600a000c217640310300c11801006004050103a5650707a5864200100c2c03a0b6140407a50124052 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 794022392 1250 794021142 794021161
    0x60f0a0516060227010f0512060a03050d020105010603110703080a051f06020102070b07050c06011427040c0e01060f0509040603020d0308040501061a0304080d142a030606040e220308 80
    0x84d5880c4000b42410750b410400305070020068003070341e61480350061450300842c2c82c40d1982d580040c051500071701030342d85252444e600a400380c5020322441002910b001d40d200c001400c0f103400d840340154581e80e01d548030788030081d540b03015002c0a8001d00c18200c422040c1420443e080b4000350080400c0d4002580301d0016081c114558880140b1140034007170704100000140701c000c03406905440028058030101445032005c02e86209010130510030b603e01c07008bc003034488151301c40310701e100d144a2610410000c2c1c450350910540c500c2803007518040b50f800002c102c009802034004d0105032030050800110a40e50380c001946184003030740c05070003042c440006d020034820213000d510003034983c0340100fa0100044041d50b2041d8032004001400c84640490350082600ca07039002000c00b00110f49142005041ca105c600c50340c501c405445402d425460200c0d004103070007150641c4e101e440020245420300d4a002060201880010021000d00740960103041400c1c040e0b002181e0014040e650f240c443c0e2401d103048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 794023642 1250 794022392 794022457
    0x120e01031b0c0c0504050903030402151207350a0f020c0303040c0f080118020409031e090510090f051908030f1207020613060c0216090f0b060f0a05160602 68
    0x44d4003881c1060b080100480000040302e030030030383c103840c0b04010341030f0099600340c18090102e640803900840307024000f1156104011070001c0c103150210429000c1e851180840141c02c5208060840f1041c20026400701000e5104000050303e01c40e0141c03800807100080d41c1554404c99007283c3c40d00c03001600740034611103182c02c60f01809001008100c00320740925412098080030100a1140c3d490702d610500309031040c0521807103000c0e60309600313800c610303c90301c064000c1100d07000d07403801400c811400110551203910698100d40d10300410903562401c1c41c0600c410f0b44003007482c00b9582a1482c90005e140340c000c0000b001100800e4003000d40b14001c0c804c031104000c2d0042d20355130031544060140005011003054030b4442d103030700c901c00203851041d6500580c10001070451403106090f044100052000c116003200111800d09842013240d02540b4003000702a0241c2c202070299154203000360000140100e00900640c03202d01c14940b15003a41e5681c120036644080600e82507416044180340088884544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 794024892 1250 794023642 794023649
    0xc030602030921041401121b031109010c11010918050405101e05190908090310110d110d2301092d02040e0f0403020f0a120e01031b0c0c 60
    0x340c04070082e5030b8030f0a60085004a0203181004000418006206d0780110820109101203600c107204c0c440790000001003001d0600c4200c1c2c0801c1c14110203410818110040700c0030600142c42d41920b0380c40a407209004841c1450503107041c40745807480458400851170b080b045940104030086114a000d15089003844000d008021510f4200341240001e00a407401c45c3e901401540000505551000d00c2e14080200688807682e001d482c02d01404144104078006206613107094085800c0070504104000c120b81c0c0c0110000704400c02400000905a0700da000030042c5098a10660b042c801344200141c22103801799039170041c0c0210000500a100c45410000380103081c2840b0810002030103c0c1c83c00303a034140a031060001210001c0903100c080300c0c00e905503000391402c1703888081686840c04540c591400c00361815805403207036400403014420006540f2510560104d8080e060340003016066600c80f0504a10034189a1101d80042d083d03140d0001200148205540300020195142481c5040403070a40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 794026142 1250 794024892 794024923
    0xc06190e060f0307030b01020a021306031109010308030103020d05150f0105010f110705040906140a0203012111210d020d0f0801030f080717130e0105040e0a1407030c0306020309 78
    0x4202d910000001601e90100840c200031640c82d04a81c0100d003000e98031031009500002040c08040551019030200003641d1107201010400700701c1804005030030000341700040a15200300014001402c0407540640340070700c941c00308c5024100fa1410202c48850482d0040288480300004101542c0d125181e6650b03a14541000c511900a04030050303107411441c094a4001e94540f080042001010341c0f02d5240000c00d03098600e9581401c030100c81c0a50b00a104070503040300b01c0c1030b414200c19100400140c0c003075480000707041c000c403524040c003026910400907a201e102c42d0342000140d00380180040c44c840105640079024804200e036019054a598501c95000c00050381c00500001d1103007054a03c1031504101c0042d280c4a007840d050905c001c00c8120741c10b0b6007a012034040303914000408031509540c1c003d4038200b03d680e26841070204484544120310001d40c40122035501003071203d0035440800c44036105035003041d0303220b46502650306e0031075100316181a070000810030041c4080c81040c0c40400b845 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 794027392 1250 794026142 794026147
    0xf17120f06010e0f010c240b15071e021f03151a0315120a150b06091212070c14030a2406171606050c120c0c06190e06 52
    0x140d00080007240a41c0301c081c000c149980c03521084e070f801140c483c24540d80c4955a103c24942d03070b800300e000b01d9206503070004140c1e040040310200303803401142c2200e907100800411402d1145584510942410b044240140c40c05500f501e08003503218189005040c0c1d40b0340d030201348034404040c0700500b242e000b210316140001d0050418004418804007440c01210203448281d200e4403a6042c1e044640041c10320700341c3c4007062000c0c0448900c0045450320045d4000c55104850701025100c80d0706850540d000180d010004220b015124175100e9031000c0d01e0740c0c2d0101115030541344950f4900e00c2e54400e81090710b9051003220104041c41000b01c640d1f11407401034003c3c0a001c2e002c1d039945812907422101c40790414a4080c041000f201c000d50100005084500d020a10003400040705e5440d001c0725408100c80050100c00424a9405001100d071846071002c000c064640c1d4001c03010841c0d402c15074034204140161070a00350036a58243c090458142c0024a0b40048215001c001e00103a036445203413401418207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 794028642 1250 794027392 794027401
    0x302280903031202090a0612060602010c0806010c06060302040501090f050108030c062a0708040314011a10020109170c2416110a06021e09090103030c0f17120f 70
    0x34000d0821650b050400d05810810289000041d004172a850342e08a614500d00158403a40540090328204043e1001c008140c1c0f035020480c03d0310211410640441c5034003011131825407082040740d85540c0559400120207071a5400117003910303020b034040400551616051003655529200d11401050781c4402503142040f00000561601001080d03804801084008503c1c00588003080000e00615a6003196443d030f6203251801c11a0024001513031aa030510b001c070080180d05102e24031128270900000700d0510104000c01c40358144061245046540780c100c03081c00200403106460340c5041a4103182d80715845035901900c2c1580c00c2c0c10758502e502c600d0390885010345100340d820740c2201d03065442903010220000306803001c030380e00209422144204d014243c10300c10349501400e03541c815003c1a0400d1950b808400d20740380141d1000513400060b200040000074000c2c100103043c2c51041c00d510308852016107072200391482002c54540302410008651180501003d5aa54085046444600c003801c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 794029892 1250 794028642 794028647
    0x2030304021507050312340c0b0a0f0f1a06120105040504141507030c05040b180f06040803030603072310140d06030b01051219020d080406030228 64
    0xb1072003601e0800400002c0c005007441130510480b418081078280c2c2c24901e04094822080c0c448840e90a44200c00702c404030205a10706074210424100c40303a540311440c040c810384807885114030207890f80c95487c1d42c03400303d80c101034600d000b50603100704c8800340090a03030b11b84400d1120040200c00098446c00c2d00700180800c441c88581e0550644030b040e13400007010340e11864002031800c00300d1500c1c54244103040e0603480b44884641d01c84e104030560750b000e00807904405820b4a240c01540240840e004090109407003600c0c2c07020000d0f480b10030043c1703010350441c03c44003c141c49034403d8202c05160340001080100c14202048204024214642e6003030610390382205c04c5500302c0c8000305d8648650b0700d58914803020b503c20300c00d03800c03407801d000e401b0b558580846032260000c0444e44411901452032030000505850310340e91813414a0761070006020320046065111000d055000030032a4410414054400071820100140c00a01599140141d442d0392040043d030040300750340d603d142901070803603901c1c1d0038030f5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 794031142 1250 794029892 794029909
    0x803030c04090e120d1b050c1504051509030309013909030c080a020108010e0f01030318081f1b09090209040905060f0103030807030606021509010f0e0f0d0203030402 73
    0x600c4000001071904484000d1414031001345400404544041750b2400284602c0c1d03ca02d001c010a905151802261000107590f240100001c1500302c1d002051500c00702054200d0203640310740b18038180c80301c0000340050821081e0090b160b85445a2000c020801c0c0072200340f060b045504000ca8034003401c0c140c550105014450130080700c030000d03d10001c800c0725650060540d04040c41d4410b00b110b6544c0d48a640035643c07448010002d0340040c50041c000501602003e010394002d6400d011400400c0e825a00e0659003800d0f0b200032190340d0080d8810000b40810b003800f4202001e0440ca608800d0304a5112154094608800184810003011591003000542106241c412110310f1100541c90b20721040005005003500c5030090202d016000070080b8451621980c58140d0b8429110210603840e030750b074200c0440c4c006004030005640300741d554003207048440c8480303a031149400002080d90b0282928010a944030000400d546500012003004909414848014009803a1000b1815440c243d0002000003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 794032392 1250 794031142 794031149
    0x51009050c040207060e01060b0d14040b040807020a03150b15130e071b050123010b03061c080d0501031124130e04030c03090504090305071502090316050a0803030c04 73
    0xb6a80019803108200d4280c10140489030040c008001c8941c0c0e034031107200540e000c86001c2c0101e51070301400d01002401d42c1d0600340583c0d007081c0c20350519521665412119840801c3c180d80c001c0710088000002165a8103d00009100e2200071420344240b400344400055104039060b0001e900788913410281d180d02c0e600e0001c0b030340c5402080c803035501c50500c243d0310164081600e1449000207884c4c0802e019054019411211424031000010441c0c0c02240090610a004581100c4010004194640f0300440d08000402202c1e07108403008840e0f075100039859000102010845469078010401d102c007499003070030100801c0e102045107054040802104034004414280030480100d10000152583c03a240742c0905a550620a424281424041e000200e1010110002a8214400700b1603041034041e8115283d0b050f2503181c00d205155469106a6072003014201e00300e07500788415003203590100005426500202803001034075041c00103004a00401d600410b04540c4200103001d03c1c44001d1088a044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 794033642 1250 794032392 794032399
    0x6030b1e181506070b150f0d03051c0509060702010e16120507050604030506010807150807051c0615080f060d0314070b010b0405030f0c03060a0b03010213060201020304051009050c 79
    0x125522202d414410890121005410a402240314401c1000c07141840c0c0c019262040e0b00e04030b10180c1c00c02c108150310403c0509806c00700c180c88800002e400744000e08840f510360003050781580e80e5901013808031081181c03207a005511100900010039020300c00c404070f0859800103008000303511000361038505440e01c0380c0c0042d074207030385440700c1440b04c1031111401910780204460383e90340e41e0f42407a81d5214020300502ca81070150800004015881c00c80c3c0ca09001c05580b1543c0d016500c00030143c41d203400030408400382510110300307011820b03903620544018041402000a0492401038001d00104000300701d000780400305018041d20b80e603034000841e041545890301103407400100b010588a80520440103080142c44000070030701016900180c07003aa18180c0407200c54a40314220b403075480c0d0804a009030150800380208603c14844d812210350003102900140c50010840501d002244043c0c1c44200107135408400c2c00100001400520341c152981101403002001c907441d070648550203200c00910 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 794034892 1250 794033642 794033689
    0x30c110301062103020708010f0605090f07140f0d0f0608190f170c2a010c0c0509070e0a030510050c19030b01110f160602030c07030204022206030b1e 66
    0x1054420010361011f828024001d11a40000c00c0112015202d01e005061051402000080d090085c0b103058600c00c0400b681d40c036420103000c41c000754195020540040d1042010840c0c044d0006060103024443c500740b103800181245440511401c05541d0034440c004c281d04600c060001c200c030324520701d8946030403004c00c0e1030064080d81d562081d03105018000740c0500500812040b61003072844072155400700c259403d050000c89000464194040d0038004050415a500c103104e80d040c080c6050303900090900781170705803125410028407400481e900845081e404060b048106203941d010302a0040100308016080c40305e400e02681c001014072640c0001c05039a07504400c01a84242c15940c114230454056600f00454800c80c41d45403141244060703d1041d00035400a080c52002044900c250001805000c095055074200000f950104d964240400342c40300c801040c0d01c80321030140c001040300351000501c02c1c03529814014030a1034020b0001e20a0308001c0002c006840b2200c1c180300d8590320400740719 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 794036142 1250 794034892 794034959
    0x60305150f130213120c14010f08060111012a030b0d030c03090b0a050c0607081b070c0308030c07060f06030309050906180112020f09040c05060309010e0307030c11030106 75
    0x14001d00a00380c011351000308031000002c6020910040c2102d6901910101c1100d075106c0221203004100e61a101d40043d100791000e00c1907074401c81405070006414034140f81201c3c1145410fa0035141c0494034842c2e07010321450f1310000c00005041c8803036400c889003814003804440000050320868100005000c0c401000c4a00c010144500100720280c0700f080e400d5500c0e000c1d2000000d0440e0000e5025142d18070910012801d0540a03030307030700c034030451075408904441e02c1c00c80305c803807160f030001c0f0401c8428480042300407000400b1b03100134510a410700160640c86240ca03042c464240d40b4008120302c200ca25001d000c1c40441da001d0f065005441064440c2c034529181c0501003a6074000652015031960142030012940c6503850910300a504d0084138251031060700340d01004034072841034034003c0c4400128032041040d42404800b131548000140d00010384c89007030385405821035002400490000d02c24085107410808000c48219000006034003c01c80c0d10300b41031202e41c1d004c09811454440341081c40411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 794037392 1250 794036142 794036179
    0x405071e0305120301090c0806030c040902040b182e0608060f04140a06050616060b0123091201020313170d1401030b0f0702150604140907060305150f 66
    0x800003903600208940050065a1640c110f0b50400e0155400244c1800149001c080c480c03500180103040c018003800c20080b001c0204801401c050380300702e0f003041c5ca07110600003607510801c21040d54106180b007a0303014a800d040900320510048115002c8800c080d4000030407005034080c0500707686650802c00361640ba41800141452140580310707600038108202c0449080300001064001d00c1004000c1c08101d40798010011507000d50095414411107103000040801e403681c0281c00c020174181084034400700c00a0086080b00584400940e41d1040015040d605007403014082a404006200850441c2440142c03c2c4141002440107441d0700000c901c1e200194424104031400403015000401040604a0070011040c800f407200340c50701d0001d00b0015105104e19100c4030312411090303001e00300c00589040007030301d40a009002540c009568050920b0700c0819400c015016107603040080001a00e0100000d080e80d0f030040c2510b0242e00410034800050321b03110700c0b01c04801d00840311124180c0111021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 794038642 1250 794037392 794037449
    0xc05100c090e18010506040603030e09060f0a09051501080103030c170c0102040e0a0f020307090e0a090b04030804060b03070b0d050405030d09080403350315031e070e040507 76
    0x1ca10542ca810040c80501a221011001c1c500c0545000b84080e0b80c0d0b07201000200c480b103200180128042c2d160002c0d4910b8414103442d03002000420740c0e442070f1031280105407030701013a8010702e40140d521024010052100d134500d000114003407a044e0341560540c1d6000704180381601009107403842020b201050131040c80c0989000101c041d000710b483d2540d40440e444035000580f00c81104628001113008604098001c4a02c500216141d11819034030704160300362032800c011b10404085648003100d400194003600a1070180c0e009a480038041d040c00d007800347c01c54404c1800035200f42d01c842401c0145021400c2550a0486e40840c0024160fa8030704119042d4469a00700031600e518007203498042085150107401528080d000c0c180e10049207402105071a040c0c01109501d00780302031000c4c070790100e8840085500202400343c0280d00200000403920349880e000d010900101d040700700291003001040158001d00007800303802d03c1400d094580c6903c400e100d01501058032561080c2c4829a50310051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 794039892 1250 794038642 794038649
    0x1060e2d220b010912080a080703020408011a010e0907080c090d050105070c410a12031d0c0904030521010b03041101051309020a0e060d0209100c05100c09 68
    0x5075a0501207140e09160080400c60419404034494450218652451040c40e024190380019094540030303020f501902d0400c0b00400300010580c00300008a8800700a0003003440030b1800307000f1220035005801c0054042e209801886000d80d07401c5041080755948803c0850700002d4913903090360380d000d4910100b001200416405040396080105015510760f218000981050050107a0364126041c0f50300c81280da421122007400e40302c0308002480450a0320101007030440c48500807500420b0407940d90302d4252644200190200396030701c18000044081a08100000e01c1d4040507250715801a00000e480c404050000780803c40301103415110781c400504008100c2d000c140003040c2560352034801c2900e070b52040f01c084810488e200799120955008200785c0301d00441c2c050300b0868085c00c000198009400c40250b050070410105600c5420b80c840c88014101d071051100050795800d1a0002d10210b00030b80b85815041058900d0648007045022640902d0b240303c6060108540d480810210b80301e04240d003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 794041142 1250 794039892 794039929
    0x90c05090f0102010c2f0f0d03140f0105010f0c0b070c0507060203040501120b0a0f031b152c042c03030c030c0304060906110d0c08010b1209030c120301060e2d 70
    0x2201f0070710240e00080c00904d40f4400f503506014801110403015940c1c1001ea40300d50007241510b0050081e98060107140d60640d00c0740c5829000110584c0310220301140c1900c40b00041008444d9403c00d01c8014010358000d40a140000c5103043d02e800c0008040b552840100700c000c0303076900540844c07540d03904510300040801401c480c01e480d45a00b048490b050003070001441c0b81526444c00903045007155844c044c4513650380c4900d90150300025074003184041034603900202980c8110034840ca940c0310311076505070f407021809902100e2208220912084c50002d250045580144100300c0050800400c6a902180100410303403245c07601e1810401510b09024000d10081c00e1400792091410700501920965119000c00e00200c0804101551041028060301c0700c002420050300d11860070642d40d40b03400c846c00781e08480c074044030002000d0401d141004a4540c1c1100000100000c41d448941c41c60160b608a8000076040350102d0405c5420489100d41503030098007a495035896941c1c505111800801d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 794042392 1250 794041142 794041153
    0x6090b0f0d110a0518041a01210e0c03160b0a1101090b0a091112060a09231e010501050109060f0e0d120306231207090c05090f0102010c2f 61
    0x50040c0d0485c86682d4aa03c5010300008640c2c178080c01907800c5049480c4000031070b0b015881c0111035114a1491031115064030b0943c000c0300001034070828822511002c09030080030710090405042c0000d030010720081105403142072154003a00d004540b91131121b03042407022103169140d028050020120043c152031a00b800b00040346c6c05c203407c00d007905803068009114515080003005141c601c0c4010009132a40014002400d4055071b6000314400c0c0d0180741d83c2c0c420020b010065094150381c0c1581c00c09590803a100340907084a9081a08040c950781d02c0c0248159030600380020440310305485031104010b00f00500401c0940601641050341c1d5000d4040101d01c511402c0184034403d41c04119400245003c000103801d140180680645c1480c080294640d19050b404110b80c0004843d11100c0b40e0160001c000380402c440e22804011009944595440e1101101006828142c09640300d040d64148101040c0503035000c00313840e00440e840c0303500080c10702d0000c2506000200f0f194132201d403072061 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 794043642 1250 794042392 794042407
    0x90806010b0414011b3e1c1101030525031505030705090c131e0f0b07051f020d06081f0e1504050a06061202030706090b0f0d11 56
    0x1260002c0040e291255202e030442d000c064011140c90b4520f807110603541e2200020b1200052a80d0340040022001099200315a14101400d6401400c03061181075046503800c10105c950070041c203a02000f246419030414005860344401a004d00e2341c100d40c0c1e042583d100b000521a40d4018240000e0903180903148405501401001d0018100c01407418200001c9400016051a00080c00320a40e5000340518078651a401c000d000c075900003094031220f00100340c4c1c0204280e10203182005803200143c41c400115441c140700541c072848590001000c801c0d0400a40b0301203480003558800c440001401100c0070340401c02c100f0001c0c02607a40301c1e02d00b14145040020300120001e06034503da9402d140c90000074800d80e000c44107c88098128803031581146c0e55500415502c80d01e1a0740c42800341007a514121015a0350307070121042038000c0c40500c1e035030054000c254201000b032000074000604241d4075150401b441c55115011f03010300001c21240c000794890094045401c40925140711210451715044e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 794044892 1250 794043642 794043659
    0x102040e01031b0e01060504030305160503070f0b060f10050702030715030204080601090c0c170d06240c0519030c05070308030f090c0a050622060509190f060f09080601 74
    0x101c91050022000c0c0300c00010826596901813607040b94210b4884070f25052565a00750f907590069000219a1141c4242d214003044090000348130092040c40241890101c1d45004914100050801c5004600200c1c0302411500d80c1100c0700f80c0c90100d03040158032580c1c10310000e072401d500b5030010b1803100700e020b410340001505a0050010b440c1940c0a94a40340e80300c4044900310b610840c00c04c00000c128030780c400302040c0c4050803200c82140280d0300903d45510100342c0010f03106d5550141068540980001e00104e028200c503c0082510f840c0402280845485680d602c400350700d50120500c454049003000c02d4002c086618240740c0c020241c03001e03283d60742000b403600d420480303002568003102070006454100101c1c03079000200000b4400c40003a8100804d120380350700701d26a20760030340c0900b001c452a0b071150840800000c0c41d842e03481035507403000007003842045030750b007561940d01c0c0f0041c041c28040f01c408803c010055401c02e15029040000c0340c030b0b0448a226882d4013900190294100100300c661 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 794046142 1250 794044892 794044913
    0x30209060f031c0f0201050903030f07050d09030906030b0907230d050c0d060e07021c1407060603020114070b150103111603201902010311210a0506210102040e0103 72
    0x10007507202c1305a68000620306031b0981308201d0341c0751010f0700100001184810402c3c00d01d90050b01d44d2400b5414205e002d445401211000b807030950208415840400c0780b198540036010460005890000d07881c01d1403480079002c84041340d0044459180500207101035003688090382c8114100e25010320280c102002d082d0483e0780141d00c11101e03d07040c2500403d08014403000d0354041c1107a50f004150f09210000c550101141185642c410030020749175400600d0b1240014002d03a0b0f01510b0002016480c520014020305000c50303403031410720000e02c03081c80400c0152004aa01120034800c032090400500d0049004201f8100103080040011510300c101002404e1005a00c03031298072030003402c16412450924000382c008917003599500c882e81c0d20807804194514907811a1040c10302144a00b03008090b11450b07040361b00071446813a05400c841d48607480a40b6410f82100d18014100a14289000401d1402c0740701d40079180041081040795955940175411903004200b035029010803561245002c0c000701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 794047392 1250 794046142 794046193
    0x30c02030706020304210203161d150a030b1509011203081302060d0b011808010e16120803040c0b03070804050d0815120f030a0e030f0a0201020304030209060f03 71
    0x1e118070040440c4003800042120192908140c411802c0c101d003800d4010300041040080341c0500070b84e4013407100040f074080484058103c80d5a07603171070704e03d03400c0f2920406400106024807003402e620f1001455201c2c0e800300e0301034a803c1440d0b00010741d6502c0d003c54014902c00f0885403c2814039000090340056164001e500c140309a45040aa03141ca4000105800d4912030295102c0020000c0600303611310359003c00c010300c4040c1440e24950006801500821119600c5149265110b1403603c10000040c051a8071039103248402020150426509620301c07004000028491701c4000f0116090000d049a075500401e101c80405a5034940004c3c001d203544403d0700c088400d03100b554011200c803400b40703441b54400c1d0010700391a207042e9440010448514417142003001e460103015405144820700b03200600083d047c43e290381b40d840146206151410200c540d0400140d0400151917005030380c04001c0710106c940440312a021900c503040050301d2008241c1c0c415515120743c1c894800503031034001c4a803100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 794048642 1250 794047392 794047399
    0x101203051e040608310302191407050114030106030506010c0f060615030902090402040b150d1d032503050409090501050f0606070c09020c030c150417040e0604090203010b0d030c02 79
    0x30b0b0f2905c149814070a41c0720125040d11030b00d80c0c0404500d03c042200801361650181c0b044030b00004094003010802007142c1820f480590400140781d042d5242004482d000300020310b03115242c02d0380b2044a0105001c11b000d21020592030b80c1c0400e02ca070b072042902c0381c1c250b60400701900402c6210701d0040c00802d440d100b6502c80303d518070a0313a11480c0c000e2041c0f0488640107000f000c9642e03620b0742040010030800052551000302005458059900100034080e11142c0c00ca001641039011032103441d12403040c1141c191254000c00903052072621000118009407100c003a41e203c0004180341c00d6415020307a41003056210f182c03040e0001440415003041d8002c8a48811001d000c0d11071078284056440742d5440030340f0a140c00780e010040b0804030782c014074420048109880c1480f104840160a018512030b2504140040c58144000c0c031560b00705192500100ba502c071843d0500d05005420b101c00010102d0384681c1d9108503400c1507440070742080d03000c40d50040c82242d0340107061030098103e5000031000c1c3d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 794049892 1250 794048642 794048657
    0x3030a03021e0c0d080601030f18020f0f030a110a0b0a020c0103060f080312100e100e060a1d0621010606030b030a0b0414030903011e0b0108101203051e0406 69
    0x8044408a6022a07010b6018144e036514010050700ca820015200a04040d903400032043c0c92031491107003c207003a16614a04000c95924010810420b184d0040c1e44d01c5a030390748040d04044e94000400b0240c0952000325200c42404000004441010340d501961500344d00040c1092200c2d4081641000350000f40c80030801e450312014001300d0040c0c9402034610320348c810000f0182000292010f42d03482070a400c110f0203480c1d2036229191541206894295090184070818420300720102411503101034240c5080080c076180c02c00c4e0315141d1446060390a00034260030003060103a141d81941d24903600502244806041c01407412134001d00407885248002031274001100058940801d41b0301c050b41e042000009551503a071a050040c100704850709509200800a0201585080c0a540703944581110740000e03e101d40d15202c81940c083d080001c0c10003d00e1803c1101902e000314180c1c0590b46001041c0640c1002d62070140c03030520600d1105038601e403209000c030401202c00c81c014010794016945000e1b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 794051142 1250 794049892 794049937
    0x813050a06020f040303231b010905030406020a03020d0503040b24041b0f0c080306191509030201030b0414070e03030d090803090706180504150308030f0604050c090d0b100503030a0302 81
    0x1200c080e007c80605a00031020025480034450407108100c00201c450000038850b00e0075514189107501c035a00c0b1a0258108114140c107054051241d140303142e81c03d0404903e140b80c16503a00c494884000d0400300304100303d0524500f83c1e21402d03200d08584001174800c1050314016111440e0040c880b090000010302100c2e115425079106005515540740e200c11094155200d1390100101c41000803005811215107040000c1e0703a036032501030040c42c801c55450304015282140001025150744c0c00e02e9900440c140149052284190800726910218901d00562101c2030400040d06500c40c19981c00c0a850805074240280040c0e04002c5000f4001d2000b00e92606036501802d441c2060746030388a102211a0403003c000071b05150b0482d40c1d00c00101c11301ea044507622035a94941707503003043c1c0b0f00d40e110440120400056007010711503030780c10061f091811828440d10000281501030740344c3c030051a21000d900400d6003036101260f020003900008041d80d40351486a803000b4000e401c039000404002561503803d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 794052392 1250 794051142 794051177
    0xf140a1d01020a0503010e041410060911040806060904151d160617091501080c0a0e13020d0203070506030708160c030504030b04171c0605100813050a06020f040303 72
    0x2910f50924680b20503045030310300f40d802d8590420050091b610410001156100c5030014801245000c0c041d110004010f13003852501c10494803182c001400041023080240000c20300001c1181c1d01c100225181025590f551510030310903801c00bc00c4040c52800e18040c1e000c0300c41c2d20a44d0491092503007049440c0241c0c14a0f81050441081c071540b0041218404842900312005028603842950705003240c2d42c7c01044420324464840076841900d035a081841c030100c6515206406000038204000615000e00307081d83c8452440ca100c500c001d101d025031791182c4c421074a05000078001003c0083c075040d00d9241151000c2d201d050121030302402e000d41035940c4600d043c01a608448030a401d80d444500b030034255999a2942600a4000d03140b81301e101d111a944400304100808407900d11002a000d0700c00508011001d5414a40086201d0365908003290b20781980160003940c000040c2c03086492510349428150706204c3c9030799001e0b01e0180001a1118071124420050040f68440c0e0750780718a814485549 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 794053642 1250 794052392 794052397
    0xc0a210e10050f010e0a0b101e03050405030901050c10020408160803070b0c0714120408011416031d0d0504050a08010e2508031201031407180f140a1d0102 68
    0xd001e0b08031030982c018805c203403000702e5070313135105444a00005038052908000340300c513440845020001005105040c280b60741030300c0c2582c81035200f820240b2860825503100d0b922030289441844c104100803c04c4201b40004102600080403105021940c0d1611441d166490300307950607100443d0b0044d80800250000004112940550042d283c040240c807100c1c6220b00d19070059505603845500c104040000e881d040c0880b41c0d6940b400c660040c1c0e102c0c13501d41f0080c291807003e5030245c2c090f2051800c1000c129078a1400d1001c085c03c07443c0000340c0190041c281d0031509000b0382801ca49209450640c0034480e085401042030791001c64101c44001d60b1400340c1403e944180601d0303610383c0c0004007060511070780040030030b1200c4403901d50050000e0700e4254080c91504000100340041d03003481c004106104605030b1080254040c00060504a802d041c0400000124000044a110b6072000b00c0c0b20000002e6000741c0340e4007225008000c0d28100b04420340b01810200c01c40194003c400c2015107a41d1005108 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 794054892 1250 794053642 794053651
    0x6040e01140303040e010b0702010e1f030b0d0b06060f19020a0611070503091203160302241e0c04090603030c0b07021b0f0310050c0304030905030a0b0c0a210e1005 72
    0xa010603179a090040307910b06e41d00451004ca051041040b442d541603a1a0008001d80001110305112200703002d4400805503840342d8203941c0a116000c800c24049200711081c00e5000200351025580c03455041c102032128070800c4983e020000c0c003895060040c65001c074400c03000d44d000d0102480340b0804040186000c1c170800744000c141e544104828070203800c2c2a40341c0034503001c00a09480c200305000315944491418000110016005580b0301110110325440c0e000100103c041240018030303055410302c010380020708440c05104003090000701d502c501002242c000c0c092094045c00119500c0c50f0252202460140c200c9042e0b50175400989402c0c400600080341c0d031000034403141c0f581c0310013044c0800a006400580d03010b014408648150035494043d85024641341001d0554070314190030000c2c00c1800726000180700ea004109581c1c040313420300b412036800c20344400781d250b9514010f003000e580507644209000060415001c4070380003400c8075417001030341e202408255040d4100c101e00450480750100c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 794056142 1250 794054892 794054909
    0x19140f040603180212010204030b10140d080d0c0804060c0e0901120f0c0f1a0307022d0a05070602010c050c1e030d0501090606030f020903070512070506040e0114030304 74
    0x100141e6200350004114043d20f403083c0c41c1940b02640124046100341c000b030481d142c5d0005010810071215007a8294001a00c0d40031505860502c3e10503035165591b43c0b10184602c2c06000d0200030b12029108441c40040390b20010050802e50b580060081e800485095a03110310f05010762000368010001402e0b0080d00800b18505070b03080406a14a48246a100792900e41e20003103882c0000340600494800382050100b0071350000d1825203010b400e10306464405035100424010b016941390002010315048402e445100e015150442c0d48a41c0720452070905241413040030154820b00001044031010344540d58000d07c602c441039401660301d4450170313514120340d40c0708a001c0301030445070882c1d00d00a28060020f0700e10f04600c0c0085407055482c2038000c0e5100036982c14003040b01641502c668034584141c0413044d805c0c655210700180d101c8619218460003a80d081c00107114803074060145030042c0200924036038507207071200011800c501c024004c10310f4050310148150142d16000040c2c508032013011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 794057392 1250 794056142 794056147
    0x40515070e030c10030212010f03050c15120a0209060703030b030613030e0607060608060c1206010c1e03110109080304110a0302030304090c09150e01080a0203090a021c0819140f 78
    0x1003403113040244041d9800c00c25500340903600b842c00120b45000d0081c07241c031002800f130f03a085040203410010b10406251156150307010502d00403203e40c0c10307035088001c0302c25910385c50703030350100188041e10601d11800d511620010b0b1080070580c0507400306500003003c0d41110143e65900881e00001100d200002e004205c03083c07000986071070204000c0420b07030f00c12400070411980e03494001d03107096019200d0400c1c404000c6003001c0410301c007120703050f4400030901c0d040c100c00096440e002c0c1205401100c44051100e0340440707805040c007800701001d4200174240200001c2240382050360040c0c03c02d4a04450f40100540459010b10b0000d184d0000d403600200910310301031800846400410340514000107003ca10a000691962070040d05043c52116482d814149040f00c400100714460040030040d046205106000b2000c60001d8100c0303803540d040e124010b0012809821014002d00c01a00a007020000074a001c00f051415042240900058440d00c0f160000c90807408524020303044403900700b0909 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 794058642 1250 794057392 794057413
    0x3061506032509060215160f0e090c07021305010b0a2a0605090c0d12050901022b0807020f150c090409060c1412010b030717040515070e03 61
    0x40000c58010000d90a5000c2c1442100042d54040c00403501c050046484840108561901881079020a03040e500c0245030324540030044544801c40f04e140c00e000c10590b0000329281500460765102046001001d8404901e0100e4074800b10340e0003640101d0182100072508960030310766001c7c40d8180c03201803a4481c02c204e0301100c115104c1040845050005207042102407c60a0b2007101d200d140f400b0740000b040c0d44c80e201d5440703860004508030140c0603c1001101c0c03c0407582507240c150040c082da10704180d491081000407454001c05034051040c4085d2204000080400d01a00101001043d102c0300d040390349641b4182d0300c0e03004070400c040e0507401c0506a030919096582c21164001c1c00d45404134100038002e40803404480d8643c01c1110f015a41d103a68200540d0400403c0b181610400c1d4468503007200c4002d650239002040c4520740d41000d0100100d0200d0b402114003144065480c0c81e0200585420308201799030f990140c03080720085910a0100d1200ba2061000c20403d00001c4c00602201c4035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 794059892 1250 794058642 794058649
    0x90c010c120309151b032406050a0203040f080d090608010b0d09020d06020d090b060a050a090f0e0d0c020a0b0c3c0a02030708010e1b0301060906090f0605030615 71
    0x100f44200c07004040c60741d407071002001c203200d000040c005400c1c1003690400402409421104180004003407031407603403070070209000803500030004c0c3c03600c40c0b0308152a1807910340280d2550203160441c0124485c1c00901080c070020000d01c0300317084509a60341c150020b0f5114421343e42d1103400e01410010a02c10096412007003d1074110092141c80503203040d124034155200d101c1280c126038060000a5100e071401e0080c0100c0c0c1080e5600003908580c0314120320b03d40000201c1020300c922410544985800041c4241541030780862107849100d01520071428882500038415044804220b00c02c0b50400d202240c01c105003c159035a02c8030079002003456203600882900c860200e21040200f40c0418190420f04030959086540120440350080980b10120301c105410011141c11001445c1e01d030500851900d500020116580c44044088a103c1c03d990000b00b40900202e0b0400000c9504020002039103209585c040c02403542c0415041295a495208042e210034041d1002107481840c1d41c14042c0d00e14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 794061142 1250 794059892 794059901
    0x6150d060209010c06020d151401020d0e0d1b03170a2a0c180501081203010522020f030a0b011d0411070b010e060112020901090e2a03090c010c1203 65
    0x2201410070740707511112a500d0600b6079000d06119000141c030380460b030300c60650020323022015001c0c1003815200d104120300000e59517200c1000305801c2214035120f091003522200040780d5103a400040350301c0161340a003801e00099219210840b010394215404d02e41402181d82680c0c8041e40596a4004c0710855400b90040d05c013404414510401e808030500700041e1504403c0320062641c001942500424220909c040b110140e10010a98002060303804907800401e049a0544a00b01d66440180c41c05d01031280c0040c0c4561410311800f403000030b52a0303c07420760301c0246200e402c16000c20b000e550303c0c41c00110380c142000d10740d001329040080b801d08610310382500401b90718805522418100f4081c0e464004195800303038411601c0c10201c0c004c1c442c1550340407005c02c0002e03440c0703a400e5240c088000b00080441059221b0403209602c0400850b0740100c2d0040758032880e01070424220480e60001007015003a5000f0345860001d03114250305088294013030001b540c1c1694001e00030940741d00094009030040c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 794062392 1250 794061142 794061157
    0x504080912030c060109060f0b030c070b25080f180a030807020118350d0506010e030f010b1906080c030405070e0a051f05060a030e240906150d0602 65
    0x5020903c40e00c1d01240c0100401d034001c1c800d03600e0101305a447c0c850031140540c96500100382c1c1c107004200300080071403c02c080b10504c90744154030107002d13a42c5500303201411466580c504d03032150580c60b108070010790100c545402210014412504c07611041221419003240c00100a0243c0291b80a0404603004001c00e80e80032240780008a000c0301c150380500104035000e4401c40d4800082d10000041000e5903c2c251000da001502d0a10304039020081a50f080c0240404060031684032800039480707074031a8510450162005d011100b401c181d10301103502820841c01401d004885107011818034140d0030f00d901c07080360040c1c1c44481141e00c8600d000401580300400070740c2d0fa0301c070b8140b0004203454443c0c00f10344039980079040002d20307007080641c0c140768429441106070001e2401400b403180c0d9075940211008140141000501c540800803594104220650034014074401c41c408469510f82c4051254801c01c50318050701c0f019a64533250408007540e1650240d0440222a000f00014410b40c2c0200314a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 794063642 1250 794062392 794062429
    0x1e08070507351903080f0702030703052b0905031b0115031e0503040623070201120903030902090702010b0310060f05060307050d0c030c02010e010b010228080d05071205040809 77
    0xf0744004035a425201410f00401c50028040601700b00d0050300c20480e44e0303080300640c40910701c2d02c0f9054074010040e000c0c03081c2000c0c0501000c00841a00c5111846001c2440e481c080248101c609904005889030000f01101c800340e0020241c0e15050f031818411050542021466110518255101c0c0c10641680c0081d940361149503601d0400400c400700040c1c001003015a881d030380c40e8541c0c620320104000002d407001d54100c80500ca03030b00c0180e0b049084d0700b5801100840000d03014405084c202c01611385980302a40044891040c801d104d5410b41044070b070410260112a8032060800e4990110340759446a034401610080d001d0069140031401107811003060305e030241c2040c000300705a00848003411041004a541c3d9a46c0b02c540d80c0d0203008000c00020100c1c020020081200d002035180c080907583c0d203007084180d41c4901c0d00040340b40501070049401480c00c41e10b4510800c0e0a40060070f040c0c0d1504045141088032190010351402018401c41d806000d5504140174082800b400a80740e00d1100d51 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 794064748 1106 794063642 794063653
    0x20d0c030206370e1504050d030b031608011e020307080703020f07050f0303010603110301060c120c061b03050705180d1e0807050735 59
    0x2030100e20424203c003484090000701440720541040b4500d41ea603e604003480004071a800000c3d01040e1108480c51115400c8003441c07140d034101c400510303990144031041040d80c86a00005151704020701100d001113400c110048000c916500f0000160f0343d200400481c27101649125102c80c5d41c585400c51640c240144014110080200240180351b000103031010625000004c03071ba905500542902e0420301c0e07001c1015101d90080c80385000203400c0c0301040002c0310000c0c086a04a94494650a81c80501541e610701010207003020768041c440c8a055040100310310f4007031040d161b5005000c030b5141302c01c400805000c0f01e00140c590000c11030240091700c1780510507264502d4a42c0116680481001c59142200c2c0d200c19102c10101500c0c0c01110134020840440c0207841c40d1803203481070ba003e140d1641e110760142090240c105218065115500c411b40c201c508075000702964003004d07600c = true := by decide +kernel

theorem cover : BRFrame.Cov 793884892 794064748 := by
  have h0 := BRFrame.cov_init 793884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 793884892 ≤ n) (h2 : n < 794064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
