-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3928
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:05:14.373449+00:00
-- url     : https://prove2.me/submissions/c8c9978f-4b34-4202-9109-b547321688e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 706294964 ≤ n < 706474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 706296214 1250 706294964 706294973
    0xa2a05010507030506030f1908030702030c01060f03021003020c0d120207021e0405160801030f060f0504140601080102040f031106040e070203070c0510020d03110d060e010914091e0a 80
    0x52094504000013600e030b60500c142898144070744009802113400400d040c40030300104481c0d000030441f024100c100080f0016010303500903c00c48840108038070081090700d445080d81d002c4e075852400180d019046001021301c035517009200310348020000d80002d001081e10403004494003540c003900c054030f058090251000580b01c9500008c03924040074000c00c07062807150240811160b008290509204940441c02c44041c0c020807032a054a400101d00405060141001800b9000c8242452803d030718217800c220511803d504034000a103109010703154913907610480c1900b41d005900887e002d12021000400006102456007682018083c01003400c0c25580c010a40b9031400c110781d4400541c000003101e5007000600a800c8000d80001c882608a501074420700940d142c08200c1841c2c141599906002a01600c94042d01c4020b00d4900040c000c0c02c1d01c0d802c3c1d02d80c81da5800c0c440c0c5100c440c2042d103038080155403071f11454070481c0000000d00c2810340900616503250700309808c451490194a4203400800c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 706297464 1250 706296214 706296221
    0x3010609140103261c18050321060109050d0204320a05040b0402130b130617061b0a09050d230604050c0f0f2809020a2a0501 55
    0x320710180322845542c03460426000208443e00c02c0c2d003904c0f401d885040e00c490b6120040e83c450720b280b80c05444e66801c0400b41d031801000f40b54280440100101d1184041200010003003400c0741c00c03410400c900503149000032008203002d6071a580413540c0f0080620080c209001c8445060340010000306d4800001d81141501c6a20500040758221000d5601c07007100a03c4040290044d8503030000300103c6c0740c0740d103e440100c4001360000744180d03200d17458882c59810a8002c402e6140000b003200f000c50014039000300040c001032040c0313802c01590701c4140900d80408108144a00f81c1c0401b100c0c0c8481083ccd002c041240d000346402003c1c030800450102d00740d00c03070800f0300392454407450010506800c030004040011a105003c1c00032a0322a0040000203080428941d020b0703103095806d202da00d4060400502140040c61403550049046040e0400c905044a0a8800c460351500c004443d1500c03942081c050f4400c0e162800c0203d0030300400b00002d640714540111040041e01140915004680d8a007400c1d03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 706298714 1250 706297464 706297481
    0x3070c0602160e01060e0d11040608061501031413080f1c06050904110f12030c101503330c18060e030a060b010311040609080d050f09090603010609 65
    0x180d0041e990100341c5010004042c001c1c1602e2070780c1100315854420000d11003100008224002c0c0c01c80c07031161040241d510744034521403500030b005100c004c1e11404c1c1299100803c80d80c00c3c3d6501441921100154001c1c807884040f00754604200c5a6962010550500800da070710007103424190400103150340101001c080d10b000360804403541e9044014026010944126811a0344280c84050a00c07001405c07250740c1040c4c0b500d066621910782c842d07801c0052031042800c081505e680c000020000105c4c0408100031400003c1051308024400d2203400f641d00302c0c880c03800014148600001040402031109034500071341c0f13140d043c0c1540742c401e01d4103c60094544410940d0b010440c881c0b210b0b541e84900c80d0300302c809088c840ca002c1105020000000c1d60324003c011010380b59a0381c0b0b00705403030207900c85c2c0c02c0620304c0105070301420740d0b039562000c0080c40144c15210305c25181c02181c06035021144600c00319680d0880c90000642071810900c10801c807024040c1829a15643c3c40c00001240b03505070140c4801b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 706299964 1250 706298714 706298717
    0x310030b0c030f0106030c0e1201060807030809030f07032a03170711060309031e0d05090d020d05030c04030228060f030e0d090b0703050c0a0c090e06040b0c07030203070c06 76
    0x40700d00f8915100e1101c490f042c0c0150080c1418905500d54555000d8100b0006883c110381e81c4c5003407881e440d0380340d0041800350402c1d4814005d401020084c004020018483c5803001e404032140b0035074081661b5210072440c04010400e18006141000007502000e80999420088074100d81181e03407070361047c1c4800f0071884555070320140801c07824280001002040c00c00c01c815121503155180068200c1e840344114080032902c00103104125846034098026901940140c407420042030901c1d02e4030315529550411148014418100107000791440b030000d80b8000e880911003142401d045900700f000c05400307070b442140d60111200700c0026000b051041c89008003600d0316299a0400782580040c10340d19540d003009060350003a110500500d5101101008442a000c03121b41c4030101803400b10703850b02c202800b10342c0d1449000326610512800e4903150044030382e0000c0030010a0070180000c0c0e1102012600a800084c0000018154500110003010000d11901c15281f4011306541da490720324100342c10200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 706301214 1250 706299964 706299967
    0x40e1902040b1804180201080a0207050c0301060605091003090c14130507030b01030e0c0315091207060b011d0d030f050d0e1c1409010c110909010c1b0302030403080310030b0c 77
    0xf00c10b00f810701c03c0b0014040f880b052001340c28440d800107818824042c0c46011800c0d80001c1c03040900c032052140100b076190040090004031340e555001422a040303249001d1080d01400b1072048524081c0c820300b0720761a07100e0780b07407005141713886c802c10203008400c004075801140c60018194001c82c0c5106142c882e898641300081c0d01d040c0309000500711050b64119400c1a40244402c0517a80e4002904140c000f0f500c215018580c0d960440e407505101908136122040100031a840d400c000041d086005071010030303a11403440340c01d03a0700001d0140f20307400d10054003c2c0301d01c060740012a10800004a2480481c10b2840c03902d03c41003441d00464400c2115034080b900101c03000351501e104031070311040c803992030310b0314500c104822003410515124010704641840360740f0400500304800c5000e014042c1030000e10520b090300e4a00c10440c040c1602c1d00e070140c0010031265200e9080307401003135045e4101d0b4056005508181c2507540b004180e90000e400060b840700032010000010306c01c0c10300d480c4a040c07802c0146 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 706302464 1250 706301214 706301257
    0x1107060e120a0509190b0705030d05150f0411040b0c011a0312042304112805070b0c070506180c03030325031e020403030212040e1902040b 61
    0x7030904040125507030a40d00104901d4031000d07403020650709883d07022510325055034144501c180040d00a64440c90a1100c046245404e124010000d44281c5180b410244002ea0361400c1c00110706000c0e400d030300d500c6040c90808904c9820b0543c440300b441580046d54500d0aa11080300c3c40385500b1201c1c00481d5030307440c0c0f0344000e9240407864903190003000560080c89044011940311259004a000342401385e113680c032550303102d070011a682003050324003c1d004001c00e0f007040c42c2c00366055000782002c02c06444504042410107400c01481c10941140f980c9090134000302390745810581300c015000044101052149001213107007130041c94056981c468071407507800f410801560800d1a02000580b00b50130031301c20003c00c0ca045000314000c03e1081ca51000e0b000c44101000e40081001d807a1403040e400c0c0360a040c02c40c04c60207a0080003901d02036000c4410000300e030200c1118030700c80d86c0201403050304401c02041081a541c04e0814101c0340c03000001d82000c0c1c032050803c1107508801c1d4207041d80201070300329 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 706303714 1250 706302464 706302491
    0x51807080712110c2517210306010206150102030307051c0e010903020709090b01090f020c010e06011a04181d0a1109010909050c06030604150b0306040c080f060f04110706 75
    0x1c4407441c90100c21101040e950700700680388171040c50710a40c22146c1c1400c50180c07144205016501c206011010101030100f04080d0b242c4198104a54a902501c2084042408205501c0c0d14494004059008514644c0c4501045035960440b40081007903900004802c840e10301c503806100c03146000a00005000d4521b814002c2c035010080e405174110900d0f00401401040c071900c0d85c681551031014000c141c1180c1310350040003e11403c0c10310b03d85540380c414500483c40c07006c2160380c101c0724030800000240f0300910305040680f10318421904825804840d15100e00400d402c160b0901401c1800709002e44007141040f420030701e030804112485880e443c0030382c41e50700d004014540505920b9108010301440c40da00c4655609074080c103503200784004000505540d9542d001700d03031000c0d800d01c814071925a46990a03181c45c1c2090340c1a41c8a10308010345110702d00d00c5100a03e200c2c5010050f00c0920351100c605020050000d02401134206840b143c4601c54001d00d80002c2c20350030320817800010400d01140c0c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 706304964 1250 706303714 706303723
    0x21e04090e070f120b070c020d0c0603050105040209010c140c09010303050c1b031b04020d0c02011a0111120d140c09040e0d0e06180a0e10051807080712110c 69
    0x1501040f18948014889040c444654401050380400340c000349031103188050342c110682c4c18000f98081f02030031030a0308000c80f403080d0404864564800f4411640c0740c2c403c0000360300800c200f440c0010f1500c120072000c40c0c008000000c7d00d180c445c050329940c0100402240d46c485003600290085800001d10080b201020018503120400341d00c40d2902d003010000c0020f0729081c0d50004401640c241901c10401682c0301d078100d80704070320b110a007040007010800d400783c042c0440304401c1503d01040c0e080c600440d40140303000007910010310094010001d45100145042d08086001e2500325511034196a0310b50702030b01d110b4010000b06124584425034401000705a8080700744513034403508038034000c000d41034204422901c0c00c1002c54120380c94031203006110500c0c6102d104c079264030900702c1d03400044900c840c00c00c0601a46280c411100c0c03060300c66041c001844400c0d00800014140b580000300c81500c91b220450300000b00d440c0c04803155207060369601c00d45001c6212032607444800107040c18810350800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 706306214 1250 706304964 706304969
    0xd02030403020d0602031005040204060c0204290d080d02070b041e11061602030a0807020a0e0601020a02060c0a050d050301060f0305010f03060b0307030501050705031504051306021e04090e07 84
    0x100551810742140d0205041e000055030040c01c2ea600400400e15403084403a18102601010384115140c641e03c000041c42c000c0908400c0c5d02030341c0b0b41b404c0911030005d0241c1c817003104101d2510449030f4500761400e11240c9040301400741d40781081030060301591011030004101d214000c2d02c5030307880d608160504015910124a65000d8840b8084003600001c2c01c0000240c3ea000080310843c2d1070b1400d020b80181c1e48165048025130501855403404100105803015000040c000c1c2c501c00c244980b101417603440580290b48048c00342c1e002c2203a0400628250300108800c0c101d2105550108606907149440c00d101c140d15140450300220050140c1d41d800038692074503856901d424003c45d49814070341a410301b070b10f0001401060310350800303220a883c108031035002503911030020000c92030f11110040c50341d00290782070f00309984882c018060500e05030051074060500312004005000480c2c0d1170b00000c0d80000c0c5113402c0f1540944100b8140204071018000601d41c112000c5820785021100030305182c141e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 706307464 1250 706306214 706306217
    0x10b160f17070209070f090e13060912110706080a0915020d38060f0705060c03011e030809040917040e090715080f1b0c030c01050a06140904060603061d0d 68
    0x2080c414861b2907201d0200001c44030084044040d030b443d29400884101001d031805050903081409032001c201a41c008414001742640d42c82d20044045690140c43c2c01442c4203000c002740c8400f011507079460641c1d20090040340f04045490740c00741c15107614800d0707801080d480d04030241e90300c840b2a115491100f9148800100c1c003002c00740c2c1c5220744a41d80300440c801d51914001c28000c2003640742e615101f001c842c07074103400c20100e80c024581065181160b5200b4018a03258a05171038800c2c10b004400301a840580394840701c45400c040700007007071000038020392405544c484002e0401c500b00800c3d01001f007018002e0607446021a2800312031072484c00c1c0c0740d68010090014000301c0180502d5001c0382c00364202925804140050b01d031a000030f140c040030310011081404001650703800f10200007008108a803e604002e00c095514921480110b55181c8594000003401114011942c0742044225900900c94800041c0c500c2d20ba03280c0e441100e0a00d150b83d00300d643d850000000c0108100121120321169 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 706308714 1250 706307464 706307477
    0x50a1803030b01171303030b060f1b0f071841060f03030a0810090510090f05070f03091a0c13080a03021f09050a1b0e010b160f1707020907 61
    0x3c0318021014401705002404040d681c03a02101a50303500b00c00c03a00d03002c50100c83d20383c4806850440100c01d6112001c0300380e81d80302d2440540c2d40604d002c6070000480305560070051001402141c00e40103441054181c000031030310304605603400b00000300410411160049000480c448500000d008610f0103400e151042c0c0402d440c9182a507000022101c045441d450240101c1c3c80e1400c5070b14080c02e21f50024041242440d04000c80208101c180340c044407120340c414440b210078217044508484d41560b8050014820303070300b10941d00340a6044501c0051081c0041c48100c0d034043c540610210081c3d500d802902c50010f60060300c0010284050054015100a0400d81e1007030f0341c0c007039a55181c0b40e54640c0c01305041d103000700041e100350303000c0b11202d600311042e240c5640d81444c048000302a08d5400f1001014100030108190040c03009141c10380310313a50304c01d6181032030b40d03d04510642102101212010015002c0d50001001e0039040462040d04011240d21491030344100301861000916001c1040780c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 706309964 1250 706308714 706308721
    0x101b050f0c04230c211303031b020c0603060109090203010905010906062a110603040f0507060c0209061513030c03020108060105030402011d0406050415080708031c050a1803030b0117 80
    0xc0751000305410120800441c2e80d82c5001041d90041c22030174021800c9544071500402c12031001c1252481580f52099070104040307580150f0f15000d0100219159005174001085403840341010001550000d40506003000c1c203607500c0001301d00344d81c002d1b000a41190f403101c0041100b0100c40c005c92000c2c0030b4a080005d01e4140c401c2170303070510f10651640ca0041d0130480c1740032401e00070f04903a041c1c50740801505540ea2460103013403821402c9000d0740215901d11907094002551482004418407542c1e0050016030213442e810b0410424040e98000d8280c9000d0820400110600600d001d0000790303c10303440007000c249940005070030b4140040455040c00404c1007040010b0703910030403501c402e8070f00c134074600c0411a8180105005080c2c03500324903002860840d4421003881e45003c80d008030b03480032044a00050300c419010351a4000c03062292086005005140e100d20050380040e54130400b5942c1c0040c0c507440c03014003602094a00b01c01500400d69a981080381f81d40d121026440000204607225910704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 706311214 1250 706309964 706310021
    0x30f0f121c0b0d02060c01140a0e0709090c081c170f060d060f02040b04051207060203030c0a0c0b040303050f06031b010c0c1802040e0f0402101b050f0c04 68
    0x200159400c0c4640e03482c10405450303a50350305072140a940190481b61a10000094580241543e17410314903080ba100c00010300300ea44034040c070030b0042480000b40c65118604031204000e08880e074002c4444ca00021408620714004101410765001c40f9040c08c0e541001816019040b2442c500c41c0d448180c60b014104502c3d5040d40c580710350011000d0303032180381340c8032039042110042c007000110401c440d00028001402500500151069030b4048a01c0400a040145015518100342c8548400f60300140001802003241c2006485e0484050404c030001440c240e8895181d03850807202100402e650300706002d4000b5406c200030758080300c00d0700203103041146000b915006115501c03038141044041294002081a545a10402041d5450719140e10100b400c12400103504240105007200710104001a00c00400c0440c1c0c9009503000b80501c0f462414050080f00c11401d100c40f0840007612242089000078000c1094010700b840300c0000c0c0a040041e241044181c5101d00400000c4400850f020354110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 706312464 1250 706311214 706311247
    0x7031101020c07350106080714030703060510080703080a081f090e0c130c022401121a07080a0c0203070321111206100503160804020f030f0f12 63
    0x1c1da100806071426200702203150060100342075001008851500c030313455404405411100a4480c2481510340b501e8854000803045520080d110f541548410707400c00100d4403a51220350410381d03450310207100781d03201c03000756240140c40e9204031401240010860400307175211084941005082407113000c0850704800580b41c150990142c00703001340e0784103040301413a1010480d6240102000d8020b0540c0c4444130070645c010003115400d1b0340580540456003070701000241014400580707100c4608020b9007080c180e07440e00c0c0d08a50701103d0b200064001b050754000040710240c8521002da41d000b02910380000c41c1d100b076440d11044082590300902a85000035000303c42038100b240c8440312090469a045a9000a02541c0d40700356082c0800040b03a40a180130700c01194031034507084d20030100525503031904650320b11044071310510003518140300c0d0090900c1119541d82142c0010700f4028200500400603082a01e10044020281d001e40e4480d64000400d01c0b983c90303048040d00351242040880181e44024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 706313714 1250 706312464 706312469
    0x702071a0f2b0905100c03060e070e010903171e090d3504060e060702060d0e211b0d0206070f050705060f01170703080f0f0403120507031101020c07 65
    0x8550503200020340c04400d51a400b14030310641003090000d000d0b00e00b03040e034950102d400c41110490a081c00205c45034000d00805084a0340112203411031b0361004030448070000721100d140d040009015000001c01c406401094110706c10414259581350324000300b14912070620b03600344440006004148a40d0380e240d050f000302e550480c2603a14501c001c115000e040310308031003080480320030705030769030705114000802307130042d240c041c1c031480c251410140070003800f406103020095115104214029080c6c240382c1020b0031500c2c02000325a00e550050b0f005450040803545201201c0501103005508142002420460550702e540503003551a0079503002500d500000f8400810700194032078070541c440c498030884609640002c203a17100360405003004010404203100e010f240c0368003001e40d0308001c50041034100807030390f02c6501d252070003030b0700100b0641d6504039128440e50349a0500000000c1070b040c60010411a0240da65980e4800f230350b18010381000c00324115140581c2c03041c40000c41d03c080002e141c00a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 706314964 1250 706313714 706313737
    0x50f1611071217160201020601080a021003090503090424050919091e0302061506031317090d050304050a06113a02060106110a051209010c0206030702071a0f 69
    0x501d0110b81c100228400c021403c035011812001030080400500b115642240a200368281d0350b440e6600c0f6081e0703035038440600001e9401896591982080f5019511011186228101340c03400c119883c40043e04903504056260303242d02c0d100300304841c50b04101d5105005060b046501600509105041d003000c0010410140c4000356200101e10520890400c20682e0b840e02441041c1c0d115180c2c54000d4960000b80d4a12225131100b5910503084d10700703001078902c100d4044c0081e6840c050552250a80c0c00000303a08054400f0303042049800700e460344040c5c0b5aa850080c401196900d29040a0004030002648100c0420035000300540103040c020941c6468030f90200c0c00c1d4240e00b100d10554059100805074904a42c000c55900e039200e554001c10310f90304030740d480d0301d40155980800070300c2da484640703981000f0223a030006040310b0030001c840c0c8040c02c0402018904103036201101d5000c034916030302c2940c0c00400350380128010071050b00d4002d400e81000c45041081070610800c402c1c000c0303c5002c0d1030741040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 706316214 1250 706314964 706314989
    0x12050c07091109060301060519091202010e040b060c01060e0a0e1c030b0418030908031c15171c0c0206040302011b020a060c0b061c170c01050f161107 66
    0x10004203200342c0d1103030f1100824160ba2542e42c0e82c0301904540c0440c03100d8050092190003042850b0207120414200c0340405141c062080300790f401150398120949015910a5681020100c246c0303481c0c01812000c40c0c44400020318a041421045512000801d02d070000d40c14030007800c851200103c3d240012480600d071666035440c4101c002d80240c0010302100d80c2180c0340c1701087c890103440156801c01a4000c3d1141d40c0c00544402036503440e48981c40000c1050605500380c0c02d0a001c0540c00046251412041c60b01440d1f00e6001c0488101c00851107203146030f0045c07a040800418200c0809055402421b01d420a85183c1d03011030601d000354440a03040c800003480741c42c1040b00d00c000c00540ca503401803003103072040d8580b40058126440901c0c169904100740002a40d02d060000c038003000d2149003100c04c1b48a00080e81d803071a1940041380940440c2c0d20511030100110b02c2401004c4c010115151301c0401c0703140a22440503542e25884c6aa004c004200002c20159480442e20718140c507200034000e03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 706317464 1250 706316214 706316231
    0x307080304051f0f18170d060803071109090f072d0305061504051902030c07151a030102070c0603150302060c0c09010b1e09010306080a0b010312050c0709 68
    0x16040a6100c02004455030010f030340c9142c050700c65440900f00c1c0c07040000c10041842140d2640c06801c0005c0d42c0100a0038040c491284400005c0c000f401d0850b440100100380643c94100c00f81c00c54021000481e107007440e00b145507840740380006640f40e011000a004001303400c0d0010a403035903106140301c2c10601a2507402d5680c90701d000c00c001e4020f0703180a000102c1c1c41956a1034113942e00c2100310350000740c000c40b0306902500c520b06805018054036405040c0066040040307ca00020351016043c2044140100800780003e1079244000c0ca10001c00c04c0c000550030b540c40340c1130507810341c0b82c4c403480d2199104209450001e103e4800440540d00d65250010754078240b46130105031042240c2006e03500c40c801040001c45907a0000309a10b82c07141c2606e601140740d82e6595406141d01070700000c4041403081c2e54030806105102e0019145124051401083c2580d503902c1481c20038414078000d0741d452194100510501c11028090180341c00d25150051070709800d1100d1688800c00390181240c0e0a49a8009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 706318714 1250 706317464 706317473
    0x170304170a090305061014270c09040f180b0411030a060506030c04091709010903060f0c030c09150c02060f12090c0105070f020918010204140a0e090307080304 70
    0x81012200d51032403658882550300060b252101c540b004865911440e000039000c580d0f040c0b810f20407640e07900864082c040d40c0c50100802a12110740110741c01540614042441c01200016030144d0074003942d0940c1c0d40070345814442601c0c0d100307900d100031701d0415031070704078400300a41041c640075080001901c440d1200e1408e0008000019809a410f21502414405121280d400b41e8000c1d03070704070f0803588000c01c85418441aa01c4040c8064060f0039000c0160705060102001084c6074a030515007403170034030344a40c3c50000b21203422100740b5801d81e403480094440b542500c20f00d80b2566003401c04010b0b10f8a04813182280c0c500d0541d440041143c500b9504085444100a64641941014071241c41d600d81b204840d285c0c60701110240e02c28411100741889a501910403541525002202034180751055002d03c4000540548000d0500d5110303040e80c004820280701800250050035414142003591801300f0030880415080b114510401c4000c3c0a00c0c914000100d03608507501142d02c540302d5445082 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 706319964 1250 706318714 706318733
    0xf060402070203011410060801080a020108281805010b01080c0301051c0210080601080a020c06070c14070303031a060f043003020d090801020c0d1103040b070b04060e0a170304 77
    0xb0300403170001c0c0070014032a41c0c0448521803001c0d14a641c2c2c9601d03d80c0c3c0d880d0541ea17540e9254003806400304621a01141c0804640300c50040d44000440102485803403d0310690119440482c0d0741a201500b00050b0702005402e008100b080c4200b441d00c0720082c01c01c4003079840c0d03510040c818103114084c004048240c1000e440070000d00d040d001401d140c0e410540e50000f03001d98404907000390009000e10000341e82e0406902c00c0ea2507540400000b00b11035030300c50b031003a0740c8200488025034030f403c01541d542160354810030144c1c3c041c1d8425074010440c0107100d0a080e000e8103284005901c04c1d40103001c5582c00c1340c004415101103444800a000c42c500d00e8400b0501809600482031100c849084034800905030002401c8540d1419503440380b00103640c40b28060300704e0044484100c820703082840c0c1d00000500c12407103403003001900720507685002d65aa00f5001190320000701150065091405c2200b480118030420301d00c01e0502000c2c00108805584110f80b031940070340d40c400e070030602001050034007006c42c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 706321214 1250 706319964 706319981
    0x10c031d0d06051302030607080403050405040506120f0f0616080c09010e0a1508070f020615010207084c110f040e0405012a3207050f060f06040207020301 68
    0x300820250404501d640f14240088605a0080c490800230440c804e10400c1e09030b100700d4140da10581440c1c1400104009048098241c41e4008412114590020410b0045140060a070303001445c445d000128a0341c2000f200406242d18801017000702524244c114a880d0b521244072441036a6601101740160f072455000010b0320b40141212a022840140e002c00200d0031040c50307200c140d4182d88600d01216154440a61040140c1002006c03846401c20505d9a481c912414010355402d00c4d1540e2400d40340c40c10a61115503225189000b0719018600071601c54460442c10b90300440f55986480340060b02e102e019514104556952121012180060161138040303ea040210303aa4998400c1540b01000c0156029115540f9003d03070f00707420800f02199400181e0281d6940315100c1d40b5242c1c01e031280e400159404c9480503624180100b540480079007541c10741c0707c5102c00750b25600c441c00c020f49000c0c48070840040300c1c0d202c00280800b6980c892070241c1d000804070707000359841c411440032074050001794 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 706322464 1250 706321214 706321223
    0x6090f0c0a05371205150f1f09050f060307021e0c0301060f1d040b01050f2806110d0210090f060504030503061831290105010c031d0d 59
    0x10100b0080b0412514950040f00325981d07500250b2040c5003040c07000c40740300f41c82012140300c5114900130320303040400004407070000090907040301003100b034000074034945c0183e0a10002680c80750b09208500d0701000040001000360703001802d520340454069a9152002e040394008824103042220710b40c004c1007d2001c40d100500248005581c844036842e00f05014010f5815208050301d031056020300041c0f580c0d1080717821041d10150f6900c6d00c010321429441d903810550300a078526000d030300700400341103400406001c0e98081e200c51f07a160020081c000b036100c441100d03107900301c210307030044555000881c3d200140e035042e4009a1070480c1e16081c01040494200148a103061600300800d164108010310b03c00c100980c0d207409400003401d1100ca0344141104ca4202c09520220801980f80c0d030b69020000c0b0004056025000410540300c2d01c1c411803500081800f8846d2400e000d4520107880e140713031801800c00f0308084d855162241c0c9d002e040e030402c40c0405401e14515a0b070140e501e40d202d81500d0f1542c4e800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 706323714 1250 706322464 706322527
    0x803090d0e03151003061a040f0b0904020f04090803090303010512163f031128020f0d060911090910110f0f041a040b030a020a050f0307030506090f0c0a05 68
    0x3e550103400450556250300c0c817507440c08900040032400d032b004100d010500140050703299035035607003008601c1000081440e0000c2e070311a2a54002030522004500403801d45c4000c50302c942c5041d040144030152140f01d0f4025030000890800401c4403030900d2416928880f81078540310400320030280300240d0340d50340c1c01c000d145c1640d140040c0c1020f10b4007240d1018000c2e9603106030070040c00746840d6034038103200c84201400d124601c1c0514010529154003070302d510041000b182c05c0915000030741022490340007983c219503a00c0041e0b0800981c101c0144117003c0a880c00b4500385007003080ca60700d44d10400540181c0645070328440d04003c0400c0c040301c48203280c2c411140d40781c010001381072141d03420602507215030712440c0724854603480d0b5684c15a0100c854084000c1e144d40d82e10303003984010f0340003202c03441d06005c418040003401c0600c10002d54494015a50001005c2c40d03c0c404121461a000c0d10f800f1a05070604144040320009004a80c003804817410880c0d41c461400c1d00545105200c41102d4507030000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 706324964 1250 706323714 706323731
    0x60f090c061e0306140f040f0603030f080f06060304030f0210150306061a1b0705040507030f0c030902010f0e1207030506160305010524070c030803090d0e0315100306 73
    0x70000c0e55000c1000c000b22400360071408110081d01201da00d030181a05c40c0c4214034000c0c2d80e51501c440c0000d80c4c00e00281001c2070385502c1c080100c0c19a07504e608114041100101e0005103503604c41c40c001d6001e4480d010900c624140080070400f04e1001500141c20814000c80c29184103000704040703011000404e00c1000031006250545a100300c45020489009007042c0c0000394843e0055080c2c030415020300e0a080c5051040003001d041e48403c1690008030340104900041c2c0d0b607546100e02c500c12602520b000c40c0450b2508000011180803416040502d45050448070260342d1001c0c1e15400b000e0241004000030490f4000194101c40380200140a845089400f10400070301150302401003001c102d84800400b810881981646d000f40100794000d070004405d65803021740704140100d81e03040e440c0041c0c6000140d403207200721407006800c2900c0d505000420701c85101410025000d1120b21441c00c85284440c100000c0c0c0c90390102f9083d404a809400c3c0400c032040e00c804000b00003103a221204021008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 706326214 1250 706324964 706324967
    0x120907122a08060a0b0603040218060d0818040b1002070303030e0102040527061002060a0218061819050109090218120d140412060509100c0e0301110f0403060f090c06 73
    0x2c2c3c1110b00c81d44542c2002c40040d9181010710035607014650042c900e900c2c000c000e030360258002ca801030045610031030284450000c1030142006002c440303001200c11400e004110148010740b2060200f580c000e100015440d041264040340d50411369030700d07181c003180700642c00c0500d6019000340c0d0043c40c0d10084203514601e505422582805860458401004e5180d6a02d8104000c0d100d800c071440e0003580040c00010800d5034154020060b1654690a5201001010020400c29004400c0c0c401000001c95200500c03450541030402003a0080c0c0b0705c41140f40d00b8000024000e4105200ea0801c0d160042403c40594416a40303290f01408040d056581204007000c0b00c65230b0382114800d51022565400c80031081c00c00060459055444044ac07040200322140c0d0f411009200051142600f1b0040a601200c0200f40b0302880d11101602e82e00c0000c0c20300810205030031035801450301e2041c40c4007000100c17051700c509030556080343d030090b00c00158030401c0c1141e00e003e0198010300800d01c900d9040080b4034103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 706327464 1250 706326214 706326223
    0x140708010603140d0f0305100f0305030a141614030c010203130b0c3402060c0d030605030c0a060c0c03061404110d080d0c0207050402040605120907122a08 68
    0x201d00981480381c0c0f025500c1003c0d40c60f40c19448150000a8a00e90711130340c1c040c080c2d040580c105280c001e01c40d0400d41c0e03c0d150281c1c01c280d103400468258000203280200700fa40444052980b42c40e49105502d0034001c10000200d4528520006095201660a40325000800d01c01d4500e40d10074507009550343d1900c5140710a2480c02d4040407aa40b08000002c00c034044419010340344044600d00e00da5400412050381d054076003580b80100b2a650341c0480e800301c010703140c420150461a54000c000c001c060301c501006800d80d1a55040240a81e10101c07221040356116414042290001e051500412400c1c0c1092081599542c0000d03180c58200241c207007802300c8003135826204a0080307062140c281e5400c0e04004220f05082c0014000d85801e20002561010942c80244c0b500000d0040760301b0070b43e940000c18240e80050b030040c00400c80c0480c5480c1086070091b1116481982e0a000e02900e5003803620324034409414000c0074085094029130310340c00c1c0c400a94464405106d101d41412100c1d501d544103a41d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 706328714 1250 706327464 706327469
    0x106300504170a0503130503071203020d0b1915020709020c0a111c060b040608010f0615080f0f1003020d050c040f0209030c1e130504050705060301060512041407080106 74
    0x10004005503002008140344243c544580d001e607589071440e101e0640260303031002010003d070f034a40000c01c40362002841401c1c2c040311141c3d117a1400350b00d840481c0c0c603c078100c605100110740151005000c003281e07030900012160585404440388004101c00050407450f05204d80c00c1041c5103840041d510311075100000300c01588602c60203003001768940c1c41c41170180030043e01c18010100140000d030000011655041080c141e600a040000c20030755500c400342c207441c3c50203044031304155201810705c40581da85001e4402c0c0c0e0044c0c00c1401c0076003406881c8108c1e2103002800c104104a1200c082500c000076005d6603401541c0080c03008140401c1c5007091500c402c50301032040c0c07103030b440e001800c19a28450b00036601c0c0c0f54001270250038054400410300810380032601800f040380e05140c0040c070351035035608240c640300100c0703120014003864079140003031800750982c1120b4800c02c0306100400c4003990001c22078081308060307001e0000548031072500702d5503202020f110701d10901400b50085100181580907004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 706329964 1250 706328714 706328723
    0xb10030204050c04080a14281403121501020a02090a0c030c03050702030412050c09040b01031101171314120d0506040c050708030408070602040617060111060106300504 74
    0xb0360711800e0b40c0c4811482184500e100641101e0a110042071510424030644121801a6004103103015880108003a15181c0c4820486d000b0307400c1e00500c003680100103020341262006501c0c0c06071014107046e00e51070050190240320442160000c403648284040c0311003940c050b010001c42d0810342d2988010707202c0308030f030080043d14000105002a21038000d050040050340c02a502d06400c005c15001c400c004110152118070031b50400e0726441d11031018540c0b20f903000d000c4032401c550440c50070454840100e0312032410407844104040f03843c1c1000070710503004100301e0b0003244410b409103410b01000c1c030600000c81c91401402c071440001d8048400034070340c7d07580f5221b0411055a41308100402c072102502041d000030001d201d000c002a0042005582141c01580c00724105150b07581d0758000d0307900941011000500c0e26626840140321841115000f06003401d106003504118000c4664602d4144146804c1050fa0701d0b51559180c000c0c090040c0c0e42d21400f5034030625000c400040b0010388000d550464 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 706331214 1250 706329964 706329971
    0xe0d0509010f09061e05430222180c05040c171b04180b13050906061c0b16020708070605090f1f0905040509010b0d060e07030b10030204 60
    0xc0c5082c030504205040e04d004d034807030103851080640320b4013032282044000f8051010400051008843e0009082140200d601e400f4819100b9000d541c0103c00144101c0d01d030808541b884031005a50300c00081e03890580d880001c010b80c001c0c0381350b044060b141c080d4030320240d0b04e4040781450502c1030300030f0700c0310540310700f540c041c0400d9400007411104031426050010010003428085090811041d201d0829030101d030344a54186501d80820101c440803d101407020560b440c03480f1803160a18500c90010f004909800300540d15240c40b600d40c0340e40000306028401c0214000b0a007902c2c0141048403951a04a6040c400500c1c0540e04101d5070f0545050309409849590b0b000581c0c4400013400401340c0d903840e81c45c03508080042c0700307000045c8148944190302c411000490000c01e80740d080000d2900640f5514100c12520f80340601080305e802418008442e4107002c10311044c2d48401003040c158035407080c00010b200000440113400d00025400050a417410a03040c04401c0c0d1646c0401025280215001c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 706332464 1250 706331214 706331237
    0xa0801050312040608040807051e07030302010b040e0a03030506040f06090207061109010f0e031009061e0614060d02400608070f0201060e270604030c150e0d050901 72
    0x100e00900841c0308110001700010300140024500001500d4000d115404446008800c100d2410002070a4214200c00c1d130b02041007000ae043c0d090040c090300c0c2c1c20545040001c0d481070a80262141030684001e000c1c50744501c00724055880350b40c0320189104e00c844040200c84d44030802c004c040c0d407207041c040e60043d0a2000b2071001c07030245800c131200d00e101611884d601d4010100141c0d64801010f40042d03060080300e000c004204240d00a030700380184103070000500340601c80c1d552251004003d65070800700703241c000c0501c506080d54201d0a06040115909619010940802c101a108070410341199810308500485c401200001102c00c0003060009030164050981c040c0d03000ba480d612408000814280115191034000c1d40d00c030585411910001c00c410762500000f079902107095807100b040c00341140546a4642c0240b04040c102450f0f1005810507041c43e850050400030b030640c010300814408070180510f030a1540c002c0c48915654000da400b00c41c04001c3c00741443e00020030140c085102203502 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 706333714 1250 706332464 706332493
    0x106080303100e090a0501052e0f0b13050d0c060207060c12030c050c16050315010b090402090a1503060905011203080c03181b1f09030305070201140a08010503 70
    0x507648101070140001c210149062402c0d101110007429280d4540107165102d804181c1c207000c0c5510a00d00c0508040b508410500c5844692084144040503402c3c1c080c0c082c01514650b500a1003101c00c0c500045482d003070b407402489055555a48a50b038070015000c9140104460000d07094112551078080e1441603990308000d4400c5d4100c00d00003844100185406100c16000b544462040b00b11454004d00f400ea214419600d0b0a0242c19984c1101801c0b0004002390b10b0100310310520910007200f00d01503545030065400c0b0030302400b0303c0b4911542d0081001c0c0c40d42c0d19040000740062100144548014424a9001d40148850f0003051001402c000020941c480342d601c41c46034843c1c1c199511602659666650401038101034400c8a000c41409030107a9000030400c03070400c7ea04440082c80000522044c200400b0200f031001e20f45500591402016125401c031169204482c1c0604240e07942e45124401250741d9642180c1c082d050b50004103909018030307440980306060310130036002c460100200c0ca04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 706334964 1250 706333714 706333717
    0x70614090d09050d0c2c070315030609020111030409050a06090902030607080c0d29011b0f0203120d022106030703020103112a0105060a03080706051b0a1101060803 72
    0x50007004038821002c20005410900c90113a001402101d03080413154072004d11210b0124036038442c20036040f00561043c0c2e01003400c1116030b003265050804001303052040b10300b102d4060207407201611a9584c0d81e00101036900412140c4412080d200560303523244d4441305c006005200a0710f45c03d16803854014040741010040c0300d1150703d41d80003001003030150b45210049520350001842c0041d1150b00740031070448042c450040c10042080f41c0d0b4a81184060080b410948182070031601d0304011121503c0924441000000040543c00001f2a2001182800406d180c844148080e45a00720002800e110f802e00603405807940b00d5010304260301c1c0071080101c160700d02005850443d07268100c204100010360007540400c601c0c1c400f903038000c3d042220009404d07124074400f102c0c24000d82610361900300b0186003882100e9104a0417241e50070000d0541d2900c09041c000e4000c01840140d03610080b6800c0f1070140580e0f00700c0105007900581e2460741c43e03802000184c1000402039190708094010442c13050100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 706336214 1250 706334964 706334983
    0x3021504030c0b060d06060902042d030f03051210150f080105121603030f080903070f030e12010509070f09050105060702010507140709090b01050915010305061507061409 75
    0xd5071581c5001043d1910308440201800b0280d00102003201d041c000784541c01354100411070f22100680700c03458100d00505107402c0540c0c803000602010704249040c0078500c00035060341d400003045120503025260654141c400c52505814080d030a0041084418009140c0001c1c2c035281e0a1000e80b00540d220306036840808400010302040078440140500e0808000504e903090030380c802c9031422049100c40043d0001d1981003071b40080c11181100520a41186105411610f40401549000d44544900121010345000281084039840807010150b480038604880e94918000070003482c10f0003545280d80c1c001921450107120f001110000324601140700d100c2c101c07031000d0f0105140814550044034141d0001c8801c8903d410090601d00c0c50b801d08100003400340c43c007a5000589140c03d4100030401e644140e0000d4800d1f01c20708200b10100030364a100d1010101c0a01f404030f5551104000680b000a004880707880342c4001190310b10503c040e98120186840c1514803411040e00e03200c80d40b60301d0700c1e03494 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 706337464 1250 706336214 706336217
    0x20c0d030c020613110120160b190302070309090c09090b040c17040602070c0e070314090a060504060b180f0f010b0f030415091416050d020f062101030302150403 71
    0x640c0050104001e00040003c0c411705142c0a00d02c010f121030b4404c903200300d014a0507090303480a803101d003143c8502c203103080140004d04000c5061030308000d03985402150601050041540204104003018010030700382d000f50003507580a02c051450510014040ba005200304400242805031112130340c1494811220405125a90800464004100840901d402800458813164204014004140c04484840280c005000700c07000900345144010165070b00c40d004039142c450340109020f80301000140c96011554090030108540ea40c5040082c000c005110a090b0000501c503541016005c685101d40d200e40f80b11903072540c00c0d843c0e00e4000303e8030340e50034018070840d10400c00c81740c1d040d110450045c0d81c1c01792049103800f80303075a001c131030101c1a682c001e01d00301d6652196064002c60307100700b809100d504032005007440c00b055180400041d252040715101078085d0034001e0307401e80c16440d034104454503107041750010545207640041c82c2c0107141c004d00c8180d0050040134064001740e0150315505008a805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 706338714 1250 706337464 706337491
    0xf19110a030509060706020a02160602060c09010815060a020d090806010b160807060c26070e100e040507170a0209010f0815031f0e06010f120c09020c0d030c0206 71
    0x1aaa090302e003503209014840d840b0000740700280000703c0c00e0004108846540d400303040b1001080201e21000f1090360042c0707041d50800010080c840180340161000070340c0901c0c001c10640c40710340480c2a0401001030851300040700040c1c180c40c090f00010a07100c5a101e50380c0340034125644208407502d58400b0b0040300c81e000010010310b48106410140900c001b0b0040c2840c62820180d44d0350740007101c1300000680041034503c01d205035400c0c1c07407023030542c00c0c80701285400d58a031070541001403180304001e00b414803441100509220151080e17032080d158400c090710070081801e0948000c3c1c03000c1440117840780a5103070f1038009003c080d00c034004c0e12501c500684030b0682d0031a8040040d00c0c0440000c0481a500c0c038003c40607945664100b180c85540c0710b94501091717644580070118015a68200c2c0c540006922180040000301c58000215080b5690040420940c0c200c901e405503051525601c0b4214003400401c10251090000c186220704840c6900c0400c622100e0340d07010b0b82c54000c102d80762400f0650 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 706339964 1250 706338714 706338733
    0x70302030d0804080c061006110102121801060918050d02031312020d02090f16030c0e04111605011a041404060c02030c0f0a0c0f03020307030618080f1911 68
    0x80b0241e9070018420318529041860045a052800c0d00403500130f000d01d5000c01d01003041135000b0041148401411b0000e600d48980c81040300100100a0030a405843c0c28184110840340294843c40152240f06001d001420210900c071800d10000c803021365190080d14901401b00380000211017911000c41300d006845032a140301342103400503001003660005008a04400141c0e501d0407008c1c13103440030a00d480002d05004600c6440800e92440348001d06d481c3c4820309402c20780003112032480302e4084501103802c0303404040700c50142c012030103606114009121144100441074100300c0030784003900480b000f584440350811061381d140b543c0c1408480440004503004c00e80c07603000401000086e00481c0e18250007401c82a142c03d01d08122400030307403c2940d0238001c1003005030341140200f50005030380500d0b030b08540000f07489003081d2000400302551035401c034200d40915000c0d82452034100203100d89804641d42c20220b240d11015003050903c072400d040444540c000c0c18005c0412002074001c121850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 706341214 1250 706339964 706339967
    0x70302090604031a0a0b10020c0409080403060903050408060f130f02040603080a2303011a16020a15080a05040503040b090109050409260a0c02040506012003030117070302030d 77
    0x140000304994110200b08800b20200d09980350700703824249050503013040c80c030303006600408842148a209205184001100004c543d0000f2544c10501c1c04440000341150240340c250030b64845c50f800200080e003040f100000341504040500b0481300c6410540b03550f90344a50640013410403c54a50f00351406076080c09011070f058440c1520420300c060301c005946034807612841415080910010002000141104025940c0354078031102800c80509140c15541010070b00c034503090038260440c03254840861007068101218825048454000e4010102c45490f40e540c200240e02a80014011645200c081780e000d02c0e40d0b2080620403600a4061400c1034141420f007640c2d40d001c000e050341017098680d80420156600c0c85900b003a5445520003120f80013040c841043c0000701301c0c84403280201d0034861604c0054021101158680d81110001540c0e40c4010058481b548a075103912003004182034212180c4030000020750607100d0100800110003840c0440a1b41d034445400001e40640041890b0038005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 706342464 1250 706341214 706341217
    0x92a0702031509010f0605060403080912070914100e070207271b080601050a1403040201050f0a02060718050102070b0c0c0618131a010806150706050402150a08070302 73
    0x2944010141c803400c01d21000c0340d0101d20415200900d05941da080c0d41070414001e8419440200800e03200e0904140c80e580303a041d014003841c500d1038001c09030b0b625500074440003800150050b004181701000080c0c0c0d8400d016102c20011100041240b650b103002155900c0028141840b64110b640188a000d0404000c000450b042a0904009402c10302918015214034002c18049034104241806040c251403401084020050f110b54140101002003e61079907000714407100c0d510f44410700759981d480d107100481e89442009181c0940310780104ea040c40b1954042005401800e060340c4103610b945481c0c4000e01121110300ca080d008d41d1110604004a0b11f00c000500080c2a1890981e0b542c036014901048642d4480301480000c01c0f580c001c400e1103071510002a610010000808101c51031080b41210001886038421038180042e4100142160780c544103c0c10794525018030041d00c2c3c0c01c0901d44040500000d4400320722403200205407061000c41c25007913540c2c0100d660341d01d200e582c45162058009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 706343714 1250 706342464 706342477
    0xa2409050a0314070e07080c0a0e060a0c021201060b070b06121c0305010602030a0f11100e07090506090c041707030b010b0c0c12030f0d0905071202092a 67
    0x50014550000605588280c1e840d0020b41c0101541880c40c903207240070314241540f541101c3d40d070844030001e010390681d11140b103a5002c07244484107580e4043d100f909079200c1c00f401962682c00040080c0000000360300c61030061060b8800e0350301d90800c41c2205042802d03103185000300190b0703607070070300210020522000c20f484d0001c0c80a071903048c6405c000c40c1420300f0441755540114000f050401d03c804401c1d418400c040c01441648059030510380703850402040d41c2c6081d01c0c201c003041021400041030f00030901608405000054041006200503a0242d880301d540c0d100707a201a601d0b11001803220f00b070440e501481481300c8030445290508000e0001101000001d91040520481d80d0200014081290f900c0c040d0103d00d80240e2524200b140c0d8529100030407402c80d00400303055007030501803000001582d41c200c4600000903110001c00b046400200320845018140340314402c400a80303941030300721100119000b5640e0b9030055480380800284288880c15120350024503a0a40c400200200050000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 706344964 1250 706343714 706343717
    0x18080d0f0b03010212100e0105100518030718060503060c040314031b0102030105041d123604060519090203070c021002060603060702010c02060a1a030a0b070e0a24 72
    0x26225141c0020a08a8000300045100b604150381444003154111240070010411101e007001150b0510001c10a803080108054091000115495a80180b43c0b108007250310009000c41e000503640e03c01c0380681024511418100602d4000040b40c3d9080100e0894485c10240071140c3c501032451350b502c6040056040003000c240024002c098020100341200f00c0e4071342001001607203a504150400048030712410468500c084031100101070304001191907080c034000c40c3c400c151101030311074143d60900302c0340c902205045c11030307042380da22818100d0000d001648203640403c00a5140c03000c0c02561050125149030164008404100c90516074005580c012990b191001c0b40003602e50214181d03050080200c405600030300d0410000c0d0030100315180d40401184020b10040c0b00300700c0081d440d10302c00384c24480481c0c1c1750f80d8281d5107240302184007803d4450150840381030304510b0520a0560b001940c283c80040c0304000c000c4000e06d405882c607402d4400349920300b400c070b0003640c01c04181e20910861200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 706346214 1250 706344964 706344971
    0x602070b040315111314040605030a12090b040603330e19020f0a020f1b1905060705030a0f02010c12090c0b030c0903010b04020a021504051216020418080d0f 69
    0xc011150080a41780b02510f01e125007100c00d050408801d2841110710607a400749203410b1342000706960000380308401030f80007150700031a1110184200e17208480bd0300015000000010001500c0d549544001401000d007071510a80e049241256200c08912480c9103564581161040c04103022203400c0d00e421201c2d40190685400000c50000c0c2603802125500004240100e100090160140103490780003800701c01800802c020480503410450040089078020300240d088030000009074200c04000c0d020040c44162960460b1030a169a5844550b04100107100c4648120419005000e42100f941c920f4403100030000d00700c1080f0005041029090360302103d03030003000130020441c0005501481c2200d10041d5101030900603d800c1d5080d440d13803540914810028600308071380c04620b40f88001e082282000e240d464908145240c51300c07800800c000c40c48001221f0006c01c0808080384c10035031007035030140003800052a10012261601401034010b400802106040c4044c2e41e22a0001458140000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 706347464 1250 706346214 706346231
    0x403090b2206091d0c04090b06090613150801080d030509011503030503150618120a140106060f050c0705060c07210605131a0c1b070608010602070b040315 68
    0x145460700da40d1004021a4095a0521508820a21584540d01c80c080204d105040c40d404140c107034490b5200b0b0740202c90351580744490590300d1030304039040303144001d007072a481d400100c03010503c5c400d9609c11441c455409584010500d801040703d58100c1c0c114070f0203861491034403035040d0003a000040c0307800f074995603070907681295010111255002e14025a038150b100e240641010342c070080303001d0034507200b50800c1c00800080c01d1110403800e01003106403040740078104142c0340f0a1400613442001007811a02c44240406518150b1003402100d1060703a0350342a18940d00001d960a2007031000d00d103001e42042c4014030450508000078080d0f00e03c000d00b05c421165860a401c00700707003031541c0340d04190302e105010f03d41031040c18052241c0049410001110001c0c1e60355802c0706c1c0115a6039920708101106000074146000001a00c00e2909500c1811400c07440440089480c1d000c1400741d200452015400403c0d01f510002e450419124900d170ba0350318042c20f64484942000841068120090f00c80460 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 706348714 1250 706347464 706347517
    0x31b0405070905220c0306080307110d0f05010b091303020d110f011416020309030703060b0a090507020f1203061c1b0b0a121b08090f06091e060403090b 67
    0x4d2440c2c1c0101082035200304005030200c4000d5480200c017400c200350030a9000c0c416000e000c0212045542e1007080c0b00e00b024549401f051031440c0854001e0095030b1403c230303190305115064220795012034007107e502c200350380c40200c10b0f40c2c01c100768040a40140e1122041184190181c02480c86003050300003100c4501030704000440c04e4401ca00d04a0515482080610600ca0b41c511031003156440c49002650a160402e8080b0f59150403d110150172035466440c0c095590f1a20141c0102401742d0b80401e002c0e0f85465103003e1742d102c4e07940d01001300511900c0c4265000794206800d40307004113001007804980410754014581c00e1008010b040d56000124049102c0510260386401c0041c10b418100b0742d1911024040a480301c0c18442c000b11000342454030f04509520b80701031030914031031103040c1805141c84610f0003902d000034403c1703d03045501c52403040c0100e004001903845150000f0020000800306c070408065200c600c01c0d64018040390300d00e0f8041c0038100801002d810000100a8100b10040d0030200d0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 706349964 1250 706348714 706348729
    0x30602090a180902030c0a06050f0a03090c03060c1d0a051e03030a030506032419090209041b1d010b1c18031409090105040f0209040f05090c031b0405070905 69
    0xb040b1003003940c500b078910841c01e080c8080c1d241540110b071400282c61a1441c0036082c2e10901c140700071600000180c01074a14001d50100c0c0b145a08060900e864649900d0030b040180200a11400030441e400d00021000f00348061183c1044800f41001000b80e01d00400d200c541c1c400d44d81d4020a8002030810032900b928100050010030382150340c003003810f00b403ca09060419060b00743c9403002c85d01c07110244564003245003205070069101e42039400e0301300204031454001d140e4213100270341c400482401d0000707124040c00707016808080c075842c0303004290380ca100d122107a46500e0403446040240800400509007200c0140840e41106076040d403500124403625004c403020a0240c072601c841c1c005410043c158086502c2e03d900a8002820385068440000250310440510900f40700e1174448010400e544080e8050321744031400980103000100000c000c2c5000f4000c200c4425000c0d20455008240c01d15001542e09085148406101c0c002064442800080e0034010181c0090103911b0100080c0c0e0b40754200c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 706351214 1250 706349964 706349999
    0xf1305060d0f0c09140c03041112150f010b070c0504150803030406020d0510081f0f02040b03011d0c0318120a02010b01090609061b050c090112060c09030804030602090a 74
    0x7424003d8003410a62100110360300310a18280000c2c41e1010091011451401c40360425000403010040c028102c00040f102202d61001c06407900444418a191594040c41e66014172085140f40000780e80b2101500518092104083d1210610f5281080f15007400d03480180041000381c00104116115000745207154420790b0304072407140d400201291488014491540c000e64001c0101c0e031000c3c644201203a0ba903500c00d003c07020001b80080031030181e9540790311032500556900704c2552120782d02c000b0100036801c24030a4107142d000c010791a003144060020b28512681c0b038800594156241e00007203100e400b10448a03402caa00c60004440805880440a804000c100d80d0020640b0141c09000502d5440d2547c07000040c041d92110034868160071142e0300c0b075007c01600740c0c41c03c1360550f41030031854030311000000d40e0403c011000100e242400f0000100502d40200b4003400030100e96070f41114425a40c4c4030241c40c462041c0010700004d40c1036001442c8010b001000e0155054541145a002041d001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 706352464 1250 706351214 706351223
    0x170c030a0f090f05061b010e16050f0301090302030f0a0302070804030f1406071b020613080a0309060e090105010e03030d0f020306190b0906090102120d0c0e0f1305060d0f 75
    0x40d16241005907011085030b014040c45003064000300d00c1e00300070910740d0241004045100100c00c0200361481c40940c404691078071080b04881c0c2a0705080c040000b40b50081c0140740c000c0100035083c07000350405001c7c100d40d83c1e515070300642c030740f205a10581d10144c110240000c105502049058040399050000d0405107000f09452001c5d80f11614190403d032200c07200c0855282c10000400400940107510700504603a24594000c07040b000340f000a400d40710b20702a140c0c41c400900380c0410000300c00500225018401c0d2101e03000e4a449440a544c0c1400c40c100b0140d00c0212440103200a5200e001c0065006a01900301c1e41080c0e443c10901082da4a1b1f000d01548481d17000c020002d40389452814034801e01c81c10410707215654103005025030750b8820494000d0003580c0000d8548202c1c2d01c20000c5038003085c10350031000c2d1250410480c0c40050450308805a0000380d5092050074145007117003020161120050028406104051600000d420f0080c5140d81c005104900702010505080411804a215 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 706353714 1250 706352464 706352477
    0x20102190c060806010e0d020f04021303320c06131508040309060e030601090213120312060918060f060504240e0720011b0809060610020703170c030a 66
    0x410b080101820701c0205100c0c1004404000018140c507081c1c2d42c1080ea030307015541c0540d440031400c04a0041e200e8154100224010310a000040c000d2040044991006d02c078403942501c24a41c4442100d1401c110f81d08c1115000184106024901000240703c0030030b60b0b100c1031000359682e81081c0038078503403011100c0100d020b5500f00070426502042c6800074240506064a80c00c4c45003000c00d81e0780005008900e280c0e540042c2e0304550a03a20b8203a00c004000d03070310098520040b0b030b2800921903021800300411403400c0900100d1040d01b00d000344a0100a071020900094909071160f0010344181030140350700c1a80d0300c9000c280c030f07112801001c0300c03440d811000d1110820b04050701c280304541a84102d025403441c2c02440b1480780e0095140096000310310303000c0c0903000d0044145004103103203034061514910300c000c03c3d8002500400c2c260710680b031800c20340d05155218414031808030340385c6103810b0058004407030034400600d164080056022114400300d04082045120610750351001840038041401c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 706354964 1250 706353714 706353719
    0x10611121602331b0604030c031b0807060c0c0c0b041d07020c060708040f12020306092d0a0803010905010e090c010512060f1f030c0518010804020102190c 68
    0x405100c0100854a0203c2c02c101000c1050701c6801030048105402e405644001103400144500550071545450604142c4425051a103000b41621580340c0c0d0031804102c60208140e54004240034074600d5540051000340341440030ba9031040203040440b0403105102079503c60724040790b032a01c1404044d1610001c1141d5031400c200e08603091002482940d08900c0301181042021640801c2c0050031007800d17078806445131240e1a005441d4011504400c6070414500d100042501019400d4482c860083e015140030740c50754400162035060740741c0103080c40b0304040d01d0942042e261040f00c95101d241141590540e002550fa14841e5034000e274000c0042980310360050000164170a14a604881349400529072a103402002078030900a4100b50002110300380b0000d52540ca9032400c5003184000181841c00c0c5a021840c0054131003050451200003901c2c3c0070340307008554041d1b0129019082c5801d82c2d600340e0f1525400441f46010000c00482c11400340b150150416440701100003d15403142600550560 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 706356214 1250 706354964 706354969
    0x609062206020102090f0303093d0c150e1e070e0f1501090305150a18050a0606050406030f08070c051c0b0f04200a050d0f0b010914010611121602 64
    0x40d06daa101c144070703030403c01c900390843d515000301030b581d40105050928040c2c0f022145c03824210721607010007850b183c01080000010342c040e24020f09284142c103802561011399689a0441e401c20b4810300e8280d1120051304001c40d03000520b40ba501201600b101d600c0e9482d021040b002d08001c1d241015075100030740030712070028000c0745020000c034800c1c40c01c2da200500c0c6032100740d0386805c180407140d04c0d03031107007004564018044c0d0420704080001140c02e428540e101d28089640e0080c0b141c040c4c801600c0c1c1040403501e0b150a0050301d088a400c10140702a405260303c031511642e01c0194101c506c00040c4500040f44c3d11450400d0848a980500f0b282610b425401e11082e425001801c114822885000b00070014001c400c01160003e1400100b180b10b03d0310340003050b80d050098202503441400200120104519901045010341c45481c507006242da9031541c5405880400d04840801c80442e401488503611640d44a45410200c4045401448800344081c1e02640510714030a08107094106500550 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 706357464 1250 706356214 706356229
    0x3060915040f2a0813230607080a0501060905040e28050601060e0603040b090a0503130807081b01051e0d020702091503030a11030714011e060302060906220602010209 73
    0x140751150220511403001e034802460014014417403840001103107404000c1c4406c0c9004041c24a038081441201050f00850300c0b5515081201d00f4000940403400080216582c0e0103014100d400640b2524107071350502080202400a92441d40c5c503c0c81400aa003002d00141400420080104101100340003031074103291b4240342c0141c1003503050221401d4040000c3d00c0d00403c0385c0e44990009903c41c400c1e02d03800540e0303086c07200750200074000e844085414003125580301e2000040b030341c0c800c0480b803460f90389002054861800040500209044114085080d40900000c0489800a40c4446c0c2004500d80d41c40085400105001403281e9002c03ea900440c1001e00009803c100c03014280350402810400003035803071080601a0701003040214030048415000c0082ea00c070184d00c16003540a1040503030006000f0440d80301e00e042c0040500806161082c06485031800780d0350040c1c4000d140075855028060740d903106403074522528000030b54811508440380041c4024250a82c0056560f548078003c02415 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 706358714 1250 706357464 706357511
    0xb0c0a020d091811090a06120f142d04030201090201030501061b02120a08160c0b0301080d030515130533090408072312030c03060915040f 61
    0x40c0080b40b00180b11048540800c0c05803860041e4002c5991100c903e07905141d401441c0d001d5401c8044d640010802a17003121000c02c070b5800c685002c001c3c0c2d5014242020036900765541498910036070401090350301c070080c1d0780039401a00612600080031039014403040440b200f2102540103075236908418046607894080c090050046203400c0008082d6001c050b1800d80d08140020320031418481c403c1c00c51724050220400700c6410a0f82c6a440340c090a50106c0041168042180c07801b0a0034008070300300301101d0599058913860300051414000303101d0b080e0010000580881c1d038016400000d11501c2c1d40f0b5080d1842201d822800204250500c44419094800385036040c0c5003102c0e644440880b45054640355120441080790786240c01c0e140c5041c141c0c0300d031082c030740040c1042065248174040125108004070a514100c011544000e15141d01e60405000c1a2960180002c040000c55030901d04240c50681221140b113035103c0320351450000500725034041c9401c1c00455182c03040303020640001c0c00060f90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 706359964 1250 706358714 706358717
    0x901060503011805091c02071206051f06120203060103090c1212020d050d092901080d081909050c3307030c0f03030e030f041503060311010c030c0b0c0a020d 69
    0x1581c00d243c1162911401b0039140600d000343c4058008110034030811260004084e80c020030000841c65003881005030408960360121034201030113081100c2010b681850850782543c1d07903000319040d907281a20195101510560405880c1d08040c804144c5280001000b0240105030074004040d602d0890a105c102002d11429504064084865180c00404440040c8100c1d180003480001c00c3c07501034140701400004001e025030040a100003220030200e001d05907201d000444241500000044680c02c0c401c40308200007020b14000161032528a4104080c0c140c4910305555481505101054034481c41010100e030404415000c0442904280858002010304402161a21000d074074007500d6140071000c028803c110312940312092501c02e6106c12810420a0103580c1e544030403124104d000e402038042c04080703446004010600318002d100d03032000c990b8801c51180c0d2600c84803005680c9083c4030081030b01404490010748001440b075a411502c10100c111070720384c40e01d0031120024a0040b8003d1400d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 706361214 1250 706359964 706359971
    0x1503060127120501020f0c031b01020f181f12110405030a030e031f1401090b090c03061302070f1a040503041512020c01091104110f0904020909010605030118 69
    0x1508401e00d881d52109036428840140c24419191421500911070812845424000420108217105000c4010080044029107003d410071003040014203d1151056014408404208001c00003039182800041c4030001009200d40b500d5141007002c03c15080c0943e440080c88241500c1090015442100e40c0360940322400d03401d00703007080c0119680d0022448041e0138080c80c640c03000d0803540d00704117845110940c1900402d00b2840310074150094800141c51030283c0310b03000e00119035540d04c2d10030b07201240d40051014603107840d401410b081c19840540390039080b41e881c18420851403924002408100c0c82542815030018080c101ba22004903458980c94840c1c410b541480040384000003501e0a44240c0380c0c0e60100b006036800207480903010590282c040754008110070315001010742c030805c04903015170701d011442e0440c0c604100c11180c224a0003442c0b0801031000c9041044c0342d0000d000c20140143c001480e00b01c01d00300003072004009a0180e400038000000501441042034800061140200c0d02403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 706362464 1250 706361214 706361267
    0x5010f05090a0504052506090509130209150d0507030209090309030a030311070f050d0206060f0105040905060a0911030103110105071106070218070c02011403010e011206090215030601 81
    0x34211500181c00b07a851036803141c0c0401c1c10f01c00e040c0628034031444105042c0a80c280084150844944180300c0c01001c199140c44c0000d041c101810001d11074065038941e0900d92000b90308000414001030500340e500c8902608112a5441d4618039440c464064001800594598410002e01e08001060504160428041d03005513841c009281000554581404070320b1003510040c440607405001c101400c1da40800c1b91950500002041c6c41000d58801d07801e42e5516034038071051001050300c9004242c0041c0c0c040200300190b0006a010540100004007a0012181e03660045c0007982c1805580c0c1140b00000401002040345241c11144485004e00b4010308010441d20713008074050300b002d4040d000b8080003504000315a6190000b00e162802c402d80051346041c00d800c01007800c2c96400c0100e0108000c580c0c201c90442c0190103a0f41200c0c0c2c1c030701c218400c036820050800c4441c022040d040354041d031100c0c1c2e6100165a0070b140791410050340072403a034591400c080010000d01040440640365450009135 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 706363714 1250 706362464 706362469
    0x1090b1302042105011b030f14060622030206190909050103082710020c03070602070e01060c080f0304150605091303030515091e1b07170705010f0f05010f05 69
    0x41c80c0406090150071061140b183c20205c3c0501944c0d040003040080707030420720041c903815602c00b03260690314120402c4104121550354200c01e800740ca0069226805101c1d074151600715120542c41d007140000d500c1c40080d901da01240d0307241c001500b910340300070310328142581c4a94050b03000c00040011103230501c0554959115150f00f44210b001d0f0300221407403500c1a2460b00c034420111803550310301400d559411036a0300300003074462841c001d40f60701c0f031b010b0400d000071224030004100080e9070411080c41c0b0164a032500030764030841c01680807543e0034814008021a640d4207406548264006c403114106404145100000c0311103070340103203100f51a0101844188110384110182d8030f84e2608002505848001241032540d400041c04ca50114040d0304011601741247c0c83e0366908580b4541d442a00d8071100e504500b114903e00907902da96406001c0c02c000b1840140d1124191090701c0c0d007142c6003003521b8035402d003543c01d6041403480140c2c507000050a0902c00d48605801400501400c000d01403d00c0700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 706364964 1250 706363714 706363739
    0xa0c06080f041104112205010806061809041e0309080c220c12090f0b090102040e19020f0a050901020c0102030901020d03050619170f060709060804110901090b130204 73
    0x10240902e5a0b101c18085d4001010103d4000f400540e2103081d004400b82201d440340c803580c0c003031940014203401c042691800c0c110700f0340d6081c210094510030035031052002c2c0308809400400c01d45284582a010035600484d65142540705030080d91103011017800e1040350b41c0340034a039100f182d009081200f4601843e101a0301d1556540c020400013251462200104884188590990100c0d0a1401c0050010401e520201d44a1035108170210034481e0b94010b0345600300e00640c0b10f840c0380901180c000445a00a0500410031440001001130404401d941016960341101701001d000c1113001400102035a0100441500c10400344025444c0c032040000007500c03451a4101070092546610114610780ea80c184940030304001b056400041c555154800840d0030b219090f04180390085080d120700748540414518403030348594480c1c8001c070346484e6040381c007450000c1c006d440074425007107172403d650342e00880140209840080030440301408001c100d02c0d00c4001c2041010540304003c00c100d903d5a155 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 706366214 1250 706364964 706364993
    0xd020c060714041a0a0e060a020120040308070b070c050a0b010315051618080d05041a0a170a090b01060917010218191e0e011403101d0a0c06080f04 65
    0x4440e9034885e50710740400e56220030380c0421aa8041d2011079540d501c9981580701001045192408102c1400b118014542d1441540400f07824000700308010000306100072a4690001c0d258504003441c015a515024280b03079800200301c2ea0041c40310010018848510034071038907202009001c1040d410201d85000b4030700f02d800b40000901040d8110380c82036002c900e41604c001c00f10700c402e454242c210184010902d5110b806080c100042d2070680840f10548501034801b4006940c48000d00c24040544c0c06d45400701c000c052820072521b5010001c0002c40b0211264024131094480c00c1c00d080c18544106088880386501c601d941e071041c0800041480320a04032409030206850403841300c0c403a10844200c04271240c02900c043c1c0c40e91050210042c84071140c40c003c030b6030449000003031662105c110305003140008211a0781640a600450b06031205584614225009085002e02c03990f10035000324144030648200341e890380c0502d1400c1040c240c0220300c596008490f400ca040d000d142030307603400b010300c0c0000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 706367464 1250 706366214 706366259
    0x6040e071205160e101d010e090c09030610030f060f061502100c170609061f050307091403060402131e0e010b010201050103210e09010b071103061506030c0d020c06071404 75
    0x3124000069019030807411160001030a49c214501d0054400c5031f40fa403004003150700038429080010800e40c41a1000800e40b0350000e0a0320317502d02c1d01e44030a00503143c0c940d1003801007030392110001094022030001c400c0380c00040d00600204040321003000c007101c0140c8105424083c1041d1075596613070520104035400881150361207002d803034075030201e8154100340d1886200450407041004425030054040c41c401c41c1b02ea030321a0f44031503c0344091468261040ca65035019400700d00814018600304412a85c8040420000150708120794113002d0301803500c07618855402d5848812040c20003081c040c0c004004828002400254503550714010322900403540c044804015048200c9038078482c4a00c40707007108004000300e02c80d5840307407040704080d48402011902010007040380029401c000c50468820340550440c28240721010041c8081640002e10401e00d4041c20040000d02400030b2000e0a000340315080144000d140001d40502014080d0303500120807202844100f05212048100090040c1103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 706368714 1250 706367464 706367507
    0x60f10080a0b09041a010609061b03020c040c030606030b0405010e06060d0e0106180e120d110412030509090a020f09011121030a0f02070206040e071205160e10 70
    0x303a11241c001440481c60141d88a291607003800b00380088001c3c0007040f4803800301c2c442d500742d903603010940f0620a544210f0010401c800030b180400071101820020150082c01520510701409001800f12682c414284002c03e59940c1e042c454294940300d089002c3c1000d440c10002541800c10b03c0070394032402402c181c4038101c00554a0242005a08681001c820300002404040d4842210004400c99840e038414017500e00b84201250394000644480b0040d12219118070b001c1c5c40c00c0d01d1001418080280075070000c0c1c05c020001d00300c00106a040350b00c0d80241d44036038580000b45c0410540c1180a030030704039a81e00600c580d03005001d00354202c41000c002400c040c985840418113040c02c00705034050403002c190070058803401c80000c6900440c4034a21206017044030300e800741e240c0d03403c034000c000000e50084001c5c08140410010220030640000e451b050a6018020841c03e1200b55401111400304100303a030950100459040311100d951a00e046032440d401c81e41c08a030080508800700c0804854551 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 706369964 1250 706368714 706368721
    0x7080703021320040e04021203070b150a0e01080a05070807030c21050a03030911011407120e060304030507260304110411070f0209090607021f1b0e0306060f1008 71
    0x4185100c8409440f5011090b0b4a455851030020909a01160f00780d01a40310145407000022020003140d80042c2d110703a2480321600c44800c0b0351140b032401041c09030000741c4400c010588102026030103000f4800740004200303854443c640709083c007802d0f5008103441c1c0d20000b41880050b4007a21404151009090008142c90001d580840d480c803480c40064800c0c020751000a0034150300da0000c078203807802481010108481c801c0110b44c0c1c00000301450300400c109210341d0001032512500003651501610b01701180681c4080010030740e910035a000c03408a40001010700811419101c840902107504210380480302901c50fa0148a01c4000d00062440034040d18400c684c0e5926030010b414450305070500d54131000d840c90140c0f2040d8141c2c005070b04c030342c40305400600038140000388503200d058140c1c05071130303080035400c07031441c80388807000d103486402c0c2d26901014003462524018506c01c003056912440d0800d0544141401c1100140080d8001c60315036101c210151140380302050700e9283d80c0b500c7e030181e99 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 706371214 1250 706369964 706369991
    0xb150607120201020a17070906140909010b0d1a090a0207140d03060f08031801110a1203020706150501051c020904240e160f1709030309070807030213 66
    0x1040400042200c603590001c0020594154060010b071811070b11400340440142508003000041105d204000503807100041c041a40f0502c00d1305000241000c07494244500358002031002003090f00404100340b00407888000715a8503001d1041d0011168051034034802c101804070b0b03400c40c00240412495600051003408004030781419200b042c03244815150807205040008014018900c1641860510032a0200b41c00001204443d40404400b060703606c1c0e41d81c04c00040d03441059420321000e0328011040400c002c03440c2c207c50350403295066a0010390392a0507250020441d05010716805951030308441c240140c0e6040f4080301c801070440e100528001c824850040c0103482030603040c0d40c00c50304081e5104c1c040540c007007918640503800020001500d8980c98505044907080780d441c00c0302400202102c03c4580103001d52804911035207800412040f9003680d41a020b00195500b0225510020400101c902c1c14481480500558005001484e141d80c0002e000c070784901c900c407400540e88950342e04104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 706372464 1250 706371214 706371217
    0x30b06130e0a0f150c0917281419020108070c0f0201140d020414030613170a03060b0738011a090307030605060f060306090a090809041503050d0c0b1506 67
    0x1803038014014050040c071280000d10103800c512600c074087c8500b120b00c0e11000c0d40481c5a00c203d004034008442d000503d9040d082da40c400812080c1d400724118a400481060180316a11a141a60803d06400080340c4001004000024501410040c40941d60000643e60750050a0300715024a003419002c98140c8480c055481001d40f0090302c0c901c0007400092902c05a410101e4060040303054681d0355480496000300c0e5607043d14010800d07020b42c00e20b070f0715181810b009031072004524600000d000d40c907589010b1880c0d009070015101c2805040307640e0184405192040400300802c1c0002e24016070782800c1d1000010306000324500c0755104501420641c2415090361045440101154038040c0e50b070078003000400c4103841d40c500592070344c00780400c60309140d0102c0c0e00a035400b81100031a60b4442c44a07000a2a550000b1560305008100c04000e99440317000b0705d001d4601410031102c40d146945081441e000050301c40c101031148280d0b1841c086200d001c00c0c01d9000541c0b034400d1807052403000018030103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 706373714 1250 706372464 706372493
    0x90d03020709090506040c0b0a0c0312150b09040b0102032b0b28150504050904030210051f12050c09100504111902010e190201090b04030b06130e0a0f 66
    0xc041c90050743c082030140001e0020b00580c0200c21074481240c640c07e02190f10b1181c2c4001001050302c001a0200003413003039000407402c81804600048400405418101040940d444400c8140000c00c00e40003c2c034061081640d140c809000442c6040e000321103a00702c0020840010105050342c10454000c0319440e000401e00603401001102a01c001c0801c810351301c1403007003010002d61405c5401290807103905070003220b14401902c0d040c0c2420300d4135082080048000700b0440850003401890600b85180d802031a0082c0070413501c080c5240354420310500c0b0b200480c0d00c800000c0d4600101030011400208070030041c9030003a074803c4002da4a1800c050001075080c0e1200360007914002000843c0300410703001c0c100c140c3d01d40d4040c02d180b0b1912a4124282c2d0125040c03554250030040704090306180348091040c41c9032041c180f015000340d942e6469060703500282e00a85070b50f403811007041100e280c0b0380c3c1c180802c240c1000042041c2d103180070009584105900005028080c07424410090000b0410003440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 706374964 1250 706373714 706373729
    0x2040b0402030a05070912020105040b21010f3b10031514151e01090b070812010b0310143c04020c0319090e15011b020303090d030207 59
    0x50b2070030403103c45802490115514000076482000201e000d0b0314a04407120b00940503541c190800f070906c000c01e051175001d41031074500105460030880b01801c094166500034140800b107600100d160a01c3c506000100341d0b2003024030694020075071809000364641100c1c400c183c4080c8689640d4000304904101429040644140c00d4441c00501e118843c2e00080e40c4416464455002610760f1a001812a201410410b61080b65001518101d8004081c03000d8004014940102100c0d0780c0c40303a044090340240030a8070000b0b00050ba02200c1c503c90085107004011000c4824914a440e040c01044201e0a00a01540c10382c103051040c51607407102d0740c9010300502065020742e01c500c3c0e0034180c507104004420b11901240c102c01c01d1085460a4400d075039080c500240030b107260007641c410103440a58090701300c0051000d040c1c004192000e40a5861b8030840e68014000c4152407404005400c040014030700780444445600501c00617207000c42900c003528810703500f541241c40c1c0d41c5002c1c4d08240154000e440c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 706376214 1250 706374964 706374967
    0x61612090201050903030d05090c010807050a0c020a050613080706020c060d0507120e0a0c0503030c1b03030c01061d0105030307080d0c090b190e06030403090501080916140f030d080a0902040b0402 86
    0x20071547c036444035015000e0780084459103c50100192180d5204880c64008604144011462207000d0481d07291014802010400c12540b00c5c400285281c01c10350028402100b0100207004000080003450045d0503d40010820035520900142d00e61213182111900e1503280c1021620b518042e080601e4046603200301400761485034518296110040e0706c0607103500c0e1b100080042d590a002c01158151017110f80a88400221040142c60a84020f1081071301480204000a5201028407602e0081c01200c4c2c07101d07200544661000481c1401038220900c41c1d001080000005124901260760004410402040d8031141c4074080d51006041d034081d1a200d0b20004551402c182c480f00702d2200000a07446d0f011580300b00d1014041140401c64000b0040b80c0b01500c10300040d8084d00c0080d605c00a50001c5078002c0e0700c85454280076000961010038030090301c0140004510b800d0580b0381417050190020109410b4066004111110180c035500d48156528903a0040d51102d030003400c00e0040107441503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 706377464 1250 706376214 706376227
    0x130807031e03050c0d0f030c17062e090f060e10140c010e0706171b0705100204060201050f1602100507030e12030609180d030b18160206161209020105090303 69
    0x2d0a040610107011b00040d240207180d9032414024004104404005580b410b040c0d680c0d1424400d40d0744028180307140d5840c6800b88640d58040c6602045042462503840301c038003030324007000c001d4030301c2e220b0f000030003489205603410340c090f140c5060720180701580d49082280700c420381102c0c11b41031090341d030842d00f19420040b500c0140c0000103914400c542e05a5100201c4144014207a0b0380d0800035103800c2c03020556035220380003a00b0300720090869503000310140c4d401d00c154505024104d903c0340d413000015035164020040e1100f18205001e03404001c104160011260031b4a000b51915142261055420741e540f000c2102e5070b101342d012440d100041d070129208141d03a140c011445030000c603800e5200e551840005843c0c440710f02c240c403c08900e160000c129000107850140c01414001c10040c0d00081103221682d100000c4a80d1203004409040c581ca081580001009091482c010036001d52410480102d0000036803003000607216004d00e08001441201c2c610040710148aa050615818030010861 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 706378714 1250 706377464 706377467
    0xf02060729090609010e0c28090605030705010f2003040f030b0105090601090b04030809061c090b071b02060c070e091f061215140903130807031e03050c0d 68
    0x5182c01060800110b61507550743c0c0030b0341401c0e03c2004030b4818070b9400091400311941002141c4044600394a02d04540700c810841e81e8a00e48405a80260200c1d0b464120070032003810203010780800f44c88d0a103800915005942c00190100d403407515994035241c1e100322100f0000e502801581c01801100c59028a1540d490604060019080c05030600c1014014042030007503004018000450321000c003854182403440d2541400ca8011010043c1c22400070400d403d4a607a12408910342170100101c0080c4e0300d1203038102218034180041081c0140304401ca1000030b2100d5004904840c2c56048465642d07131a600c803903803410505070740e00450000107800c0600031a1000800c0c05081404002c950800000031501e40e81e041ea00f42e4803418840342d020400100210340013800b40002000749038804941c080c900b070407800e210b2178111802c0c155a000400c02e10300d040b0075241d44d54020407a0000400815085803940c0c0300303001c0b0040d000314031b02820912100816004030140c481d0b00c866030041d100c982c18007400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 706379964 1250 706378714 706378793
    0xd2f070f1709011709071a040b040306050a05150a14191508070201051504050703181211070807090513120512090316020f0103090c030f020a0e040f020607 68
    0x801a0101c0c4d0280803948a0700d03910355090b0303c2100804020210646040507800043d2000012000f1240d410800803440d943d80300000e100443c49070400080d1445c2421544045070b5001e00f52400340c0240d20110f010569a403039040042d103410240030148641140d002802e2982070009140c1d0070106075000050b042045080c0d5002408585c0b1803041d55030741d24a040342291400c44500303118100c0701000720003605050340300b180c0c4501d5034100022410301400203000d50703030403031102100ca0030340c0d403124100d6090f88604550301c4501c01d0001852403a0424080c60b445003a280200d500c2c0940e60030000d22250807003000d410781150015461200002601802407550f488080e01120100381d8401150400c403000080710044c4443d090b40c110351020039401c0000744101c1c0c0b40c03014101600c80e581308012901c10080c91008500c1019a45c050404900c10b01948024a500503801c8048030300803c8003180240b1031030105031fa41102d0099848101e4035121380030401c0008e042c00e03442d000c8203540ca14030340c4000307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 706381214 1250 706379964 706379977
    0x100e060a090f02031015120519050f06100903110d1106070305041d010509070c080409110403020406051503040f02180106020109033f110703050d2f070f17 68
    0x83c4480e200c0358a40c3e10340c214110383d00c1c030f03946c0c0003c14070065494520307116840745e600180300c0a0003020a410140111003034507010f641d00d2150303030885420301000e488c060301210940100390034000505461511000026901060002c1c040c00d114a032030350070044100303109031945000400c03064580c102d07410000c003030350401d0180f03c003212111002049401e07081c20080d03040b43c5c2c00404c0c5060302c1d55803e00c212071107400c962003103c81c40010720010503008058043c015803d1641c4213550388941c554010002501e40790b900c1140110a61082c0401c90a5074808480e48503400c0621400c1046e49403002c12144648101007000602102d0000f141c2103906411985800c0c0c0280d0b0b43c0300e000340784c12107d6449149089501c1a0001c5045407480d00b9001100201004071824480040c10b00081640100706500618040340080d100142c81c0c050701e80c4078840c0e5601415042052904040070003246030121300ca491150070301c10004105802086644d5810560482d4440c412450192a80c40780450581014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 706382464 1250 706381214 706381231
    0x30f0e010c110114041e02030a0605070f230a050c120310090e0d050a0e0105040f0303080f070806030606042a050c0c010809030f070507080a120314100e060a090f0203 73
    0x740f9489134100104214020f54002d4207901e00b94850b001861000309449000300d80500071901c001020411500c0354910421160301c4419166084610040442d04170840350b001940e800c0d030060406515560598500e8406070808030f40d0348030b02a289514144188000700b002840c00020005001c0100c1980340031108404024004000006090303a01d580c4c0b81100a40021800d01c10944d81034819858406408410f06290b40ba05868060440181a958100341c0c046000c250078403422214107081180c0c001464613108600d4100000001c0c0c4880002e4111442182c80e40100000018422006050401c61807080211541856006803480d004008200c0440c010380d544116154000c50b40103100c0c50141010b94a003240c0f1607103540c01504040760a4500384510030340414038200800c1000b510500030358510034500c2d0400b0b0000e05603021388061a008941c507400b03000002c4c10b40280c100690300385449040d001d030303500c0700410305c0d92340c1c40d5001c00d20300c42c10303d80c1c260301d01d4010340d00860041104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 706383714 1250 706382464 706382471
    0x14030a081306030b1f031802040603230303101a19110c0102031309021323030606121011160303150b0702011709190303020c0601050a15030f0e010c1101 67
    0x15403041118440d914908400291183c4209038405882544003000c7d645d0140d00d0680d40d002650041812110300f504206c0304403110078547c4489841e0008040300007600a4020346c654034001150040d441d0580c41b0795900c4400c02e490395001c5004c01402e5455010030407000c0c0840342d4004000821118204804154030300645081c0b40303483d440481119180030303c5010030b00c901e034079020034a002544211584000c0740510b500104440c0300d46510b454058048292182c41000300108140c10000082c0405200f60100720281001c200007081240400d032029000190076441042e4003c0b462082c01c000600c10049400c1403810180c0547c4205000000c40d410094a42c0e1180d0140c203103482400e4007c1d002c52903020091603119500c0c00e0080c2d0011a010903207000041c0c000d004c01c29141964412400301b9000300305a4a0b000040000e14010f1204481c0d025090b0718000341c0c0752080105195803002c15031940350050040d42680c0252030001c89680c000c1003c02e51059000b0858503054401c20865402e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 706384964 1250 706383714 706383731
    0x3011118150a021504051002040308030a0506030a031706040e120a110f2a030105070518032a030c03100c0f08060307050130020415030207080414030a08130603 70
    0x32080d120704082c035030020500d550a428030305070759101c0200103d842d44112888a52410200d0014000640c0302d030810136100d05103003041100703851001b0312560013540f1881c03a100c08aa070000d84407d8220090313112103055200c0c1400714024154200321904c0b20b00c9020601c070554089800244032804c0c00b540c03051803034481414020b840e403141c410402400e0303020003075010ad1601d50005075028200c1b01020000d14501d00e01c00300c0e007512003c995000110f81c010a406001081d00e41c7c2409100004902a264100d101442d20344e00750800485114991108528a065a101000303039030081c05000301110310040d0406145005044a4244440020003410010700418050720601c1c0c042c4070020042d103c000d04001c011a40050310914416000503040710304821010300d45483c00e4036480181001da503403810800114240c00c00d004c01001018410403002010409620036982503a0001c1d0a0080d0240c0312000680b920400070400f2b03000d0301c40068004d00d00d0448000303180c105e0b403051710207000c28032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 706386214 1250 706384964 706384999
    0x7061e0b0405240102030705010f0501031202061303081005090411120d020a170f0304051006080307020a0302130912030c021501050d030305060a360b0a0b030603011118 74
    0x24020b80d840c108403903c50001c0d4104070280c21101c1c0780500d062040341e0619805480362801d488084050764015175540c1d00500a0120403007211404010031300042849040ca03016004d20790000210140400581c1c0d00404c9031201d54a884000500c0d0042000c10281080e003005200e090499410f6445110401e6418400c1c5402050b80c020441813600030b07140080c1c25032500201444002c02300341100000f0840115001c00503c099401a8092001070104a80d4441d5400840300c90390482c0c0340c0d5030300038041000142e40390040d0000340c80c1d050750700109085100144034040c014941d4014902d40002c2c40a44006515910102041c403881d4220307441490041d00404a401085c05110303000f0a0012102e00440d029400040d0041d20151070300142e690340c1c440c4d154550103140b10121140f5042045414128140f40040000d07038108030040044001c0c15001400d910f400b403082e0b403c0003030f0101c0050103540d000c0d40188540c0d407113400041e0341c82016a2000402030031000702d80c2d00c10b0f403a040c084075411 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 706387464 1250 706386214 706386221
    0xa140a0e0f101a15030f0601030609050403050903062401120f061e06030b0d061a090921190c0326040519050c0121060e060a170d0c02040207061e0b04 66
    0x1001c04c21002e40c80c1d51246820313099020001800c2da8107154a401c4006404000d80c403580d8801d6000359100d03a140d9203031004241c213040b800b81080388401284003811156002030003d80a90850900705403200c0c94086220130045c1407120004406035242c003000203003030a903850005070509084008622216200c05007a41214030040341e42c1c2d0810810813110001034102c0d8401841030034190b804111904190002540c192030440f0b1a11541d00300c80c40040c0c2040c0741800340075403602508945410040001107036103d000903400a28100480000540f00f40350007480c0c207040042e1480c510030b882c40c4414604107179140064070110303864402c018000792484800049540125844409000c5241e109401141c0c0300000002820b030860640c103050407014068801c0b10001c04008400340c00030b10740ec0042000e440465403040070700c02800c210541400c480802e41d20b10203245814035604880c0f4034000b040003400ac40d1401011a4a00864412562a82d9120b10804030b46003c041c40600085030030301054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 706388714 1250 706387464 706387489
    0xc0d030212040803130c0324180f030909020a0c0b01090519020d14130201031103070207350f12040305060a020901050f12010e0a140a0e0f101a 63
    0x1c003480c28000c00c0c00107004000558000300e10105081e8002840d40344c001c02940141d10448000229190100e8620310392070007c013003088501c42c03c105244244050720195407885000070050480722007041e08042c000c1e005000038103131526045444144a01c1c000d03022540340d8100b0b461409079000005041d003e14054584154000c0c20100440b0b40c00d0078002010b90050505106070544525a007408694078140040c4907040b42e0510b454507895500003d0b08641c00b201e038110b1542010010031040075000503000e001c503001c098002810f00c2411a242c5c080d01e00d000c00c4204070940b50103201101c11000154071201410302030a460800340c84031a4140b41388554880103000b60481c40001307451901ca940504440c18060400928080e0f5601d60013038580d11600d500400d6050500c01400001c90005406030300c500c3e14501000b6001d0f00c00403244011030014a500b0300c0307945030b40c4456034190003400525900b4074030a00700d600806080e10150080c000301002c41001c00d46440d898061031034400d200d00755 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 706389964 1250 706388714 706388737
    0x12040f0b030603100e100c0314150907180b0a0305040b06011e0c02190e090f0105220f120e040f090305040b030709030813150f020c1c06060b0c0d0302 66
    0x328100c1c070203500094036510314185521b00a8080004001c9a28013a00100056684c0d00050285001719036000001000c1d10840c803880040c142210345898801302c032500f050b01402c2c0b0110841c006401c401640d04190066000400b0124884201503010b801c03142c05244108120002503488a0045035843c5a444507503650440440320510410300070a110042240042c0041c1400d100610a9218001090380160b8140002004101c200a030034008082109400d200900107030802c061308021501e0036808401502180c1009002042401027080380496800741d00e01204181d03013040504440c4001d0300c10b5006d58101180c2c101d20300032074400c1c001c40b241e240e21514109400c122600c5c4031904001c0800c03042c40031050001c4080b4403103c019100060b19101400c5980741000820360b5440c1c4625003190a000210550f8030025402240c0495284d00683c0c046410003008d0b01048005164400040c2c5004d14001d40071560400d0080107103142040c51049401c90b0307084680c203d080384a101c24990 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 706391214 1250 706389964 706389973
    0x100504030f14030705070c051203040305070b0a120c110105040606050a0f0305031b0712081305090603060708070512090106030506090604080a0305060103060b1204020120070302090405070812040f0b030603 90
    0x102043d001e400034041b528000c001c4404003d0300d9501241082100c2c01118025500220f4104200002042148081c00d083d4402034203140400c00040e10340d210f50750340307401c05070303280c03502e0300341240c403404540b018524000024409822310f402c00740000c1c0f45038010395020b41d101c40d0010410000014048049a030301000651414010420b40c9540382c03844030030201503001d50400020a260f00c00c03410f1907900e0144404558402620100101003203265004c2c0380142c24200c1044075503900401c2d034a500004c1410320050603610320f90200c5203403280c2140c980b01010301c0814070085220560254007924411400c551440c0c41c0c4810160b5906411a0014a840010030070384a42e14407941026802c0203040c10702245047e140d2045000a810014002c240164844100300075583d0001c0c0c010044070351803000c2158804451f200310786521480c000a40104c005c140401e041100804c1304100034070300c90041d1100300c500c59000215561003440340b04c180047e203c0b408200c241c010001ca034040d020040040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 706392464 1250 706391214 706391221
    0xd03050304260c0303010f12020d110103061d191527020d15140a0e060d02060408100b01180501080403020f01050106051c0c1b060608100504030f1403 66
    0x12010450b141d03400048099814011041c403000040280408400500196460398104a04003020b8400340d07010024200d5402001c40268960002d140e882c143c0211618500e10301200040e0041c0c2403d50002100510700700b18070003081140e90f00c05008420460300c0c450a0a07a00da9260151580c004c24000750300901d940401a007451a0120b69840c41c000201504e041d00b000340300d001700d80007016034010b00c940307600362101180c0d80c0315900c1002e03102d40125091400c05110115861041d68000d2071104100940400d2041e500c0c9401049030390340c0100180c0c0d0b540c0d280c08130592261401c1601000c0703242440400003c642c004d2071070059188416403c40c00d41da1030304004450080007e40190254020700e110942d420304203000d914003901140c0c4405036514015400a941c1031605080704410390310b807011410689031b0105003501014501251842c0f0002ca5041103001030540b40e102881500c90001d609800f555160086403182d4041d0b104d0101e200c40c521410b0360b0029440d6038000c107549040002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 706393714 1250 706392464 706392473
    0x1150f1e050a0b1305060d060e0612060c0c0c060d0e150f04060b12010f05061011030a0f1205270c0d062403080409240504180503030a06050901050d03050304 69
    0x903000c1d16502914000c0700c01e45e16004200c1503480361414020070758461400b8001c0038040c030a80c9420500c00d40300c1c94007003242018910740b540c5010b481c0c119100c01c00500b22228131400c00200440320b0008222a0b03444010300550700080c090541090b0007401084542d041d9616404031851194900d504860642d580715607c88004151601c106a800303c0200d0b40144028004d220707084030709401080002c2c01d410710004210302200594500007c00128680c2c01e2105003000c0152108401c0d1410719902c246040303c41960002c401600204c0300900e000200300c4006901140700c0300d42c41030340b07040031141c4a0001c1460340b1a2400f07460680c11500034440480000c2e03250f84115141c00307501c10821101c000c01c050300c21681510b64020b41c0c2820001c6001c0c0800200c91040c03641c1d807440d4041c604604c801003090f900c180301d0584a00ea21941e034880600185940603004104032a42c403a0940e5502e00d0240d2000c4000c02032405818001c0c0c041d100086428100072003103686041d0552102c0e81141e4440c1d54 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 706394964 1250 706393714 706393717
    0x9060803042301030f05040b0f0c090f040c300b0a030206070f020406051215100302150906040f090207060615051e040b120411100c030503070201150f1e050a0b 70
    0x900b18101a65141000201540307441910301952240e088031140b4180025040322088002d1301f0490503140802425080340e41d070034030340805080c00360f5000c03c60072030304181600c0c80ca6801c2d00c020610303440461002c4082c0c4a0f040f541500e503964000411416210000344a02910280802900103c04002e40c00100f0a0030f68443c0b50380d440280041074050f1140d002c14882d204125541501e907020b03011903420000043c02c965845201802240c58040c65500000d9a200c200c006007854203a00049284454403407004590140480558111070280c0d1030700140003c0d40a0f64007912003a10b843e40c040b4205118800c3c0360404043e540d5158200301c5060844985c0c074030258090581a0400c100006000c1c0c03400e4094601112a180506141d140034100030a5807000b2403a018410840c010790403d02c1500101c1c1601956010300d407682c0c0b01c0e5035a12059005201c081150594025440300001d080c01100c0384071001d5800d0b0700190740480c000d248050b40c04407050700506502c05079085050090b22038600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 706396214 1250 706394964 706395029
    0x161203081801060b04060f1d09010e0408071a0f070914060c071a0301050109140109060c0201020c0306040b061005040509040215070804030f1a06010f080a061a040906080304 76
    0x7400000c1071030f56040c2400b41c0f588564040000700b406000a11051500140070300c3c0c540c510344005014914124000a070031460500402c03144030034010200e02408600825079940c0c1c2da00200c5e503000400700c059404480b5000700c4040c2d400300e440c000001c02c52031203211614212040c99841c1010122200c0030811aa0843c0b0941030360303886540c0b0005070020301120005007507005580025629411701e00014601115a00510814014840b0712080b40e41d021031300c0000c40d00e207840c01c001c800c42c0c240700417400c1c00c2d529041c0c150305110711818042403200001c1c0040c02210111007441110b400c00001356a203001d80d10800e40d108103038000240c050f0410b0740034002e0b2611609542c0b4940070195031f4214554000c3d07041552800349030b0248208204040d4401094412400404060752900000080c80e00c0716032800f42041003084000b003207418546801410180a00da411898000481c076019082c580081c03040318042400c1c210300041250008c0110b50607102e00e00040380302c8031000240c0103030300c2c00b000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 706397464 1250 706396214 706396261
    0x807031b1a0c0c1507021615090803040b0a0c031407050606031902010801140102030c03030106090303030b0901180905010f0f0b04270b04110a0603020702010216180b1c030216120308 80
    0x100080e150000110704c0d00000e4070812940054100003040c004082700b0050300301ca4641d0b4030030002071081034032090507144070180618107c44128440d24080340d110780c2080980e06d10480114200c0d04105001c075038103200d464150704903030f2280429040242da4210300c1c84042d020806000c01030011920341d2081500c071070010700441c1e01c1c29810340161131559109900c07480009481c240c06208060303040c0540441d10034122100225035042600410646002800045115544400e4941081000e42241103030301703c281404c00a10108036100000f8110100d00144500d150100040103001020020032001001c0042111050b01e26a1100481c1034082c00540b0000050700e4001015900d4000280c050602d03641c1c05070b2550354600c006854410100c1e8060b00140000b2400d108005540c032010098204e480004203401d6680d402164054074016540034a464001c40004207040d0009003428290f44850001020140d0310220000d0700140c0220040019403210b000c581c2031a004d140749d18854010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 706398714 1250 706397464 706397473
    0x4090f0506040c0303080109050408030c09040902030105150a2405070309051f02010e060c372f0a03080a0b0a0f06020c0301180807031b1a0c0c150702 66
    0x2580340c191420008440881c0c51800a450a00c101079201d04007a0040200c0842881a0b040c036a8510f1601d0000400560381324802040101070343d503c5810059550390050001c2160342060343c01090301084252045000d2640740303000050710b1507002d40c00284100395103182c40c10908480021565079004140640c00c110403190007103815914034000d851000c01e0320410b4000e1803076240010b0309484180c9443d9030345805c4031040019541c040b80c111141d000217101803240380b001141440d1030740c0046440f541c0800c4402d41c141d418540e00221480100d9020617161206002540140060a154040d003400c06030020300000c00000e00840e48a60048141c4001242c90302d820004038050044035440742c06d15403560541009884d40601c2559800c0200390024051258040000385500081502c02000000000340701000d041c402c0318503045d05646002000d848907110309001614070000310707007009400032900c0810b1540c01d6400c11110101c0c400000b070700c20044101820303000408028810000e600a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 706399964 1250 706398714 706398743
    0xc0e150a030513080c01020301061416030e010c05100b0f030a080901030b18190f06030309031704050909070e07030b0d020f130914010b010f020a120302071e022d0409 73
    0x8002c0601501785580c0300050b00c0790316184005000e54081c4552551200b402c000302e028030242041d0740380c0515050b041c030b05110008140100c9003130f601c241028290b07000c2c0c0d0031181e6402a06400c01380c00c042c81124008001d401440c00c03d5220100c1250080c0654801c000d07001d150350094010955111004150107804d44150821440d500c00884583c1161040b03001940901401071140300000e0003517020811080f03013199006010b0a0341400087c00c1c16131081d0349524000780940454015140c090f000207041e082c00a185503860101d0300035a0914100303100003840c0640319226841e0784401c01001c44c54200e0060f02400500f501e000c16054204204609110310b8149034094100308900c113030400002500c1c598891421102c1565105041040e00958208120740c00141100c0b85a0400d50b001c0d04c214504400341c00038496400018840481c51900c940c46140b400c005105090081d0f0b00c40045030001c0c041d500031a1004140300180d011030100c100020704081d4005414a8410345903000d503101d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 706401214 1250 706399964 706399973
    0x5010906120c02421512070909080c150705070212010b0a140a0509092a03070609060e040506100509010504030c1401020f060c04060c031803060c0e150a030513 70
    0x900c1c4001e800c0c94100b0400251a44c41c02120f50a25102240c140b5246141009208183d6110091840910408241e510580e201005112090040401400c02c000c940d542d4034080250f900070000c01c203002c2c05184c4d40d2422a2310004141c511500c081e0303480e103182c6405a801c21120f1007d03140c00311015981c40145c84826160141440302400800c1c4074034503000e4030181001030700031194000314040e8030200180700240c01d0004214180c0b68002c9880b81c0110304076248003e854655000c4503038540b142200015000d50482c2c1088240e404036900d2a001e030841400f0300059070b000766555a0071011307018244080700d02c603070040c0c40e000005150141c40c4c00d5483d1100c1150700c6d23443d04842100310709103083c0a51503804001c51320205444078050030b030b680341c0780b04410464000c6200d100c007031116801c000703810541304410f07006840340c14011803080715440f03090050003040d1212540e0b000c00c8100700e101c0400d1400e01254039441c0342c044443e03490700621407170440141c50007030164cd20780c0042601580004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 706402464 1250 706401214 706401253
    0xa080d09060e01020316020c1302071704031a0f040302060c030a0b03010504080415020a080910030905010e0d0e01020f0709180807050a0605181b0f060c07050a05010906120c02 77
    0x2400c0760b030b001507120300707220910b1590b0060880c090019984640d94081c982d84540103c03204021286100680b01e0340f03e42084130a400c2d180e24101a40503001030040208100c1c6500300711508400c044080f49591082d28803a0710380c0080d11b02902607485440010f1543c00b400e0b00469101800100118a103030380c00340821300f5a03000f550200da10034008101880081c29480c00422421030a10041c0341c0440d86423542030f8540300d00c40d2131a0203940e0fa402d1849c5400d00a1700840070241e4803900030014140756051464841400b50115000564004c160800d10b43c80080d40740b00803688500589400c07440c01460000401030342803c011158943d600c4031011511403000390a410b40241c02802c03880034145005400c0754030081c01025003d0700714550707801c135210010f01d0320b03070444a410b0403038107440c000c100180b40c8003011440a94403a1002843c02c4401c1c6020a40350222001921242485500d50005681e040c066024000005004d06540f0b0035a01958001402020300c0e80151540488800e1000140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 706403714 1250 706402464 706402481
    0x305241011120702090702070609060507020a0e070818031918030503120907080d050d05100e19050109020f071e06090602030601110705090601120b06040905061806030a080d0906 78
    0x302e00c804902c0390309500304480c0c050361144007840645046400d004000c1d20050140c0a05001c103c1d000c1812001c544440300d48001801d4a42070840c1da42c43d003100000c000c02e5003242d9104038902410054580c541d400401d4030a20044a24110031224040d10301b22200c000070b02c400400701c4c0030010008080340d01440148800f4490b500c0001e06031410420051801c5440d90100c2001d50200038943c01c403d905c0000c1d51800610f00d2804911071312080702c10f0b640610650401c25440003038009221301e5007000c0322001c1d00d1046820013800a6030b0703922038050803130190740840c1c0112441040038100146144203500b012540d80110304040d00a6911844220741c05040304941d4150700005020503980c01070301800b0b04840460003060390341d0900c400b0608914000e00128184601011354030420a400e810007121a14060001038459541e0f01404010303200545145000e2014603040c2a0180301c02c0174454465400075009040310f1032161780c2d0349016071185410508161703641545000254940c0a503054 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 706404964 1250 706403714 706403743
    0x612130311060f0c031f080f28080c070308030408130b1306080c0421020103140906060d0201030e100507020601051912030e0a0f03030305241011 64
    0x2240515025145090400c1c984100754402c070100310182c0d180c0d4070025403201c005100291643c030303520703ca05660408a803800c020310307209440100e41c2d400002842c8a11003241d07030071108441e441d07107442c0020024020000104030020784222000c505080000e0810312003640403130b240035943e91103102c0b0582042e02d080790404000502c00c40c0d03010030418083c0207002c2d00340c009842e02600e20a40405044988503200502c01c0c00000185002c00078000d440c010901c1c89119049403c2108040c1070400c1c01c0501207011a180130b6040340040d0101880714811050341c0001d1145031184010460b08054500d030032810551139a44c002070000081c40402c040050342500443c50b41010540a402c0082c141c200b01d0040d8940c4500a4040624001c440e0440300180b00c0400229150f042c12503d440000a100ea0091103c0f0360004541d03c0b150710480c11030380a96010000c40c1c40c0d10ba002c65102002511341191001790b910004010b00c0c01180e088580a8a800d2102c084c024091401d42008038180c0103a4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 706406214 1250 706404964 706404991
    0x20616181706071119030306050a0b04080f060610030e070b0403110108090303130201111e1e070f03030f18060201020403061104050102150a140a0204031a040503030105010309020612 80
    0x500c1d8036030801100e90002483e0400c02820b03250703d00441c3c0e581c0c0c1505000150806010020030916004e40c0c0100080c000280104484c6516885040031590203445061030503c50111411488100450040e0291000810401406120400c214040d04501e85c00e200940201880080c0004620b001040118494144c9042d102c01c000000740020b10024041003080d041001003040c00c072a0301c1c0c103102100d507090800780d00840d00340c1e410514145009411807420340d400f5913200d00b031004c005002c2030081c051117100d0008681d42c44800ea105e009600c609010380301c1000060000030b01a0102c0ca0018020389094000d03114440101c039100019640030030702503540000c062003130142d90b010fa203aa44048c498118070749407030440000e5540002d851208880c003140c102044800c029030b0001c4450a00e00083d205180c180381030417500942c410720045a4160211203603961006030f4040f041d1256400802850a50307103024015006044c82c2007040340d001c1001c0018400e00032f400c18800307008559084041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 706407464 1250 706406214 706406249
    0x2010209100e0103050a0c1b030e15031816061b12050903010c05090303191206060e0f0103050907090c09211109040f0609020402042705011502061618 66
    0x4d0200d40b0080e007050740301401c0c88004a0309540007010314440f407031410b085040300401818100c0302800b20f103644550181c0c000840e402e40444050103140515a00c000c1c40214602c03070b400066032034541d00a00ea0201662000401550b4041c10200131400840149006248541d42d540340e00780c06905444000b040d8041010300d46c50500344505000d40d511820200e18141005001985c0c90207a40e10f01c508104160040700c405620507000b1000b03640403901c0a201068640070090208002d0310b62490040001c000f480120358400d0040901401d1f040000e0080942801d80c2040a4040050030400b40003070540001788960455812403900d0704070340d002288081661400100c400e401414251107541d5650910010a12102001c04501d9110030001081519072020034042d004541c008080141100f20031007485a42898480540f14900030402080ea201c0030340c08540c244c1c3c1490000140e2040703000901d1a000400c4101281c519824520490000010014802017490308107540c1c028015200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 706408714 1250 706407464 706407467
    0x120207062a0807120f02011e05040c030b010906080c041b0818070f0f080102122805190506030d0906120f060609150525060f020309010903020609280302010209100e01 73
    0x841d4140346213840240300408401348d142038032100840c84600d0565070340021404101240c030081004560002418000d580d440d103031300004100360300c1042c081c1d005065440f00c15151034420181d0508100007082d0388203940d91421a10000010320481c0d500146404019014204105400045c80d0921442c07540c60300b02007142d00584020340c00180d4680c0180000304650480c10781c0c956001d2060903003810303102420509a40300d90600d48480300c116150100740202d18184603080710045a460170244090b80712182030580c5c0703c44401d18a030020b129107000b0b0016522402e0314901c2c2545461b40403aa55a00d00437007000c684655000101188044504000c800f500c90407400030780c03107641070407418408081c02554208041090f40381050510407480000c0090759402240c40e040703081811901e81c604401c0c0f15008201040b0150b015118180026000410025141c06d40341c080c1e801d1084100901c1103e4001410751329000c4003036540910491420b500c8000c400025035006545641049805100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 706409964 1250 706408714 706408727
    0x130b0702151b250b0a0c020d0308040210080f16030209041803090f06020303071209240e0f0a020103091a10180b010c1101020109080f07120207062a080712 68
    0x2c00000070303040558010f1008402d4403541040710290902c03142e0383c10380d250007200c00a01c940d600030760054000040030203040d0f00c110018415032003590008241071515100b07566440c0211500e6420100e0b81c400100c0c400741e0302ea010400b81c0e86a00b070250511502c4400142aa00052200a170400300c1d00801c6051541c007440040007046400580e040312800d0420094907840001d010b5802c0c08821000c008402c60154089219031b5004040c80084402c20b1941180d0030b410381c218449401e003444e140c5151880e01203a510104071307080c40246004031840c4d0064025145000e4292045620031511040039510b40c5c90701d900c9065080e000701056070078501c01850454000150143d664545440b0385800c1c0d80040c1605101a084480d10b03900014034070040f03026042010004110140c04100c0482c00c3c1592006407001c107100345000004510075860803a0b6450107807003110300045000d403030701c910100c140c0d00d02c0740410383c031603e00c64800e0103035201e01c03405a010140803909203460b01c034100900343d030000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 706411214 1250 706409964 706409983
    0x19050a0506061f030b06042301020f030408030409053714040f0b04061d0105010503191a0a0609051f050f030a020621040312050a02130b0702151b 64
    0x3581039006040d8110843d503030032020308400050680d24007907180351b40d42d0842a9002401e00a680040744500fa480143d11012020302a501503c24022615607002d00402941c081d250354000940c02c1901e403000d00b00180c807015250b031000a41e5021541a0005005480200c1c206980c5100030017401e002d151008403070f0910409050604100d081c08000f846454201c810280c220f81b2801954599040000c0203011480300c6c14041484c00690285c00501074100a048034412025603130300304000c1e030303880c450f0740c2900e200103201c4824101c980d540c929086040542003100a003000070300d20b440306241d00032914196500445000c3c0d103a583e00c100c0d20b21116150180030265055451034000e8130110740e403424141d0307000384108008241540c08480e2a951041c0d403500b84e41000106007828100238202503441303004414114104070010344034447c83c2c002c8903054100400359a503190300c3e10102458a0f000118201d81c014585450440508181406406001b442d10440120305030071000b003a01d03006030907 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 706412464 1250 706411214 706411219
    0x21906021902060a0c0302100f060810021e0c190807021f09061b05160509070e0102071203030e070e270c0904020109080607080435090319050a050606 66
    0x46030300c6070041c2c4030441540c0c0e8079544d505054800101c01d103401d0b41061a40100a8001c6123031a03021b0444240e40c1d0803240032604d030300302079031002414072640100313900c42d0600741c60200c110408a410002104401482054881415a05020308018403462107621030b102c1607403410004201c032001c5d89012010020400c640340900c00405014200203402c51203c1c0c4950401d02010108511840c04040340c20007001d9440001d8034800c5508501710106010140121409500042c0010f29528010365440c845010140c0042000919007160b14816407aa107004030b0405403108200c03a1014000c0007042d02800a10b036640c8030a03d0b001c0c510480012102d054040240c14442c2000b4110f90081104100154180c1d51034109603250300060340d0b1324902c1e6122880074421001007001095000030098050762103a101c40300c200a01f001c08a0b41e4541070482961800806448443d410030081c000707004060010b0140d484c3c0072440a6080351566003c0d034162859004426030100b000710601c62250700c40401c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 706413714 1250 706412464 706412503
    0xc06011406190813050604121413030b0709090507030f0b0103020f090603101a0c070501080f0609091006060509091e130602070807050114010b090d11040902190602 72
    0x20701c4600915001e01032a250140098640801d60f040a560003284c2010f81050444066083c5843c1c54101d00411407101c00001c1c81401c10710504104850485000c000200d6600080e1030440e00d40e4020f4502c0a0300c11014400009000900580c0c0d074003c4a1140c541502c000850142c00504481680c00300c00c983d9041510400c2040c0c05c00c0a0141074448614040d03688039217036a11180b005281a0041e00115407000d13001019603030380e1810f0030007401c041e960340080d103070402d68605c010766403910151450001070b0070f5480020100c2c00c11584956102030404101c40d560040880c6040455006801880005100203a04c50590814040d003540290074498000c80180e41c1042c508100c02d0003800b01c22130076007400000340074409140c040d07540060b0040c1000e5507440403894018000d00c10461516001650400001509914601034030035490000c0c0905c4099186a0342303080f0040103129203142d1140e41c9400c000090b80300c0000030035800984040039182d076410403401a290042d000124000081c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 706414964 1250 706413714 706413727
    0x80601060f080406150312120501060f0c0f120e04052a0c0c0a0603020405100306060e0d021f09030c08210c03210613151512020c06011406 61
    0x10301c500e501c076100d4800d15001010303403160314046002c0c1c9000c84006014400c0c044011041c4440202c072a2032491407502e5500415400441301e0301924024481c3c1c41c081707243e02d294250040c0c0644000080c06208882c03031134000c030a95444c08801c02e5910255000101d04560000c101d0400744030340fa0700200e035803080d8542500658403c14108005500342d4607d0301010a00c0740c440d0100b04195000c441008000304555074aa40009009400912500384940b641d03c102c0342e00b1728000d1050000f513070159900d41d02155480814003a56142c842c05c103c0c2c010410000100004000280311110620a80e80369a001032171401c041ca600108c0b60002d0719541c004844081c0761221800c56858051001c2e46240e45600720602c5d1035046020b00ea26a224285413503001941d00100d40e41e0045c40b5020880b4400c0c0364060000c00041180d12888441c031182010300d2081c800001c4c21080010741c120f00d450701440307824069144100f66008044240c0b00b07584518014459001000285142c600042d070b1001c1c186030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 706416214 1250 706414964 706414967
    0x312170411010f0909110a0e1e150c0f06090105091b01081801051501030e031e0702041b02010524010f08060f0301060f050f09010308040e09100501060f0908060106 72
    0x1076040028a05000044a491545030b0241e281c1c4401401900d1041101006944904486a0004041000040c034144ca0140b062410101c401028403680034080e112011607406e2245c6c030107904000b4014690248560291a0702c10401c00d55408003a00141c00d09040044595081d54000341c0300340140d40009448444000c4020081d148010007403816804079142e10846100c81400401c0d190142d5081c00100008020885000d490304007007a070f4100f00110b101c100458990081c50b4a14803d003060f00c0f01c0e031808595413405021598001000040d85c5100c0c0d00c1e00704048070300080d840001d80d4480c410820031f46030f0360720412001341da106038602410060b03a0008200da1510840f5800303010307107600070509035210700e125003c940070050000c201d05034940c000c0268012091190521480c2c90742d41c014030074140b05030741e24100c0c6da0010401e411f050810003450382090004003200ca6a1041510320383c1d0510b0300d800307602d000301015101c00000780b964200003070540712940c000b80101ea108500402c84203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 706417464 1250 706416214 706416233
    0x123060607030305310515060303180a0e040b0a050a02030105090f0a060b0f07061524030207020a090204060e010c0c053d260c03060d02030703121704 66
    0x465043c90000340e150b4648010151801030a4020b0f1910012a4104418005986901c440c80d0f07001d40c0403982d01940400060615120483c0daa0340c041d0401d204040c3c04003a03210303108101d448018408203050341c481e2440340d41908100ca0681e0900c000c8810301c00480540d104054102001c035106504d10b604040c041303810490b01403c0760840c02d92420000e508446264080c0001e85900410795580d50340900500040d900900c1d019200203180459a104c41c0707100c0034150003200c070b14080304408401c550751424210500700700440c046c142c0030401d4400682c0c07501c500102800c415400180c40300c1c00d00c0c0d8001c00704500d002c091814030401c2c01e004c0340807440d4400d072030341164411032344200d0301401940310654605001000d140744000d07150261528900504080c03440c05120782c0c0305600e001c1d000c02d200400c0a002c09036001440305c082c0c0424070750040c10380213561208000c0c01e69452504564007080c5444684c0d80103030340007483c2c1c021170000175611440d91040b80c10803a989851034101901d650150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 706418714 1250 706417464 706417477
    0x18021305070903020918070308130608010f0504200d060e0a20130302040f020901080c040f141f111218121c03050916060512060303130801230606 64
    0x7041d02800107545c101050030224101800b031015212026032303d01e0f12009039046101580049000c242c4081401d603c9800454101c0790428400350a0314901410302c801091040d150f10310100951011501c18806a802890461151a4001a0a0b20700003e07000791f000081d10081005003801041c244044d1030001d8668081e404ca12019610b207543c1c05218074803a540c0e4402900075013081c2c2c04507000d550307950140003100d00c01e807074038145951030380b640a009109500404e503520015840034443c0c1828420039500c4420081d0400001c100f8a003480303209200c1342a0103d00160020788510f0641006010028800800180c69030500c55030074403140c003414555180c0c50061001c8810550195400c1100103d4900080c1c1003030206480c0d0791004000d848102c0d16407219100307000b0000c10001407407640324101d5081d42d5030203040c17008103a022004294050220369151200340081c400119090000e100101a42400086c003039429450890850203071100f40c1047c0120001040300649894003120072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 706419964 1250 706418714 706418719
    0xf090b0a020307170405030114061306060f050d0603080309030703020c1905040b0a050405040b1b09060a030c020f0313050a1508070503040c030503160b0a0c0905130f1802130507090302 81
    0x1213548941d220800a401542d00a503455802d0007000210400c410705024020300c0b00b0b5078070f0508040015045001e0b14654410500000ca891402c1c251542c8210041c19461003240030108000c0d0345c80c0c0720134070036400a1703a4400f010780002502004254040041880c00c00307050300c10b4048903101e00c50203082490395116060103075032164100307907455071510341c1180500001003041005080c40c1c03c0402c903908003140e81e03130700c655aa1b505405005244500b50b0780b021400411a40c900500d141088025020340101701c1d09501c100d4000b24403215090003d00a4900803030100030000389407004011000001c1e0780890703106121000701d2102c20381e0000c82180c2c41071050a04665a45692415001211003540301502e64000402c000d4a20a05008c1540c1014001c840c0503040361992165003040704d10082039080803603050001000142000b960901c3d0a102d001000110508038240300f40c1981e032020f400c400ca601d4000348050840c43c0c01b0001440d00350420b2410401890546006011050b03240000780c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 706421214 1250 706419964 706419983
    0xe0f060a0c02100f3303080f371b1b180f1409060115030e0321130305041a0903030c0c040605060703020309040207060612030f090b0a020307 62
    0x703806000300b00f080480803030190104001d9406030100b03c020881d210000203030a401d80210468404400b50b41c0c151056411564481d5a02d50707643c030075071944040d0313410f40e00b00302c01d0145501296800344907002e4205030180c5c880710444544207030844082c0d55024201400f090940101469211651002e586039201e030894410504000542ca01400250301540941b03445644005e00003a40e03401840c00080f0300c42d420700072990001c041101c060f10481c4d0000303d41d4000c4004000e400d0601c88180860303039140c1400116680546100e60950b4819039800e4200c0f119011038001501414074120343c4202000303100c2c01720200d10755000700039200d03620400004980704c1004803503454140040328101c190060440b6902c1190078400c9480d004048551441145032038000075884c00d14500f1140341552540c040d41c502035540e41000025009070a00760780450399150041136a8800c00c1030007182500030f450300c0c00d04500103c40102040c40d070303402c1485012014808802120f030000150f400c519440074001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 706422464 1250 706421214 706421231
    0x60306040912030e070905010303020d0c020112022205061207140f07030e03070f050609220903020a060c09140f030a0507062706020c0607050703060f020309010e0f060a 74
    0x402801c6015400380580d5440381003901c119805a1250380781d120340000340d4101d9079a4070200303412110309100c0a000341e0000500841081d219291401d141032050400000c00b012021034001241c00107103982c180b00209450b89201c01980203401001010212842c0b8902181e80112081c2d000024100105008660484840c512403140c150b0b40d0707032000d2410306500c402e02402c4c01040d01e201e00c0f08260081c06030300d4000c100c00503040400c1c0e09440c00685940e1400c0801d0050090f10180302d0f80b000c285082010304500098614002d01038080d000360700030090f0581505025045810381480340c814010190010081445600d1603d20683c00455101c00c0020304080424100401ea080081050080650100703016422031028081c2020803a8003601601100940c0040780b81c2600030040075a020217451806454184014040f44d481801940c602a44d0390781ca400030f0301c04901d00700c49100d070040304020b0311401c24443d16009070140d100503c032645070300800c070f5280c00c0043c00043d549031315003008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 706423714 1250 706422464 706422469
    0x5060309030903190b25050903190f17090f04090f140d0f090e01090504020604030503030702100b0d150b013606020609060c0d0b09070c0629060306 65
    0x107071182c294014094840c0c0c3c04000701480798410406104540000c0d0140109084045540303070043e8442c03000d8110110b00028544c1a911a00300d02500d6602d4400c0b6940300c80105000103d451043d40300d403843d640c0d1204035241000740504126503074544580144035402d20341e80d84072500c080011040d20000360345aa00d08040800e00c0307181e800640800030140e50202c0c1c80c44001500c48005e41107950343c0e920024500c02c00c4a0040491046034403101c0d00e040140704d100015840b86801501c02001140780c03540d01da8446085401c1101d80101580146402c0d00e07642c20280600d0890304012030740d00303404aa0036074a100002840d030302c0721960030b56200c4181e03415074080c0c0c44188130708405280007612904660450403054010745540804855800c5001500a0000640c103016400c0c840c085c08a682e10581d048002350400740b503810109461b0501d0b80b8264a41c9004d03a07004580c617540303c1c1c0b1103040d9820135101750360010302c801d800c0b6403c20020110728820200300f440007440c00c8031141d60ba600c03003000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 706424964 1250 706423714 706423717
    0x60620150606071b030302060c070308063601050108010609082a0303181003022a1c0e011d0d02010c020a050301111207020a020f04360203250506030903 67
    0x2000f4210341c0e0761001100303003250300c4d8110300c1101e00c294201c801035980c815071500c450040380340c0200400c040c840800e415182008008082011905000c2a24810392107500401c50300c0900300103541441c0c40c014041d65900041c654050a194102441c000f0328200b40f183d503034840000c8c00d0366081035010804a801907640900401c1190043c112030303c50508900302c00080700d00c420b113540328008200d00402c045009009503100401c0b01140b40803041c41060760840702c614600a03440e4240101d42c0c410a406000a140c0c42d5560700503078548244d511083d002600400c4481c0c0001c8d00e40d0036210012101d6030f1181e401c80780041e4286002c0000354102c1c400b080c0408107580140354103508118410b920400c0da84058050000b0011011846882d00700c0d050f0b8951064950207900800003034000c00c2c00d0f041680180c58400110710001110450020646d5100c9801c081c05001c1e68864407652030a46c0703000c0100ea60803040340301c407000184100101440e0590300c42e11850b80100c80c04000500c0d059001d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 706426214 1250 706424964 706424977
    0x1208071d010212190305010e0907061d03030301030308060f03010504051b15030708041a070207030605040f05010603080a110318010f091a030105040e1903200a0501060620150606 78
    0x1050144c0701d03030a10740483d6050b8441040d10b40000e203442d00000d649000c4020381401880820058101281440b000300c03100065110001711406900310b4150040e2420001103009600a964003c41d5040000c00c1120f20122811911721a0b03041c030003408041000400ea8051720400c0000c00c00000c1d1880000c6508607292402d0007001d4540403081141d500d0b001034050340301c0c03445a48004615041030114003810350040e50140d0060f0701c03003201400000c07060b910094000d80034680e6500842000d0740d41a00f0b46005800c07c032044200804ca51114a4128003944a002c0b10302c00038500340211048080e0900341258a030701c2c10000b1080c101100d45006003035135006051070280860158140441c0342c80280c0c4280300312805585405450f0f6107502000c29000b42500100304003036440c074213648007101d9510b443ea0b5003000841a0040070a00c0d040304210304508a8850300c00400c4140c070b4840060982c101680c0c0c000c081c0341540310002461079001c103592410f42803203440c1c28250340b0740b0340206560380501e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 706427464 1250 706426214 706426243
    0x601140109050d200102070f1e0b21060f220204080f0a110f030d2f0a14070609031b120f0b1b1e0903191208071d0102 52
    0x140c80600c107200903186000d13220407441c40c108811000d0003004a81d2813845110b500b400c0f40d1006170170300c00c0244083c0c582c4052441d1090107800340b07489205070700e0310f40d124405604a04010355501c0301809803410100d5407008044440e402d11010603c04a500900c4c240506c888000c4c3d000944950314045034155806804010101c500c100100b040b40c5075105100030003070365601c0b200174040099150002809081c060040d000d03040314101280d041d503140025809200f40742e41d81c9641c6100312101d0082100c0d0310810000106107501c514103040c40d00c405038210902c065000240d06100c101d4010f2000d078100d907404111700f2030520142e20503c0300070307040e60070401d5031140303c22046080c452410704446201e4050a07402040351501c0e12110480c111034491200c0f0014240300100300341041074901003e104004070f8113480c040120000a040ca000700c0410200d10041c81c0781c850500008254002072440141002800c60800001c003420810210341f94182d161810f940c6100d441e403017030104540a2545 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 706428714 1250 706427464 706427479
    0x504060f050d02030a052a04290f060d090b0108070f0b1309050f04020306090c030c12070e3103020a0206030403030e0601030b2a07032f030a09120302060114010905 72
    0x4003016a500c0c032030f43c5000c90006030201210f141d6180742c1407050b14403034050340c0d032030803603c516000c174030171412a60180c1c1a50001d032214051074072f9241c0100030010401c1c4030000054001d0702e864a01e00400043e0003aa4982e07010b09020301c042c40c0158400030270b03945001416521020f02d040d0400705101c054029482590400382480b0b5510000a00706025902c224150389081d40d801c1346040c0d44440340c100c5030742e05600850031004542020103690342214090b81c15106100d85940d65020b48160036111403680540c2d451034855413030340c0c0d558101d2214404045008101c6030588000759109007144010b84511000000701c5c0070140658040d036000014003084d60303080d681da42032210000d5021a00200941c0012001130180013001c690124145090700320301d8100262030301c0894441032810340350018004413080920340c0c40050213000c24040b001000850303982c040d9100040c004403c0340c0c00002441021420503000035000f0983c503040d0740072403c40d100b03114152001220052603940c4000e170800344 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 706429964 1250 706428714 706428733
    0x70f0f03030b09092a010201021315030b10020601140d05061305010b010e0d170408250b030f06131803030209031903050304060c092d0504060f050d02030a05 69
    0x416401440754400200ca01d040d040c1e131640716090301c2d4240341901d164540400301a01031141a110b4410078401e07418400103080c02801c3c08000f1090842e500481c24200d80b4801c0342455541c9401805040076041d81d110003c4510000003175900c15040c001d424503000000c0703607801144c5541c8001140240c0203c129105030400240e512003040107400191860f508040000075036500491003044003031400342898410a00d203854500300c03440e402c0c0a000d1680000c0000040c4440d0030016040500e0480c00c889482000505000a2020482e40042d0480c01c0610402c10000b81d07010710503030f012100791754214103d0001751400e00140038071104196005d807095003210502d90705070b0180564000c03c1d070440e1104041602d5180c1030740015100280007034001c00000780000c00580040051070510309103030305040d441e503107070031100900700107103801d04c1c960501c884840503141a0200010541590704018581c101a140c211400e0240207583c002e1002c8107001c0115241000074501c52600130098440112 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 706431214 1250 706429964 706429967
    0x10f05040b04020f15040905130b010611070602010605130c1112070b1003050319031401150807090b042d080f1c02060f04030e1002030d1d12070f0f03 66
    0x9800342c4080c0e000d000c102d91080710030305203004449480a4219070319401d1620303207240e450103007800074901224400c0c0d250720000050714498001d03000e401c4940341c3c2d00e0402c00c1c2c400501d19000503a8040011603051403805c2003540c807501c0c01c01400c0d5425007400702e9440c03501c106c184c8070300c14503e000c90001d104016800c0e018114440103822100d10600350f0311b0b103540701c41c0200c00389a01c80c0c0c00050300c3d80c3c2007005050243c0194001c004607501141c02e000c140c1050b150072a01041000340d1060442941c4030300c881e0041c43d4400c0000d0f511880c281895006582405800703662400365000360071182000c104c086c1e805040ca20080310120310040c005e6168151105804c035220142c40c83c0d141c0d414410380f8040810f214400b140e20098121581c018000c0340d903885030a0800c6503016001f5801c1c041c165440710900d8640c40c5619410b03030174580046070390701d12985041d011030300e100c0c045c400d102400c40c820002d14900803500407950741c900d24000d0380369a61405c08d11980019444024240c4807809083c1c0c0c20103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 706432464 1250 706431214 706431233
    0x7020f0105030a150608060a091e0203041a090627060417040b030415050c0a12051008010504030e0109120804031101020118140c040e0c0108190603050105060a3302010f0504 76
    0x7d03541551840d0304181c1d5005510140d8200c1207205110002072030008140c032020768042d5610034014210680e07818602c240c03018003140251554029a0031402c1002506240c603011804d84e840196040c440d02d004009009846160180c001800f000420b000c070504032001b0f8003a51b010f00750350003409640341000d00d4102112114048080d41c03580c01c0100040001d000c1005485070325446441d40c60f51003a00000090041c2402460720080582d41040442d05100034850544542d103c0d440ba01c0400c0b440c4030000d030160949030300c0800e0760100d0f04542000900480f00f510116030340003021001c503a50040040c0e016003410448040400d050045650a1041c216840a08004101d041c5c6140e03540075020301c23080d54892244a02c1c1540000a4888a175128121556010f1007094600450500145142c000da42c0c1552007070300d0681d104e2051040902d030005c0310100070454541c02040700c44514148001003501e0840f12244102e81c0c0e069252650300039044200d40c90f0420004010030302d818034040e07054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 706433714 1250 706432464 706432471
    0xf0a0510021e010519020703140a03020c0c03071d041419060b030111090d260c01051501020d0804081204030807020c0f0a05060706090807051f0207020f0105030a150608 74
    0x140b0340180c10b42100300c44103100c2c00f4040d601c0c0501d002c00101c404020100a54400501101000307231000051112400050103400918603a42d400340e903442135425400e2030305441c070541314880c2e0040d44041007a2144080f0004000482030b11003c8146d030390382003a0004c240440001c4210b402090f00c0804c0b0a6111082055854414501040000c180b0300505081380c240a111036109007040000035241d180c41860880201d10500c030801c0e0068000135803200318600a044100c598102054200301200b0a0140c607901030400048598950a103c0000b9901c0103c0e40c000d0082c80712181c04074040c00900000c0b9981d01607044941c045604151500402c1501c4c11030300c00c001030041c00364103c0c03580f43c0000c1c2d007200460300609100c001800c10b000c00505500c0100211011a035407001100041c09032000f0b0200e82c1d018101600207014400c0c425058a40b00100d0074008500c104600d4005981c1d02540150016080ca0400c0e2244c0d42d40c84254000c0461084900c0d6079450200005102a80060060722 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 706434964 1250 706433714 706433743
    0x1b0501020c01020a0e03071e0302012f1006140a030f2306101d240a080303060324070302030703090f05071701092415090218060a0e0f0a051002 63
    0x2030062351144815456218005801c2983d0342000c0200701540c401c001c02d001700c07407202c850704546401c401d070715007000607990950325a83e4010f4903c0c030f90050b9043c40b807c801003540349044440494501b0000d46442407501005104410b00e92104042c0301d0554a9001d00c0703401d0042495100c208408640e13960354046031142120700042d000803a406a007030004080d40e40e200808000252584050dd090340000156440c102100d10b01c802c03405640d0b8901d042008200b0403000d181c5e00d041c258241350800650300011913090f13950000c00030f003c461511506d980405a80f5005807a03032102e110403009000010400740c0313901d40c0040401c040c0b010100c2c0340c1c811552150024480420159103041c00d994a80c40090807502c1264101800760091181502511545040000d01c243e900d005c1010100348503003181e2800399000c1902e10440f20b440304111580b14084603014100303480c1d400c0081c000a1420b12584c01090651108680c5455003402032014002c01000200d5125058100954402e041c125200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 706436214 1250 706434964 706434973
    0x10091109010914130803150f0303040306060306060509040807080307090515030702011a03150c0d0e0709060f051e1809010209010216030b07051b0102031003051006061b0501020c01020a0e03 83
    0x104d401903005002c508069115070701504540d540310400c514a040b200205800c0711210a90000c07950701070000b8009103200c1c00000588034254101341049802540003240a40a11030a10000c00d00d044103449289500c40c00c0d036030360313551084c0c0c04603017680060b030249400c00500c0162481c0e08518001451250090b64000c0100e0b051840c14a10354400b441c05264260f0400c511b501c2003410139181807a0b004101c403102038500007110f0302820850307001d840f202000b50403281041c040103201c1d01801c0007c112003d06403112504000016240c10b200701413102007484800540280358a40743d98040705460620001c40c402d240c103141ca076010b58884e0b80a02d0040c020743c00700340050035180900506494102c02186015655001c05807141d42c02040350a4a0740c520b241c050500a0090004612a0a6002c1204403280c03440c41c0507803524400ca00345c00021407d001007449801e13030192440548542000c0540f2003415181082070085c884e44010700c0c02540001110034085401030b00d1941c402c0702c1a4104c2b0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 706437464 1250 706436214 706436221
    0x6090801140105011d0a150206011a0c03040e070210090c060e0612010b07050f06010f05010801090e120a1103190801080f0a020f040b040c0c050f07050310091109010914 74
    0x81e8031801d09004182c046414400340e000c03440542e55940d0310000b4068a030701c0035240c03542500c0c0c1504511217031480040e130003540144080019040a0007800d18160401c03030a0410000009450340520301500b4415a11800000c511a10801c039a190b8001044003c202c2444541000b40b102a913a00607031000c54048000d5030213508059044800002802064200030307400d0148000146d070188074107a40c80d04c00c0242d055001c60091000900030540781810a00b801c0ca00700026015500c142c0c00701c80c0540c6000d401810155022a1f02003145948a010a1355840c0211050702c0300500e598060000d803101040d21540d1200560850b00c014500742c981b0b0301c050707a07076608503030340c07086a10300f0014190461964440141072940028000ea240140003103011942074011900301c072229110400001c01651100c014098148520340031140c0020142c1055401c0c80046550395092000d404821659900d43d10f0134803000040e0450344440c000c0402c1d2417960341d4811580070700b8a86007212005140780011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 706438714 1250 706437464 706437491
    0x3110a03030903060f1d030405010f1409010804151d06060d0503190e040207121709070605030c12011e0609270e1014060306010503070513060803030106090801 70
    0x10501200d50582d981d031000e506640c1c0e040060f1000014461120b611409807801c00010010f0306143e8402d002d0085454524050006142070300b103584040a01108255503c1c950315004101c0302610028203014101ea1514548440009407030001d480d0005d2800c8094002d030380c045107003000d00000b4942150060b445035401c0107144135110b600145a035108000b07007134180c100030100e03103040714480c20412078081051010034160f0744000c0085851242c100c15405156400510728903032645111400502490803021059403164580104810b014004c000620311140540032a11401d00d21400d652407941d41d0040703048000a00b070034034521003c3d030850116000344104062811100c0340107012101c9042c40302c8002c0104d4091245000301500d446045440d1801004014510103074120000345c184096010600000d1010f0034030761107a08043c004004998000959005440045581012105891061500901c803560101000f40008400003880d01d40040701c0504503056600240641c0080040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 706439964 1250 706438714 706438729
    0x2010e03120f19020f0304151103150319062f040b09060c0106082a0a06031119050405090a0b1003020f0d021b2b08070318050105010311 60
    0x9524059418000007030409204441c0d181d00403002c3c40d00c09104104002d000740c284e0748107103544034610200006110400412500d4441801919a810031000c802c1850f407900c0c1e444080e000d40d903484a6040149803aa804dc8410601d2900d9510340c60008511171509001414500900c40801408001c4006501c20701140c60344c2c00e08217510542d0b01d41414480c10840d542c00a810300e542151017440074200380b00003482500d000d0480b0b417008201400d80703018408100b00440c0e280c1c28106910000181140d26405400300130344189080120f410303002c60b4003001c45e600408544944a1005d68640c09565420100038803d44400760391841c19581d8102c600400c0d21240880c030768008a0f030700c0300500c8161081d800b804c069806102183e203403011039403494060340c001450b40b5020b4880046441c0268004002c1e14120307000407840d22003417910071001e0180c54103a0000c480c080c044c14000003150740384a50b110b508880d0500d0b002e00e00d0080313036092071802003009010882d02c000b05441080c0c010711f440b81 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 706441214 1250 706439964 706439977
    0x150914070504120c0504020a1107050d03020312040f0503070305192f0708161805010501090b031b03011707060201180602070c09060605120f220510021902010e03 71
    0x1280c07249024644001000e40d0010381009444803a00b061010485548078001000000403640c1e4004070948036040e06030500e0240d42c8090320428120300d441c0006a00070058810100c1c401c88441d4082da41c505017690500200c41e4024018000014007808150b00f1030090b00e0401082002203410107000682a00da288110041a449074240b6070b00600007170603100c4030851501c0b10410f444100380c3e01c580041c9851076036102440725a1128000340600043d0400d4100050203224082c01517524000001e050301da60342c080d000403000000f00040034004c546002c5441521080016981c941e5500c056226800c01c60110705c4880c052800001606071050040c2488071204411080c81e01150390340e00070003513000310030884440c120540300203490002841020000d241e1621115902d102c0d0f4409a07042c02401048a82c01e6803910341407000c004c840c01840605842411070812406e0307a0b40c2000b91807e0315814003500594000100c84001e41c541c04000f44506c4007640090040c82c904003c850303100d02402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 706442464 1250 706441214 706441217
    0x20c010c02060d0203071e2d0f0f0215040b01180c1b06093908120d14010f17070312051605060103421e15091407 50
    0x240700b00a810307078059000316041489130500010147ca130300b000c0c00040d0340024003240824040504200d0548441001e02d503a4a89448400c101e1028990050b0525104804074010820a44a503c1e032a43c001c00c41035030740150501060610f440c251500744440075090288004c0044132610501d50241c132030180742411a0280c403480306483c1822503140c44440205410b4440d01d8490410f04041060203110300d02c0242d507150034000c0904036440c0003560401c4204c00c802e02d200390300c034104151600400c01455428000c15125507598103200108041d081c4200419217210601300001400b02400040b0380c110341c40d48124100941c1c42d19506074407030010b448050f0401403595200e01c0d201d0301c10b0000301500c102e0030304141400c0a09480b0b0910b007500c00d0700308641444c1c580d124601080b0a600369021000040c10807a0700c448643c641c0d1140c288110590350a41a46a110000e020482c50740b071030b032601c0090f00080000300d60160300030200504500c54820b44529007907440c103510f4184190750b4401c0046 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 706443714 1250 706442464 706442467
    0x10207030b06010905090c0901020c1e15120a0e10061404050c13060e0306062b0804050d11040509160311040b04050a0209040501171e0a05070b030106020c010c0206 72
    0x2036840e21684520000c1c8428100440780350049642e0342c07411082030280c0500b00d1102c1d21070348070300006840c06031080c20b02032041d10000e0310608441c0100c00c016203c0711055940d041c280e036215944c0c00450141c4540b442010401c40c00b08074210406074000091905100304480307107228661202012038400703010703003a0818280c0060300b03014180358004a81003404c0c6001145080407280045020708015004107001490b2040e182002e454104481c3d600290300319040705440001e540b044219403100c980490743d410740e0700d1105051013640710640300184006040342000e9805440d2540768005980401171003145424013056071001e000900081160038002ea0041590858448000800015160b1680580c0310031405c20741b40c0f694000c2c28000c1c50001b1026840f40c01c42c10400c000d4a005812000c00c10b28071003c501140074001842c507003018a80b402242c20000d40303660a0f810000c01c450040c0683c071034040e0000b004410318000354104c030000d0f401c0e207030342e020040700450300d4030013241019510010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 706444964 1250 706443714 706443719
    0xf0f0b060307151704050a1415160914030a061e050c19120b04150815042d0c08150906060d1101030b0d0c081002091c080706020d050106031a010207 65
    0x1084d1896a041070241040301d0400702c440d52800c082c61903d00220015421480070f040400b13185102054000c400e0068004171044014001004800544a4a28908a103044c1005151003d1080340502e54104c8011301041c580045442e001581040c1c0b040c0c8491b29040011b90104046d00545d000c0740001c902c030411001d40b0000842e400032262030049000365507035800401c5030f502e6115040c1c028000c0ca1500300780d185000b8030316042c06c032803215140030700d0030390001c0100080007110050f0b50149405125240d00303003060083c45040d650f000c0024041080c1d1203010990707010020701c3c4550154855103c5141759900501c158030b400060b54495000300c0c05011703038400202804040c030359030707603045c98005000009074001403084d0480c1542500c09404150040c0708101c0305010694200d60041410751a00301448086401440c01d0702c47c07902c46000c202083c00820140b0300454003c00c1d000401992100c65005c5005c0041c1028410704c00801c0ca4220b10035244014401701608061050700030380308091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 706446214 1250 706444964 706444997
    0x80d0c0e210607140f191e02071a07020604180b100e2707030b03060a090816050703141506090606030406050615070b01180203010f0902070f0f0b06030715 68
    0x3846094600210410300c00200e01c0d0a440020b4400603041403100d0740e00300c0c4c6c0980007074922152018440080d1203484440b903030968000442c40c0860f021220074060640200d005101076000c0c1900084d406000041c0002d20b07001c2120403240360490b039540c10004d9002c948100904a04018815808103035001d00008075482c000704174100c0da42005001600d06155000d03070840180c421645407000c61340d9180031a9041c2410007003d0381c0130b80c50032070401c645420340d107500e03000b40940818401a6a00210b02d001000420b010b860000d507403101c1550101d036150341c1a980c0b5107420003080c030200f46210000032180d1070f01d01c0707025008107800351a252540d111500c1e02e601808000300040e8120b140b4607030142541507100d0082c103005001d00c149281e1941040b001805a2243d0400d000d0101d005100500440361f01035800b404690006200694030683ca1401300929001c0c44805000002807180ca6030901c00180300c030500c241000c0f41992141c40d100e2210024411032400c015000030201e0031201c0d0260f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 706447464 1250 706446214 706446227
    0x60e03121915180f202206091a0403020f09090a02090705130f03020609010f12090605070305240114040e09030912010605060a0309080d0c0e210607 65
    0xd1602040814031000c444880e02c80c500d603c0d80105180070080d1035200c000a140d02c03600e050301c09124404d100030800034008104015510701035280400c000506c405034480c0c01842e01050018009481c80e0866030b80002030f21020443c410302c80d07889410345505203400404012641560b60040084545400e99418807100c60780c010241c0301e2902c245c628507009030f580c0d4000d051090b6900d84da43d588d1409243d240c50403452050340aa03e115000b0b00003440141e440b001a201d045074280703480810207190280c21600118511125280c80f45084214801e1290707a41000e441042c00791801d01c11501d8003110680f111014111548040c080548883c0e5298803e82070f581090a20303072191420182c032140b1140100c002906e401100707500000ba40c241c18100b9121358001445103a00801c0503c0c9171601103a00340c40f603400c40a08059607603c0ca82d042202c00d005817411b2183c03001c3c0801842d41b00f2140513001b05144241280305145d04000a0303100c00c0c3c420035000300340b94a100a403140e41c0340c05c04141d449 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 706448714 1250 706447464 706447501
    0x15140301050901120807240c0801080a0f150519050f240604030b09030714070303021c11240105040b060f030c070503070f12030e150601030e07080a060e0312 69
    0x7605d800c100560102c1c801040510aa54240104500c0080f1280840341100c0381c02c0c2c2240c090104544c010008083e010818603615600300d900902822068a000072002d03074400103081c5007510302414007241d86d1810a0003d03882085c1302d0f007084a40c403003001006059a0444030b0780422280802c04a544ca5490740c0102104900680703442c0c0dc060b01c03903548203020542103131102c80550001c0352490900200006001c01b40a034113010382006405c68400175120400110207551070a48064145090351140c00100c1c00c00c000c032030507515000300d1080444c1c00b08006aa842d82c50400b00300020590385000d110750b81000c240205030a281040c0240c8040d82d941000788950040c1e1024820000030544c1840244203080c0701d25031401483d1203078a801c42c0824042106001014a03190a1449812002440369941c00c00c0000c698000d9640780c0040f00500401d0070035031680d019070320000490329070024481900603c600e000740400d0400407492075480c01000f0740a410301000d5808542c2c0c828405034000302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 706449964 1250 706448714 706448723
    0x304050a21122d060518090705040c05121312021b0102010606020c01030504020409080309031e13060c0c031403040602240106180509190f051014040f061514030105090112 75
    0x16903551711000140c0c40c1d4120344803004c04120520400001c40070621030f0b2800791804032820855100e02c010001c00d0741c02061181411112940e0204519000c110991052154000202040c0940301040252600c001f141020030b20f40d1007000c0129298018001d81d000d07108180c3c01400503070f8803a0300440c045c2401800c244c0e0800c1d17441c203c107404103004800030342c0300b94613050080d5039441d000002104010404510600c0700482805003850f000d804402140c11036040340340821070190503040802d4100101d60001b46864118031403182052000300c003a1084a645409417070b10302e40b0714203943c8200c101d8040050203c4031000c0062083c940503a00c54200400322007126500b11345c8540200384080d00a82d41030015044000c2050090030b2a400381d24000c03005000f091026082038107000803d41d0701401170702070407a8601da1240b03060b00e460303100c3c0f401c01028034010f112081e90340301c0b0a110301c07a040b84034200084022540114134290301c0c080b40d040313842c040c1041050360f19051080c02409100201102d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 706451214 1250 706449964 706449971
    0x111606020c0726011104140303160303061d0408072a080703061a03061824040203071d0601181e180603170304050a21122d 54
    0x41100c402002a10083c20a07452459003840d60310f0328855000409040c100034680c14900d454100c80129025501100c2000000b65940345028001a0460081c50840c1081d04610000b00c41890740c141c0044089859800002d82144403140d00b00c0845542100c1c040c1c04508208071010001783c5507103082c4051040140883c10301116020010171500c075542c03059005520191085c0f0a101c40340c85021400900315903000071200a4002003912658001c7c807407100b182958040600ca20014070069907103222901c03840c0704400020404040d06042624268000e11030032a01203424031001c0701140108a5050001203196035000c01110881040700b12400b50440c00b80d000a00c0e12010444510344040085406070380b10b003020ba80e03c4040034441d00480056081460810110300c00c444241c460b4100006a190f0320758582c205a45011381d2803500814203454288804003c200ea50303840300c034036482c40c0e4039541c03001d03c0030003030801356154034282458241420340e050b10103000202060081112222020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 706452464 1250 706451214 706451227
    0x30406090b010611010605010c15091b180605040b03030d0903022b030b19030305130b0a21020901091e0e09070603060b0c03120c0705070603020d0c0311160602 70
    0x200351041c0d083e07100c140450b401202c1101511001e01501d400751a0070b182c210b03980d01ca20b41350040c0c5442d44d00f05039104035a650048030b050007440c0b480c1c610a900b010b060f4041c440e07512031400d46081104c0f041e01c201603151902c00305240c030f00341c0942d0014810040c01141040c500300a51001040314550403015441102208400c013440d00c1b001958040807005c2e12246496060005000e4071b4840342031500c1144010605241450704980140c16213815282040e1140402c82c2842d540300343c50b4020041c40310001c1114450942d2150324040c581140001003036500080c00d82080981c025412014085510420b06000000c0c603008102490a85c0000a0b80815070751072848a0b802c82c2696044180d0f00594003d12100fa00b5008550007400b405040510b071a07440191607403680034960030f40c8000c0c81e010002c918803200e0f89080d00c0c007454112003a2100b096a800000d00254040b01185a00c1802c020f45521568000d1280d00925081c2a50143c80c02042420840c00d400c1081d400303c034501c0e802c1c4000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 706453714 1250 706452464 706452473
    0xe1801090f060b0d05060a020904060f0909050712020a03030305092a030c03120a0c050a060c09030c0509090c01030e032a01060b031b091f03050a05010b1e03040609 72
    0x4032402640a2918407607440c0700da0900b08155508106450300135108902031200040c4002140c80d40700c1094180142c6503504000000c02910042d8060344002c076030341101080c80c4090350311040f6024850030444465940d20489042003441c00d40010b035010240b9081000404c4c001d0304515404030342c0c0d500340d5101c003c402d0401c600454903a42c0c62b6090101010390343c5039600381041801d26540c011002046240c1603d050718440b803203032031010420820318090090400c2000c10000e40140c2d4400c0050102c41da501c00014220f03041c5100039501c4101c00030000855042036052503000701c07000030180402030350080055000e485010840740790780c401000f5203c2c8028801080d803108407400e60304403501e90ba1303203092a4250344841d040b04129040030801c0c03200c50b80601c030940700c07410884280c0039202e101d00070020b44290701c0d407103028502c2145620040713000340e410341c0841d124080010007040b40d81d880b40500c070b0f103600030b11400c0d206001912104426011621010b95401031244802150411031680c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 706454964 1250 706453714 706453721
    0x303080c09090411040f1e0903110d030b040b01030902130c0e03120301080c091e0405120a0507021912031101090c06020604050f0a030c030c031112040503060f100e1801 74
    0x406645000300402001c100345001d0090381040143e041d418003081c0ba950f545403020071601051f503500305a03200d00500030503005042ea0303900000d5140c203480b8804510325016001d000340003180d40c803613454242d9070717001c2e503005c0e01c07030b90030b50a402404c114150140303d007022000344603240707026080c040d070b180e1801850740d07040010b907400d50016001c4540b00d51410411034640044100480d10441d90740e810001c15200c02c040d0644481ca0049002265442ea402c180c0d0038003048202200c2404c40000342010450740040c000c01c0306a100b502e0b0303900c00d11202e00c3d45858421042c09050001545c3c1c0c8c800320b0210788201d0110080e110220000108110b450f070b80c0380e9408055600400141c1c10010410041c0903084c80342c0382018070700030040d01e1310026070354001381130209808000b014081c4e070249203018503202d16240803070064260225081c5c0340c6403200410207a001881401d00c41e100e800000350b031043e44600b101c0c2c0521039038040d0011041c1840307a200030804000308000c6c80c03101d10980300500e0b45000d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 706456214 1250 706454964 706454971
    0x31623041205061503061902090901090903110d050a050a0e0a030308011a030405030a030c1808030d060605090a2738010e09061804050d0906090b040303080c0909 71
    0x5a526074031840e58500a414400002e01c004140c0481c3d01050041c0d0f1404281c3c0740d07020302c50414600c5003e040d048070000a0040280d490740241c606000420030140310742c0500c50180c020344a284000f242298429668504401c0c8480002e00600c480300c2c403103000e407024240c5120315040800f48001700f40302190442881d030780240d0025506000400c004404183c903126005001540b07586546040c1c0c80c0c0c03e80d0b034411050aa010155110300b10311525100d0740301c1d00e125520b005460b0fa000ca95600165a480c1c02c90081d440e100d0b494140002801c6008108a90090b10054000445540f6151041030707070200510601417050b00c805192213000702544140703440e060034a4003486848001591803807049090703201915161000242200060703070000c000c1c151103a0202c0d28041e65503110700104004003101503803204415103c900788810400d01082c00b441032034055840c070b143c00781c0d0340204031401503452050340041c40040100f8070210b4425990294896603e2032160718200b10b074004101940400c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 706457464 1250 706456214 706456229
    0x7060213090e030f12040f050109030f1206080a0b04050a12090311060901050304110a09020708120f060a1a0417030d050a0b011b06060302030303250503162304 70
    0x18014405420035100350110002502d00943c24512406580340032131041c030b151415900c100c2c030005010007809095004005501000910500c50107103806444040c040d41e0b0700c40401d01048078405107414031300c5460201e9034403030004c0155807181d0301c0341c01d6542e00240c0305035141c0c059071118801003903001007080e080541c0c60740c580302886d156080c04c1441070240d16896100780001c00180905030fa0041c26250040e811100c4c140200c0040310024508808950189010f41d00201c0c1d814144000140588060b0407125842c102c0d5540b2071000d014000000c0b40c08a90150800300240905640c2c14444c5410041903400e251600d900d41054414201040d658400da581c40020304006d89030050058036040259104107000940007171001800d01741803a510889007501040301e41c0140140d5030440401190080d05a0340c1d41d0418601d1010181d020031110039820341a610700d01d03489481142101d2065200c2c6101c0c44c1c0800070b40710100c0d408a41e100c7c4080001961a81c81c00d51900c0a000400080c460f6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 706458714 1250 706457464 706457497
    0x71403010f1b0909021c02030711060a0c1d030607050a02010213240e0609010e0a030f0f020315010605070209180618010c05030103020307090b0117010f05042901080705070602 77
    0x20b900600800d0b103034103e140c140303005004000750b0003190b0200400b0201685405601e959070110102d40104044580e6500d40c0309107018401c84900e582c0c004185400140d40320701049070100d0290200c074036405607158056102c100000c041605c40c401802c4160150b100140c6041c0014000c00100b001c51b400c2403001c0a9148031141c0b40c034604c480030742c0201c0c0d0300b81407181401e401c0303000141040c0102402207050104864000b2000d5640c040e00c84007840d4032542070031030192541071200d580c1c100080124002d200303440400e140d4605e00c20415040f10001c0d82c40515010340c035800d11404143c09400c00207402e00546451154050a0203807610400001300340c4080f00140342d810300c1c252900d0000341b4042c44070410052000d6107012a05505039401018042010702800004980c1e41c0003045607201c0350381d40d2400103d04035030000035000850b0300441d8103104403411082003184011340140203400caa0411541d040042d40070340d41c11503001c03445045c8642424404d40701c00041e40e01058108040c0c0d8003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 706459964 1250 706458714 706458761
    0x2070318060302120703360b16090b0c0a02190503190c050a05061e1201031109010b0a051c0617061e0405030a110a080a0f12020903071403010f 63
    0x268080956001d00289002d0010f000b6000b00c0c0390502a8501c102c40103071f440700450342003840f210040040030301d0380084c00c10114a0449209050a00d40156110000313211604c0086c800e00000700340c503006081e110142210302c0d00c0d6401c004242002190040740c40f0f41400e0009446d40d020710040780d054070b12110142c1141c107203107007a092010140e001103104100201c2c003407060340c4070b501c103995403071030401c1100741c00b40c4d1a20311000260161005144440802c00004010400d6030ba80c502000141510b0700e0070b059880300d0b03518076103000d00f1052100040c414804404420824411140c000407a12400116141c030f40b800e002d050902c1d800c0d1010b955101030140002d01c1c400c40148000c40070184880300c1a82007a03504c06440c1d2241c070004408000d2181560015120700b445102d0720039910031415941c3c4c210701c090203420600210f021001080440c140d462110303c1900880d00703482001801380400d141032607081032681044410321038141d940d40c1080e03580c48903a841228140c214030000d5441851 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 706461214 1250 706459964 706459987
    0xf0a0c031e020a1e0903030305180f070305010c091406130f0b090f12030708030907180f0b01020706020c060c0102070611040509090d020d030504050c091503010f09120302070318060302 81
    0x1504110f003443d80c00130548802040b540c0442c100042d258146030100b0961a410f1803241c00c08008201004a4015a01c40d1380d0218000604c4100301e9100320700034841c0341e024000079200c0b1481031085091242115281012502d40000100b184040116060358201d4944e2503078508a201a0401503240800180190316440d144e880c4c6100403e00302c0d000c4041103007401c101510790140303040060440e00e001c00032030241c4205000c0e54025045803104481704031620100d00b80944425246405028980011005e1552011560701c2c00d80b11660024045981800b0074401c25a0007003200d000703195070a00c00c500025009001d00341e18111880300b403e03156811706081141660000d0540182540150340c410303849500800c800107000b0355403d000980b599141403a900b003112030240c03e54481650b10800c056503003000903440c09260158003c00144528044110840b50803000c0a001c07903408085001080d84a40c0041000700c0c420315103800c002030040c0c50080000e0858001c0c4000ca82c001c1401071441 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 706462464 1250 706461214 706461227
    0xf02240907080c0d1112060702031201060c1221060b1207021615030b0303030a050405010c0507080d110702132004120f031107030b1501080f0a0c031e020a 68
    0x14000316000d0041400c000380065044e0601840007484c410400ca5540020b585180070f4030001aa02d07000e41d030b0380e89410740000752641c0c4201c2c0d00785544101d500004c1081440381d54081401981b1612a40d06e5581501040d01c2c80058040c2e47e2a0501c1c10052482d03007980b9600a00c00180320076a04613031911909901000147e100501c10011540726140220340c1c81c1c0b1241d607080807623032108210600703000088030850141101c1d1101c50740501c000070a000d00301d1004c1d44400d1045000e00000c2100307141d45141103031988070b00c080103403161500348610401c01402d0360040c902903400c01a03842c034280c019400f00c1e40444141120031242680c40d890022060611140105c8084580320640d290504100907a0025a1600e001030078040c03801c44c03900c01301400350364010744545a610898081d07564a290501d403084040b500700400c41e8003011510301d25400b4402090007510403000f10407003959130004240040034440c484904154940c501c0001c0d8845441c1c1040c0082074802001d0383d10f10224401500e030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 706463714 1250 706462464 706462469
    0x4080109050313090507050a12060306140604051b120a09020a030327050a030f0c0b040b1b030a080f191a1c02011e110303090a02120102030402030601060f02240907 72
    0x8460400c5c041003c56940035003160b0344150b10b4203041c0316118190104034001d0001d0341009140302d00d041503080da00340c03402407402d1003500c00700d406002965512801c9201000c1901b8a81205e10303040c04148451204410841d50003088928000b4220101c1d400241c8144003550040e40401c078034041c500220600c04200301206200e00d40700c40001460a070110300c0118240c84041c1400340c02a00d0b103820040034010b22801841014902500d03941c031151080101d510101c49040e001d241d4a151a00b807020100584074180c0e420380325004680d68480f140142c01da40200b0380c61803981c800712101e2814085100760714180488000c0814411241014401c940d030314140e000d00525400310f04900140e03840303001d074400314005503200161401e85c0c8109440b881d29601941c1c00d41c2c0000b00400844080000b841c0b107506000316400c440150700d0003038407800c038841514082e406800801c01800741a000e01080b840c001d909204a44c25603400a050b0f8550b5149040801c41d8081d050007404102003081282102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 706464964 1250 706463714 706463729
    0x100504061b081501050a0203270a050324130f0b1b120121022211070c030807080f070f020f10021b060f0412030909050c03040609060204080109050313 66
    0xa505084003201034003d400402a41003210029601c1425407092064501c003080303110803a0301207080e80c07010f40d600c5641600f80a0281140c05000910342c900010020041209043c1a4224541c0020002d0000d000141811201c042104035280020500c2400c84801401100302e09940e040c85c4245604841030400407102c1c462041c840d818400322030224403811929046840c2c0c4d1400c804540c000b051203c00c240103980700000191040c004d1a07804101d12208120031020804004600d14940c080d015002010700910305406040c00010b03040300081154074088c0703020170300b03000f1840780d404015840318404440c4011902124003c6040c015048018040101d07102c1100d0445e002c2c00035a03928211071036181c0c200e140d03060054161214822203500303440340b082456a5646032002d82c005806d589100320b0001b05c2c003060000d610f038940c3c441ca03805031001d41010f500c1c50312070380c940d200078180240003510119401c00c000a4141c4c1c0074400d040e01d90307200f04013451b100d01d9020310740e41100c0d646600120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 706466214 1250 706464964 706464977
    0x7180b310b010903110d02010201110d020d1401060c110604051e030c0105030c070201030b0d1b3807022206090e030306030a0813081914010b03031803100504061b 71
    0x804100c911917071901c0503140c00480c0002400100d01500b01c4c00715080c00a803001441c860001c1c115002441110b8414209000c000b01c1c00114034110a400d12805000400c030301f88150008000c0c00c0d04c00307030b80c010040c2898109030b241e10000c0c4111511414041901d2000800146c0d14101404040d8031170b1005d0030060b0440c940a0402c02c03840c420041d00a040641d00d89816000c6c1e952079644000554110310f40201c1c440140c05881100c1c6d00900910790720f140100240c00b03c82c02003541404500350540c04015615070a884040855009400100da0240340440d9116045c01010000d03c40030754074040100e840c40c44c0c21681401c031201603640d99155041041003181c0d42d240000c0b180c00745c55125800b169a45112000e04403070f28030980241465001e03d65001241c1d205d9094040e02050050070f680041101c943d20b05803ca52150000b140c25030400c0c008088040c5114503030001c3c000d0040c0507502103001d6684a8021075a0403036044890701d590b0b0001d0390701030a0282c101c080040050a015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 706467464 1250 706466214 706466219
    0x180c040c080114010c05010905030702091b1b0f12040612021e07140f210c1005130b0c04060e060c0705040207060612030206040b0907180b310b0109 65
    0x801d5070205000e00726201140102c43c030340c180d202c0d011120340180c001c4d0003000120b106181180c2c90ba800140140d106240f00320100303030704e04110700c4100d0520030340109152410000c0aa00511b45501070b042d070000f4094408800f01201092100141c00d0a01000b95030340e0f242050000f4204514160326072401600c1031015818000d40303086280d8203030780300200b45911050145031892001d281035403080c046000341409100e0340b00b0005100c1c2c443c0d00651903440c02c00000354002d441280152000b0102c80d03070102019241c2800c40f81c4c0146c2d0410809400e005c944070442d00c4001a404086d00c608140f080005820810254401801d0443c400110352581c42c10f0720000c061661031681d0701540d031207250300140100c03c004440d4403800040001c042c0e8424910501d040203516034000310780a0303824000160005104440c0810a1800d81d986000181500e010b07010304440241444a03d980c1c0120419011050900700d184400070000d00490606036140c06600c0300380280d40704501ca641c14480d80e10802d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 706468714 1250 706467464 706467467
    0x10e0c06040b220308030709140f0108220b010e1003020105030106081302040906020a030525270b0c1902010e091312050a03150f0314011103180c040c 66
    0x8460440e184510456215502460b281c01070214481d40c3c40d4090001080000400081602440c8204104e448444440b0380d10a003600700c2800754294264402800c6010203065801180380d04d403c41d6582c0e100b0450300c45070300484080060503050540c0d840031100700400441090b11081540140c544c0301ca41401861540040c00c2400b06001b00c40c14040000002800580a4603500e03000d1030f0000c2052100300c5071410158002c0d8424054840040e042800286008401c004200e100722041048220140038070407080300e0305a4401e111066003003034440000070404040c060680502600502c041e5904103004da601d160111816007c01c00811001481d00540e802000c80364079948103445200641e43c80d84100202d8050801d4000c02d01c500070340c030004003a0f07030003009000c0f2034106403410055216075014228801340144a01d003441e5900403800d000140000307407117084010805002080780c20181032002c80765042103480e10888000b199060112050404c0181300030f0741c00790307400c00c03044020000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 706469964 1250 706468714 706468717
    0x60b04030f15020d060f0e0f01050307090e01020c0f0106081e030a03050c0d050c0d0b1504060e0102030c07140a060509010f03230a0510051002030307030b0414070908010e0c06 77
    0x100900640824011000d0701e0b03045404950b10a00d04810402c902c076203070008660315400c94050824000300311400221030b00391b0031106034103a40c0300500a000c82d61810307083c0000b070302002c2c030740d14041d54003400038914044007040310b0b610a03807160380080789040c14a0942c0b450560501900c031150300041c8505012090007100712625005d1901d8042019030b5030781810a418031400e10f50501c074900e008100a00469172070041c0150440c0003d041c801c0041c0c080030400d80d140d0000c1082009002000100324183c0074402c182090101801a00e0402c10b04424141c1040034035071003900c08003880340042c101840c050019401500702070070716a091945550008004c0035020103000c080c90340d03c4030000000c0c0c400b5071601300d01c0d003003003840024103207002c1803800c0243c1019509520700d100d140c0c00101d89481c0c1803426002000d44d0790700440c150303644d068084024104614030650030503907641c1000f40c40c640080c640341c0720b600603461b0504110f140000303281c215140c3d0020b28080750030050360042d844c1d54030340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 706471214 1250 706469964 706469993
    0xb15070204050601110d0f120902030304180b1009030501050708010819051006260c0102060403270801050402090a0b0f040203181f0e0d0e040203091c12060b0403 71
    0x1030740068195140d400503905004c64400c0c0203c20710440301c2c10a55240d00a060b5408180155200650a91441e1745401074840007400250306030030601c810f12250a41090030400b0000e242c00100d41800200049411030380d03940c0d0080d00003150984148140202400b0b504d410a03554900000c541d894088016140c0880e81e490b10902145000100d00f480703000c0206071000c68040d0010001281c3e00c000c0b078600c47c102d0100120031404006079500c2c00d920041501c0804a0041e00944202d0b0380b541d0f42140c4000310104210700d00c1c0a41846012568012040303c405030843c0c1000040a0802d801003200d0103030020070b10180a410510b86003040d4035081403000011000780c5015840361560324828070403e030f265040b07100d40d10031400c111001000300600950400f5285100b0420042a14501900e409030300a0003400300701004070341400ea06180e4003d40c2d101e5440400d9410f07103001c6480c4070300c4199202e8403050000303420301c001200b120f0b8640716800c0144032605105140c1407455803104007611915 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 706472464 1250 706471214 706471219
    0x10e0c130302040b030c040218152d0f270d050c0f03010b0d03090e1b070f080705010606090906081c0807110f030d051602100b03031204060209040b150702 68
    0x40604d44003546040140401c451002841992661000051a40075410410324103120b00c500020b81c61410840c00220b504210422400301310090800207011034005445c12505ca0100303041000e08150b0203020085d029500582c11f03107555140814042c4040f0f036106c6441c180c441c6022030715010005100042417151a0710a45030342200b000d005001078014504124048c0e081240d200b45202011303800001041502c0d104001c100c2c0755190341e412940710007404040c0c3d00c03003030500f0005840410f903100055000c8a10420243d0b20b0300f4607c1c1d80d15400d440c100d6010401088101c00c041c84800f245000c2d0301e01400d5008011b00e2481e03010000d520314006103505550601c8010008a003000f4850025082c684d614130003100d551b680d402d86120395983c0801c0400400b2464540824001440380c00e019800408644c01042c0d42592401720400804001c0c0740c9552601c41003000140e1120500c501c20300c079902030940143c0321002a41800281c03980c6980c414410004c1188110424801c3e60940380c0b1550107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 706473714 1250 706472464 706472471
    0xf01031802060417120a0c0b101805040c1403070504110f03191b0507021002011b21060b04090906110309030c0c060301050d170702060a08010e0c13030204 68
    0x4050058110144032006500302400082c00320380040c50344000b100140b0004200c43c803401c140c030b809501c075001d207980190000c0c1142e500240890709001640c0d400500d00302581c5100c41e943c851520002c02c2c440141c44509456904200500c00c2e1642e21000502c0b410001401c640d58440002e03840e8070a0b80100b0b0321842c0e4810403085601a1441a40c000c2d00002c445250742e0b0500c10380103100215400c0091040c1418100802240034034005c480c4208011a201c4604001c0c1d01e82c200040315540c1c010b21400c565071076541801403201c1c1402013087d00c42e00e4544114030f10340458610300340200c20014030710450a1030002c10004400500f120211801306000041c000014a0004050124600e1800b01c096003c003d020702e40c8004002005400d00c40d070110390104100da414400140402d114017540305869480e05408186007420840054000350402c1d49010800da000800301e4000408900000b00280d006002040c945d07440550880141441c0714204000d580c40519406805d0000130301440c2c0303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 706474820 1106 706473714 706473731
    0x110a0b27060403240c05220608040212070509070e09070e090a200309010203090f0a080f09010c240c1b0f0201180303200c0f0103 57
    0x90140038242450310f1602d40c15214182e4412041d903135025118548070180c45440303421460640b5480e2143c40b261440e007400c0e18030400075011007803901003a10a110b047d400030f4030180d00035811917801c0505a844a034090600c0115801983c201c8050030031b125000350402101c0078036540998080600d075039212800c541c8061035044054001e41014045030714841c0c41c3c0c200d840403620081d40b001d4010348038041d112042d031049500f41c1d1a40d6012060182c0362405008024103881250010920b103501900ea48a01d44603070740b03081072a84000075060708140d0040e8003a0001507007040080718a4400703007600100803402c000780760280d01c0c9030004c24140303140200b5a5041c01904414800f01055255030b0700030310a44c0146d0164184900c7c08240150688517820703210245210b941c0c0c030301024113100100003020101c040e4010454012006404d03149d2a170011403d00480300340307004201c0d0385 = true := by decide +kernel

theorem cover : BRFrame.Cov 706294964 706474820 := by
  have h0 := BRFrame.cov_init 706294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 706294964 ≤ n) (h2 : n < 706474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
