-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0187
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:20:02.132671+00:00
-- url     : https://prove2.me/submissions/8a694b0a-eead-47ea-9a2d-1ef626453066

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 33453242 ≤ n < 33633098 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 33454492 1250 33453242 33453257
    0x61d070909060f090804031b05121c02011104050f040e060c0a030c08010515180301110405010210050903030105060319062d0e130f050303010f0e0f070203040302010309050c0907 78
    0x380b09452260180c1403061420600186156484d1000326025a0102a10100860740d84950381154089000020a0064a2005c601302c042c0e2000e42c49500c081c8944200e4180c400d04000110700c18441c4100306207401183e642094204801e0102d86112400684e800c17035a40c0c80e080108100411240e4850940b0005450344e0b442489001401e071005c040c9490305000e440d1f0010b01c425070743d91306c4035854401c09211403511011200c1040d004044500149505946043c50500c40ca918000c010010380380c0c21703001c507804a0300c103140c0705040f550110b6815200703420131301c010b015619001c4021504600a251000140445c0b030290504841c1345a02150300d2030321070700d096800751070700e0f07403840903a085c0202054280c80e20f006014001800e00901c40c2c115410b4038402c40c0200000c050909010603040001c807901c0b580c4580000340070502d140148214814410700040304050f100328080c2c0f251240358055030a05240d5030055000d4024400101c03060f00604080403855200c0a1100d8880c59059903400c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 33455742 1250 33454492 33454511
    0x4110301050a120201020a060b010201140403020610051e0d0f06020f0405040f090b0105012109140c0303040803040603091104020c0d12020901020604080a0207080304171b0d061d0709 80
    0x50302c05420340c00070250140701008070f00036030307008074000746910340101000c102c4801140041340100000d0a5103c1054000d000340001e02d0b5000804910502c3c0c84005607a00f280c50310b0030024090701c104c40f0300c0d82103101c2c521040038034281070b201c01c0c104510450011114220ba983c07000f05a810010181c040640c0115041006141c14018481810804181040003d000c1d40714003c44030300500400341400f1028040c00d1841d84c070f4031501c22009a1071041081011072914100074218844c00d5802c03404d102c0c442c613100b40d518002c4221000c844480e0b004515003031900000b41c0c007802d0244004d0743c03000404441c1c40000d0304d4600013801c21081d4a00540b01c0c240d1400d4028045c210020f4140d8041032041c00207180598000881c282c0007908104c0040d02c620401004900e820b0098200400d40e02000c1400901c958210050710f48110220040e59207a035801110100d0342555070f99a80c0d8000c07c03910342d00000c502c41e03520a610400000506401034a000c04140e440d0208982c09440015501d030001d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 33456992 1250 33455742 33455749
    0x813080307110114030a0b061b0303160503090615060405150702040f0501051e03010908040f0602061605030f06030a080301150e0d0f080a1b0c150206010501050f0c0c0411030105 78
    0x110340b8a090a01081501000300b983c0070501000740040c124030b6440030240e91580c1c4240030382d0320742c04080f100da0350342694900d45640c42c1d03001a40c0b01d00900074074030701c200b01c0c16001d802520310803200d5000424855450f401e00d1241c1e07005180e6140d0700b2650402000c18191110b03030340d080440310003a041a90722403551044c0300446484801660075076141c200140071a680e08910750104003132140d80174040d100902d00090040c004483c004180501c0010300050223010b00b803100c01141d07150340950b01c40e6520000e4160a1441e110600300c0090400c10000c0e840e100680b07480d0750040006801c4904074001951282040d42c020381000f280c0d4081200c4140309690320400315100c076001a14400c20302c000c2c0d1758400010440c017010050170782c1c001081d00a5058420110307500c0210036540700c05085540c905025803045070a020b0b104107440c0400c04c4074031003400010300d603040b030788183e448515004551074091802e0b0400079600c1706a016014080381d007584c0d83d0261403400851810003950b41c0d4503080c00c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 33458242 1250 33456992 33457013
    0x30f060c0e030c100f090513090b010e0f01030f0515040503031b0f03130f080403030c0605060105031018090b150a0e0f0a0207060216030215091906090813080307 71
    0x2098803d030320100c195025030300d4503001c90310b0240c09030921a10720075007071300d0a849019503508400e81000d01582948e40c5100340c0d07007090b0b00c180e01500320b01c90181d80300d05029911800c00c4480ca03c0d52000b101c010400186000c40002056000300141d400d1420744c09814940c5510645068401d940084107108070100da4605107075100c050700c030082d80b615401040b020b015010052a4125a00c8503542c40018058042c0041c13030040d5001d90040c2c0c0e00c94481c030b03010702650800001030741d0325450710000404a5005a04490003010412100c00d0f016203005a08001c00250328040003400361035100040002d060070261b24021804c440712120b04440b4041400f00c2214154405040d0443c61014003028850306548581c0207138580001517580c02407401c0c01001380c0305000c034014072050b5640801050503400b203840ba111501d012140741540d03c420704002d5a9482404070401e040304881d040a0001362250310031841c0c1071090941274201036071100b0039059920342e948504c18a4000041000401c40b10200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 33459492 1250 33458242 33458267
    0x160c06030c0e0102150604020f0c01020406031a0d231005040209061005040608100f0305010c0305090106080709021b07060203030a050a020a0804020402090d020a14270718030f060c 79
    0x1006400340790b0010000303688100c0011040c00017482c1d4004a00c0c40d40741c94040f200c10f81366542c1c01d1595080e44c81c2000c1d000f0740c002e11071080000d00c1c04103105280070186c0c10160300740100074880014120107498128011805444401c11217200702200c0e030051000b44600207020822010015107860280144a10708070014010303445081113104001c0a944c110302620196519468102000d80e42c2030584100f281c102e03004401c1140c2100000020824150803c165040d07084d03030140003e80383c80300d645003641d03054012a2140c1d0001c0906102040c1f055015180ba11402e40d04940ca40c9205a00e0714203041e9203800c4040160000401c10040c803040c2d0203001c0d00080d810000310300c4c10301ba02e41c0050414130040c4c4024412500012540345030341d111603503a6282600241a8120740d0364803462920460101d0b103600340511445035401c07100c60788440108641e8004001d0341e07141650352050031590040b842d01800c00c0071030350b400080b0201d60020004501d50344100740021342003242d1000a840c1d0346d044103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 33460742 1250 33459492 33459497
    0x603030712141309020d0b04091101140702040203070906110715081905071e050301080601050d050708060405030a271503060b0c0a1106031e0a02160c06030c 69
    0x104400100d4040400600d41c01c9854059044040a0a510014401c1c81c1c070000700b41c0301815011900744060b50080c1151101c0c61410021000010b080c00242c079030003100a407130030161224510580d406045518143c4030080801e502c2c00072968000f4049070401d94004000031b00c1800203108064011103a461019002001440014500692010008800304815080120b60f80108427011840c0d2001c007981700340710350180820b240c003641c0144201d01544801c0b2401503028070b40c1c10741c10302510889050703404220143c0708580c03d00c000d110051260300c408465601ca0f680f00064040c6050184902452040300a076690f16081c007401080c480300f140c07421480c0c40b402f4500c1100c4908a00c5030404131443d042070100c10510300d160070f034010f0030641d000d040755540002d110018040d011070324000a51042c0341d0301d4103002c1d11742d041c800c40c4e0100300d8000084041c440da450441504144180e9031012000201500d042001c880c1c1818040d00c660088a21051500c0f00313021494040c06100c505800700e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 33461992 1250 33460742 33460747
    0xa0f090e041e050d03050f06100203120606070503040308041404050f0402010c1b1e06030b06070305180604061106010602031c0b04110a080901060807140405070905090907050108060303 81
    0x8038a005220015000902102200e00781c02c0030380e80522031002e0580d811005540101d4136125000d80545021282d04040d1071100c800501d0794500b1604e0700c2c50b00d040c1c41d4021414207100500c2140f580d400640380d00d40c408401c0c0720344070001d01c0c200024806544902034158449241240d140300f81788200300a40d10441c104003c00c819100303640744003540180c0904e07182d4211070141c00e0540c2d00203600c0700c105250702d225403004145000300802a06d0207181c0c54502c2211150f031000103e08441810f01c07204c2d44000c082000c85d0100e803041003e0300309041228002407040061034000794050b800f5620a002080b5401c03500c542425041c0039150041c015800514a02015500e030b0000c8002d8500da00303a50f4507a241c0315031200d0344950380b19045101c01045c140781c0d41c440a002c00f400c054030440304d2164941c200345005c078400402040440880f4460a0805049211303c0104006044028026020031040601c0001c1c15075445809038010484003020780080303400c00d000101b12000c01000e9502941c001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 33463242 1250 33461992 33461999
    0x4050307030510110702130b0406030602030c1b010b0a060503040302030f0a0f0215040201080604020f090607050303240a0302040504060e16081203010e010b070201170405010227090a02131206020a0f09 88
    0x1041365816487e0b0800b140003d0001d910b000182c01002e25030005001342e4800320410203070104000007440a150500d100300440100d0745c1500d800c1c2c4104901c400d23000000701004001c00341c080d001441c1c0140c46030060b03a040031803804401819030400d0804500162140800d00d061075018000811045100f04006019240c00e400103840300001a1655001c1c3d580021703030b0810118080241d52100000a01c0c003692070032181029507170380d0000d075541144030b0110340700051800b06c0039050001c0d06e1409450042c10030314540802005000003041030b10210b0300c3d45107401010300c041c80544030141251001c0e51703a003400e0580c51840d242d03089082c044800020401440080c0038201382d1411110400107459a83d076492004903003060b403980038500605100b0090004100d41900a4041c1c140c0e911000200c0320b0344004201900074100000c1900f154041c1d003c558080125002403000c0070f0175200c0e030300c039041c0d2b00c220368424088a4242038030780742d9011800281c034681c821500d03c120050742c50301107461303802e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 33464492 1250 33463242 33463249
    0x140d051b07030f11070905010e1e011802090109030204090f0b100806011412031201090c08010501050712020c031516050304080d050402011803050307030905101b02030304050307030510110702 84
    0xd0300800403003800044060031130040000c1011501600181700d091040d56580c80a04a1003482038542548410b040f000d01e5803403010701d0054904881d201c8608011584141401e03100961040902d90b0421140300800300150f1114004c0450880c800d000c410392407110ae00300000180405094503007654070321740040101d99000100e031415203946941803112104140c1c00030380b10301c03071a820507209800049001c41c1d081342085040c90484001d04d400b4800c00036100c00842d041402405541d0103e0010700c51720010410245603a106100540119284030610500103413070103c2050060341e52804400800003416800b000b2505800a9414410b041d4181340c6d5425880b80180203110781c402c2d07600c00000e4156032042c07040c0f503e0102c10101100c078954480c148a51250300040040d00481c1c0702c0400004d0b5407c0080310509807800f1696802642601e160855225045008003660306102c1800301040942d41448040001d5200d00020100300c2c601a4008013600c8040b40f80b003c0c07100051010720003586 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 33465742 1250 33464492 33464507
    0x2120d02060a020a36180b010203040302060301030605060301090b0901090312060501020703021014031005100e09061e09090102090907090305030f0c010f060303050307020705090103050a0b0601140d051b0703 91
    0xc003a4200b404912980010756880d41198641ca00c2030345460070021300c90441440541d1500041c6c5000d104020808006a9981c411488000c3d0803420070401000030035120790050f41c02100040000c6100f01403500c6e2000001401e45011020303941d01e00200e400c05400805221030311400d0711003440081e10380b000107912942d041c800a0b00030740e20043e0b200309203880b5501608106611036080703a144c0c1400c44540ca40c0802d14001e45000301c12440b803a11500340035070008030a91000402540072541c480c400c2c0880c2000744184d6140304203d401043c0020381e00c0303200041c40782816400042e2030300400301c100440881d002c0c00300c0040c0554900705002154004c030840316454441000d555840c1082d60340a801401c00708078441c00c10340b9014000c0300b00765111000f90700400c080c2e03003251500341d02c0e281003000c4203c082c80300400c2d990002c40d2000020701306a040d0fa912480504240c41340d8802c00300c0c404040d500103809095019030318400c004040c219003110320200050203070386604003401690042c3c64034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 33466992 1250 33465742 33465767
    0x50405013914070f030201090e100302040c03060803040e0402030d050a0e0405060a050612010630090305071b030510020a0e0d0c09090b190c0f0302030606040302120d02060a020a 78
    0xa1401482020b22940081ca50749001007402103541d1143da40e8080da00d40b40700b0f40404c0b800078440d810f001074091080030100c1d004031440702068003440d14660800000304603000031201416200c440000d04410f00780301501c01465121040c080910b0700c2d104040c10250185400c8007400700c107000440c9050790201a020710711f41c0c02d46001406484a80009403030318510f90100b58040310000c0e031600284c0a110b103050480f900f13900d551001e000111500842c848400e0760018100c049480750a11804a0303030420b49400380030f8204103251060030313140d60050f07400c03281ca40b0f80100916441081040b100700151030300d00300440021810640003240c000d01560190070b8071440f81901d0b542e010203101c1002e142200801c01e80300d00700454000c0385031008004030704807010990000143c1040444460381c2c0159000100e581c0c1c0c4003008030110003c20340003504068142034014201b480040300603100c903600c03800c0102c40ba40c003e14138001030f807100900d001c0c8001c1040d040140184003c110300b50708103d0000c5407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 33468242 1250 33466992 33467087
    0x1002041208160605010b1306020f1515040c02071401030515090a0b0909070509010b0301050108160908120403050613020609040b0105160c051002030414010806030a050d05040501 78
    0xb101d024154810481d6103103070b00a41058a072030000203590720910010101c030303420501c9200060350340311000d07600e0b23520303000f4011880d400011300276074014000c10740fa55105000d41e0b0307442200400341011404860420031036801592048105010031800c0700c4080d041c4000034a0148100e00d41507580d0344580e4595174034640100d1840c0e02045401c1c03001e4004600e0000007404100d00f52921403482d96079800280702780380c061700c911000401d203401c1c544203c0b4143c44040c0c488050540b50061180d2501c51340c54104410070a40c0040465811402d00c54030700c080800a1101d626141182480e6052000c0946564581c3d44003084101c01620340f0815242c0c076400c202c40000707140c035080006880c41c0c821108034006101d402d101c104100030703106580350165942070710364400c0400d181409903524803840c01f6148070104d01c1e500104140d07120761a00d03940244042c0030b0b42c02140c465543c1514260342c515040000c10000b040500a65a0012213100461907007101e00d40203426141041140a1003800901c0d41c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 33469492 1250 33468242 33468247
    0x1502071703070209040606090e010b18040515040f120201090c0b030603150109090506010501020f0303060d02010509060d0501080d050703140901110a050708060a091208060301060f06111002041208 86
    0x6020041c000c1c1c4030469005000e50300f86240070b02d0a0030080010b405030490386440d003044010603031014440d100d03007440040d01d07c9101d8454100201c0c17154400030021206445005c81407c000800c051120b40100e105000c243c503c2882441d2100081c84481e0f40d010444e850007a1103404980001080f20841d5409c592235992a19400d01107414000c5281ea060200b100d5403000003606842c55120010003070180d000d07140541d0700c1d58012a211071105070303850070640c0240041491840c190041c942c40030f02c141040392502292401250b0b16030031400000703100700e03034403401006890401d12a0343c511181ca80b41251424a4030f0764050040789280c00340305060100130942c40ca85900a031030b441c4c895244001169001511440c01c00c0c0e840e405401115114001c42c404a109050035004a208065103c440a9070b074a104000c101d0b14a40300900c600e038159240c0307200280c00140270b803005015011b2603a8034860480d01d4440345190400d0100313401c003010310401c4100b0488825414400351182e0180f81c0c9a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 33470742 1250 33469492 33469529
    0x90b0603061002030d021b010b04020a12050606040312080601030c0f050f032e030606050402071112100606020d08091b010507060905060c03040218061c02040603060c05040e01150207 80
    0xb131450181c2c00000c000148002081c0f443c00944000d00d0144003064402404240f03000000c4c0000c3c1e004002c50400404c00c01c40780980302124030341103240c0c0600050104c0b41015500d4a074030216903c00c0202071b000c0b5120070300780001e6584c14001c0c41c1241d01c1ca402c203840100c0612000810314401d082080c1c0c0c00c444040041001246100540764401c1e8440c0c04880040c0c000312100300c261a8107110862b213407481c0102c0000c0d0f40c1405c2c0262103146410050700c140c3e4181c82014007492401c1e003d48900b80780540c44c1070703039080301442c80751102404080d401441441e102d400054200f0030050881d1481e42e0050b040340a02c203490000e80a007030030080c68101d449a819151010191410300300040c4140540e80401c00000030790000355200d01d008035825003101c0c1e02c03102200302115058600c00e4000d015410f105c400078940d2400c00019500c041c000080280c0d69884c3c410031900c07480401e0000500c0041c08001182070000c07030a0240601c51548621280e40400c0a50f0b903e5146c030500045e08828034056 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 33471992 1250 33470742 33470747
    0x610061d010905030a030f090f06021504020d021206010501090605090a1205030c0303040b070306050f01020c061303050307050d080f0919020112050f010609140303030103060e030702100513090b06030610 89
    0x400041c400501101c103002c45c0d62038042c01c0005851703007807000120700c60310010b807c0301501502070449a06402038103069004600e00000d0b480020300a83e0012011049140140c550504125124061001801465040000040c40c0744465800842000800c3c807060700d07659505100d17001105d08002c2c40e415982c1c50f901d4203a0450155404622140c0400300400c0140b1546003c02449502c040d90100b00700d80d160400c2001e106800076409005a102d03092135003031406c0c074034002c1c501c200b00384403002c042580d07030b0303450740c0c07540d480a20115029048131451f4004107800800310ba0b0403401501e02c15001d4500120541da403050080240b010703580f850300a4074113690242e0510719115589000030f0050385001441c3c065001030078414000001c10100d00090300814022110003111001400385103142d28580f00c03000582003000c10010300e070004100780c0f40141d0302c0d180d1041080000c0d8440c9a01c40f41c0207400d6030141052540117200c070500b0a5010311040c1d580c00204e960001044842c2c445c2a50303c1e6208 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 33473242 1250 33471992 33472007
    0xf090513051c020105180604060b030c030f1005070c0506150d12020606120d020c0f1207060c1b03031e020f0f0c03010f110f070305070609080301080610061d01 70
    0x140040c040e82040710410b003000d04507104102c00b55002400a0b4603101d8500c4400d03502107014071040e400c80d40c0850300040780b41d0403401e13030048001c04455510814800080c1030500b00b4480501581c4070314800b1071400c1b03560049030b03030100090034204a0a02c450f2100e030f8603210010201821049103500d40007440e0b03100340c0300d0051310b0780005078003886040d4004080e55480080c3d80030351007902000c00c1304401e001c001400301c12100d056809040303108111024894000001100c481e44092419200e42c11440c081110200918050b558010000020304050318440f001d5003559040c0c0604070390900c08283c001124000b44080c91100b01c0900101140072410034a024001030110b01500c0030040844000240155150004030000c0148210641c10074044941d1001141e01c071400c00c1c04044682c40305280a042007a000341040c0e4a4600b82c0e58400044070035406040b10b11420120051101d020100903146d4006c08803800c04500a0420001030611440600e0200c04038016004000c003030b9101e03412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 33474492 1250 33473242 33473281
    0x40302090a060b0d0f0e010504050c040b01020f01050c120705041508060d0f0b06031203040b0105010c08210114010509012001020c1902031501031e080906030403030b0103050604060f0905 82
    0x9a5580f9207804004c8200617140e11244140300500703044101100e4601845407a0040c1d40c000000c0000003145418440940312540c40f10f415030040c0c010040b01e9513400c0c0a418403d0820510041e928081450388004001c805090107007004410b000500944018111880e080020f6003011400c59032000d00092880560403002052405031500c40020001d808403c2d40c0a01d000700e01703860031500303500100c0155002c00c81c0e02400300c119a400402055018042807142a030046e15114604900b19200310f880c1c0000024401c031020f84480104400110f01100c01c994440034604280751214020000346044542480201510f081c0605910445801d50481c0c0020240c501907801c40000c0c1101c01902d022404002d80c005c0c0100120640c4492011851a050347e41c070140d00e0000e1b01c00481c16100381556902c08803880d803010800c00c58240c0c1c80101452265219540204590880b0300004050740d002400c00c1e4043c0e414200240281d5000d8840d0400340c81d030145c00050a5035800c010100b00201c0003030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 33475742 1250 33474492 33474509
    0x20a111302070507260303040b040204090b0405150a0207030e0f12010903030b150901021207030e09010b0309011d030a050906040306090b01030b06060403020d03120e03040803120f0c040302090a06 86
    0x36680b0400001180c400e04581210200c00c400e545880b424044508840300400360b103810030000280010040d001c8503800500180001940031825620700100d980159010f641550080c490038000d01c00c04041c80d42d1249002c030007035040c115a81e41c040d210a0381400d00324071980040c1c0d07403000305868000403040915400d40082c80300c00c3c5036040240c000c143e100302c03041c082c0d060f56100c61030460741e540071100003032010307070051030071440e912540405a0030618040b02088101c1c00009042d03555101404c0c007828074900a0fa9070380c2001c00b1154219054042140c280c65500c0d419001e0b03007100882a200790100b141407070307640d80001c000014454800c5030001000b10745003042040601c0300f1000018180c80c0300380c84858141d11000100403050044d48070082d03100303207070380c980c000001d104110200c6018034005000c20321303828045129003142c005420a000da58404260b1034484e0220f883c115800101600c14800c080c180100e100c1a01c0c851070001070b019141c03102c04940250303500da001c4d0b4011301070074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 33476992 1250 33475742 33475747
    0x2d0e0a0c090209090603120f0a050702060706021909030309210506010b1902010b060901030b0d020406060f020c01030603050c09070215090a03080f0f0103020f040e03070606050301110406020a111302 87
    0x50745008000d411100300c4601a804000000320b00b0300380052054034803242403a005d403c12031480c0d000c80303072540a80308500410606221500040e15008e0103426054802c000260722031a24007224604246030441070001c100f40500c0400202c2d400445402c1075038075022503900b84140061441c442609400030003042441208000176158084201a003110f180d81850400b200d03022800480c240e1754070b83d0380b09500040c208515102903000c1d0f4031218844501405100e04a2103d4002900711000c942c402408514884600304c04194113006c00410060309090400286042d51603240e0707284140c100d5a07001d400c030000072855081c000c014503480c021224003511001e02c7e00e0200e4903160244034030101c01043c80000441c0a40a440132454810240490700380c1c016807840e002c20090401544070315402641e22000b0740b0081c00300340f0040240e18001c040106010b8580002e043c2100c51465203040c21900c240402d1108541c0401c40c08000d507000028010700c06031200001d8004c0d00b181d41c9440c00035100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 33478242 1250 33476992 33476999
    0x19030c0c05150f010503030403050d0305070908011802040f14011701200c280f020a05031614030d02030d05040302190b160503070203120a02040e04152d0e0a0c 70
    0x40e40080c3c4034100b80d40e0b500780e5503662401490756a01131404000c28940061034034885c0c0074031907030041d80d2003107280c6440e4501954a031611030868981d0fa00761035040c8117621101046d8140345c061048103c402c000104602060072040042e0714406008040311181009802c2039501c0007500704144c110909844030800c0f100b182c501510320707407212074810550b004000240c4c901150103080c0f8241c044040c0440e460f42c030701c16174a60f000155901c200b01c2e400300b0420004103141c0c03402c00005403002c070502c800c40103140c00c0551201000e0071700c400f054405d40c4000031a18403194040191341103408080c10225030b6440c2d910741a81400c0e046090b0540d5540d600d4100d0050020403450030380102403d42d04030101c072040d08400c80310f41c8011a0135202681c010003192519846161016a000d40c60703203c0181000e0300c0d0400e900b50341f0010f0f035081d190b03003042c4001c070b4503c6070052103a00908280d0b405851610070300c011802081c000d4144002010645d50007450a41110a02c03010b24030583c00414480081d4a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 33479492 1250 33478242 33478273
    0x140105011211010f090b0309010e0313090f0b0114030a0b06161a040209010b07080c07062318040c02010e060f0114010c0b0f0714040f0306050a0219030c0c05 69
    0x3040c1980c070400e800d2100740b05035001c0c10500c0c4058141c1d1382c07140403a13814100ba074940ba42c0007624020a42d07607107824004c01100103101400e00b02c00721840c010304461804404009540018141d00c040600d042c103440550b070380290000d0004550f042100da10380e03584514420081140550340c98102c0030020304001242010341454603158410103031444c03940d0380300f03a0645054a04440c029045a02c15005000505420f809058014400d800c61843c0c00b600610203800c0444640c0084003003000542d1042c003065a9102204106c9002c00c141c900b8550886141c1e241030081c1407034103009958401d03d80c2e000130701c00e4205144140c22002190070501b0002c914a031400024426800b03010100c00044404e0340c031500303103a20310a4024041c0c1419445060003041c0400f80500298184400b14000c10281c0045a020f4001489443d0b9402c8029146044c101c00341c2e0401003070265810701c108900902c2e01c295003e0b82048035558034000416491310342c400d40341092a10b4000c4c10506c00c0300018100d500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 33480742 1250 33479492 33479519
    0x80301030303141003020f06071a10150e0f06221701060b031f180204080d0c050a0b0603250f0503011503030807020709020c0607090f0b0706020714010501 68
    0xe2003a942000040f10030030b03950b82045825601c021810304802010805460200d25002c0c1c5014000c00031440c5c2401a0755400ca14410210b001c40e0302d02d1420100940c404059401030000e00490b10700c64000700c500f0200078003001f00404003d214540071840c010294035440b040d2480000804405a54500761030307114414484548100440c15840c402c410010040c1070081008488650010070305540b50201a103640c681001c0012001c120104000aa0455403030030040b030081e00c40b040103a4450503e411641840c3c00c108480b01400030242c2d440002030030000700d4030210741e0030030170710300d0680c8442e00042e04046ea601c0c21800c0c03025045603030314003001c3e02082e08011140941c0c203c042103036445050600340c03603d01002d0580288000000c04c0440c1c000c41c9801e0384003906d032064408294407441c15804130b81007100311304a960f100c60108030304587c0108041000e013040e1003038203513128945940122544a500d170003c0c0019004142d1a04208030320070080515242040207010239030311141e41c00c1022 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 33481992 1250 33480742 33480749
    0x9060608010b04111303020d0f08030705030907050102010605330f0a030b15040e15030d0e0103050609060901151b030c0215090303030403050a0507050d030c020706021f090201090b0304080301 84
    0x11444d000d00c030000304180718102d6a220b0022250700344d895103590208090300e10302c00020b0b0303060b00c08200c2900000781d034400298460601511916100c0c00c0c420300c40c924209003078220f07a041d685000c0d070920141c0d58034591904402c1c0604110682000d40c00b81c02d055400c0000c00c0300254400101e03000d61281c9420000e00341c0e0031340a0b5410041407012804004501e041d01c070041406000801040c8507100201d0071482e802400c41e1250a0680c0c480c0010138900300e40d0050f8100014509a80300980751780c50300441c0c0e00800210ba961640b420701030002801690188280462a60305484081d07180d8040d85c4100e6501519000003003400109040c05003941d00b402e003040780b140f64064140c2e0f1819111030140c40f01400050015030460ba11564207541e29400b01c20b858050000500074a00011020400750461006a5a01160195041d0700c0645490580e40002d402d40d00982c02803444214001c240100f0400c1401c000315400700f450005030703030925031034001c0c2d42170a80000410061081a000440c1207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 33483242 1250 33481992 33481999
    0x8060102100b0a031403040f06080412030506011e020a0506010b030a11041526090109060c0f020a1205040308070803010810060501022509020c06040203060601030c0206130609060608010b 82
    0x10700c501e00040d0740c100c03000048550ba109224041c01d1001c10b4140030803041003a030a004913454070381c40700302c4a4410b864544c030000005820303104000030032003580c5482000844a0070203100c1070604800103055031401840380011f0309110700c28007600b18420402e0300989900101030304c101d03585801503040b00c1e45c0100d612040103404d059510700015185e03002c4030300715051014840e00c802e506c09001c071000d202840c0343e0300c01885031030000000208104032241c0100c00c0c840000a21020624000c42920600c2ea540342c144407410102800003500424002348080d880105250f80100d95801a100c500a030f40025004110102c0e0309400c0042d40710086050b42d030410b08455000d4121524103003642c407540030b202d0041e0855010b4010704102c00d03d040d81141c0f007511440038030b180c60b800580c00320303080400030b075a2541c056000d00c42542010700030950026020310b02408107041d0808040d5860314003034030320f0480c00d956041c11700600050750b02030000554032400c24000d06940f03142003400b0342140d0315680d10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 33484492 1250 33483242 33483253
    0x30d110c0f060912030a060f181415090402060f030c03040b0f01030210050328020913050f161e08041101031a0103020903010609021201031502070308010b030604020d0c08060102 78
    0xc1d81c1400107070380c5101e000090014529035981080c1c00c0850b40003d0580113417680c80312400308000354682d84480140075240b4a84455544000f019029103a001c500541407009a0050281c980c268900c1c29007150003c2d02c11100540b00c5c0d2001c00c3e003038490104000302d40f19000c800e20103201c1c036002c002d40c0142e01400300c03400103407248201688246821320000b54010130315071022807118055005107a10101456445004510b030307150000c4407101c1603a40400c01d582c0010719002c0c0d450b02201510380c0603103030a801c0140b45000443c90050f1480a00b21421440b082040c1d111780620403640c14600c0600701a041e042807090000c05400b4040c252411220ba55801e9a90b60070b951092080f06402c030269800c080a540750040150000d41c4403803641034042d501c1c0d41010601c04000e00080100b048000c10802c5c2c00e42c903600f06651400710503c01111420300401080000c203a1000380c0a054031070702c044180c3d40e0b0725141d000030000d00c01d080010340e1890408492303c9890360008001803080d1403e800390350 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 33485742 1250 33484492 33484513
    0x10e010503100507020606010c230d0f05070f031116080102040e0108010203060108060910080a0804050301050603070806040303020d0b0907110d0f0c14010908030108010b0307120b060111030d110c 86
    0x40954400316400401031b4450000600c1c03941c4114001c0c4140f84c020703000384c207000101e06802849103400144440c4c0d10b6005003140c1c4003881e4001c420308500d805919055081c580956181083c14440c4c00340901001301c20180c2040441741840b03410583c0300700c101c900000315684c680c498041c2d0403c3c0305001c03035078042e0400040c00d00d0040c004c8030700c0381d84144d455102556801d004c214042002420030640590209408685d24008020001c480c5000e28255501d5030314040c101340c25504024200e81c081d8200681c1080102c0000030a150003503850705001d0703240c03856030b00710400a0040c0c40305958000607031414810340396044462058003002210075101000e40f000700588071000c1034140c610000e0341900c2410013240b03141d10340c0104004048000b14494075035440745050b64100b0780000c89140d43d6109000d046203410400300700241140b20150b0200300c42c64450184c400f1009000a05102c0c200700c4164180c8001e2040703c0310f801443c40b00704030705047e1a44000d100d401c92100b002841c0700c0e02411741c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 33486992 1250 33485742 33485773
    0x20d02120a060801050c16060c1b03050304020f0f01020601090e030d0f09060c03020f25022106010905040803060f040603060e0c01030608030403020a0510030f05040803061008010f090207030e030105010e010503 92
    0x155040703000c007254180410101c0e50340000400f0b035a07950008004504141250222030040c117250340b00d0099331400e8490925004002800380080c800500c10b00c0c455800c1c3e502642c020070101c0c1103c50f10100010750030200420181144941c103806030320b00c0c0c0740c607a0320120219a903001c81c44140c0180d0040001d01b00340e02d001c0d8124410b04e00d0300c510080c000d2000603c00481c0a0488091100900240009280c580c3c08503c2440c076600b0b4502c00000c4120030340c0c1c0c54041c104010307401000e40c4001030000c1d0901d41c8800d8402e100181c240781c0256503190350315886443d1908100011540003c04201e81041c030000f05032908040242c40740002d0510000040090b8000280d4041da0340051039080041d01d88000c100c800040f8440071001c4c1622810403032021241880341c203228601440c0c0b12942e82c1750003001c11000c001c89070a00340034400e131030006201d81c0783d2401040c020744505003401031707480300311b4101500e080c0c80c0b00c11100d42c0741d030a00d40046040c141c00800c05040b544190300f2070700c0c0c180d20280351 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 33488242 1250 33486992 33486997
    0xb01030b28110f03040803071403040f020d021c0302010c09060e031506010c08120f0604050708060909030c01020f0d0e030c03160c0302040c020105070e0d02010c06020d02120a060801050c 82
    0x41111041601c0301c1000d12082d40554041c814111020303103092a000e0020241e40c10071a0143c40d03c560200030400156044070100c92030403201c0044e107141d072410799562101c0b144007410180c060a0100c00304811500c07034514840d184010001009010f50312843c00078040c1000b00110800280c05620004915001c2c80740c3d05504240180540302c90580c1e074600e4415803100a0409040042d12a0084045155400142070010002d20001e1740c40c5400c001001c2006000380505008901c0c000800c111710354804101030300080120380b07010b007036100c0151003803940c020070b20048030b95403000400e01e103958845401042942c0e481c0c001030000602000d4075039102e0244000060907030304104039804004d4541d10b10110301c0f501c586030390403400d500ca0300030404403002c40d001e00d40136039500d10901c000755410248949000b6812030701c0d40459a441d5000a060b03820001005242d03a0b004501800401c08540503110745c41d4112208066074503054071880c000d00f1440c0701c1d07003580d540b800002c80c4141d80c00104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 33489492 1250 33488242 33488281
    0x301090507051c23011b0806040b0d050d080702010e070e060f0301020c0d11120c0307150b010f1805040c09060f0201060b04060e030c0604060e04050604020306150d06080a0b01030b 79
    0x104c071002c1c0c04441003400c450b420400807008003550313614243c009442880301200030407446a80c44040c5450702400307100c00c45000c01440d91150b0546944100041c0e00040d504400350424a42203005450b205000c1c0e02424110784a01581d029079407021803180e2809001620401c0116452000c0c240110241803c0740b0580c000200309401003d0f001c0c031190f0051018810703060006044820348405860074920744e4220700b42d580010303000042c088044c00180588135248401429040084403442c00003e402028860594014480c82090868000c0a00c1d81c0100041802a00a000440560314003c03c0a01d080c06860f0100300500300341010300c0d10510801c001e50301603810861800d81800c2e000d403203400e01811001d038188a640b241c14400c0d101c0d20050001840251501c508070580002000305440c8014074a5019038414070401c681d40e540e02d0b80c19100340c5410104241e9440d0071000c40f4020b04041d8202e858223104060a8000700a03070710005504032401480c101c603080d2614410300d15901c0c0c0000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 33490742 1250 33489492 33489503
    0x60a0207081b1c050a020c030d050405150705160602060a050403080c09040f0e010203060301240603090807060c020c0108070201050f0c03070905130b030c0105070309030f020a03020301090507051c 86
    0xd1020b212066030b4072007184603019411152070840001030f0740e000050100440c2c00060000c81c940125903010440d84901080441c060301010b42c01d824001c02d140101c1c803c1c64460179030422101c01e841e10380c604680901c1c0d0480700303550f4035231241c214220100169220710700051103003a00280340611188074103801264035a44a18039034542d9251429a5007280c5040c5900955846c03082c104d0603194800c005054009400160300d903e001410103003110202c0b028001c1c0a444812a4128028901c110b0000d88626080010700e100030343c00c1112082c059541e000f402507142c0640000c400c0d030001085160320409998181850790f4414049003070b15416076099090503020404102e6420645000e1640503449103405141c1a50300c0000071050002c0600c0d00d05440c2e40c44a40f000c40f03050078880303806111020300b0010300d410300b03603a40180711911911018102050b075900081c01c640d115000c040c02150010002d0000c0c0c01c0c3c5040ca191520050720810344161000324145045808800b41ca040e41138229 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 33491992 1250 33490742 33490747
    0xe060c0f0a0302090f0622060201020c0c060307030605030a06050f01090902030c0103090302160b0301090c0f0801030f0f12030e0609190201030f061203081501030203100b0a0917010c02060a020708 86
    0x4000c2d0302a400c030b900e03980e51180007000c2c094843d0f2100c801034040320499120342071290061654501d0715034625001070003164010040340500000001d03400c9100b0030140c070b5441d9a0f9071444412401800d86800295142c05200031140c240107140d0049030003034007030112504007640d03500000070440701c00c00002905900a01940010303503001c0e82c40038028500074010740e11144101c042010003080981c0084020400c01700c0107128410641c410080007003800d040407011200c04900150030548144001403445452030b46040400c849020300010a40d44444100e509010b01c003405005071540b50440710191180000043d646070001884030790821071828801306192082d001100548034240d503072180140c440c800040c00d001100002031a0718025510a2070358145908280383e49201110102d040500503c140402c61020040c00c008aa0b0591291030703443e000c02009031259086644030b5104520800d17207000c0e0807403064220450a0303e82e68203881310b903a40c1c0e600300003c86c06080e002800d202402d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 33493242 1250 33491992 33492007
    0x1506010c020d060903030e060702070914090717030d18030e010804081b011e02070b01060f05030c0d0e060a1508010207150b031207060623030d1d03030d0e060c0f 71
    0x16580321004c05030084c500451101164904c061030b080e070541d99000181d2000740b04010080c914421012020380a030240e04a074100010425554074081c005c000c058407109692035085d210400498034411800d25007032021004007429504483c0d032592081e4003146031000803070304541c42084031610440d840341c07550382401d81c000c2c03960110702d1025805103690740d80c9105950404900e4400a2240e01d800398000d43e40f0402850f1240c050b035011781c01a0103200e0444520707a05141c01c842039992142c0180042c0d510b45d2400d100c518040c0020340203101690203a1410301c1000343c029007042d01e403465401071034039178559101d004900302c4c45074110141048000100484240b031241d0454440ca003001000c403107544602040700e412640c4164001c891203944d92004028850801c1d000010b826064204212140c00b40300119459015504e01e031300801c8040f10350309202c0e2110300429a003040c1d0140440e074844500e04000401400e0b010002c03e528410a400100646043c0084403560340b8001241c030704240701c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 33494492 1250 33493242 33493253
    0x9020c070b090d0b0406020a140c060105010e0609120601150f09140103020c1902031504030807030f0608030c031e0c0a1106040306050903090406080f2e0207051506010c020d 76
    0x1003030111980c000f03a900b011402154001c5030b103d005500650740140c1d11100c40d50f010b031114100c55a19051084188000b048102e000325445046813000c0c03c0030f04480380040005a034900c2203000c1c075680130540440d05051404001000e605a0301c0c2000034101c07403000e245094640701e41300315801d00003812080d41070107404901a40d1084119040c18094180f81b4222621801c00780130503101000603400010b0b1000f580303002c0052003c56942551000f519040c00c2e103004200c060300602c0e8101307058540c8040b10500046610503401440d8031400e42c0d881e44a0130b52103d480754085000e810160740c00c00c08205800140c68121648500d00e40001d100855040e5144101040c0342d60751103600c080d0501c00080843d402c2c0c01079034441d4000c00003555030340c0100300c204000c0390241d8012081c19801001c000c40c68000000380c18018030240c200e11140d00400040d013100c0e09409035048a83c0c08c0c00850752108002002410800c3e1501d5140c5400d100e90b42d22004503460000440003951220b106d00e110760200c0d9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 33495742 1250 33494492 33494497
    0x31a0607020a09020a0c05120a05040b1303080c0d020708060c071407150e01020609010b0a050d0c1505090306011212030c120c02070807090501050a1703160308010f09020c070b 77
    0x10710141040c904070390741c0c05609080ba0044400d03440411500072007401041801e10500004032010400711707060070a00301006050b8011802072044240c00010303038408420b01004070b1401035502c070840130394500720300d903020751208103282c0d45901501c40d18070086500070020600c1ca12035801000814201040c03919180450402c45070700c08182d010340d44002ca91070540280503070104510b80c0711205202c010b030000900d0090001c00c1c60407075914045201d60107503664060340084500441d4030266a024a0802d20781211059010780c0c403a110300c0c1e40402c40103820a000c1c00c020b0f201107041e030326240e0340c504005c98444101d0b4802485c0a1400030a00c030403902a6001042e1041d80b440e0000c1c1c1c003517940303a0402c112101c610700301c0003581c0f20a60420002d007040002c5400b40c49004018000c951400006c00c80040c124002c4014241c82e1400000a444d8100191503c0092898081441e6a858100a89490004e0003500f494280c240004a840030b194001c036a010035806c002049001c1c50b220140c0c0c02038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 33496992 1250 33495742 33495757
    0xf14010308090d0c0815060117060d2a240801030503030f180610170c010210020a0302070206120a050604050402010f11030d060816060207030515060402190309020102010c031a06 78
    0x8130300c020000f01d40c0c0d0004102400c0314a80f070400c2c8940a0511200260110240101020408101004003c4140c80b1302454036080c13a80007074050071801100c2845070802041c019410010110a031000602018040c91a0309440e064200c1c40c5403041032070402c07107000d0350034007000d8203507402000030642d07083e05071154aa00c10700da1184020200c0300325403c40d05014040c0e980c0e10a03691080c07002c1c171280400b050301071040d49842c0010004194040d0010b07440e86428110b03601059030125600c403442d0300a4040b5229550b00a20301a550505070b02c0b032241c0707110180c4c5c1032501c1901e4200041d0b65800c3c43e108940c043c0360142c55030304419900120844001d025841c0d0f10035030780018000a10a007086000700c0000d8416800a0498612000000c00c481840c43c1c2c050811136111a004001158001c105440803ca101428241b266a8500810064441c4504e1514204643c005a0310165030640c840341515100b64000c0c045a04150b000720180c07020380311048220202c3c0b10304c40007203160050013400306 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 33498242 1250 33496992 33497003
    0xa1203050a120b060f180a180e1603050f010c0305131b0b0a020a031e08071107030507060306150c1101030b031e06010e0708010b030105040c0c0f060f14010308090d 72
    0x220351004010a201d50040d005842003a04040354807020085010304000c15030746c0036251400e0f2940303481c2041e401e803c101a503001c40d80d41c0c0c41c4041000000140a581c41900b041f4a14040140d80c0e4940155101d451504c010a030754030f0300c100307010320f24820300420b402494030101000102040d40c8660b0205920240d140c28480c420460016580e48203501074103480d542238000e40880d50060074068510030002c046010303002c0000004002c01c9030031085241c1c0248092812014403038000810a00d0000b007a0405855840350349800500603174183c11030002d540f0080b83c41c076079807603094105a0f05842031020003041341003600c0012405511070f5020310182c010040c1290001d43c80880030005001d038400c01c0003c1078009200500207c0c2c00442c00c1d51f00300d4854505640315614100764040d040c003060040701e201d0354941708908041403103101c5d0312a100d6049220390700c0c44002c03442c0c01001007401a642080312410031100c800c8109041c50001c0c1203d401203e0303146005040b4042006000c0c10740c0c0c04481 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 33499492 1250 33498242 33498251
    0x507021b060c12130b070b0a021e0c07090f020c0a06020c0a08160b06180a050403050403060203190609060f0302040f1503111503130f030302190306050a1203050a12 72
    0x2605802049000c54071080740c10000c0d43e41e82680d82d000c0d02c4c004a43c1240341c1e0420304004a20000f0340d40c208403540016841b00040c3c4901624184d89105080307011b500c04c54200210300424150004208401280d00710036081010151001d0440f0680c001c89c5c28168264000100d88008502ca43e0020714000d800340d030a035002902580d840000315000008130500500c54070a403501005441c496550700001c080310b2852000800c06000d8018413802041e01d031000d03465901050800d402502a0382c05180c1c464415900e80c90f0140d40d40300d16040043c82001624100500003035900158420482030314407526505d03104034150f80a03c0701030f00500c0a821050345e5180d840c1c80c13240a100720381030040c51155205008240b0242c0030032a4002e0b20b550210055801001031000350404246451041c40d44100000044a01c07070030103600034090380da4205c0b40008044241120f031a419848281034540c00c0700c5034a40c03552225040710810310f02d40802030200748100003038072056004481c0c0b000c07903905100c400326 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 33500742 1250 33499492 33499507
    0x11b0813030c05030609060c0f0705070e04060209090105010509010c1e0203030a090602010f05010513091502030702160e01060e060708090303040312030e0606030303010501030f09060e070303020601090507021b06 93
    0x20140d032140e62094a841501c40b03000c1c0954501404003a410440702d40080c955030030b0422000700c1c5441900940d20006000082c440100501407010500a0446072001e51091800d403d244029601407020588180244000440c02d0740c00b40054611403541a504c140e40511160380b0011404403042c1500d00903d50b140114005a0f420401403039034a08039513460311007604c4c00c81c02074256140004075465607820980103100d56207508402c4541d0041c140800b01e03d048060a00181a1603441c00c03950380e9500000820281ca80c001402800702e0384000c1000320700d20340c0c5038000c10031004280940700014480080c010741030303d441c401030505280030b6007100b403501415a001038910b81c069442110010f40d00340c41018642d0b018070810303190190324400340c0000c0ca0218002600c1c2e100c14080d00e414507a403280001100d800da03a010f5000c0e03a80c04403007003014004c8030590795582e10302840700700c005210301d44c004580344071603010701801995650000c0c544091a40d00350a028000303014a1034000c0000d11519 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 33501992 1250 33500742 33500767
    0xf030c09070309170702010f081504060e070207050105030903040302090613052703070f0321021809060109080718020c15150102010e03090603090106030507060302030a060e0402011b08 81
    0x2a006441c29280020720028501c2c240311203100081c242091500300340800740160340c02082c101d003005414600720507260354038005000e0ba001c0903003045820a1501c2000319040300342c4000300c0c1c00b403d55a022508400da4a10044034a80f03c00c0b1680111500107100030001401c180c4151078200750010f000b520400308440180044550444d500c00310b607142c40c505105480161540a0084888030000e9884e185039515140d60000b0010b10003020000b22182c200c1c1292441d4440e100c2082c0d042d00150f583e00c05032902d03040003c00081c0410321800c80300000c00d07100d42c01524294120740012020b042258030f03102c40e080c030b07503900000c4a18034541c0800850303c0c10343e818066401204411304c038400f0941804a4150402c10300c6000281c1076a2600280080c0380e0f0700082950711081040f00d1550780d99907000d15181c050076050740024138503c1554070211380b00f03070503030007940c4079902c6d060042101640c0c9000d02140c0781010f0320041d01240400c1c014003c524545102300b40e0f86405001c100d4980745008012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 33503242 1250 33501992 33502009
    0x110604081f0b0108240102010204050310050105040c11060c090d02090106020f060a060b0409090809180708090d0e060a0306050a060903030212030c0f0c19140606030d0206060f030c 79
    0x98100c001c0445588491216034400d814041e802880c10610b189491005400c0c0707000007a0b500e1113211200c2c10901500d81c800d40440e0040c05014007501c2a042c2071003640b034042c2000380155881b660030320078038855540c0300d88100a981c04c051002841d8649a050003003085500650800da0401c800614600c05a180c403480a402411944c1c001c01460502e404402d05010000d03102012841c10a44108411001035084d0340940d2040d0200085804041c40c041645110384481e01e07070030010460703030f40c1c09200900c0c90780c0344035198540b0349a00640c0c0d0240d155444000380c02c045404600500301789251400c042010b0141c4451a0030001040b6071114000340a03090141d22000c00201c6040003482055030501c4042510300000c02290f041d0f04244041c00454059074502094907003000c10014009203080251a0040010702021081040039051403610910010520001481220f0120b211070a0000308160046103540c060030382c90b221003040244c0c400c40b00207160760601c0703481d00c000d1166440c84403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 33504492 1250 33503242 33503263
    0x4030201140f0f0a0b0f010f0504080a0303061502030406050403080d0905101b0215010e071403010b030103120e030c01120b06120402010e090408070227040507050405010f03030c11060408 82
    0xa03103a5180440140c465143d008000300700d100d09000140040d525403039803c807036200007402c240c0d41801001104847c54000c641c4150001d00c21840107109040d050790202c000c3e01d80d100d5165981007003154007643c1e1fa1240d40f05800014030b081001b00041410800a048020b44480c808121200710f522564608103103a03001da642d042d5528505000b01101e007140e034091140343e0001d45026582c4d8400500516014450255050798620006410901c104603031042c02003c050516201e58503a0395481647d0400d000032501380340d00c01032900003d0b0007601c403086101070050043c1224040c65004584800c003850340341c0d00d11611511440441e0f07446402030a1106800d80e80c1110a14240c000140900c0c602040e49020f00541c0c2c06110215400201715818075030140c034034000c0f5030351742a509500005240d00c6a8a152a40d0003400304004e4040b071540c00b26201190b050000b83d032140c04801c1c0603d40d5104c018040b6000d40f2560700015040002e00040b8540106081d080554039640d06050100861 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 33505742 1250 33504492 33504511
    0x308040303180504020d0e1e10050a0b03030a020c0a1a0313050f010c0e0414040309090c050714030712050301050f0103091506181b050a03020c1e150901050714030403020114 76
    0x52000000e41401c10000700000180c9110702a0088c14000b02074a031580c00759625403032034070341c00002d00000340d540010018000160840e40c0da10b502400007034440580030b80e418403400900500240c2c0d1804c1c0c1c3e821205a031400c1d07240f00d00d19100c55550007000c2510a500300d03074070701420340100c44d089400c0c400c0180211041c3c43e00b400121258003000115549040c240f01e59442460034480032961100208e401e5881001002485500d4128169034600490300300038183c03d1200300f4119030010100191000e02c4c4510548040385590310400d840c030707000c24021035403c001c0c44182d680c1d5640c40b80e00f04528043c060507451409281c04a225800c0d07650300d402c840059607100000c0858440319210340140541c2440c04000c00c0341c000d4600404a2183c108a5010140c01040c20030b50398000f8029190307040300090080c10740c84200c02c9a16100c1c06664282c15070740c1c1c2208001040c100d01030084601c0703420140d03a07244040048580c080f2081d08080c105400b190340e510b003008440120084524015900315 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 33506992 1250 33505742 33505751
    0x6010e0a0b0429160314120109020a02101a0d0212030a050301030203070e060f010818060103030e1305010510030509070810090b090109170a11060a05061002070308040303180504020d 80
    0x72071181c0341c2c094500f03450308181d0904008090486030a020b84850851707151405441c03a2014154500c07580c058145610340390020a000014401003c1c1c4c0100003000b503540a9400c170310103990441d012961481c020141c2c40050f03002900f510324020740c0d14040d0a200404000d0762200c1c0309403542c07940c5c010210100102e50000300510a51030b041124000420004100c000e45240010110715802d0060304254148127001010856910300d00d01034400401c03400048540f41c1d81d40b0f003001006081c0391a0640d009881c680042c010201d01801014140c075009011840800700547d8200e00801c1d000340344a0241c0035501010581072802c0c44995400c01d80ea401c0810304400c0360504c500810360140012840342e00d4600150001303010500007404501c89103030442d484818070348081c1d5070138018041c3c03d0700a02903082080101d82403544034901514050351040c0d204100d20070141c1e601d91040c040500340e6481030008100080c4a010091040f12400c5c4111045a55850118090340c00408030b1038901a00c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 33508242 1250 33506992 33507029
    0xb031005010e15030f0c060a0903060c0c0c0f1a07050102040302121006060801080604031805040c0305040605010b070b131e0f03030b0109060e0618060c06160f0806010e0a0b04 77
    0x700c2d00e5020f01d010200c001d801c2001e0700d40301e01507444010711043d41c0035101c00300c3d82101d0f071070003445804021504410144400302e18035030b00410281a04e0400ca50480c16004040f5203420a00007150940c1c00c9003440349041d0340c83d18184125170300f0903581281e4641d000c1201200580380e800c02448020342c1c0c0000bc007034900791048000d0a8554a0700301d40c04010304600100983e80d4000b0b04e50742c2064140c20400b190303d40d42c15802e0302440f4540c024076009401c1c15440c1010a0303141c1e12451040d13008004c20013160b41c031101d400c1d82d02e204880000e4034030034071200403c5000c4019030a80140910943d01444031040d08e101d1220a2440d1040903903440c607401540e403080c0b54060054100c404000d1a0100b421030401c1c0700904070390411020359005840c00300710b00b02007480d07920500d100003030000d101035100c19980308001c2d9180022140e80040014040000383e405000750400641d446450f00e80c180700d5030b505001110714a00100401758000740c41400007072510501002071004c0d00c816003100100200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 33509492 1250 33508242 33508261
    0x70f0204110d141006080402120d0210060506070c05120c03071d0f010506030c071b080102130608010605030a0e0a02041e0b060412030e1504060804171c0b031005010e 73
    0x3048402802d0f00c910302000a1a07103601010b200b5a400c0b420008155242c41c008116402c043c02c00704440340c4038684500d100e06d500000d182c82200741808050004035182c0b01840310b2070160b004000d1581003c46001e001c9072501c4450248000d030740400315144103103880c00092502c04039a0080300302d00a11281d1240e025041c11209610180e010b94000c01545481d020583c1444010503203140b210010880508022150102c020b191808110000e1202c9d2110102d038001e51202c202d03d03a840095000000302c0500640b07c0c0e6048400b5a1106419540d50b48820f0b0060000581c1c10b02c0d0b180942a038030001641c0c4c038170178a5140314030280c00c8800d014001c0c0001d011241900319291048405200c1004158040c6150003c180d505141c5440c2da4a000c1c00450403640469840103030f82d00002c1004a442c136071000c481d520990188580740d003010b0029602929903c6040003043d203c3da210701150418800940140d034103180d0180459040c190505010800c607a0282c10459140070b501050184402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 33510742 1250 33509492 33509501
    0x106080105060a080402101107080c12060f0106030903050702040510030b07030225020301060317070615080d03050402010504050a14040e012304050a14010e0f010b060708070f0204110d 81
    0xc1c00365403091030300901d0040035005842c01407000780310b64070380782c003448406100d980c0036030780c4c020200112034003152243d40701070b19240c407541040d005444c0e0f400075003440f000000d0111300805c150b950002c9607900303000c421006802003560036401c0c005c040100e0b20040c1c807141708040c403503009089400521815803a0072000c4c614060422001c00d03005001c01f100d225000d15508041e00360740304110700100c50030310220f4058006d0b940040e103520380e1800d003000d8040510008141080c82058204840d9104561025011890340070b84119a48102d400300d064901950000350000d005062460625554000044102460b1f4012030841d17640305238980b02c603040034020007410000401c003c0c000301800e000300300031b40d0f408040000f40380d14803940407406202090040c2100c594014007280c004500242034207000c0e1010103059080d034403501c41d1019141c0c106116400c4124402040700703181c2446a01c0d40103594000200036211141d6001c4401c1c0142d465110300c210a001c0f0000c8141c841943d03e48003070854 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 33511992 1250 33510742 33510749
    0x80a0c0f0602070501180e240a060e01050a02070504110702040f0506010806060a141305010f0e01080c0a0e06041d07030603020f04020a0507020a030b01080c0d050607050f07060c0801060801 83
    0x84450880c1030040640100344802541c200b0f291003110b60354650700c44d00707020215074480b9180c0303102c4405028110031507664850400d6002c10b00c3e52080441c007424440c611001d845203400007045409007180942c8190003c10fa02001841100c0246440e2000501100c1008010b903616000c0003c100c81142071a008034501100d40c56010405841c00c88000380071018000c103007902c00e0400080e01c4a00038000e0071006040142c9801c816142d10700031300e400065000601940b03020408001904151904c10400c03003e044034103944a4207980c1380c042080031250010380003d801e01288141c03030100e940702c20015000408200304000b8031303864a2001d21400140252643c010107061860a2000d600c1e02c00c2200c1c1c940398180c50060381c424844004075001e004590000b988004414000014080903944503416103150307106840c000c10344c1904025216229850060464000d42c0020f2820b9010f080034001000441140f5440c1540d5a03840000b12110500b03003001041c450030040c030040341e2214105024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 33513242 1250 33511992 33512009
    0xe030c1f0c051603050a020f030a0302251205090a05180411010f0c020d030c15050906060613030210020f0d03020d050604020c25050a03050a060507080112080c01060f080a0c 76
    0x200b580480e502d036810548504084e0505c0750008031700600501c00c1201c0b041c14500d43c01525214500341c100103019500103000d0b01c030030ba0300000492003e10032601c482d2150340d901c02500b4104964411055600b078111101c1c840c0c0c40002d50100140c6c50300d40c84072414801c000e068031101c461405182031071110700385000481c1084803000a21181641010400c2c000f250100c403d407141a001e440c0440311010210350007008500c080100d416111003541106004922907002d03101284d44203000c1c0705260064803042140e4a41855040015040800d074940e051030013403060720f400410b42c1e07102e1071400704000d01100c0081c2c0c3c0054421007080c0c2a106050700600704803815450641c154120940d50241d04082c1c55807040001003184030382140c120040000c100241096034095684d044c07154035401d0300e070800c0d0380d4982058009480c4034869003405058801c0707420306814a0b90340e510f489030f0f00d4200c0081016190350701c000100c0d107500b0802c00f00e002001c0150041800c150700d880c154440c15800e6004058 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 33514492 1250 33513242 33513247
    0xb090708010e030406031a150c0d051c090501060902070503041410050301230a080f0105060402070209010e07120f09031106010e01090f060504020301030c03020a0b090907030e030c1f0c05 82
    0x10b064801108030b03011515946030110390f05007440b10303845c11000d1050748a40d10480319108200140c0c2c000d00581120300240081d03c04040030b2103415a004c0c851742521014005101c2e441ea015071210354000307803640b4003070000001c0d0b503510f890841003244c0c01000b00765130b140e00100781000100940001c58031070940540d40c4007540800f00700c0141c15400180603400e50908034600394480c05800704e4a10000c680010301c403030100d540c3c6080d5541c5030008202020115400e02c000611282458000ca60545074046d0009810341e1034441e0210000ca0003a0081040041e0300705030490403002d50240080313500d000340e40010424041d181c09001c049594502503200d0f0000001000b600810180c1f150456030040404184410f00342c40381c8008001d00c0e080380703901910100002c8240460741da00803080d40d1090f6625132800342ca03594880310b41d0041c20051a4001c26160011b81018481e80280368610712000c1124107000b50980000d04262403a64219030341911880d601c0050702850003500301c01c4506080c040d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 33515742 1250 33514492 33514511
    0x50f010614040203041e08040807050109050a05040e12031f05010804050c10050705010e160f0f060509010c06091101140a140a02070e010603020a1e021b040b06070b09070801 76
    0x10852001c42644180d40c044001024010a110091030340f030040800e0b1003141209140040464000303000b40c4a40c2d100d08100030429500503102d4400ba604020f00303018046181c0800c0102034a80c07407840342e10b0790041c82500c1c1c100c1c5000d03d01541c090b8564540710b01c4d000ca0411524400c1c0d0842d40e04c1681005084028040401c002140300d04192005603818070340c05040c1e090a64142c480c0000003031296103000b00760040c0300c101040040c0020001400105e81680d2181200641c2c401809844140c18180c01c00704007243c002c100508010700181002030ba85046a02d0b00c2d41141c11549055411a002580420840da809034920034001402c84d4814103240304441c0041c2a40941e2040100701c540c000764000f0a00d0081000030f0041a1a400421403580c4804005000e50000c0199101013207207030040340c0d0901d4020207400c1e640b642d00e60080c42c840d40c1c01c0c880000c0314200c854007140c10a0b5a46030311070aa403502001800524040c0440e0300f940d04002c1e010520b8104641c1c44502543d25002420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 33516992 1250 33515742 33515759
    0x203010e0f0601020c060c070305010501170d03050604150b0a080c0c03160203010e010e071401050315040209010c020303040801091a07050a08090106051f031416030207050f0106060309050f0106 85
    0x2039030020340840a880d200d54410307006074a4061025030060f4080004540d100301106d00090703074802e1700d11480090199999440c464400c000811392001c0c0642c00c0500c80b290380a00c254440c41d03009500420100301821500352408100182c1e81011080c29000030710b04d0740c600d030080300310b903080200b0a88980ca40040f91152544078001c04054510000107840e10006540d025003000b004154401e000f00700080107400701540d00c82d094800d480c91205000d8400c1490760180301540e1044070103506945c001ea000508000083d03110360501418414503c80050150f281003000e4005805004000074510503d400c118618516180024000c0520700c0c040081950b800015a8000d03500d03414543c4145e12280d0f46640900040e030049500680784441290716140c9025100900340c64540b41084220707610014800d00704c00450f50500036012400711450581d00ca540204002c0340030384281c401c12030f00881401e0a451895007d20000385c1c690f01c181003072103828052803a8a8030100001c0240c2d030304d0080316 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 33518242 1250 33516992 33517019
    0x9030f020a02010e0d022202030613110904050c160b0702010b03010b13090f0503030f07080f0603070314070b030907090606171308070f051005010f0b0904020706110a050d0f020301 79
    0xf44d5001d00d04000c800f03002c54960034400200c1d001c490400310080900e05440d01e00a4000b2a400351003419515050a0700d800144103500398922565043d07890005284103102c081c2101030312084030200204046564042e41c1035141075018131030f0300410300381e003451607009003034410341c0030302c20f01c01d91422980c8441c9540d160329000000c80c66050119080c481828800e01c0e03c2c102c20000307815400004100b002501c4c090101c507119403025200c4000f50745410b005c00c403000908131051074041d402000d0070b2012a00ba005018801021202203130110354607100588542d40050702c001c9600e034010384042c850300090340641e401074442c91034014040c481c0b000300d1515101004c0c14141d00c8003500c424080a10000e2812225126000307a0011100d08503807030722036078481045201a0825181000100d41d6001952a00f000c81d01c8034118903040140d0101008000c0d40110421075040c0c2d82d0f0700c0000d40a130400c20243c040f030041e90f1910741e1544050411030042d00c040c0c0021601c083e10400042c49000c2c4c0f064075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 33519492 1250 33518242 33518267
    0xc0604060221040f0b0d0f060311040b150c0c0a08030c07170a0b01030305120a06080a060e07030f08121b04090e010609021815031302060a0c021309030f020a0201 71
    0x88000515002d403140c2003188529000310300480c228034800300d804036850000704420700b060791040040c04000c0043c0c1f0101e550500004200020f01c00109010345016001380740c40300001801d02c69803400b0360384600389030b0380a0401107086410201c1000d0301454900d242c2d200800f01c59010318a020201c0f000300c4d440e14201c7c0541306110756880b000c410340c4941000154040c680c8420340c440305503141d0030040c10903045001c1c0c025070344400400050307100e01180103a000b01d615800090640044660324800034001c42c0e84a9040d9109003000040032400300103034445040d015466550340c03050f4204e4207040c1a04020002d1001b50003d0946142078001c1e07408507000c480811000060140800d0101409841c007a40004a03640c008030781c2448960100500c50600041152290403c1120318100c400b0340c001110403440002c40c550070400035040c032800500c1ca01d015803410304201c40150780001d00c010010b0300030507103072561001d00104158000012101c64103c7e80001d080d01c3d046a4002084100e0030310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 33520742 1250 33519492 33519523
    0x80609030702190b0307090e090d08240603010f05100c02010215090a05010f050613060b09010c080c0105040609110f030703080f1317010b09010b0919080a030e030c06040602 76
    0x284410303481040f1404050301000c40003a0743c9041c8550001c0c910750060103031140d180d00310300110714840e0380082c000081104039201e034034140d0f03a0288040d008500304d05a20f000b8214100c80304a913a07480000450280140348070807400c15050109020710b0428009908003400b000f4100c9134090313a00003034404210f807071030300306506995900c1d01c440707040503000080204035608145a00c607080845070030044c0b0030601070381c8418007000d9458101090395494460807004020410040c0000c0d44140b00c1041d105026013a502d00d08410b1001040c01c41e0000c0394107a542690780d0b41d8080400c02d44031440040800300321b4002c85c00c5d030410b20010751134101c14880101500c3d400201c86404c0700c001e8040da0f0b81000c80c0805180041d42c2c42c2602c1004040c1c2071070f612015440e04c86030385410700d4041e0303805060b1140d5000c014286460b18003031045088503d80000c203003e200c88000074000304100800440c440c440d50380c0d03078000605102410700c0e08600d030300c82d18800e80c028403003032000d2580021401001a90310 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 33521992 1250 33520742 33520759
    0x3110f040b030a030309050f010908030c070c030b0108010504021509032505041806050c03070804242a08011401030f1506020d09090603080403030e0a0e10060207080609030702 77
    0x8400500100600000305800d8018411218203254066001082007030140b015250284001041d030b074201d800c03408005041d80414400308480340e40b03220140c1001d912901c1c1c1040c8154894031110040b200036070294a0070b0307440c2c1c0c007004110b0400d0b164603c006070404041c5401c05030307040d0001c1e444c0c1c803a05c690400480b550480f002c40040c15111540024a07020b00104a1800c0c0c1d034694095030031700d100098641a04000110340089140000c50f8460000f582e921300064a40c0e90715501841a00320b1840d20414010401c035415040714072512401e040080c00308401d044001c040351040b100340750038080600c0045801000004808501e09400603000d2030002903013000c11004000030301105d21180c0b015804c140b00411480d40001340e00c0c0403070005849070001d00c0e540389800700070341c3c0721030000900c4441c05201c2000060301403519035410801c004e0481c0e04503612140b05200b410300c1105d5051441a00a80c1002100d4041c00004050228500541024036000c02030719500d22450f00c000340144040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 33523242 1250 33521992 33522019
    0xa050403030605040f060e10240507051501060f0206071b1e0b060109120f061e050c131409011e0801090b0609010e100e070909020708030901150311 65
    0xb644140c025000040c02001600f2240580c81c00510a03401030408511840000c1984c0c4000703078003041c0444d100c490380b100000d054003003000018081c0785013180502c8028080d0703900248042c0540350244948241045a6604d4550002c01c200c200c42e1415007550080028420382d580d000e0301c2601c040620114101210140745040f07102503444c00440b030b00494070303174020b0410040d0b1160244d02a1800b6625480c1103030311105100c0c0840c802000080c9844619190140041c0e075980040488500c039860070326007030030300c01b840320f007a02c00c100c42c29002440006961128544659030740000b40001400d010301100c894008140c0c40071060140114031400c0b40c20040803440c091307000002926000d8000c1c0401001440c00311140142560841c2c0300700300340d50000c12220105c961607441140113886030700b02c051420301d0f00820900b020f082201002802400410600300700d000900103036101d0241c0503502d24024640d81d084501086111203908200d003010000f003500c11080c5a0350181c104c0d07194041c1400e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 33524492 1250 33523242 33523247
    0x40c060e0d06091a06120705010f05090306041110021f020906090a0611010b01080906060d031103040f0306060501030c020d0e031f0902011d0a1205030c06010e011a070b0a050403 78
    0x24035040042c10750b400c211140c2c2c00c100300c0c46800d21300c01072842449a0542c40301005c210b480840189840550f40c0080d4040203d507100304801685e8003c039040140c90041d019022a050034800c0758165100a12004000d22a007014040058101e040d440035050443c419074591602e80b85644c601c41070390f031f00498158155601c04040300c9a5404c002d2000e03c2d4141c0d1108050304402030001322103840d5103132240d40c001079400390b40c00c40d1080d5802400b0b01403680d990410041a0424604190108508000c10018180042000b40060301510080e07403140c4d8a54030b05041aa500794020074101824104507400260f00007400300d810f04050305081d80c11900300070200e40381c80d118600d0181041c2140f030703910f0322040329588a11061780c001c0e81c0c7e4041c110b14000b0b910640300b000004094008101d101e04000001300c030701c0b9843c1035510680a40b40360150f4810020b150000c281c0001a0100985004000b01e510104410701070301d0451007000d042071001d0300d0700e141000b401851410210b8641e800a000c251 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 33525742 1250 33524492 33524509
    0x4180f080d020a081602010b06070b09010902060d021305031b090a0b03010606030c0f02070501081617070801051002070b0304060c121e06050406080a060b19060206150603040c060e 79
    0x1400201103441d07a5500e43c0081c8210720076038100c016516902c160111862040c0150700c423003c0060101ba243c41e15560700d01041c14002010710000e5540e444082c80144d4034100240b810540c001e40150f201d880e04052403030060a180d0105201c3c0c0d00071080364104000d46070150b140a01c0840b81c05209580c1d0085290141404200c2258107510f0488081555074055200c003400344020358420481740042c0710280d903200307968000c46020440481c0015000030317140c070341c40060701070601e0003403429001194900c10744103041d40c4400215a0803030061185042c241e01c0074540310804e00c001c00741c06180402d100724a1202078800391005440e180020202801166007900080000400300840012034080f8402c0d07074200d415a1102d0360402c0c3c400211031403d801010103407070214025040b62000341da030342070080850000554002c60101500384444154401e048010081c603005032a05140c80241d02d0280560740e0f861074480d400a000740008a6020100d960541c0e03840c0c1050707101080644000b40708507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 33526992 1250 33525742 33525757
    0x402060c0a0b01030606150903080913060306050105030f07030305160309050d050d02010507030c0203091c0b0405070603060b0a0807080702070b0705070f06030c08071d090403080603060604180f08 86
    0x24072501c81804100060b184071107040328000d080c10841e054442c2c2d10030b1491604028100700191506809201180f1840020105900010314260a414881484809403040c80d4030690b501540c4070300400407420184482941e424130324000d03001c100e003182c0e0054558000e840e81c01d660040944513020405001f070902c031000c0c0c030006103030201107040e520700383d41e4441420320344900650802e40803a2510b07010780102e542040442e0095400d00f01c40c0d0040c010b8641841e402814900d12207290328010901e1541c0d414012801180544152418000080c1c2a501c02d5030100014010401c1102202c0340d0040c2142c1d0801301524080210f621064412413510150781c09c1951400000103a4100704200002e221040b0752528000744003c0c0d42d1100c0950840d0342c10162400861201000545494070400525482c15103000c0c0750044a0064008154180e50840e011400b00d4100800c0c0030041c0b030204025a8000c1d0102e03010b10040300b20002c80c1100700c40740700d8001c105d1145401860304002181c001d84200d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 33528242 1250 33526992 33527017
    0x2b0203030c0f090a0e0a05090d020601060e090c09040903020304030605010b03060a0506030601020a15020711090c0403080c011107031d041509020a020a05011b08010b0a14091c060b04060b04080a0b040206 89
    0x580c1086d9100000070402600c0ca0401c0344190095564105e0010907018100c807040c1c0c86100b021048081444140903005020040c1034000b089010681d0340d82e8415007220318080e034011501c49046280c80c001712a01a04000e101000600410180d550341e901ca92081c5c81c81504c0c215120f441c0c00700181d283c2822240001c104d1040e200c50784490a0069010b01038960051803240c0309980043d051146504c0151042074103000108020700204009100900301d1190100000600e00c03e0280c0f0780c0102e42200b40114002046c42004220100c010060002401d0040350100101c1c0800501d0b40c6a6598038415200f05c150081058200341e8000d01c080406250400001d008030085818480b00c03601003c0c20000100c0c0c03203800040703510700080b8250f038000e03243c6458450f00d00031001c50b000c64907007041070b5032988405903003114650429526030004102e4820382d400f28401c2a86010003098074540d4000d40140f440c1803104210403030002440b00c02044d00f20f00701130216119030001c80c100e8480c5078080c6e542e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 33529492 1250 33528242 33528269
    0x11d030a060e01141f09060b090913080307030f0608010e0c0111070b04120303230406051815010503010c020c01080604050709050a0308030106022b0806010306082b0203030c0f090a 79
    0x200424410059417001e900c1c41200360151100444401c66440e4022141015401d11004903035050850b0307100c2d001120b4101e2420394295913500c03110b0a038400ca46010000b43c481c069010844418028103000e024200000c3c014407c1900c003a40d9540c0380000100d040100c0a02031740290030003030041e440600b901c6e402c2e2658880d00c1d9a441004000b07000e03c04c80002c1c0c5411282a240d107a00020b5070f80c01805944040841d844a4548201400d40a8000032030000c0919031051045010005000701c01080d0030451070a44c0b5003c101800c5890241107101550810246901142c0e0b00866943e8000811100000c0507110f025080300e0602c1d10f90407141e04448440000701c02d004a40026604880059080340d100b290300303400b218641440c2c60726203140c40c3d007800c035403000315801030340343d10360100040c5400140c03c1d80ea811118074119000150107641340d07038000040c4803080082c420310498002c0740010352550610000d414098400c0c01241c22580b40003141c8a0010780d1359000361402451100c00c1c609 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 33530742 1250 33529492 33529501
    0xc0807090608060c1e0a020c0603071715011403100503030a0207030c0603062102360612070b0f1207030f0513020f010f0504090515011d030a060e0114 66
    0x100400362801403520714400d0000090014001e40c088900712406003002c0710b002e51400d000e0b00c07001c1c2c006c1405d00c0c042d402114580e120f5070b10740b00050351140703203a65507140d089004040094017164029102000c494030083d0707103003038a980284400c4a80c415000d54140e07695503040700440c1ca088960015989030000141c0003201e964001440b100f0740380650300b10034403255207a1003030301165401d01c510700e00c19004000620020072803422441900e400030b060f500303049100e6001c80380030204010080550720008001c0a11208006400e107038000c906580300d00f900310160000c81c0d5600c1d030500c60f080c0d502d000000c841403078405600c00d4802c082d40607605900e081c01c0c01003025002e00a010441c003503507072402c40091001c0503080000180b10360017911082160100c44011182c400000c0c20b20014010104000a0194014426144551560003140c000c00d0581000107203801c0f40d400300000c46a00700c10608560340d502040d480c0c219640100c000550064041d160b5001d00000658200100032010421 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 33531992 1250 33530742 33530759
    0x2160e01060f08010302030c01050c031b010510061d04050414010c050909070c020a0302010806040207050303011202010e0a08070b0702150a230703080105090604060b030123150a0c0c0807 82
    0x181a182503454214000718a00ca04448020f400d00c0082d51552001c2c110b101c85500401c014a4a03451070419607141104a24880010101c031601905c4982c0d03407042000480860175103000e003d80902c0c5001c042c804641044840c0110000324110302c5181d942003c41d04101e0301c4601550300c2c1240d40c0081c450651a8013010700300d43c019660040c0924107800019140e43d1103000c003000c500d0342c0242010307030507800c5400464074007000419441d0003036800c0100001140040000e18001e100071213a800851050744001400d41e01c1c00d424403801134640400074040c18174003080707401c1505c0900020760f40314400d500001d01e0419044088012080c00080c141940350b40c0000503514101e822086041841c4c10000540207502c40c402c0c000d8001004e440040c131036451f0451001c1c1c1c100c040108003180e410340b2254028001da0081e40006016510840d41703042110010702900b040d02e0080701c1c0704002c001c2d081d5100000d8890900c0034820841000f60003420041c911044070058a00d030401c890615071900d029 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 33533242 1250 33531992 33532019
    0x20c06070302070209130503030a1d1902041802030604060203070e0402030f0702060f07141617030a0b0402040b0f09040608010c0c060608030301060f0f020304082a030601051507030216 81
    0x580c000d00b45c8100190200421480c2e90f2211507214004600c3c56462404a1004040c1700f108070381e80942d84400300804070020824501980a200c41c1c2c0b00c4003225034810003080325880050801075502c10100310380585d40110300b40b84e1003a002040969241d4500904a822242541c7d444e54802e202106001e0710404191250b4407032000c5408803001521525080f0840d10b504440c0303c0b00048500d804041980a17000150181009020000150042d16691540c42c5817407500d000380440400320403c085005203000308092801c0070380b408c6140a00b48101b582032485640c41c81071040710005454011503d03140d010300f0003040c51034000c0040c0307a030120303008003002c070b1034141541c50b5400d01c07901140f1041c002c8222412100107445120300c0311380300a019100d450000d11981c065000900000407650800c0c8072003501c4814559128002c03610003243c07a00e2f11602d201c0342600950010b4014030898552f01000e2610511642107103480d04107910302280352411060700c8003400f400da003100040880a0111 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 33534492 1250 33533242 33533257
    0x2702010305150a050d030e060a02030919030308010504050612070e15041b0c050f01110703030c08070e09060f0418020931080f03130302060c0703090e0604020c06070302 74
    0x90078041a25503400c04603406801040c4a540400103100030010362034111264010b030341c400e040044903072030007030005103454001c21882030140c0c10010343c030071640c6011034070080100800b5003caa421401c3d0b4a0040541c001405114021540c8001141c65070b40d8500c0d001c5e003a034034588102d0300c4250702c401c0824141c110584072000d801c0c0c02444007440710328082c0a100d840b40350b842a221520880c01e1030403500b190306624265524000c0440c007101420b0280642e08002803c00601581c0b03000314034004040303130400c1181a017045005024014400e500c1551400708400c12103040459440e800001140f040c03101072007641c801d203058299001810b9492450030094000c940e0405180d54040716644258408480003040c0e0905103411621401d154280b68461030080c24250308081141041400990003a20305c038650a1f0051032040c101035041013065444880c0e000e10b1410700e491a40c0c040c00e20740f1035000b4100d101d540300300001c2080d1202c1d416611020355460842d030986c01c00e071801400940c050342 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 33535742 1250 33534492 33534497
    0x60109020a050c0a14010b0604050315060103091406060a06031e32040c0806071205090a02040903050921100902030c0301050415060501030203010e15031203090d1106100302060a03270201 82
    0x185040b854238002c401da0341240c2c005070242c201e1262242400c669400d00070701d01d506041c1d40c1c010700c07008168000382c03118520302c054005001c0c60030680200200186103a02c400d0030541400c0d5224000710b503140714441c542c41401008035404105000c11146022600d0307080800d81c0901141d013181b40c9207010071038000d134003a0010304207460300d41c191070b41c407490704840d214040340c0c442801d0300012241c1d03881107501c20f80e2441034504020841c4d0000d0182d5540703c0050300050408101a06c540c0b43c00d01107101341a412401784000c0c003280c044031984030b910300700a00300000e6a0341ca1550541d207040c0300780b00110000800822081c0b40924000502021800042452a01e0504041903e5000c0d200b142e060700d2544105908965609141800024551544030382500910012201c03014513840a503000c1c0b140d400c007070918801080700041c4081d40c1c912050507580c1c800d20a11141d03000444041082d2601513035001daa0741c100c440b00750f0107003461075034100512000101e11010104240c00c3d011116200b40d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 33536992 1250 33535742 33535751
    0x70e07180815010317040e010f0302011815050f070c06020708070611120d09021003021c06152d03090b15010909051302040509030703020d020f060109020a050c0a1401 73
    0x1d00019903680642c10040d0b8680301c005006001260800a03901c58111052102030718258803071521031017102c800e80c0038035043c41550505104541c0c100d0f040700401000004407000080c6428001c1d002d42d050204240240100069807030030304090041121203d58000144581441d99030400a40d1901180b044001c2d5021700304000c68247d110307002c40c0d03000d490020005c002c40c0c05181c00320112540000407404000780c5e5080d01ca00180c0301d080c0c0491205900ba100117890302c0900490f402440d1105a04c3d6410900d1b003c4188050050b81c51040003030000e80c544940303050030b0070a4000103044d1040c1d01d107141500d5180340e20942c90b4550040740c52a44039a9032041a40c0b28901e0758407030141e44542c26804607005c04410b004448465000075402115164008180340e00754010400301c40301524185410741002901605040e01005164048034091005041c040280154135460741d03018010051000e0700012200c00d202d21903000c1d0741c04900080f095418030042440c10106c502c1141c14021086d5090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 33538242 1250 33536992 33536999
    0x50f070608040305180d020d06050609010b07020310050a0b0a1203090f060e011d0406030320070302090703050603072402070506040f170a0f0c03030e040207030c0b0405070e0718 78
    0x41c4601c030b001d20b41c55260700782446140320700205c1441140c0280c40d0484020f08031034015170340d009400c2c80c03840c2c050350703000079076051001c00d0029401c01604035030039600c001c004801c010f840014090810035080400011151980340b855401ba007583c00c2c85c5548071412020100300d0710031034035666284600c641ca504540310340d1541c1800c2e030b8420b10f12414010400310480f09030554013034036074807402d00c032411403417800407240c400080d00303c9109403c103800241c410310000c0040040ca0380c0e0b0b080614400001081c01c18a0355000501c0c4940080107181016100c1c0082002500c00f00650030242c10101c8000b005802034071940390f8032026a5602c0360051040e07550020352401d0003800c0700c0c1900c5010b84d501c0056402c02c4c0c06181181503103500c0d0910391090360014004207007100c4480b00ca16200d8060f0715a002d1450038018828054002c2c26817055104100f00000260000385440489902c4000c1212998950510303d04041035940040c5000c402070041119099004103a040300ba4102c8820f040181e0f103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 33539492 1250 33538242 33538247
    0x7020d060c020708010b09100e090a120c0507050301051315021309231b0708040e010609030308090304120b07020a02090a0501050a08070302030304090b120a03030204090606050313080a0c02060304050f0706 90
    0x291803903520340d95070302000d05c09e4020402c5019031103840c04080b80d0714a4116515040d000c0c01d210148000a0720302804401000024032081d0010f020443c002d02040c00c01d10740301c09450700044001410303041c0f0f42a0000071080306406440b1548070000c03091242554884124000c0c041c02d48480a0481ca00100440803002256005001c0e5103251081c1e01c10b65944045280c1d20783c003070841582c1e4030500740000510b8060f50a0788078081c105a03a6200209850343c9400340ca10300c005402810b0715082400188224020103070840499078004030016183e4442c05000e0f4184070140700e02a420141202c20049a0b004a8011034102c45090303c040b0300140d0b58400160300e44000c0d001c000e5140c0c03c20041001103072190340251540007070040110070300003560140b25103080c0740d01904a0220f600424200401c030007611078a0000c0801b8100a49180352006519001c100140401030030b1030f2010071a41c008034070603070b484034015501603d032a0392030515080440e541d010502c01e0300928418034002040c03e92 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 33540742 1250 33539492 33539509
    0x30f0609060121050711190305031012080a03050702070b0715020f03040b0907080d0509060901020106050a081b0907020307020409150e03030a0501170a121b060b03010e0313030807020d060c020708010b 88
    0x885e0031f020262050305a80d402c1300d8561014000400079240e150010441d4491104481082d43c401c02003195103456071080503080d200014150400c1d0b4100c650704016022102088174130581c0d0104584000e041c8040364880203002c2d0195011440340c001c41004200040c0046550199044101722602c0c1075407403a03429510700c0303452000400110180002c20a50a1844c0a8101b600c014000810301503154008610103604540c00450381c2e900035140343c03011103c074501d11380c0703100001d45039110340303141c5004007a65071f00c1281e00003402070383d64a00600c1488040d840b10141f6400180c014843c507100341403000d07526001920311030a4a031400000044204004400074045880781d0042c0801903055152450f140346012620b01c244000b0003d0614180c00000d04800442d00c60380000685000c0603003414215420304020704200d500030482e151411a904255008890303000821550341d0480c1d00c042881042c0f0350000400e11b9060514013106146c01254100035100303040000c0291030b454400300180788 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 33541992 1250 33540742 33540763
    0xd050c07060e0d05040b090301060518040c0501080f01060c05070503030a170105040b01140c0309030102070309030320100b01020102131401080f0105090412020a050a03030c0e030102030f0609060121050711 90
    0x19130f082204200159004019254200005000007202a0f56001040b51081c1d81414011282d401c0703410041003000101601d000f4103009c3ca4010042e160190400700310b08810f000b0502071050446c281410428204040b201800c0e015040c0c03a1142c11103c006841e4030b9414201d45c4016840c0e000100e0036041c180700311686640141c1d14110007500b40d400001300b69020032102040e5000400020b403254409000902d5918840c3d0341702c00710707980340d410010940c810320341002c24404a544408403085100180d84e5813440000100010f4103604a00180c2c0244100716a080141500d41070005d1800c0d030410b10381c9928003080e22004d44690320181d0005c2c000200f4011160f00c1241100820045084034804140c5240700780110340c1c0a44a82e1615881d140340d2900403070000340c4440320700602d1a4044000865400c040d0006e40c1581000a001c054020008119500600c0c0718800a292a03125151000314010260301290115031250b20b00c1700901011104000400c00441a0007503208000440c8500d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 33543242 1250 33541992 33541997
    0xb03090d110714060706020423040203060906010f02010905071212080c0d050402010903020607061a031203040f030203091801060e1503060d020a08010c050c0105070203040e010b0703050d050c07060e0d 88
    0x40b241025140001c10a2154009400550900801001490910062015088044500301182886c12017010607511840c44a4040e0740184188141c503103400c1c4480c0d4002c18242800000e0744040003049004200780e03807000d40540701c3c48a0008040b40c0b1002c0300705099004150282405c010300b5800d0f00c20305815140c4a1a07000d0812201d074160720280e01c0a41c0062052420903041540d0345c00050307943d0043c45068480950310249a1844081d540103005d0f028400d401501c81c43e0502c8260b40418000103001410303150380000700c030007014400c1c0200c03002d0031001890010000046400b510309000240603903400300d84a0306030100c440c034100b00c40c01828442c5028052075642c1e41c2c414408503e617640070880c5c00030000c003c0801c844000713010320480d00601c3c2d55000e40714151316001d1070960b000a0029815504100400e0011071000c08640e030540d80c8c0c0c0750341159540e88a00c0c04a41d28452041c0c8162500d00c0c00f4207200351400071900804906008940900c0113003d072480440e00c2da200911503401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 33544492 1250 33543242 33543253
    0xc02060403050a1e0e100305071403130206130e0705090603010b0c0a0501020d150e010b0a08130609061a0a080606041d030c03040509010b03150918070b03090d11 71
    0xa4482c00052141d900e01d46840510650358140300f03244c04011403103a40229034a5841c10b22642000405122015154078085c0040d040060b000303444113042c520a41450300c00000050a081c9081d0300a82509030f015102d81e60350f04000031420040c1c500c0340a13450b103031003048000c0752115214009440348503800416980c03a603442d04000040c2035112012000c143d00544049402040003803018007a04000c400e004111590004202c1815103296003022640520320700050008042d1030040d2224030382035040048003500d903c0200c01441030b0f0860018090307411300c21030408100c2250011450000c410032f0100e1040404ea00700139103401c2e98007a0105070750003007000402c107140030340201a80c0b94080c0300f154500d00d610001c05045a01080c3c3c4c04a460384006800c010354200542441d0060000700708c00f078218100320484044e15001800a203100709951030114210301a041c2c0b0552a510360201102c0200d59034940d111101d40080315201003500408008a000d0f601500d400450b207840035000d00b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 33545742 1250 33544492 33544501
    0x80703120c050a12030e07050103060b0f0f070c0807030b060301020313020103051e0c0a08010602030a0e040525030b01021605090c0a03020c100e0115030206030411040b040908070210030c0206 84
    0x365641100d000c280da8600c00c640385800801d4400044483c07046181c1d030f0110398406d01d03403541d51a210703050384100d04040c1380410030003442d0201c1c403d6610403e0a204041e6844c1e0720b0396418040da0290000140051207080000102c0703400015a103012070f48100003010195846a04140c01c0340021034100a1140d99000782c0c00042d0300c070703074007442d401451040084a84092800090740075417085070005003180c1c1c00200e01c0d03251600040024018000c9e880254036002e81d0440003040c01909132401030003a80c0300c0000c500c0083c2c0b042d0035070403003507030b040150703121014582d0000b0060203c0058490150040d0055808a01403819109055410151200b0395a8889842d15016588500300510406500b070140014103c018032150b2240300030880041500100a00d81c1421658000c801304202c844a600400c01611205c0a0300d0384590000300007688659035001290103490305d0900ca6a015107010481d608112203103001d899454025540c030310141080700415422a64a20f040700b0140e4071100004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 33546992 1250 33545742 33545747
    0xc03040b041202100c0c050610050612150d05030706060e010b041206020906030709030b0f041703100807080106090609060506090d05070905011d15010e040902010521060a08070312 79
    0x3209030120303104403201d00340c04c2c21001d03007103400203100030700003650420040c002d100041201c20303000381064204404c1a854240000c219108000c10151030798000f8000902003000604c0055154402503c0302c00c064800d4980030751a54801c0c07104644482c50400c001c030301002000c5459050320750182000303280c0303810014018503102c41d201c400ca461075020013118011b62140700141d401010503860f60442d0b40e0452402040303602c8014803100c2d040c0e994070708020200f0010341490860500421480f5501c0d150038007030400c00c2d4081d402890b80c0f440f94000c0040c116405520450031500e000b1070400642c1d841c4c980107000c0d1565481a542c3c05070050104440305c2c504441000f002500c103c04640b101c590300c048002c241d5000340d0000c41e00c881c584030141f5400b080c404c0c041c2d5000d241c0f110001003407515800080c2c00c2c0181c10307200e0b50040e80d40d00010070440e40a04122540f1384204046003e0102c1803940407034541f0790403140c1600030300401000085622000904406580d03028140005007625070408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 33548242 1250 33546992 33547013
    0x3150903050a0509270412030903050d0b030c04050408180a08060601081f030c0501320a090314030406020c10050706020f071208040209070c05250803040b040602060c03040b04 77
    0x3074560145c00c5818458440078807080f4403034500280310001d81c0b540382904250030318061070700241003810304210881c8006580102200e00845203018005240f28000700881e1402c0b880e010300c560440d1514042c4814420420301902450721007540d4019120910402d0042100c0c0314410445294040400b103006507003c0d01001c3d03400341d024101e0f0032100c5106082e5500c1d80d141980143c554920986d801c2c00507584c841c6500011051000c12041ca40b01401d0480c22014240c50505040410202d40c2081c0907204280d424000c50b040b00740368405c011304150950710303030b40140326003000352041d030724804400d041803a41c595031008940c58003400c203055900c601c00030750300800c100c03445c40703000b00603285c000f0355405003104640d281a50385800c2c52400e88107016070352601410030018080755203650b200040000a02c3c080d00321382458425200084d81d4880c84410b40a5001107140d40070100c0d01040d0440310340c01400441c2c990782d086070039644580c240d0304e180b448241c5028155020050000300414500c101c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 33549492 1250 33548242 33548257
    0xb04030302060f28020c0d090302060702040b03010e01060303030b0f10051204030302040510120e010509030a120209090f070201060608153304090605100804030c110306010f03150903050a05 83
    0x10f41c210150010400180501c030441c600c8a800c90f4007140003010f040e03041200c861f4511460030000c0d40c00d811900050701ca0300848500070310036034496070115090b4500790044842070210500030302c9281c0e160300d4080c002e4080c100d21140602001050b654003841c101c51790303e500d1496600e0304c900d881e02d0b158002c8070300c4070700500c140d0500d6020000080e441c0c480c040c9100031010030765511018469050075550950341410340640311a8101828805080800300480314120035505040380e9084600380ea8801a00442c201e65600c507a82c2410808525003040c80c003440340741694001c03c140c036150413054842600584690000020100500d0b03542c0c2031182c0c80c64110a4607494400604900c66034000f04102440c0340344525410100301005840e0280c052100a81001c0b0307003444070308a0a035070040c0000d8006001504104c2c01e0f0b0031210070302c40c0e0040b41002058019040e1003c56071189101c81c0f4410032448201c819001c0640c1c04080c0c0340c118880c0c2280b81781e260f0340e218505941c0103000c0300c482d08480c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 33550742 1250 33549492 33549511
    0xb0910060f0e0310020c010e010606080c0a1101050a140a0e060f07030207060f0213080606180c040e0f040308090a0302061b04050d0f060c0903080f16050102030f0906010b04030302060f 81
    0x1042c000107980c0c01c1220310071340d182454016a8600e440b604650a4031a50f04410007207a0400c003003482000c0d001200c04e94080c1304040342588608280000711801c0070355030381c0401c2035460b104c14020340000035000b01000c946038200c00140740d2280c006990481e0b036021892403140d0081c0c00862801d0070300340707550350300072125283c05030400c00322f9150442240e84e0f12400740541030380017509024428402c15000c0003010444090312030303480c00d000482c0d410020740c04807500c4040b0341000a0302e03000c0302c0c0342503a01070240c8448400d990b2520080c0a403030000141e41c1580811804000112210000903480400b260725a01a00c12a154441c100c410180c18105458403060240b00100384e40d16480c1d241d01d02140a800840070803101030a00d1822581c85004c070f1020486034000c18000304400740c04465041c020b1942c07141d60760f110556040200c200144004105500000038000780c207800340d0100b40252030700010344031982d9a444403945d140c4600c0c8070040158000c82c000400022642e0b070b000c0e9003c0f030b002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 33551992 1250 33550742 33550757
    0x1150507030c050303070216080a030905130207050709020306011418011119050304030204140105101404030f080702130204060c020f0415080304061106040f0b0709050405190b0910060f 81
    0x26520f05041d0f4004440500c0141c2c4245800e20f00a48200401c0300100701c0c0c1380103442c42403455100203207040058040c45014080140c0e80c104006d00c180d0441c0c800b190400c06a42e000c0d6101c00d080400380d0300a450440c00a100c4020340f00c01404030b242116101d1619030051846000e00d50700554541d11030000070034403401051060304442c8040b6148941a0341f064001c1c40d40d860031031042000f04c4202801d080350040e03000c0c00610240e120311401c2182002141068102660301d01d0804043d446250401484060988804010844540701801c2030902c201d404403400510450014102d004902c10340000070294224280503003410390f54403a100c403020b08049060100326207024007458041e4030a0129038000102007200c1a48160b0015511001c00068005410a91180f800e10302544e08003410003205070000c00c03081405012810000d002c007400c02c0c02145482c110900e00c082100c25141d10a904280740c0b00414502018030b24440c440b8500342e16140750030b122089138584c1d01d0381c10040900184 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 33553242 1250 33551992 33552017
    0xa050703030906270b0901051317040b0d0911010c20030c0306010b0a090e06060307030f0b09091b010201140c07020a0305010f020301050a06050705070902130909060608010b090115050703 82
    0x2a40c5a04c00594456441c1550124146000941800010480c41980e49403100780405030400c681d03405010347c2c00c25411a0242d0248404800900c202c3e8426840c11800040d040144216508801e12090081564101c1c0c3c544050055030900003424000b04a2600032009210201100c22480300710301018086501100038100401d18105013031300034001001d00440c0c00b540d10359010303030260041c0144202c48074503414810082a0781c0e00010f0300050030316440da1a0702c01542c440340d1040704c41d110020040b072454100102c4264903109140c404c841503040d0445111f200e940140141c46070381c820f81e103403000b00e81e413030762524801030700f003468102d80c445ca0b408000408982c0900a2980922281b9070059595240104207c0c4005107540070605001c824004003021500200d0480d0440300d40b5000560b50300407001105403444000e030410030381705142180349000e1010a40c84036007907518441c001c21048144200300220002e0034440c2c0d07650b004003103281d01036161217900a4800310380700341401100c4810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 33554492 1250 33553242 33553271
    0x1a040503010e032505060c030c0d09030905090a11040b070f05030d0f050105040b011d040b1513060801050604060f020709020301080a030f0e01050901030b0d0611130503030a050703030906 82
    0x40e40052034250700101e050740e4011094250344d0100d0a0b65040e040c03002d06150741c0d036510791000504521010303030040006803c3e2031000048440c10b6011441c100700061261170040c014115034013509005250034000520510750910590b802c1d6203061881604052401c01514415880082c0032229810803040034070000301700300041c044d54a403c000c0865410700c1004990215501607001c0380c4a01c1c10401c01000f140d801611845020060800c20500c000080022601822218004a4108036144803a004c0c1030355100161450107080401100d1700d9940350002c1740c4040080c0981507004034204000c000c5a0b009a903a1507081c0030f42c0c0180c4070031a80d50150311049070026401080700740c0000240804055001e14030910f10105810028604c603003440000301140900c8007001d040c0b40c3e0340c000140032692462103003c0302961140b01440441005505513126420407641c04040300d0168802080615010040c0da203000ca1990b40c5506018064a046001d0710031800c0036252180d5075400d0036000341 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 33555742 1250 33554492 33554501
    0x31209150307050c010b060301060906030e0a050d05090102060604060509010b03040302100c0c02010201050604050c0405040c0207090f06050102060c090d080306040b0d060c090504150905090313031a011706011a04050301 96
    0x8069440315922980700c0b013965803d40301d07170720309061003800100018007050342c0000e0001c0c1551001d08e40000c06c806d03c0c0190a10701020200050018440e00b22010741e190b902070001c00605034203900b83c0310680c40700b40500060344c4a50041c00d034080001001481252454005075910501038411120380402049084080324650009880042c0105000005650b0240585600001c0c04d890401441c03800e120803d2040c002c60040d1845103032240c209107542442001b2030406045111410001480f0520460000f03000c103210323175409801010005559001c100090b29061200a04030206495140d59984116400180b005a100b980c0c0c0303042c5040c2d83c41da1059907440500c00c603000038908002d0b583c00342414a003640a1807003541030101d6400c0944407182140b0480f10303e07600100e4980c48444009040d070107203030f03990003200e48080c50010501903e880040d1000040511984a60b46c81e5280000301d02030403a20085990b104400407c181090398014034400d00401c1012420592104d001a085d80c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 33556992 1250 33555742 33555751
    0x51201080c040c050309070501050a030207061517060f041e080d060608010b0403050c0f030a02090a02070213230c09030d110609030903060705090604090606080906090c0312091503 79
    0x3644801240d84180c02c0c1445007404540d0103007051800c504d4880c000c29640d000c58000c4ca81000400716108141031700a4043d603e14551046044c000c00703010001d4811200344500c42c1c00c4e0000c82c2a650500801c001182540c05036000e0030309040b060f603540e02c03a10f082e0502c128150b01d41d50b9560a4040120f80c5800c06010036101141010610701c0c640800181503807411b8110460540c41003208000103000004c0c0c0d803000c3d0000751030100f001b8808400090401c510711401039044055041041400001c581c010030b4628401c442c050a0b030310303050001c01c00301c03240402c0c1c4065115101c00014880807034a08015401186054990302e0009034401013410b041d51090110041800410848001d410a00046a210313409000450404084000281d40d803140500040e0038400001901c29064541204540240c240301c0010301001c2e0365480f000f0700410342250080440d0050401095003410042038001d0510002170091500009100514076580d0004130159841034010802c094604180409144103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 33558242 1250 33556992 33557009
    0x60501030503120907080d120f0203010305070f0603140a02030603010615050901090b07020603010b03090109120507030f03090b061302070c0303020106060f08010602031e1b031b06060907050703051201 88
    0x40c0d64030000389048204018011244d00e41101a007071150050009284201c131a0754902040d00951040300c1000900742080b40c6016240000f0005c800e01400141c044103c030045407100c100980d031010202d088402c1c540c1c0109140c420b5802184104100b900511740003a802000010441d5540c40110728200402c1007a0000c0ba00205040c2507568011500030000c2108500f104e00e0540c0e01e0380003804600c4140a07501038a072020003c1604120300358082c05d03415a005000050a00210001803c107400c1070b00224000f950341030028445134400d004003100300340d100480c0c1c2c810781c85004c00c0001480031803030b000100300e90901810300890303007940c45d04d00158001d400006040b824030304003c101c6100400f210090100110041089550002c2201e01402039500308840800042c01c0d41d807640d210b403030780300c0c017015040d4060a040d020002c4000c040c000e04620082d03903c81c000c0003003d82c440b0001c40e4850391100194001403000350040d801403000c0c51003440e0643c6000180124581080e0f0280c20403c507 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 33559492 1250 33558242 33558247
    0x1803030506030c04020403050c01050a090b0309060406050c0a0c02040507020a020d11010e09040b060f060721030522060507090e0106020106051e22200306040606111018060501030503 80
    0x70981020302040245003c04d0781c0a51605065413166030baa01074400b422810000700240342075402d445404900c01070b11a1888495030b03400c0030a90290341d0303001510141c030382d035180c00b020035070270400316013100c100301029194844805030750b400300710041900400380300c2980140d800340310060ba00d425091141c14402c041c4071261125220005000300c0c03542c10300e203004600f102c082c0700115110b0030070180c7c44581112840d0009001601264190091000003400c03450301c610011540c500502a00e20708821a542c100042d07520884d440c81042c0440013403106402c1210019004243d05801c0542c0c00291414051172040e601d2422040c45d0744241e10450060750348000c2441b15180910003501c0b00001040038000c020010b800181d18100300c5e1140c0c07030308540300d030180e52401070341c1d501725400038400d15100040910054280c1c0c0340c90303442182c0c624895450b040b03000c46c1d100d0184070305040c8049114003c00b40d400307000b0500710051a4880c0100000e100742c8203641c00046041c02072a0103984140091034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 33560742 1250 33559492 33559501
    0x30903120d050106030b090a02070203070506030405010b240406050d0b100c0b070804020604060323090a030806030f0d0c0302030909130b06090106050a0c03031404030207080d030c0503010b0d18030305 88
    0x40c12a14113030406030806007402c000c0040c943e02c41d568540c008005110040e9141c0030351002a10700007080d44030680101c0048200010b010040d4811504080c00b0740d0980d05002110300d0703400070400348104800e00e0160501060045a1145c00903082400c80ca10000a1840c0740b04d000070908a035000e030380e00003d128960044200144003e10681181203030030403100500b02540081d1090203140110000c142d910301d150308000611a02c04a40001d05106840090620400f40c076100c00d8112819004640c48802042103414000381c1501ca0f148400c010300b907005203108045440c4404060264214401440310b118150b458502003405840c40c00c0209400020324038181170070480080440c0e01c04c100600041040e150401c040320b0550303941c0e01e031501e41c100c0c1900d000e0700104180c00301c58480d544410104400c1503000200034003550025411500d902000324001c8099038030906180000820074801004100716030b1000d447c4d0301142041c04600000c15100003541c031500154160002600c82c820302 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 33561992 1250 33560742 33560767
    0x5030703020d09030203070501030f020d060b090a050108040c14030a060f02040e06010309030c111c0c0509091c0804210201050402040b12070506070f0203030408100605180609040503090312 83
    0x76000c98070a050441103d880e41d00025150080d45c46524141a160110306824503225811900d800c242d1580420805864150041c00c80d007043c566179004091505011980d5802441040d210340d51100ca0f52040307609009108074941c0c5482556505803040c0c12605002410318000d00181541c0181c0040c0c5552419044003101c040181c0301d681814580451980880d610500030b5070182d412200711110401ca03c80414024101070000c0c00221000392407000800809200d61401c45504a800d00304681f1103a034038946402400c1c2c0d501c107000301e40f101c01c1501207004250790b0354418081c0c0e6403845a00d002c041e00c4450a81441c4120005075900d0082200f1131605204203e0018001d070b541c644050110800e031991002e03907025151141202090f540c0070011f0325003508805603405011703261034503500c580b01c550720000800c0450029050a00111791400c1c503040d80400b1008400558400792071f14020b000c41510082c2c0113580c0c03030004100b15495030f2001c10800030b40819480c040f650340c03010941c48 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 33563242 1250 33561992 33562003
    0x1308150403090b03040812090f25060315030f030e04020a0c02030f030a0207060c02061908041109070e01111c0f02010509030310031209080a0305041d0903160c0f030503070302 77
    0x142c3e507003000600601001c00c00b284252818000700c504907980c6510f5001c0d0540c078060329108241d0407480389007e422440030a0800d0f610180b10505059848946c5400055003030b01c0018041e00000c4029034020000300d0090326940b400d4034020305045044070000d0740403a09a80c001c1c0300c440003003101c003181c04045042c00c1200b0803100c940400030350300304040303c0c0703000f074841d50b42d071040404200c1c00d9103442096540f8002164811641440304060400c1c0814010b04212404c84042d2400120040c14001e603040143c203841c820b6201c0d56881d002d40d03100c00010740314003a1a05080c4a07a10569507005651108130717040741941c5205889040c0c1c1b0030b0f0411402030a48100811340d0030f01e60003c4c8140b0840c4000c114210003660b50040012201d101010011111001c403540108040e10a80102da03080c15001001001950940c00398500b1700d1409040500023014243d07000303286540708004600c0101e41c0480503013007403841540e0000485956504d4000c0c020015041651203400c002182410190104035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 33564492 1250 33563242 33563249
    0x1020a0b2805190e1c0e0901030506090f1902100c02090a1a010302040e0411031606080a06080c01020606040f0b0402181017010e07110f010e010606030209060d02130815040309 77
    0x824800c4061303440d002520382c0a80c03100600e000d144140001c0025014840380b82c41180040c008107580e60303480c140180c2d105000d55a105460203a10030000ca0b0141c041103800c4941c40c82c0e4520710340301800d6402e1101c80015501514100803240b0560801a80c41c0100310303004480020011a0040b6891440024494001e910f9418548104401c0084100800c1347c1a4000d400c1034440110b0300149011900b044c1003500074003445482c0590206059811011150158282170410060b0580f28a0043d03954500840710318050f031302c8000041d0942c41c00b40c104180f032104000c1d001c640784000402040690300038034506080c000005948001d242410203160000c1c4c00341d4500701200095140c214610700b43c0600500d0580b0b4450400100d8042c010700d8070714244c4400d10222001e00307610208050082c2804080b540b0f0a5080c0900040c1c001c0c403d00a480c001400100218070f00300d2580d510200031f50040107245006480d442002420850501c8098a8052070b04004003082c035140c9801024061b5540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 33565742 1250 33564492 33564541
    0x90302011a0409020a03060203091203090d09060309030509041521020f030703032a0c0b030f0a110409091106130e09070308092e03020a031a01020a0b2805 68
    0x30f000380c1c0581ea6441404040702d40080f0010f030b03a46c40c0e03640b4541c213094200603803c0c40c0c4000002800000f14001500c03050744000c1c0d60310014078640b00c010880582d20701110280025800f409606003a20345503000c40c1041070328803900e01c0c0742030340c95000c10040c0420300c03803018142c0021344c5030703100394200017100c54101c10049002d020035904568001c2c22040d142d00f40c811000198002001d007800320032904c0b5820b550020300312007580d03a8441d0074001c180e000310344151007415a10049816002d01d8000d074082d16030160540e03800c0c1030800040030002c0034222000e552121002c40700c40361a0719000300a180c3c15640540301c180c01070a08184180210010700018000c0d800b1030020000b04615400b99148464111054208060b5003001880768444082412103000c00340c03903000d40791039019402032248100710388044c00b010110300305294060080b0302030a40585c000e000c200000548400300300d64002098600780707013030507d0315a61000d50300c0000c003020786003580d60b4140300010f203051000160061105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 33566992 1250 33565742 33565751
    0x2306100f0303080705040b1204020111010902090c09031002040605130b03010503030405150c060708060a06020609060402010309031403070e0406120f081303050f03030106030b010f171306090302011a04 88
    0x4aa0190403401807101500b040003240104541d14444e50442e070003021150289a04d542c0c0d1000c21201c0601c0c15182240454003189031a5000c25040c02204041c80d0000e0400246130380f41c2d4103a210613030100403c0b40c0c1c9800b681a040028401c1032002e04007403c4030740da800c2d03110103080144042c0003801340c01180c041201840100100d40c0c2c000700700c40c182c88060315210301c1ca07013080ca5094030038080c412481d02e080c0601c00402400e2a8030080940c4591004c03903000c000280d907080249d03140c1e401940c010b083c1e90481c0c000100503502a03040010742500ca8a0a04410311100001088540081c1c4410000400410076040c051900d80503280c00b801142210351400b81266950b403407030303808140d0020441ca00115490f8041c00b0700e400030700000c2d0b800031300342c881a94035540c080b51039a100b401104046482c1400440241d4401d888400c01441c50b40c80d039140554000641c281206001030190001071041e070b40c3c0c0310003e0058003400c0c420b40e11940001c19108003810459004401c01000140520310f0b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 33568242 1250 33566992 33566999
    0x1050d05030d020901030209030f010903030b0d0302100905070f030b01060201110f0901030c050f0708070204060e09060a1815020307030c030c020a0213090f08030906060303031918230610 82
    0x80300b168804501c400c00107a8983c043c0e00180c3c081d005211031650706008a4151646519040d082417090070712a64003003104104503010458440da14503405401640100004a07443e80a075101c14907440c0a10f0031160255501c5100368102074540d0011208965004010071490340c0900410310307a18403482e420f900344400300140c28920f000303604172241055143d4402031a20360080f01295001c10161000c141c2d00d0285060040b01a84902012409585080c40c00603460018500c020300803955003001e0007003503d42031300c031402800424a107012003501c0d14490400150b501c0b00c440c01c04641080025840e490101806006c0340c51090030f01060500b4000800305c82e541c04644c42030000c3e03044030540c07821410068801c0041c02800001014095400e040c2c000f40015500694421007110003254400d540d444203054a83c001502c110800d10546541c6031ba025415410048108034402e10070510030516803a144088203c550301c0144400c010901c80c5142d80341404025880340301000150406c3d80b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 33569492 1250 33568242 33568253
    0x20d0c031104140f04020d05010c020109022701030b041e2a1a0f0c0f030c0f0109080d0b03010905010f05090115030b0412091203050a08071107050616020306010305011401050d 77
    0x404444c442041c5500240c00c565844404c25404c82d0414001c020f06a100c3c1d0029008290704030342a40300e903113181d400860038101d402e40e40f10307282141c9000d0f00c496403a541c0d504c0003a002c00740c01210301000303a4010711007020030700c540346685900400800100b441c683d001d1900889000c420303100b00311440101400540d0440040d0300c241c00220b000540d58a8034980d4145650291280001560048240403181e0850000192000c4014003083e10005020708000500b21982e490005000810521400240a165600c401d01c0d00070090008521501c4658481e400c46a1043c1d880e03032400c4e50b42d400c5c025125401d101d50300704e94580340001401c003411600c806003c0360005100808500c2c1e41d8000c036010910810f40040101034403481c0a00c50101e624000c1c149030820b0004c03400144000b000520060320401490b03400a607402c024000715410038060050741e501610015400202d80b10070a40143c508004040c000c5000e0000000c0c420b0300301c1540011084181d20803841150030074100f801059 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 33570742 1250 33569492 33569531
    0xb0108160b03060a2106060f18090204060803070b01030c06050a0806090406060b040b040812160303050406020405130f0c020a0b01210c03050f010b0402040f0b03060607020d0c031104 80
    0x8480030034894a82c0e03103003c001450030307182d0b0300208842c04030b9008850b02680841c1c4d45c01e180610405081c0101a00c941c0d08100c0e003401e03481401d10310f420b81e4890850250442e40309200700750010308046070240e2602e0b80c0030300e19031007083e00f00d4100003620010028441207074248800b924403440e04500d405800c110080a5203005030000d8400c520940200c0c080202e281d00250040006d5041992641d0b581d207171210031368005108450340c034012100f4140d080f84218085551581c05068000c0c0640c3c0c441e10110020540200111030050b4200b102080d036030b032445070b1400c2c0c8014401010a01c107007002e440b84281d0756026030540c1035500810038000041c2d0f1a41c5050305540382000340351f8440d4880f03402003200c00310100d800b6003c90300082c004014048040b844200303111004009204a80b45881804204e2141d4460340700c203044040002d120b4058038400540e00801c0007880c036400d014440d00010281041c140d0112403442107400b0030410096055186030a29074112410000e65880705406011203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 33571992 1250 33570742 33570749
    0xf0506010906110a0203011d0c09010302010503041b08010614030c03030405010525080a0c0302011d030307140c030f07021318020409050109060608070602120c0c0f0a0801050a090b010816 82
    0x40b000900c3c040c20490204212010103400400a10180d040c0d082885000c14550442044900942960303400c24105a41c40d117040b0707513040e981c0f18a56135543e101c042890560192040300d88180380d100023042c1074240240d02c044c24003400004041d0490204140c602102e840c941d0b8001c0d04140800c1099030b8210302519104660a40e05402c5409012000327000c040328480c000f01500c0021889d0f0f80d00c558000d0410b0002c03071294000700000501103600c0c507581c0554103070b00c2100c2d510400c00101402d10441c0300701c00e080b8005071014203009410305032341d04580000d40c00041c40000802c182d404d602d0716405070040f0a000400c1004403c02e20b00c4001c3c0040702076800a8055a15444040704128003503005103c110b411110411905803242071403926180d00703104600051250070086103c0780c800d40112a54010004000c0000795200001e00c842d504144000c10760144024000050448080c0580c070310907001010009196906c501d000030b09040107800508440d4441107603620035840105440054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 33573242 1250 33571992 33571997
    0x1150302010e1c0803040b060418060c020f060f0403030507080903040b071112010e060106021209240a0203030907150f12020c010204030b01031a07090e0910050711010f0506010906 79
    0x2c101c81e0040740300c1ca60414040d040c0040c0c0070154105000180001d035010300d108941401311a01e03064100001d450400c030100174110124031000c400590140d0050880c0280e0740142c40c1c038001005c801c10708110341141d0022236284540200001c060341442400d510050604080ca8242004001c4950b41e00480c002d0140c0b42c0c030000385036403e020041c2c49800e07152100400c020301414024026501801d8407003945a8280b28200000c1442e50011516250580070741c510907082407034413001c100c4209080c0c209882c00700c92a0046041c03e5000500400005515800070b5507a400c0a507000b40c944680c0d80c3c402101450b101100700c01455210000310080c901034074000000e84080e410400c02407281030a465075648c8000741c00001c1044001c85a0b0490b806056003000d100b414403420340b4080000c0790301d0b40c0044c405001c18441038580000c3d180c1c00081003800c0301c0c55565500d541c201114400d480030702c00315841c02c40042d0340b1502401240d8403900381780004d1020b801c1090001e008012507000d900103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 33574492 1250 33573242 33573257
    0x90f06090d030c0e040e0309040f050c180a0305010216030f0215070f0201060f090606030605120309061602030105010608181b06071401050a020714031201030f02040207060501080706110115030201 86
    0x80f032489a03280c540b4800c0020810004500c00304426541c80d0b03c0030380118061410180101540ca40358800c6510500311161030504c1e01d80750010121015000f003050301ea03c07000101020020130824405415000c1801d141081d84405a04000c1d03d42c031010140c0b002150300007100301124010050040360021a5401c00e2400d21021200c00e030f01406150b004024441c0e2174160014002500303811090440701079031400c108954645041c0306503040c00681c03100c5242c0c0100000384081c10142c00600070000303600034090b81006140d001900b9039001703a00c1000007450728000d021066540483c62424103101d80020544211b1241046044c0820911401e100c0d80f40413480c41d00303100059400e1510000b210000300900d181280a41000b5084803a05540d4004507003850412240000100c8140001d9601c1030442c503840e43d65140f20851303690f0002ca030025001d1100500040543c0600b0b0301a05228016010060400304000d143c008203c0900c2d02580c10040c0c1600203060000fa08020f50341c080c60701c7c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 33575742 1250 33574492 33574511
    0x102010207080f1e16140a05060906070306060201150b0307090308030901090606050409050a2405010b0c0f0d0210020706060302030d09060f17130807080d05060f0a081911040c0206090f06090d03 85
    0x5003480c04047c40580140541010480000d001141c030030b1240c1c80e152000c00c0000d0300c840040f0f08842c0c44202c4652000903079841840a54035450181d684880c840c1340c569152070b165034810219400940305035030940e450350b210404001003405400c02030142950208a045210740701c01da40e4603d071b060040c04c0c04424001105d1510900d01000510300721461046c025035960b8481c001d000d80c4100050101c500468840071000c0601144643d010100c50b40200b0b0300031450003140000f54030600d41128583e03558000000181c80500955000a840da03c900c038441f407614130301800003e403c0315440c0800a0951244c50410380c8030703d0f102e0704810304291041e1403540c0d0380380000c01d501c102ea4000d041c05034003180100e00004c803500807c3c403903041039840007800c0780003c0600000c180caa0045100941116541321040d0303140c4504a03500d0340c041e1450540d000300305004034013100d04c0c8120880068011400300603d100c001c000380140c40010000810241c80c0c24401a078032081c440301484201600c924610 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 33576992 1250 33575742 33575783
    0x70f0c0204050c0f0c07030c05030a15050a02070c080105040b0703110a08060d062a05070c0e04050c06040b0d06170a020108070504031a06090a05160309020102010207080f1e16 77
    0x480c54014010004d5903203082e01c00c0410b0755240507202c00c4580c03190010f008519800c01140c410301099000040b0314560952040410180c80700a12101c015907007840000702081c04840c40c103006001546c00001d1900742414144109040148110181420018040f038071114034422143d40b00001d00d080c2c000303603e4580024183c07882c0c813000a09002e0a01c2c40740704c0440c050b0a001c4902a0650103d010411000300d02070b1f03040e0245d680d000c0e0034842900000c1000100c00341100303500074490700c140c0c4c0000b1a0b60f400280c040c0c00c660012694000c1c08112a003001d425442a003000d014519140ba000c552810700c00d5aa03001d604000904100e0400e0100784c146000e44151000307141e00c003d00d04003515817828200006a0f046a5051003a00032002061246603a07100f03180c010710180c1410580e085101201364040c250701d00c8103d0440d9400c000034800301e8508800b0349401c01c100c0722056507944c05003c1c61526856101320016003da802c004017107031840c1480ba0821960ba00c0350791080e02d942003a428 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 33578242 1250 33576992 33576997
    0x1b040207020103150b0316080606040626040c060e01020304050901090c0903151b0302210720010c0906020615010e18040f02090a0603030c170c03070606060305070f0c0204050c 77
    0x3c4e1035948440010100302000c040e8042c0d44982441360000c00e00380512003089403001c000341c480c0b5400000400040c050a03200701c66038071030140d5041c070500c05a041c03c080500c03003602c115400c1d202c049280c0e0062190b60f80c0001d808094060900c0214145814900007880b10107041c0b04450199503640c1d51600741c0f5014080540c01550000ca8400c0107548402050000c1e10750840e10385240010a07003d411300034080e00c20345e900450503401c07400300c0c1004400c50700400c45000c0c050030148502451a029001c1c060070318441420310b028004030b1801040040074040501c240c01450954200c007080149400e14007484218030002482d0813160b05e804800418000003100c82c4480e2300d113880c0d00c104028490502c4a0003100c920940ba103000580e9800700c1001190461b000c0140029174505007503010580311080740360f6006c08050350740d1070109584000c0303245900265080b14010713255001001901d815202d200d030b110303443d4244080700c03441c180c0d00244080810040248a69a1180030405101d0303076205 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 33579492 1250 33578242 33578261
    0x120e07051c1101030203040809010804060e01020a17010f0e0f0406060b0403030e15041208030a020408011b1103030601140703020c04050c090f060c0c01050703020c03030403060c111b040207020103 86
    0x40085072580100080780400518503058580345030800003081e09510138400c50380300302e030000401c0303041010b2440110303440b00d006030090343d4164072081612401c600130310050008240340d464030f03102d030440d1040000389200164001c1e204100c0040e000c0140541c42c5601c00da02090301e0782010866512490480020f00250300301104466004c00c001c0201604404451400c0004495840000d40c8542110240d031280b03004400131043c030301c08000300091440c00a03581010f02100c0142c05d00c2d40341c15015007100c0e150488101207860003542981160340042c081700c05200c40c40040c510f0352030070000181c107809907055030315012100018030303c0600d8400d214600300401c004205200300e0600314100b84070740e003140c58202d01c0bc00d111408a15240740075000c80d664070340c140d80034003800d075278030340066440341c2180001b503056004554241285030340500040014502c2628002001c1d401c0840c01050681c6031100103e255001d03683c904002000f0607034000358200100c80143e0344003003e10040340a404c0801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 33580742 1250 33579492 33579499
    0xf0f090705040e0709080c0d020312160605041101110316020112150b0c0c0102010204080d0806030f010f050a0b040c090e15061308060702030414100c150b0307060906120e0705 77
    0x20f0500c140c1e0ba0f0300030940c0d0121120301c82210107a58800040002c40c501e180c00c000d5140c2c1c0545111001d09455202501d680c4811045d0a820080252100381c103480003182c003210386c441c200340b030f0404035030f0813400403e401c5000d07800450421100f16031641003442400c1c4041c0c180315029101002c0e50016410804030740401441d48017020745c1c0d64400e00b281f42c02541409140340030b00c2e03564082d154414429102100c0d500d4000702411681302000b61210b010251026130140100700801009903008d01810340810f0f0780da20001420f143c07001c1504101d4401c0e5600354447c5d42030004880b41c441d402201d5000703407411b0303080c804100d0b00d0b1040c85600141d01d003505140c00c014085010707005881c4850020040f903440307400350f0300e150f903078030781c080380c5038425801104d0840c014101d05c1d000303a090040020b8000141c50400e00c1200d1620b03100d01c031503c0c0809030030ba0f00482d12110110224141444403400400141c01c0140450b03090050160003040045021034801da0349e9010f0300c0110b1402c0003401c00511014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 33581992 1250 33580742 33580769
    0x1031a0c0708190f031a04020a09030b0c030a11070305031902090d1a0f19020c0109060f0b040b010302030106020312061f08040309061e03050901110d0605010206060f0f09070504 78
    0x103c4501a0f10051101107000c11041030f0194881402402940c01c2e40c0c00100940f411801071108004c002d401500342d002c2040510340012001580c9200500c2c001c1c0e00c2c081c2c010b501c900d4055580d106440d6154a10400b201080c40701c0e4002a03000001c5c2c0b904014500d4048130a54890b043c008001e005416031658406510840c0e031050140440a040b04107074a0200301c440c543d11010460386104050318441c001c410f25851043c017205c4240e02078101003445800101d002d00345501c4100503904200c03060a034050340e82108821502d0702c0d100301c85005100b03007401d6040d5031410304041e440b4014803100701c45840e0b9200015a855407001031011600060285181c003e01d41c203200103100c1c1e0800c48084010558001c004582580a8602883ca200d080300106110f0600c402c004c8001d8a80a01507142943d01c42c02815a5002003030043c111034080318800003001c074600400203260600182c6030034094410031004240790345613080180c040c0d40d8162a085029140d00c0e90403100e03445560702030464507219 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 33583242 1250 33581992 33582007
    0x30807111204061d0114070311030d02031f0e060d05010f0912021b09010b070318062c09010504090c12080702271902070813091401031a0c0708 63
    0xc0c000608156541c640e031300c08142c0408040146030b103400081142c0400d000c508007209000e60a0004c0280610031b2030801207811185410910716008030f403030307402080e8001c001c0110a00b2001d00520352120120610400c05d440d002d805500011b004e03011a004240014451090090942114455107041c0d9800c0207010168100289204070480309007005011381c1003d101c174803510b41c8000103011001001d0340416445c0c0482400c5540c0640011401e00c03241d00c8447d04061079a0b00800001e0400b503e51040601c140390707540300328489041005400941c0c40a00303100d5500e41c2a003203030644005407400552009142040e0f509001d0562146100407260599141000810405002040e00c00c2d03562909290700d82035081d240c08100340148240700000d800040c1c20f504188407100c0c0c0200204401480c0c141c458642e50304680c4241001c001071464080c4c2000039010dd803240c0021568003051909465041d039403104401d466551912040d15042808a0000c809a004654840d41e000400c50f640300c61 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 33584492 1250 33583242 33583273
    0x204030803040807030e0a0807052b0b06090117070306020901030209030a0c03050c040501030803070f180602071e0605070809010509090a0c0f020f0d03180602030f0f2203080711 78
    0x1004d0700f1000a40008096a96428508030903401d490040f0040c0524a00b4030041c80768000340300700703d0f0a608411180804840c04650b036030341011070040d000703801e00345061010701c02404070690100b9228030580c1208044e4110101e0f0340d42c1941d500c0440940d031107a4090040300a170003483c1429074140541c0210000304920004441c0071644100150b8400d6140d0204000480d03034244005420109c1c100b0015036018031460130341e80840c00da030410350b5108160311035901030b1000d180c11200240c0e10425042c800d2101002c4d51000c51686111101d001e5802c02800910500a0450081140e00c0105070310205a01036425507503903140261203500140b401e0492080a81401000b80e8042449e88040c04101d5101042c0084440c41c50002041c07029851413044009110166020300d6060103010704200040e8030b400203502618000049080500b405d07800117104070382c00381c80034031030040f5804d0082c840c40e071000960398229018248160325903150201910000d150700480403460269103070311000c520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 33585742 1250 33584492 33584497
    0x5270112060c0207150302090307030501060801092a03080c07051309110d0b061507050a050102071202061b030c07020a03050718020c030d050c0f04080105060909010c0f0e0402040308030408 83
    0xc0c01100c0500160100348010ba8491368140a462926071490740d00781105030086d001000b100c1805411900d40c01d54070b4440a085501503003185e03206946441207a01030090015007c480c2e60301000c102c0b011012040c54468003910144401071400744042103e02d000481808a80001d040c003620100188184903150002001074120448012050751080c100b0340c14942d801c1c1d020503900c2528a01c940e00c0d02c070304219080c0751154040300070305000c100c2a00042e106100d014545440790b00050f031580700500e402080615005001000c56001a04000940880303102045000e80511081641e84c0c4404000e080c0b1440384000c040e4200300e00b41000400c0280010321407040711000319070001e03420b07100140342081e4801c00f25185401c0e0300601040c40b0a00080d480726422407403100505242c01c645e03000c414001d81040d400704405075076030020441282040600d5541c0030042400030415900c12502c081c0c1007c0200f020f540400242e11020039840c0c4443d8101e80103550014956038580c42c0c6032515800e142d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 33586992 1250 33585742 33585779
    0x60e070311090108070509060f040338040b18030a02060109180203070302100203090d0803060109090b0306150f0301020d020306040c090303050403080f0f0304060c140a09052701 78
    0x2031078460103035454001a0242c8060399016074540300d031910b800300c0031501c0d50090440c00303601440401125082c41c0130b0800602c0194818864140c07150310780070351401204010a80b07611201d8141d515003c04036454852a640591310440300f042c1ca40b1110764a607141600e07444002e4003444001586041c0710340003d07100d41210b80c2c802d002e0006500c0041c1200051b4220540250543d015403014401442c3ca8049a0301c100302d51f1040705d00700703500c00c0c001a031144610384064580d44000000c1c40040c1d680601d05801401080318140604820000801d541e00c10040804a001ca04604201780030365038030f24441c03c2d4100c01402952034100781c1e0340240080d0f00640303409114515005401414600406600003107070307059101e0b607041518588559402c0c0c1c1c0301c4400868551820002c141e80c0d24a090003a40c003e600400001403040002800038185095081410dc205082801038402c070962110464090b00c10644a50024052442000e5064079030708400000380e2414200101d0956002d03107442c40705 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 33588242 1250 33586992 33586997
    0x30070b0f090c1512090115030c030311160e0a0e0d02030c010b0306010e0c030c0c03040b071a0c0301060c0201020c041b080f04030504090504080c010507020705120609100b13060e07 79
    0x19012420100f0000c83d1224071410315429050001c0d0f080c8191404100b54880001d03000480c1c0340c030200703000c891072503201c1c0c2007210b4400c1c2c000400d2051651207580c40c16490300c0003001f4208004481d41501502c1c00503c15412003000c2600000c040c01c559800c10b09803408018229000103071702c078102a44903002045d680c8004d620b04414683e441c81e0001d9214102c60000141003620384035901901d10641c4010720515030f0140402441d07110100420040004100c42c03801c5946481e11840d20300c500c83c0e19420390711802e240500500440060007030840313045800b203060205a0048600c0140d0a1a00d02d80b01107134007924018081c0001e0812700808103c016265694184a554406218142c071106480103000540e0602c0248043d41650b4040c42e00103000303091140c00d080922424600b510800c84400f001600190700c10441d50501200240d00c001e420000b410861600709002a59400081a8aa1680d844448020440d100d10002c4088401d05120507c400c0e13031201c00342c4490078010b40b100d000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 33589492 1250 33588242 33588253
    0x2070b0a0516080606090108040c0e04080712020f0d081506040e0403090b0a091a0408030c07080f010605060d0510150e030d080610120f020a020a0507050330070b0f09 73
    0x12051040f08428450740307005251605043c082e178011148050010f208494945110a001c6a00c3c024070388a01d1040d4030420b5059510002ca260000a814042d03410405540c4079120800c43e100010550041c604290f24240034160707551210401c03a1038ac082c241c190440c0f4009001300c0d14240b03003060548624000d80728050316070303560190703000644290418480060303129807040c030984000348142c001402c030b98642a81031544840d00213046912840885110340d218080070801140117000010480c59240b00800c070f8289003201290036882114400c2e103407031303a0f07440015010b01b40190518010740b1170724050150b801017525015182e0a020403125119205001c01405014490004c984c4201c0d000f900f24100b00303601c160141c542c2c1c2285a06c40340344585644030040410000c0c400380a001071160700611402040342440740c2070803141d8100b0340c000d8024845c803078003440c4420b4108074442d48000c0b030304092030601000b5900754001e40c400100003490b06802c1c8440014000701c220b00910030602a01c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 33590742 1250 33589492 33589531
    0x4090b01020d050403080702030a0212030702120309030a0602090a1508040b0f041509060b060c070e010b04080705060a03090204020d050f090a031b0f060e1c020102030606180402070b0a05 82
    0x241e94140000c2d050b40080c10401c410300004143d84040c010172417001d030485440ca6026800181703071004a10301035002c5d90002c20f40c94294034248a01c1c1c00302402e020081d61403c050340c00801e4941c2c00c1c192002d400740f0380010b40c0345425120190307220020b011000401c0c0341400c00310001481e600c010356095a04114100205030b41040c0003c840c2d000c5d5601c4035005d03510085000a45d00501b03208482642c58964600c6c210842da107841c8003d00502c03440801410314a4149001030021903010307006401e07640d4090006000c03036900003942d60255203007150307041d480300290348007140640186840290440d00119014103028000c1d00040d005004c25562a55103548a82d11580d8400b060030026000034000c11507401006132604030321061a010710303030a18030614540c40f0300c41034070490080040c86a100000c0000e690401c00e28425506569100a5245080100c001259030149004151003d0b81d5180180041d68950b41210980c6904c0b510240007407070001e00c10401842d00f01c529540068842000e103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 33591992 1250 33590742 33590747
    0x70e0a06060206150109030b04020103140108072306090108090a080403030302040501200a03050901030b030a080903011d071404020c0f0c130b1302070804051f0207090603030e01110c0a090204090b01 87
    0x407113050043e075581e5103c2d45151100214400051700c00c1c0e0600d0380d600310380300304a82400340b00d50117403d80c18014801c46250400c94190343c6090034680151542c01c03561044180c0e250001c42e00c0fa19402d103424174094031524072450400002c918000c4c0b034101d00040010400d86c01d81c01400855030241c80d6005040070b11349111445019840360040150000312402d00040d01443c01303440180010702d0300141c01000328003c00e00d0502000010703580e412010400c2c4820385401d0048481c20240e400c18014035000303d111103990768010303004154a03100181441c90407502c4039419a103011a05404503942e01004010064480119414590203892206c0d040210b01c00300e40600302d40c0da40d01a14900c040f04003201340c1e00003908001c2045035040410000010244e03220440301d010104d11907021035046c01c3c91600a860440c43d50301c038000a81c1460010004a41c100b1241001c0c65801c0c2442000711440c00d80c2c40341001d0f81001441d6110750011404220310400f03078082c10581d40c0410b0b080181c00c0450006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 33593242 1250 33591992 33592021
    0x1110307020616110d0806040605040204030503040b0c030f040608060f06041505220b040e160806010c020a24020708160303140c0604030309060506040905030f0903070e0a06060206 79
    0xc10000d07912100202d142541d0100c00344900c512039181941690714425400c90900940042060018030706a0901c9400d02c3c00e4400c20780100740442c0c007146401e2450383c809403a80181d11607240740482c003107521040d9900030300440301881d407030140c403070381c0c13191143c101400d413040a607021801400001201c030303145d0600b0011901074950a41d0958080c2038540411219540000902c040d0402003440802c00d0080402d80344d40a404040d040030389850401081110405000701202600255244002800754101d070080380c01101c01c1c40e10364503250540c001700c0c04000c503940c03105001148440c640d0152201d901180300e51120340307038251141035549002c850b43d540c5130b000d40f2640c424114070341040040c0c010300b01c003400c650385411094100800004010700f010740c11901070300407039164401e240030000c181c8a002d6104104a500300448044d0b52039031603481c007a6902d041c1c111800012003003201e540030841d031030003000d0b400c02d5001a407528408840280205204400c058880c08010501e46200c5640 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 33594492 1250 33593242 33593251
    0xa0e010504030504090c020304091109030f0d0e01030203040206130b0405040f0905060115020708060108030301031e0c1e1206140f04120c080d02030702070609060921050f06090a05011103 82
    0xf43e00741894201003007100248828119442944020400003409401ca07005219892608a000540f100c05040626080c0140c00490801301c0e085000490380311900300301c1ca882407103000e10300180c40341d44030710214903203101d91440c40030803400e041c00000c1d2019020004200782c1e5000d850074022851540303020025140150001000f82d00144010301820180c00d007005250714082c411070707525036618a0705904149007030300809a20f030000001072081c08408a070030030394607100003204104500c040e01c1b0900c44010a010740d030100700c544d0b403a4004464166503540c0c05000081c5107026662b0052074480c0c004c01c0340d40c0070006252081000520154060444684035035000a511030b20024014001c803644040c85c07070212100c5030180910080c2c0708880c40698410f00c4070340c004011140c1050700250001d10180c0c020001c2040d800d00502c88121103040c248800e815003006240103c40c0340c9072a50070095a880c080549206d000e04000d10144001070904203d40034400800c0424191440c1820b140300c01c07503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 33595742 1250 33594492 33594497
    0x31b0206070b0615030106021c2c0a0b0c010b090a0b010206040308060307090515011202040501020304090b03010b061c061d040305031305060106030e0105101a03090a02040f050a0e01050403 83
    0x11000002c502402030990f40704a0041c02c140d004c40d14035040031140d0b0000e030402d6005a1010340385032014101c49500d214801c007541003503d2080c0212080888000580c0341294061a060038440d499490303100c80c0c2000380030304511003a03c8a844000a900800404c02c0c03440c412031000000c140521164400d00075040810f0340034007116903c549084d644805d0241500c0c0c0c05202c1d81c1c00024280c1468803a0394010710307a01e0903036004125400c00040c404016a6004004580b040000b00a10703a000411102126050180400d80004420001340106054403070a41c1214000419040d01618090361060425800a0400540d40c449000ca5a800c00602c1e040d0a04450280404c01190241b400b0b1507001560811030000218540d461a00b0800b00383e1101d00800c0d00c1d100f00c80140a428021154040c0203288829a45444c10454030000b0702014050380a01b88008045603070701c8400c3c8041441e80e90050014450780d003541e44c0340402403200322001e510551621445184044040c0140c50107590980d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 33596992 1250 33595742 33595747
    0x90f0308030c1303021309030f0e0a051005040905070c020a0602010b0117090102070c06020c130513020105030c0409111801021902060912060a0606030b09011d0a0b12060103031b0206 80
    0x24a40716082d600c00300d0f91400041081d0303800001a40d074906000c40c0a045801d02140c1140b0600c0c024104035481c14501d424018410f9000e03515494408400084903c00c6844603900c40c0c2d1000b0a84107881a0b0700700494403402c1c101000ba545800030080d101c1948280d50508085594100481c02c996459145500180c0511042d01e100e10300b0300b42d001c0d04003000d07100040ca0461aa69030030445c26259011074050b03007103050a18060700c2d013000009201c01c080541440540f42950050304942001a4000d040c004007002069129130300d1016140079100d035038420424219402e10f250210b4010164928104403ca00145160751000c0307a00100b04007801ca2224100b5665420450706800c40c1c90007503005034121400c14403440080002901503038440e400081e046041000040a030b034040e001103401a04280010400c030411a540b81000c1d040328408100300b902d84080c04005001c07207821269028070700c00101c9064000106905049034440c0e1a07581d002070003c240c3d12106500c2c2000071b90301040a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 33598242 1250 33596992 33597001
    0x3050306010c111906080c1e070516080304030512040501020303070309080d0f0b09070504050105070303321e07050a080604060b03090304090b010810091a0402030a020901090f030803 80
    0x6002e0010714244a0b45101c1245808100800d0440300c0003659141c201c28901810891150010481c0303801c40038005a443c81c08415041e4a051000035000c0d122040500094072014000c050040c1c030240d6202002c110b007055561109117031b80b0f421038001950301c0e0062804031511540d1840440c0c08507041a0007640c19a0384880040c0c0052840007070a4650f02010011407181c0c1b41d140c400d034681e40200140000d1718500001c02e2000600e4000c11190a0290401003408560707000402c1e42e031103503890310300031440300400d1148a030705080c180032100096055800841682418040d010722460360b8440c40e0040f03444801c0d4500302e440c4265552000304a0801100044038821a410355012001400115030035646001c01419540211043c040c2d85d00007040c140425061030042c0e4590010034603098110341003815038905101081c0c803601c58442c0e036807000c8810b49040040e0414030088014001c54481c500444040c002c1d6005404150004104290118454050514200a403508001001d042d0750340c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 33599492 1250 33598242 33598247
    0xa2304060801210b07091d0103050304030b090a0519060b180c0a0302090607061509020304112b1103010c0801152102040602010212060f150901050d0e010b010212070305030601 77
    0x1903080c1d425442c00783c0210440042040f44400b42d0041041d0354501d04900c5c502501401060031602281c46042d400400400c04a00004161420f8030b8105800680c00d8a80c680300034a041031180009010707004041514204003a0703a404001e48500850051200e440700604200c0303100019100d004005c0b5400000c00ca140e102d07038010780b02e404001c1c10014a4036031031b04002051500040001c480f5140c89142c0d06010301d030402c5103800102030702c50301941142001d59681c250381d44aa0b1000c0e00aa004072182d1400030110b0111f8840c3e90b030449200c0c2e00038031150820312075004807407903034074065820140c160301c00b6440340d80c03400c2c103d0b05282e004110204030100100c42c141901042810b01d081c054010540d07c0071f070340c070082c4001c200a400059959551071110101075000610891103620410030f0100c80d5251240c1c480f14003c6402d000f00e40ea500c540005071014040d40c1c2c0b10300c014900d04041100c5e0341805511200104200b6000c80703c001c01c0e10061aa0984940c0300010001001440400c03210350 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 33600742 1250 33599492 33599519
    0x60519090b0105040323150f04080a0c02090f0609010b04030f08090f0306101e060e01030e01271104092a0306020705060703050105030316030c08040504020a2304060801 74
    0x980501d0301c04d141039500c0d115100c0304e0184080300c1300c403034420000310320401604000d0360000103850000b01540340741c1110381c0c120702000100701405c00c88000a950354103034421080005800e034010248001810108403c030006541141c01134080c2681500200f0280c0d0302c40207a84c101e0b0381c480c95a0050803426500c480c8103030000c20942c0d07041a031b40040c50805030303400d0054522400704a0060f010340c614043c0740c5c005081e0b98183c1b1400350061800d05000441d4848001d0b4900071080c20080f488010710030a160062000b481002003040030b65035540e200c80e083da08000b0116014060072551110390384108000c0b40e4800d07100628510003800951070b1002d42411000340c240c1e000c2c4034403c00ca60340303481d608140d0317208004c202c0f40782d0044010403110580510486000d1b02c400c0e4002d60402625090090701c3c2e03000d050028081c0503011a807038040040050881d4040e24014009540b6014406400b0b0900360840c5c1100810281d1100307a076010414030402c1d90200ca40503540c40ca01350b4079041003030019a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 33601992 1250 33600742 33600761
    0xa030c0518010302070812040b04061a090601030510080f0a0302070b040b1605070302031002030702190c1703131508130206030106080901020706060e0114010c080901180f03050102090406051909 85
    0x1c10047c48100f8031444c40b5194140310b14000c0040101a00e49403408008a405404a04071a0146000300001c00e4644100050340301c5003e09000540e5122045201614003003030303004600302c0c801e105003e11241004526802d030380744a84c080301c0c1c180d1f0301c950949005000b240a028a2584240b01c401c00440d46510780240660040c41611a155181c0c0c021034104840c1c110007000080e000414008210750402202c0c6c0390303e9214410b200e0000b000d0341c030101510300758450740521017003014040c80000c0381803080703400701440d4044000700b0035960f40039107491400340401080800d1055001030200d0818042489115030300401c0146507038203040c42039039441d40140203044607650074402940040c4080c42943e001e05030301d42d0041000e41c90000c202002024080d5a10b0400030040c00703000001e074040050307034000002400d10860009074101c0215070700c02554000341c10010f94281c00818001c0650042c418140140d40500880303444805108240380c00c61520000301090413010481c44c2c1c0c884c1e01c1014038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 33603242 1250 33601992 33602003
    0x10506070f17041211090603060a050601020f1005011d090a0204020f040b1b0606011701030b07180e09010f02120406110d0609020408060a05040c18060b0a0201020a030c051801030207 80
    0x540a072600302030b1203a0400d8100400080c0011001801d004540b00d6005802e04119081e946600c0c000c00030035120000a403034030010030b490b0f4001c5030150b8001d210303c0405100f40b000700c840c040341c1442590090202849080d803882081e800800000c0c0c0d00e0b484861145220300c00402c90b03100d1070f81c2404001d50022901780d16610080c48042800b841c11001003400d62516000b00e100481c00412942c10103c0140c0214180140440746401c51011040654112a000706101c4c6151741c8107241a5461469000c803441c3c280310003000807800c4040740c0c607154040c50400300200302e009051070720782c4102e10481d2039500103581103000040000d000703500144034070407141d0303e02070401011a15600c00e40707d8a40125603e141c02040c2440002f008102056000008140c14030850601d92903203d8003049500403414800c01c0324013054200c1d2041d802c168018a014844240d4500e1b024500138000d4000c11460000a420b1400000b801482501a180481101030300d109030021020010b5000b540b003e20304581 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 33604492 1250 33603242 33603263
    0xf07110111030304080a030f060b09090109231008030304030809011401050a0e07030609061502060a0b0a030b0411060403120f020604120528090302010908060106050909060418050c040f0203010506070f 88
    0x1083c08c035270240c4c50045c00d0060741103486607080c4041000c03002d03058100035403c91401c0085070040402e0108c82910b01c400540079034407070729071000408081e880e640100c040c9100002c240810164082c2d1f950f0b21822407800208805510380b048900c03000c000380b04060780804c0f10002400a00041003e07079401407040e0034000740c40e507660350b0903800741c90b4280c1c003032107801600498420185805208c4d450380304072418401c10111003100c00080b24540303140800381c54004c007180001c082000041c101d02c10b00000800050712540e5910b440d5140d4540e041c02c82c0c000800140080008600004010340110380c0280042c030800d81a0408032182e0300b00394000116041201e503903501a051159505c1c0144007280e441d914101d04600025103400e1090303000407020340c8a4401003202d2a4840d090314200d111c01c0314403a01d103885020008000d451006040f0b103075050580c0d50360b402c110000a42c0700b010003068409009003211458840100d010034450141c0141c130070005480003a801c0b20b8080540d52003580b9410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 33605742 1250 33604492 33604511
    0x2010f05180a0303020609070b1c0c0c06140612010b010c02012708010b0102060c0406050a0c020619170c0c0c0d05160602100b041b0e13020f07110111030304080a03 72
    0x11100c2c1d14560040c2d0141c4c0080e003d100c0720072802d0080300060041c1d04800c6240044402c211200006100780020016544052520343c06d4131950301282065001401071181e20f1884001102900080e104079118914070701d401281000c040c00f50810140058680300342d22480780c2c006403104056150410481512a0384151440d40c40d100041c0182850000010303803401140e001914004020b401007440e8103041c4401c2203219445803c0b0740080181e85000003000d0000d04c0412154010b402c007065201c10a040d8400285a00c814054011468201c02c000c1c240c85240300350210b403240401c401c3c1a80c107c3c000c1048541048040c4002d01440b071012190008d40000b2401600b2895400030401a01310070740c041401a076074002d000c42407030304a0f400c003c0030782040c6010b0141100d604100050010000e0800a255a000502400b091803c501903503038024101c2c0800065010072030031a4120300d09040b0124651007034000306203a1200c0c0b0019423030b60f01c035912a444190001c3c00d500301007503250100340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 33606992 1250 33605742 33605749
    0x1060504020c0304090b0105030103020d030e010c0812160306080a0b041401050f07090806012103030e010203090c0108010801020c0307030c060603050703030c05100b03030307030f06050a1d09070302010f0518 91
    0x140042d16042019540301d03800c01e0115001d40c0d80940c181410071000348018009030b52058100184243d00d41001c030402c9040d0001030381c2d259200c145c058a80d034000328180910004030400c0710711488419400c451546031084003601102c256004244030380d809801090006011422115041401000c0d92110b00d16941c0146003551421a400c14a9542c0c41e010304c40110b8000209802030050503018156540c140f580180c40c5000002d011340c0a8051354416106150086d80026094215031000f07554034900700003410341d40c01340c0070b400500080082c00009040101071003a14004241c2c440598907044640d01d08a542034a2158262402540d44a00100080c400c200010046102c0c0c0c41e00c2c1d00c0380240c4d05240341090f80591140c21200d0910312115203e6501104403544581203080024512048598020092509401541d00400340800115a00e0880482c0812140e6415500603481e40e030350043c5903d9002c2880000d01040b04002080c0701e19004501a040d00900710311003c040c000c000000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 33608242 1250 33606992 33606997
    0x3110609030a1e05100e0d0e0f040603031d01050408030901031508010507080f09030703080402011116080f0d0914091902030a0b0a05010c0c090905030c0d09140109060503040b090106050402 83
    0x32011206003c00103104100041c0207035051001381d0340b410080310322100000c46d02c0384c40d0b0300c0c1c400d020442c101c0409202d0341c0e11041c050301941c2c0c0181042201a4803403402910080e0f115114121092103003a08070752540c416011a000c2e645d490002d1410405a0300040d00913004400d0350360418000c100c1c01050641c0c09124940c0706001690307918500741081c00001c403400750003800181b626041081510046500202490781169080c0ba14030070000704a10900d0404030000d005002400e402000010514000550f002207c03030404d054030003035048800103650004c01c512034211188039080540e8424500400200e501c00c800c11600300e03003070030045990300403a441142d002c0b00640c0c4d03801d180500e90130324a075100c014010a0030802031100498035500414001403054081c465181c1c850041084801e105a4103a540c8030360848140d24401d401c0601481d1543c090a01c0e00070a500400226601c581540b4044a806032501803468a42352195086104000d0064401e992103400008054885200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 33609492 1250 33608242 33608273
    0x50c04030218011508090a0308060f0301020703030b1c0308150409080a02030a0801050402090d150603140304300807020111120405090f010501020c061e0f07060b030703110609030a 79
    0x70828840d604210b00d0115130442140700f50708002e0510100501d924000800031401c41d098108200d007a901c000014645021919050380c00d54004101d941c20960990003001034a94111243c42c2070b101d03e2215400b04190525020b00021061404070798602180d0135960080c40d0007410200f00b100740c0341c4984c48580d102e17000100041e03000081c5051400c0d4485125400340c5000c407419407030170743e20000060100e18031807809408076035500c00f5101601250340c00503000310380c44181c10020700c3c990b82c4020780340d03001403042c0140e11006402d0b2038489000c2c0c0290400700002c04c0341030200801241c607001c5d400e4000010481c1030040030800078034030b190100822019182078401d901e03500d608200c10311100844c09070205020700781c02e80060200ea038020421140e83c0e542507500545550404403000c5418030054a02c2c0c00000300040d103414064450300081c005035015000c14030050101400781903540c3d02d140b002800b00d440c1c00c07205080c5480d051008164200000b8100d5034042c50070384a180940c02c20350b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 33610742 1250 33609492 33609529
    0xf03010b091e031002090f0d0b070810081b01050c011b020709180618060f1d0c0d0303050a060e09030406230f090402040305060a09060b150706050c040302 68
    0x2484200078500262078080380c107030001040910580c1c0e0008a071340d5008075210640b81503000324038001140c80b844051041c0310703002400b81c050518142405201c8800644d4200300140510340010081400460300b03200700c035600c00003408a00c201b840001c0781410311007181070400c1010442c1c0c9021300400d000703c844145007101d5810794411541c5010f0310380308055100065050520450f02101d031030864000e400030380c00000c0442e1000b0b060780c6c201200400040010842841c201c0e009d224000700741e0006a15032401c804851a581c0c0180002e980c07000903050301030303012a1100c845000a0301c00d80205802455480d0f011034480d0310b843d1070100d00c81c0115441005a413002c0790801007a54410040f071000d54a43c0070440465650000e003283d21320410501ca080e010000845a03000d4880d0340c120380003150000140c816508240101ca00900b003280d0302a503c10741041d00b04c1d02c01d0314081006009031503007204041d28041103a035402000d000010b154001c1440140800400340c0c4411200303810880480 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 33611992 1250 33610742 33610747
    0x15040b0d0615060e040c231204030503150d050303180c04090f060c140403080702011403150301050106030501081905070e07051c02030c040b0315040230040302060105150f03010b 78
    0x200c00a103070950410244d44181c1c28551510703400c03034000a07079010794907c0e510004540036000351000303403d108580c1a1090712102c0e41c10030040c10340c0000554051060180e0800e24003580740704010f000703884002e0140c00b83d0010008240c100c0c0c1110f00d05040264080c0076240070361356003c0011308450625100f62009035550548004014140c440c0540f040c065080a035407400646c0740040b0540581d00005110703210020307040d025680aa402c01e1a030020401060b50707203181071001a0f50341c210b81d0720035501960924002140250213402120b0603901054010420b03c9150441106443c0341c096069500e8019808041500308030580c8041c803c005c0d81c1c80b00c030703941c2c03018000091030030000043d0f41ea4050b1040c07052105912581c002c54040f02c1c0e14809613601d944400081201074180c400e54070790700910015940c1d1507030381308410458941c1d8a50800c048400040c2032600f6001c00c04480080068002000500c010314105180140640d8440b00d81030503d1402800d038039143d402a0042c6803500c402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 33613242 1250 33611992 33611999
    0x10c0206090109030801120317010f05040b0102060601020d12060b04080c030d11120a0201020903010e100e010b0d080f0f070302010b270114190308030402150315040b0d0615 76
    0x1004610380006079103000304070f07000c11920010402071040c02504411600d0600003c1407611a54409100c540000414022565140418540d8240c94841c4034081ca040400d0310b0010f600101c0c440b0700ca040d0680140c000d040c03a0365012550081c1d00140c01c0d10f6107569a50101c4d500c02028007503c05405a640144060014241054074010b81c1cac20801c010840141c50b86000c01070085640002c1a11105c003140d250818a80183d0190007002c5100c0d8056282650741904e03040005140300000c101c0307500c100154031000080c64203a400b2000865001003003681e8400c001003222005050b02c8902c0403601d41030242650600c050b079884000240e0050391607001e000010314207000d0740c4e4814000d041c0d4082004034a0b04000d00400414131590f80e00300c0000f921180c0035228a45220070160000c01d030086410f13203d15200009400950b8140c0c0034400381d0031030769050380c3c28070126801103050940d015010700000c0100070217401c0c040b141507041051612074600044080c0103098500a40e503489120580c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 33614492 1250 33613242 33613247
    0x1605070803040b07030605030303010b040603020d0212040c03060c0e09040206090109050d15060902040302210c0a1d01050102010606050d090303060e0f0a0c080c0a03050606130305030406080105150a08061f02010c 93
    0x1b526085035100c0d8008100402041244400311800c803651800c01603100c11480307112100070b01801210780b08a031205410030040160326106034050303e203d036408101194040f6411a044001000b08680003000d080202e005440c0c268003074000340505140401e00a03441d000443d40c03283c0040d200311040d0410b911100d5030941180075035400b503c244d078411820f0070714540029400181c14007c040324404100c40c030702d6003400d0601008142d1f81c40075140904103951780d42e075210010203a0005000031500c04001045a40c41030055600b22410740d80c5a078101205500584001e040141d400c0b028103945050008080040c03905031841161441401e01840c50106002c1c2c0c140d8180713904400400c0301c40401c0008101e4504159042107046103400101e0f0396038000810094031800c0140c08440d00030030780000030020000020030a8071240d41d5020f045986e200b0030700141c59031080c10250304480c24070094441501c50762115170304c41e000501400c0901036581607081044422150500140d44580b4904149134 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 33615742 1250 33614492 33614501
    0x1214030c0d020a03030b010c0312020306030703080301080d0908010e0703031809150513060501080114030123010f14090c09010513030501050108070605120c09011e181d1605070803040b0703 83
    0x100c0c01e003400008d0b0491aa4014819a80201e10510443c0d0100c042161600d04204003c0503661181035940d0f42e584071408182c2d1a020042c2600009001303010100c3d00d104180102207910590700c0c020720026027190b13810395071148c559005a45240d1410000104031145008170315603000c0c481041c485103030031310b0140104803452a60001c10141232040030812070b40d01130111411a401150003500c0c02d0850704c00a409000c0703d65941c0e00c00240c074038075100e600c040c03a07600c64100d03200480c10240040e0fa80f840035403490a50032001e64001103202c005110111035800610408105160142c5001c10209500250340002c0d08103480d160340d248018840030404020f214040c004900b011810540305281814084030001c1150140c400d000c103810060b0b074010380900c0f16050b018074070005030340e0410000074800c460b4079045400082c505031001611050800d01c0015801c414040d0018981c1d400a42c48400e580f50106e41c000c1000c2040b0707110200b03003020081c601440c0f059a0b441ca072800c100d440101900c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 33616992 1250 33615742 33615761
    0x103080904110a02060a0c0512011d180c0907170709081b0d080a1416020301050c07052d01020a0302030105090c090109031106040308040305060405060705041214030c0d020a0303 78
    0x108040000f4090241c0020390554400c0c07103058003103120060f030b0a040b901401000d412900b4205142c002081c0941031221341c15070442440b01c9560785651f000c1002c1e10381c4c10450f48054403600422000c14441c100400c58035402441c0d42800007081d06020052600c0c1e0f8011160b6400241ea43c0000344a000c00c2070041e0301c2c080d010310300e038441e6030003003040011010103040c04024180b00000440380b4240b4003a00d0145064201c03078400a458280300030901e550004082000ca101354a03010000f19516684001e5400c10380e00718000307004140340502002c8100400e04142d42c031002e44104801100c40d42400100303000d5409030380141c0c0f0b80d494103040c80059000034211354810340d001d1003e03048a03684100d40a0072660801e504400c2c072103000021a50500c281e410181460f4000680031040c803500154290156114038112106d80da900101140d2034095070143c1108407a4802100700810b21030300401c489403400b5019a45081034403154075151002207903078100540c2007144c0b002e0605400d0f2180e550003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 33618242 1250 33616992 33617021
    0xa0e01030302030913150504090606050a082103010b03010e04030c061d0609070602030a05030709092904050402130207060b090106080708090109051905010f0e010b121204091d060103080904 83
    0x484e42d450300010b03011982c1f4000e0a019641c6c410f102c0c2d040c0000354001d0801800c0150403100407d445421071521900300c05581d0f05010b030941420340000410350200c0b8129800c07010107505503400c1040c88800400301510607000c2000068568001c5460341c801c5c0303423103400300e5400050560038074a205c50800c0b900034503050841d00300300000c1000680100031552900c0e1140390155607551010300a640f0031f0341d140c001c10642450044880084600218506008003035942c003480300c0000e1030100b01c262441250000e400927296040314031404170742d4010b4a881d520400000c01c01941c0c503400f10381101003d034014000139038010240568135801200464004142100a00039174549803100740d512415a0120310407415810402804c0c00800c1d4010100550102d8052154486a02d03034280a404c103135101c607116501c04071860140d90400101c01c8190048040c403181004c0c40c4c0909107006000204140e0525203a84840c2030032103006010382c2e0b01942c4240000c0ba102c40c40c07035007404211038608541c80d05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 33619492 1250 33618242 33618251
    0x1140c0706080a06060314040605040309030f060603150203061509150309160506070f1101090909050c0f010f02070b1303020603010609180e212a011404020904110a0e01030302030913 80
    0x6501f00321004160344140c1015021806880354503080b1850b140c2c0394000380c00030a001003580e04110043d001070003100c1c0105400351381c41c05a1203880040744010784030540e004104d01000590307141e0712405441d000c2c41c000c0017416010544185031940c0e40c000c4502010580090705004050500350b4003001c081d22007070342c140303003020340d036566a203500d200024024090350b41c1c0c45481c00141e0300c940c2e00817000d001a010309128280709840c0c80e6580720a10020f0a102c3c4004110380700103175115541c41ca4030340119600509105240c080702d007805a1000500340300c4040007580c040056194400190700030540d07543c801d01c0c241d03d0300b503445441015041c00544280d00b8903080d581100350000c0c0941041ca0000a207200d5a4044000c0040703a100351a0122480134154848402005414024901140b4200003d0105803c41b01e0002c080300400c40b8000e5000c2d00400108020070325048503c10540409042d6101185e1a110350310071181d000d074011030042c1e0001640400d5410b0451a804a40c04004800d20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 33620742 1250 33619492 33619511
    0xa1113030203070b03061509040b100201020a020106080d0507030e03010204050604080d03050703051302120c090a06030c0f081c0306120b01031b24021005010e040302071a03040201140c0706080a060603 88
    0x110781c0300a0599000c5030f540d000c1840123403039036590b00ca002501802030900e40250000c580181c007070340081c030090016502c0c0072400581c032400800d00c08007103489030b0740e61440d1025a907429103002c41000344040d010340d800d10011915441e0903000380003030f102c071400510305e81c5d205580003406d45070001c280c0c004250402c8148865008000c020202c403641c100c5010400724148410649000360380c100321580603030f104051140107501541308000350390064100d5034105031549260b1a00304618410b50300c02c0e902010248210560034039106100d80403600d004912160340c4d00c8900010240c000c0207407a0143c0d00380041007001318080440e000140d242c0403844259241c0074542c0310101c10300055042c495083c1c8010746489d40300344010325015120b90810091561140113401004c0c004880440c0540f041c3d105c0811000c0c006002d1040a002816401c1d1641c0d851b54011102000b1004120200030703805e10403801d951900b80217840140c40195036005151410111040644015a00107420f061500b40f085 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 33621992 1250 33620742 33620749
    0x7020f072106050a0b01090812030a050c070b0906060a090911091909120e010504030b1906080f01091e02030712020d080a050310140f01080a1113030203070b0306 71
    0x30046038a401442000302500d9900c808924403400002850340b07103850300700030303a07810290b00c1650449420f90799109160380790307412035a035012042d207901204030084c000590b000810350002d81d030007a4017140060410865076100380401000350f44c540840d0b000740302001250300386861084002c103c00340c02800403c946880342d1440141c00000c0e64002c0c0281400035281e5428042c500707202c171080300c204002d10707452360518031401c13407415644030300186132111640501d601c903031f041d41c05894103c07a80f20401e0b02c034241059114260305001407041c41d268407000401e400184054207a0181040001c96680300510302510b0060480524140003141d0019010158500150300410b494080f4010307511044135000044030140c008070b00501401d40007604000c0c2581c010069800365040307a801d80801c5840d02440d810b0490a04c0b50650850030f0303010952020340c030504071113401c0308035500001501c00004030300b00c11943c82205901d00548011b0002c00450400708040801002031701d80c1e180c110709080001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 33623242 1250 33621992 33622003
    0x1020c0616060f0e03040308040e010506033709030206061002070602150603010204030f030c0303060b070b04033b01080a0501050105030612030412060b030607080609060613080303040302060f07020f 87
    0x42d281c5030b601c0302e035900076120b2540f169400345421400c03262241d5492900340300d682e0060007182c3e500150b0713000000d21801c249041d203000c0c040b2080c040b01071009610300b0707500381004024100001e803032000380e2000304c036a01d01c81d011840340240d0241074107152440a1042d44052010340030b0456110f01020486e00340d001c00c2509000a0300004071200da2110000640a40243d40000e450303411030300429020540c00c0704003074801c58800d4070141300c003e0ba03441e620051401504005006101d130070300040c000a00c500321480065121100e01524401c080c06031000094174561610001c0040b4041d1010641e0480c1c0c186a1087e01b00000380401c0d810400004d00318080075020f5030080d9000050042c2803502402998050441c0e204281482106800c1250103041602c40b524028003079200410213852080810b144500c00c0540b0a028a0710f50b030080c4809540f0a401e510700c1118001c202040d0907209100540c052400307035005242c80e052001c05c82101d00800b60a90041d0342c0007107148006800049107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 33624492 1250 33623242 33623287
    0x2060f0f06010c0f0204050f07020f011112070c0c0306021b0105090706080c04080d0306090c08060a0605030603070b031f0e0118050406060503030c1606020313140d020904030201050601020c06 84
    0x24480980111844d0503000d0001c0e00c90000d6100e401e050030040f00e030105a4400384900101d608858802e1706480001c1d0807190140c01000c0040c20402030142d01681002d0b60580002582c83c180d40c2c10115629110000d0b41c83c1d402c110360007500002c0d0300150600c103000f0009030700c07050710080180b82010a1440e9480c1600d00c51101406000300000e28000c0709007041c1c030300408000e0300751aa109050000100204501d0241d00031440c035054940313041c00c0c419006184030301400780401141c0390a01506440e50f40000700b009900d44103030103000c5040a0540003460284210040202010744603030300315107011409410400d10402521300412130b0002403a107141004a144800140701c0d19030741081800341c211500308a40601c000200302c01451700008130381c41d45095200404081030b44541c0c0884c0c40e8070a034074103180654252801403110303c802c1032a442130001700030a4111340000e141d01081501d04129801d0300581d5445041040790358040c031034013620306800c0b1102440c186800412000040d40c0f40b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 33625742 1250 33624492 33624497
    0x301050718090e150106030519050c03071101110706020909090c01021009020f040504050d090b090a1a0d1104030b010b0406080403030c020c1507060b030a050d0507150609020a02060f0f0601 83
    0x10080980c0c3c800038844040c2e0f25900040f4881035607100d01018001c0c02c000e5403641060000c606404040343e4641c8a090300842c10100700c02c0c515100c0380421030714246142e0180c8500e55a4104401e000f84441004010f202c3c4280b1015845000e901c0c1084011a00242180d001ea00310850007005a030b40490780014481150600040105241c0089000701401c0c01d45960002d24180038070050000000d5040c2d0b182405a542e09015034994a82e000d1074040d0420305071300458641c100740f040074604820000340039080c8440c0c6082c81040d0510200f5108100801ea03407100c00050140f06000304a055140908a040b0f5410318052901c50010510344000300041c3c1010341c1e591191044070f101b07001c882034041000305902200e5aa4030b041c6510b5501001c811a8210b24082201c03400d0306004c596032400b2900700c006071240c140da226095441d903001003421034049000ca220410006494030810010b019030b00703801611181514006468028058044403600c07002c0010404000c000035074440c1c1c880703c00e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 33626992 1250 33625742 33625751
    0xc09010b03040303020d1a04050a0603030905060c010e1c170108060703050c071202030a0e03010506060919090608030a0906030911220207080a1704080d15050618030105071809 77
    0xf414210003e028481078032800d20304201e864117148210913414081aa811a070402c2a45c0310156480d0446207640300007404038013400000c0065241c9003000e007240e0700d060800407508080582c446400c014030302c0c0d00800c06444a20150021542c0407070014582c2c0d104825203120f550401300711030b5848600501250405469000140d1803898980517a001264440d5014510140117032002c0e4681d0064150100041e88001d180189442e05010b803502030382000d0921484c10302c1c0300c028040001314140c074582c50714031504e0300000e0481b0180700b044000e02d102405583c44a8640c60002d0507c1223a60010702014105460140070602143e5250481ca50450316011900040f4034440610040940d4800040f03101140010174060101c004080c001c056994810000b000704400441500d025a00034102079028404421007600325032080081200b50b01c00c02100950f5180000c0059200018420070380c4c080032014591130809008554202841d030601d50009032400d5440464107450388074810406854 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 33628242 1250 33626992 33627001
    0x14030303011a0a050403050d0306090e0118110d120c03030f060b031618030305130b031902030a09020d1506051e1c0204090c0305070b0322020a080601170705030c09010b03 75
    0x36130201d070011540141a1090020034010280080030b8910405c4c039020f00305014502c030044184528014400303900030300e0119034100e4071a6018828015552504070303508001c183d0120302190041200c184483d5a481030307421a40c42c0050998800e1070b508a80340341004410300c1150300000a0780d0340520000915000030302c0e081c0381210394802402d030404012000f84004024560b108001780440e620401c9101840741e541c50706191584422185a0070a10f4040c00d84030b100381d15600219005101c003000400c0c1ca1015800140021107016400c651000b181542c540c0c40da00b5901402c401080c044907400044920b50340e003000e502095088080c403608400621188001d5400034200b142500500304100c501c1c4140382c0044030710348901041da01885801d1002a00029a9080302d10464546489445030f000c0501a2001401c0d1000d003240d000c000c48201141c2c0840401c007242c000c02c0c01c2d20042c020580300407030b41c40c24150a60080c0e4000d40114040c0ca4003501c5210030341d811503006011003590795a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 33629492 1250 33628242 33628247
    0xf021b0f0414070e0a0e09030301030f05030d32010e131506080a021c080409110c0a05030307031d1c020708071e0914040602160f05060114030303011a0a 67
    0x240000344003070310049024020f000d0b80c400e0340326054400540f0301c2e420840d120108a0484031040740c04207120791042006100103405c4075041c9a40d5071090084074100704a03180e002082c1c90310320300640c94034400d04071502000d40601403040e03030360f0f070b1140070b110001c2d410000c00010350000200b254010540d92013000c010008003004c0072183d581d00c0c40c000c008654076120802e480b42942d036001d074810280f02c4030404401845508403201250f002c404c05262916065407040904007008007840300d01802e20000c17030059010b024490341d451050024554a00d40b468014085070b40e0f038403030401d030300d08900f04070205d09600103004100d594809046d0303842c0144e000001c910f09041a042134a07280039041d00000d03841040310421700002900140380c1c0b005911400004120b0300b400360800104c1d050040810041800d40d402010fa001207941728410780200ca4803405001c070061542207903507520000040002c1441511000c5804d44218040d40c03541d450300b010780a07040c42d0240071580f01c150024010f2005030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 33630742 1250 33629492 33629501
    0x305060f0319020405010602030307021902010e0306040606080f01140408070c08030c010f1404120f09090603150c0201020307120e0307020d0605060103060b0a0203120a090501060806070f021b0f04 86
    0x200c0041c111a903440340800c0000c1d800c010110120701441c28900080740c214000300c141e91054030164020074108000000d1079491880c500016410b103d0384441e0300c071b019202400800e05c01d0340104400318195180c280100e02d40440c0041241c856458a0103c00300700811400480d0000c1d089600301c0d031030740da4034108506480031503804144107100000d46024412019000110b03006201002000581480400312480c01d1041750001d03c2c20b81782c4603000385990700660390543c01c4521490907040c183e4840d00c8000440313016410558980012200414403c0487e0048080229040c4000d508600b8060005840c68102c03030b00e00040320352555140c0200d440304000f502c06007a00100b802c1c400c00c0050900000900301500c10b0740c0001d09018001c2003c0d0441e9044a118080c01d9006502d007001c16016044020310191440176440d480302030700404200e09000d15400f8000c03100180065041c01d0300b006e000803200a074a00295000341c42801c40103100954100d0711004155403403030381e40c9103010001d4000d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 33631992 1250 33630742 33630769
    0xa0204050405010e0f0703110301060f03060806010906080106050d08250204090605010302040b240a0219060c0206180d030e010212040507050315040506130507030501020f031e090d030506 82
    0x142c0342c440001454074010210900909218030103403080d0302e90800440950b1180072280400080c10401005030612888150604401510300001c1c42515800d096003400400e0740030001d415215401030080b48020f00c9980d0083c0021905200c1400e240d50b242c1d26903000324607154070030758004084500c100481c1020b111600d070340100108205045854280e008107000e00090b8000d62504509035441d0401034a6400d121021194000302c0101100480960340e002c40e200000710f008035403031050307990080c070480c00d90248a8200807441110104000f494490b0051000c110072914040d103070084100440d080c076445005290125802669004240c0607100d405c0c80c008046402e0420007060040200c1c10320280c0310118207850344600d440070707541641d6a003070368003810035040315011035000c04041c0f02c8001d456205000f070b0b5005035601e40300e05007207130030900d1039042175000041008031180c5121210561b180740c1d01300740c00190401c0d400003544c2d440b40300611020f00d41d1354004210349a6482e100c40f0781c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 33633098 1106 33631992 33631999
    0x206040b070c020d0812060603010308040608100b0304051c0c02090105090601111c0207051203120604021e070203010c050325030f06290406170a020405 67
    0x4803440a003018080c440200c91000050300c810b4030780c11909014440c21502c41e038495140c1c1e95500001810300e4803c220800051000440030019a41a2111441c10700f955a844245650817160f42d504110b0b0f4806d004001c0004000c4c0c0040c149640080d64004600c0070f0b0700d1600140c1d124008400d0080d0300202100c014000d6091042c05140e000405241c51600b1204040c0b01504225021000c4c55500c00858044004580c040201318028030040e42c60f042e001c1c03012420141c480c0501c540c82801003860902283c0265201d0701680c000e20010525110220380502e1007400c981d0101004900950078007030910040c0e0b0092041c2c910884800d40b0410240c0038402e6091002a1005941c0060540d0751181c0b130b003150a24460b00e400382c0402150500c20031511240d40c0c11015240710070300c900d05410801409549d07800740e20360040c1d991460140589846400001000c2d0280d908043d42 = true := by decide +kernel

theorem cover : BRFrame.Cov 33453242 33633098 := by
  have h0 := BRFrame.cov_init 33453242
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33453242 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 33453242 ≤ n) (h2 : n < 33633098) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
