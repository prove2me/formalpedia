-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5267
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:17:43.413968+00:00
-- url     : https://prove2.me/submissions/345d9188-cba1-4291-b6b6-0401f8d8f260

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 947122302 ≤ n < 947302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 947123552 1250 947122302 947122307
    0xf0f010c0c0f0306110703020304172407030509010e0601060f0c1e0b0f04050604080903030d1e0e030c07061b0b090c0a120201090611030d0203150301050f22060f020a 73
    0x2d000c80f8420340c020485550498100d5402d4080c1410040068100300300c10003124000362030818414044074145c8024000b500d8a0980c50b25254072503001032900b001c10081ca0701c0d0180700305a844180100244401941d1180c25074491030140501d0091003d45880c41c030081e0f120390001109158011820000303840d03c15078982a114441e003086400e031200d0030005005c10000081c3c540219442402031026072100e43d203004c400c0d0090707880150103200034822180742440078020b541a15031424042811500c1036a00f0750b0944480701d070845001da208000b0252101e4000890008a50075458411450071994084e5072070b00380d81d800f019050094007000c1c03014100000c5816144094101ea2210342559590106503c0c2d5030302500c060b021502103541080f0340d038003a1405103a40084a4141c2c0d1403d15070202d43c000700e8000341e48c40d0b603541100c20407072401820300740f080707982100d0940c11150b00d524020f41101c4918280726425400f42c51300000d00c104000301074014442c41d80100344195110307070300001300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 947124802 1250 947123552 947123579
    0x10f020c010b030d0c08030105040f02090310061a040e010b030403180e010e151008060f030706020a020442031a1905010b0a0513030209040302030a090e060f0f010c0c 73
    0x80303a03c03134010070729040d003618050301c00d0420003507008201e2411680f03482c0800c4000c185172092301d40b11903000c0189100310341c1c0520400e107108419280c0041d0090405200c298494101c200519070194104020300c4400309401d9401d0450b1a0a02d0311503a030303911498120344d00d4044005050300c00404901c007240d042d11490029040c1c4503220408504e40c0d8941c0c11440010340c24814554210499910b0000614840d4450a42c03000d00a41004101c1c907090001c213140c00555030141005030040c1d0707d5101180b409014070200d03014001c2c40120301400c4542070928000102d09a140750224085240c04001c00804001000b56045031600000c244054007504121030304841c0024910440c1420f5101c45042d072181c507050f01c0e010034001d810034042e40e0003a00c09a00040c242840818426400030069941401442c4a58407035400366807640740f03000010b008041c5603003010710385001d0f140400c4540d480316131585450303201c201c640440c00780e540001070307070011803500000c1c0c10812400000304603603852425 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 947126052 1250 947124802 947124821
    0xf0d091404060b040b1e0c0307051c080106120e150105030f062701020903030403080909220206180406030c050f010212040b03190c02060f1303021e010f020c01 70
    0x1101210100240100801c6500b14001e14083e03070024003041c41052280720142c0300a0030400c502058113000d1220000d032541061003408665840001c0b9102041820300034003003250044442401000f016070009032001c0014010301c410800c1c1d09062001e12540c5d6000703086150480c0013944c04501c600d4000d024042400d001d4540248a0f40c419540046000290980703d1211400340d8208601c11440001e0030f286a84000e0720302d590248940f00380ca40c0c2c184020300086100303003d456a100100014400a490020030a941001a10290701808510014000380155048a20580e500014060501c0400d000d00c211500a0710f09440403080200441d030305800d4a0703080f10952484101034004a940e207201e407050010141f030038401000310102034005103070003900d40f039519000c541c1d20301002d10440324072032151001030b0710900501541b040c000820507007110780f140304030443d0216510043c1d5241c1b81c8040402185801240107004110f080d48450b41005400340c05560f1210740011844c041d050400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 947127302 1250 947126052 947126069
    0x803040f0b06060304050d0509060f03090d08160206071206090e100501150518060c060705030406060905090a110103061206230106020a1214190f11070909050f0d09 72
    0xd0101c0e48903d441401d0301d10840e4000001d00c070311030200c4030440c1d0640155031040d40210041c02031030440c031003800196100e626004010700880d410000014200000075020488100b40c0004004081e81d011400b0390380201c881c10214940c40d4100100d070001c0c0100e0340802c00113403030302c019200f42940100f04a100c4119010052043e41d80b40c3c42e4501d20a4425000310000c1401040003017402c2203000100841c4410080a0710305020700c0a40d00c078205002144d1140006400000f00b0040010501c00c440c003500110b039040205207000c100280d600c255500c80581710303d602c60700a50450784a83c11007009441a682d05603603aa0300e92400744064030851035000002044100c0522031070780c40e1f00c0d1150403148140d00510395410345858140300b41c0c0d0248407074001c00c00001184004a071408000b88820080c001c6040d001c004003910040408008046500c2003142c200860b400790b2100080000a4405071040014082d88910f441890004944020300040c00ba80032038580141d00003e290085641da078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 947128552 1250 947127302 947127323
    0x3080610021b0f0a03050102161b0e06060c0c040c030228050f03150604030c15020c060301180b030616180303020601141c080d0f110d02030903070803040f 68
    0x500041c0d8441c55103881c002500036241102021918181d00c1040f440c40000e0305020025480e80c0b1040e00b680d10101685000410b200c0849081000d0f0000d08003030030b0820540f04070818184040e452000e074010380010b00c00c20010030049507801c0d0a00030703a02075501c02881000f5550800e200500039411401c0145040095601c0207007194111051944928421b50703200e42c900501503034100c000340c02c00780c0781184007801c00c44d02c0c16584c0c40300e80040c030295005503000c20708035141c0042100d28809070040341c411500302c0d09603081c0030344810003030b281560700444020000c1c03030110110340c0c010b00102c901c05034548503a00902c40007107400c92503456005015520038036491624403003611802014400100144d105000410000020b000c1652140c040245204208058905240756040c9050340543c1c540500152580c95517001e40b141c03000000c07248209000d44104d400c100d205070300400ca886510b0395000000603a82c449e0a0040760540356106c00e10b075440341001c0c1844e511114511400f100d40440300c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 947129802 1250 947128552 947128579
    0xa0609020306090f0c040306230c2805210901060621020d0905031207030f0603030c20060c010f06092c10111905090d03030522030806 59
    0x950003200e1180401a040300c10396101e018940014010040043d2600101403002200154641c010074164452234001d01340250040d060884d050240503140e80301d011410848846c0c08aa001e0061403588907011034200f1640200f40c058450f4801c000c008102854001d4074101042c0e6900c80d0304e03000fa510200200200c075141e02054840d0104405440000c00c1402044011124540c00a240007550700102280f007003d0355680a1031070308250003040540081a00b044841035161182120038800e05009100c07003440c640380038080442c030800c003a01c51101d00d202103582d94001c1c4042066004080d0013a1b0381c0d844500c100c14001c000b000640f460709414204009400c0030389008140d070044c141400386140088540c2807141380031002d0740800c124050040c014605901c40d100345000803060611542d07403401c5c21403403000504240108002440003d100080864403100303038620105906040024140d104d94108441420840f5861340031600c442400b0f40030954040510b0b402180103480032600e0302035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 947131052 1250 947129802 947129819
    0xa0e0703080d0e01140112060b030715121122050d080f0c1c200a1a151005041d0402060a030b13020a030b10080702150601020c030f060a06 61
    0x1280c40080c1c18104184040c1482d45810b5200c0194080520000201c10b174070000248100d0500740d021045c1840364643c4c40b41440b000f03001e000d405a90450103003020508210001c40d0801142068000b0040c507d14000c210b403003154040203400c0800d500c8680c88068038950921440d10144c0030004607203c01c1d00000791808c0c1024101c080c29400740000d41411a945e079a003005070412002800303a4401d4040ca0195440708104004800e2096551685849180ca40b6101c1c01079140740b681a107940121488408564060410130180000c8020100141c030347c03110403204448031050080c0d01c07152000609120540140040c0111482c8000c034555000c03140030304840d0140220341c0650030241c1002454031180c400c0e070110740c00c16002825040721007810642442280c00103ca0346010a590310403019013864690980a8691003d00c0c200c4400e00c2d05010082d1642e0810750131200d8012070328085400f684c0240031031b08038540c01030211142101c9008106030f0b2003d050710409811440c0c14404980c505 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 947132302 1250 947131052 947131063
    0xb070203160803270901030b10060203040302060706020310080708070f060e0102150603070b040305010b1c030f0c03051c0506010807050a14130e010801050a1401141011150a0e 77
    0x104500b01842c10305003002c0203907032048950010f90084101d0a4814402e503900c515a43d806140a4501030000c4c2c13514640e048100c07502c540100741594418002007005a4030702c002c89480d50341c0014056200e03140e4540302028820181c00c0317031205001e481004075222200290881c1124441d00000d035905035030701e02c1a500318950071003c1b401600075001c200c84041c40c0310440e40c0c000c07102070110740c030083c2d0302c809820b01c2d50495007007141c3c240d4450b034651591380f80280d80d540b000000c502031800c807101a55005000058006866814460b03600207510038140180c0940f00c0d240107440c81034805003108900d810040c20b082300c0c8640412100008111a05d01c9001910112140307a00c40760003800301d02c0701c03d01c80b5030888102881c50700d00314200810070352540d004240c004d101200020800303041a0040d4000c1d00d40300c0c44170107120388880004000d8002e004c0c41c01d000101c000c0e04c91200303036990400300b1103001c00800c00c509510310808082100c03280e2001c03d44e0344240250702c001c005d0000c1c84041c2c65100c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 947133552 1250 947132302 947132309
    0x60f030303130503090d050f011109130c1e0c0204050705130b03100902120901060b18010507020111010c020703291b0702040606080a0e011b0c0305130b07020316 71
    0x550060000480042882c1c0110900902507000c40c0d04010707140001a010400b00441100d0b5508640c0c110210303d082400f0b030200307400c0000805030401c20840c0203c4c0c0f040c0810b0b40b181c00c4050303c460000c00102d014140701c01c44416107024880c4034006030314020b4030061808904901a5140500090182e0b10031401d88a81c81890409003030000d1520001c00b9498001034103070450080c01d40400144c0d00700510041c00038855980d1641211300c0c180b0569400c492482d8400c00b0000c8040205038542d0501d03a002090201090800700e448000d00d000403141c44030401c600c84040d610b8940b441008070380005000007140c0c458520b0340701070301a0550303100c020799103520000c03507225030040840e40e00c02041e14000c50242802441030309001c62a0005420b590150f8004004a07031100d0034080600701c140a000c0140341807030000c0c0011041042809003045800ca900410000d0703500d40d00b020144101d0448010068800748110b03100d4070307030a85c1d1480f07a0216100324400d10036801c4035142c01e00c0e00c0c00703840203d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 947134802 1250 947133552 947133559
    0x9030e240315150301031b060c020604271e0c050c0d110a06090b1501052805090a0e0a140907140d081207180323030705120a0305060f 59
    0x21030b26490000e000d402c0c1000e000d280d01a0102c90f102800868200c044c50007580610071007103403060b8000090b1200765503a0480c0d81044860914000540c40740c1c0d044400f151507000c00d4221412a14204210801c0e43d0448000900c0c01c01e41c07001c240c0e80910314503154840190f401004001d1151006803014410092580650340104080e084568051203d5468607056082034070780758185a0f03200001c540110b08102c4020011409011030f6981a030703000e041414083c00d0007844c2c400030400d4a4010f81407001d0040504c1c8040010300907161068082e1a5140c00c00740000c5602f6488414440180c041102c1c548089032425084603032001c01e120741540215040c401a03d8902e0600065986140c603100a05801100c1e0140010000b51340d03100400341603103e01d44582082c2840900289200348044804290007518901800881c030b5402c40c0610002021ba0144000e140304800b950540c000c02d000a030490044014004a4818550040c844112143d034104440da0f0303004100100c1c280803c071001c0e00f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 947136052 1250 947134802 947134807
    0x2070605040e060f030f1c1707230f0a0c05060601051201290307080f090f0709020d0e03070803043806030a0203060114120114220609030e24 62
    0x540b4280042c051380351510140545405040818503d4508401359103070752503410500481d8420369500c07400f07000d81d00441040d0b507440c600300703214010840c400520200716403000400c1601569141d1000315500c881840c59469243d414030b280187ca220032001041d90203002c0d900010b24a50310440c11915050b80050380610940d09201e04078040300c8526409911540e00030543d040c1d901c2032400074600c030300b00660300c1000601c0c1c50000c2e06040d0780041c3c0fa05916503c10704840341001c1d00072842030240c1d002e00340010780b030b40c020b402043c0281003051001080c500001070b2041c244944480250700c110300601c507c1e0707960503015200200401d04090405044da01100800d0300d52003e148519800c184010100e8280d621590002030404001381d01c11300c0d15a110b00700021960401034003099469403600004c04c01c80c0304081080c01c80b036400424000000700307294060141c40e000000d110050b10b801500800c6a20407910b0b025000c00156130055114600780035080100d080449031150790030301410013050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 947137302 1250 947136052 947136061
    0x8190b070507020616060c111b011806030b150906090d060e1e010b06070f0f020112050a0507031b020a080f0d0e010b0a0515040b0f040512010c02070605040e 69
    0x944840014000c182001010414032001d0703900e02d4003034140344040b5022131054940f83d1400e04100c410b80e20a990922802c008200d00340d160204d100612040d00e0300301401101283c0004032008440071031040403032403c00d130380483d04641c954000c00350321a0a6541c540202000502d40403940500e000565202e8401c10810741e42d4104007a410031400d12610022070714808860000382442d19011004218070303070001800c1000740090041c1804c04000381c48441c030708012a00d50424001510b880540f1600e40c1391450030840e4440d001e0009501c0c40360030104040d060507403068028100c151044d40c0000c0c200302080a030394000e101481654850740c0c00a2189850343c4d0b640d86040d400400703012611501c180080750015860f80a0a40100c07507440000800d032141508100440034503070002400b42e0410702010700900003207400c03107094581c402ea40c0358031112034002d24843c900c541c1e001250080c2c1301280c03101d40010150000f10081c40150292250740380c45500841e0980203e1007403501d000f070100c0105 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 947138552 1250 947137302 947137313
    0x5011509081209010306080a03020c0906041503121803050d023a02031b07091a060f0d061a0d0c1e11010e070e0906160503041202011e060e010819 64
    0x400f50404181408500540c0c4e40d10350905042881c0b0040e00941c1095450426515000d078450390302507000c43c0d04214107000051080380c1e03a991070000500800b510300710034160343d004a00c140c0034070201c1500d80c1c0034a6107e250194403600c458440401510540038114880400030714885e807002400c881c2d003400c00000720354000808005e0003140040d80030810a0b0349039802000d00032500406000020a02c0310300e0903403000210742c000c40380000c80c10300c41c0c1500045d564800c0704940b4901400102c25403140d45c0380104c1d000811943d807040c1d0a4141c2c241012560035250070252080d0905030604000c08001c001341603400e43d0a4840e03150704d03140f0140702003a1007400f03401d4911010032460000940810f6561000d40b0348042600022081d840c598100400e620040207800d621400d00c030f980044a40070448083c0241c08091f1005021a050303451070b0103001e2007540072000c10b40007601d00d80a004040c92031407000b050320380550740f403070036020001055050000640400641c00004c00300c52001c082d4641 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 947139802 1250 947138552 947138557
    0x51b0f0105220f060f0207050303040b0354010506031207170f071502041508090f070e0619140d42150e070504030510050115090812 58
    0x8044440c8602c071010038100c032001c1200b009000192a001112426958082e1810844d58400f61003584104014000f00c1c0404090b640c201d1070040f1000b10424946624071030f0b11090002840c2d032143d0500d103483c11121800001c06c5a046a148141c214144a002107402d9440489006405034003000c8079501c01c1e03409000801200340140308412001815007000d0860b0b50101d0072880718441c001c16050140b058003e039014403400207190840ca450300d03101d401c15000459104140600c402701d000036284078001d014050740350201c88152003403191a540240724400701526290700505107506000340910b00000c1903402c0e101280d03480e072003000d600000c01c0b0f03030400c000c60215010340301ca075540c0c481442103281ca0985109884200000b001600300001c10381002003c1a90300c090601d24694920400c01c010b00d8291084504e0300c04880c0e5481000341c910344103c1e8402000d620451041c0d405c00081c1e6480141a00c10320b0307200c0d1076041401f000441d04640e883c000c6451719040702d000007a040840700d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 947141052 1250 947139802 947139847
    0x3c0903300e0315091e01090c1d06060912030a0909050117060c070804260616050702040902040204051e040b06040501050a12060f03080d050f13030c0206070c03051b0f0105 75
    0x111210a414507150b0b0700181075500c400b170080d07916031010340100180b2880600140042e0b0421164201c551603040d514640c02506040c09000b0024a0710816120310010f0602100800b040b2951002a10001040f41d0002d100d00890580703080300125080ca2610804040f041103000202115103980e0a00303000e40c0d1002e1030488009a007084002015401c0031a80c100480414a00c880820300c502035a0341402c00082c0b0017004416503940701a42e141d000030a450700c80760142c400140c0364070180301050081c030803074008a90144d6132901428141c42d40110300b00c80782509541c113100380c03603164041c0203244c01750303001d598085002808150f000c54070400c02201c420303001d6200480c0d1355644440145015541d60820380d4107240c00031f00c84505041c00d000d480e805c400c4025551314203150180704a00b80382004c1e0703001810040c80d5202e24096598480035140b019400010f041502903403480e001e40d8641303114402d0340c0001e0ba103560070082883c01070080d4800140603142e25140c050034600100d08241f1269 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 947142302 1250 947141052 947141071
    0x4090b0d0f1a07020304030b0c1309020c0f01060518243c09060111120a0203040e0901051b0f07060f020301063c0903300e0315 56
    0x38040808034041e400c0d54a600350040c0809115501c110315860344100005041405650080104100140b0f5150300242e110108003000754444900709007a4010149590010343c01d40c0c00850070360003c95000c195071b060f200044d80200240c0b595078040c48002c1c1009880362040d5448100001c2c410170722411880c0d5001c24510030502c0500030748001074903030300440300c031000c4010a40204801ea400e0041c00c0b4004c000d070360140300c01103880c001c0c001091000d0003049181080304082e049865000104030b90405940c0d425181511a80c0d0b402c0025a00d41161086568882c507060114424803c184109405048044c19215000404144003145c55005032555841402d0420103100030a40318810440705109040025a4a51510324001c00c80c0d070020007807103100300840d000004200c122590301840c50125810241d035070301c0490030684803a003c0740d20107000f089055013904415080d618a5603801d44509040343c0d85410760f420100d64000341511050741540c0a5820707680300c60681114540d002e40d040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 947143552 1250 947142302 947142319
    0x90f05012f0a0501060b0d0501050d1101050a2f0706110d0e120d0924080609092503060507030204150e031e0f0d030b0307030308190e0c040f060b04090b 67
    0x540e5000d01711500741e0702c0306000441c041441100072415008090051004945140300403281c0d4680003020511000b00c217061000018968514600407918010400c1c000303011981401c03450039803c20240712202c00003299000343c10020800c103004860307c1002941c7c4000601c01d01001000c01e480064000210a41c01041c1032440314000c10100000e441c403280950318081803a2415905100800201ca102103000c241c80c0c88811001d5808541180d000c04204d94211158039420f001c2c506040c1084a0000c044640c20007140d846545143c40908403131050b10701b0803507950f44c618202c04a008501415030380c0b0f481ca03c0c0744000785115440080314000c0080175908814181c00207009001c0da45000c0039059000002c090412060a120480b4109401c2c14103105040c10100080d490310740b41c0c0070040038410880041076803440a610300000b509003418040000031154080c0f5595502c010307149503c181c0c00d0030030001c8920981d0044800b1100c02040c054181420800b01c8806048400a11500007429 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 947144802 1250 947143552 947143573
    0x5101806090e100b0619031d030f030f13020609011206080105010f0f0812041203050c0a0b0a230114011404030605010501080f060d060203091c090f05012f 68
    0x2240300b04102d42503000002c0003407807116031012041d0b4035101da00c2131241c081070140052500c88500da5a020b424146400039103080d40e410010764281e040e003284c55091101181c00140302c08183c2c011405070f000c03c28a03189a0b074650307401c1c0c401c1c04c0079080005c0d001081032020312119401000703441070403621401c0100b840c2d5210b86070103003140c400360f00418048040e900f0811010150202c001c2c0949080c1c030140118003440b400b140106d100c0c9104002811000300101024184100191502161500141c4d000983c0034102441d006030195142c1e00b00e00d180090140341c0c100c0c000d003a14031680c80c0300e59251b6180e1a04111407061b40510200b0f6041c0301c0d920074142c44810106000700060340c0f1541d000034165041200042c00b550b802401203000300310780c50902c403107503a60013501c40000d0352012015035aa6265003009040c0803940743c00000030b980504c080210030b41c02040f281c082c0c0f103a19000008041d50f41004652040500305d40c0c6100c5c031a407036080d005500074032061440d21913180046504034580d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 947146052 1250 947144802 947144819
    0x1303140c180717280204384509130b090a03090e1023130b030d05072f090c03060307060327140102070b01090b0405101806 54
    0x3822a0807000301c44c0c54042c00c0342810350002c0c44d014001d024107011420036090080c1c02c1e20012504d40e40c5400d00000c684411004424990140404190007480d80d4030340d84044041015074400b40014012110141c010040180c08a082c0c2c0841041c0c0e654034003464207506c0203000b8419400b800c81414003c1760079412002c04d40030070b1140c0c0904c0c80400181003c1a080c10028021080d40d0048038512944e0740070710541c46100c5501e030007035a04800c203040d1140c4990031110b1141130034548071904103524240401400610b44e022002c03001c020b0f0140d4070940c0460804071182c2c42500c00041142c03018805030743c2c5410801d090502c0941c140c29580c036001c501c050010720120001c03100400e21110000c200300c11800c0a0000c0c3c0c005181508052008261001104042800032000781c0324402c04040d940040c810005810395058000100071903503005e090400540a2009001d420308050170103105084504080c81034a11802c20340b030115a0240c10400e207148041c0c80c19201c02c1c40240c803290003080802c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 947147302 1250 947146052 947146097
    0x150b0303090d170f13050a15111507020a060608010c140708210901060b04030305040308030709170304030b0c1e030903220302011e050f09060c031303140c1807 70
    0x1460b0359803d445d5200c42050008106441d04080d00070050070604020f5100c145181841c804032030706104440e224210b00d00f618000118800240c04001030701800308094010a1002c04180501e03028820345486d4844942641e80340c845103c0050b01c10099182c00301c00342001f0701035140c0300d0009580341003401e0000003c0d42c58122400c48140342c1010a01c004420248a528020000c440086040500d982c82c050428003c511024080c13040000008188502c81d55070394019000310b100b03014625040303150081c1d07a030f009408201c601e444144040b401e00c95400c02982e00705200c51568a0310980394601d0001146c2015100311000d200c14131041d0314401030807040c01c580c605601203050b5603610b1400010042c65074854111008804154203600b001d0b0b0050890b0141e440301801e19503039424820204100f88901000c000302c501021550703900002c0018035100442c0d01400003001341704400013146442d014a0607913580e100c1c0c00910592002e500207500140d01c0304450a203070344c0c007099004c440c2c0e8419 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 947148552 1250 947147302 947147317
    0xc1a1509160824270901060303020a030302220801020316020703051b130f050a0f1406010f200c0f060a020601030b10051905011b050a300309150b0303090d17 69
    0x2e6a80c24090110404844c0500341d0002c0340c04020b010341491502d020b9203462000c08080c0805800040303000003d61208042c4000c1305880da45803940558480c0c04900070b4005030707601340800d468052880c03450341c4000b50f107006586d08040602030a001c840c120300d6484210240840d0411030480c040c081c83c880d580300f9801000340f90341000c15145484078400d4110f840200380c2c0213160b45015004185602c1103548140c1c428400c1c00d001000d924401c0e810744005440340000410000c80b400118046500400d2001080000365100c0c0603003060f00003003109134000c1801880041e4441c00040000c6901498400d03084048001c007000310759107401c0818425512960f40d17000c0d440301d1440030401941c0c01007410b000d04503000600340340864a0b0b0f494a442c1c401d07800010f01070301c448000400006120300846c02e0440c030840703001e00c0b05200001028001d00302d140d60aa070401e4501c01e803080f8041d610b01980d005410000c0166181280000400c4422240b480c425500f940c0402c6000240d65400e50040400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 947149802 1250 947148552 947148589
    0x1e14030a051018090b060406140d03020106080313080111030108031801030204230a06031a0126070807080a02070309121b08030403020a0f0e01060c1a1509160824 71
    0x201030144c01c5c4040458030190455000f1450b000c020030240c4031803d604844503800700c42098641849050881c05000c0d0b5400121035800001120391041800210000446c0d204000a11800c0841d000c40743d0240000d00c111042a0002c0021211669405886001d0242c0505005007420384030141210051012030109075540640544140f4514104014000a000e80d103414001002e1000c901400e500105e60038a040c4085545482120800a88105040030b2003600b100e945141c1f803e002080c0b004192500400300302c4a4001c42c9a440e041d00884038071a030181c840c0c020307440c0f03400040705901003000c40c00d90341032070100c00c05521403800071004070041001c200156219810344c010449a40841c1e03100c080c103000310110400c40503a91001d0207045603540e040034246100b50782811002403c1e20f004112011040d44100300c21038101c0210010310082c240da0207074282c0d80f003000220020b220000c010020828410006254120581d00e40c4001d244420800151031048804109a070315005005207c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 947151052 1250 947149802 947149811
    0x1f09080d11010f0501030215090f190e01060206090606010809100908040807080c0f0114040b070302010519090b06060306060705070f03060c050a091404020f0a1e14030a051018 77
    0x901c64240502c1078550001402003016500d5903000610321401d9144548000d81c0105e1100915550391800080100004d8070390342d18011884821480e0b020240103011707070341c0082e00002c900c081c40000c0f410310a44c140e90091026848110055681140c0241045510f00c030b01c1242001d2124640280307031180303208020f40b40d1564100b95031181045066040101507078094003e40300031355142c4940fa105c00400f801c16031110b2041d50340301c2c01030748215000950100700015415040641c15401300d482001c040c00810251460702181c0c80c1a41e101407405004224060049045440d155004540001d00181200d15112030399a030941440300310392081808401e981030800034008540200c4030800c28500d0b140b8901020010050b2043e60540200d0590724241c108058064683e03034101c40310208a640701c25184c081156000300600d11400600c9403038210104070040760f901422803420340020195160382103903202c00d10000146070040000d41d212a404000081d05031141604180505c600403002c00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 947152302 1250 947151052 947151077
    0x1b0a0605070c0201120b0339010302030105060a270e0108100c0f180302120a02010306170304140409020405010b042c1602121804050a0b1f09080d 64
    0x20100c0320010300c0801031100d00600d40740181e0744098003050704606500c00240c690084000300c1d162450341400604840300c980181343c99032005603550005a154442001020300084c40110207900080c81025004007060103e061660f0080b049001c10b8030404000720030a0051656050b11866694050b4814a10741f20041c00244401d1000741c0504040000900125007544401130014058001c9a001c004100030950084591290030f5002175030018400300800441d21001516600ca14a0490109140080016078800c03069a400100c00107840658105850a210180300c1d88044e003030f46a00c581e6650359040140c3e15031040d20f0180c041e48141c1921541804102680780c82c0c03200752601e400042c4556a01c54107001002c0543c003440d14140040f58942030502a4a424142d1280950030703100480e108103141c101c800c0d1000c1140301201d06110507110105030300120b4030543c045942100703030f41c000e0310180e180c4040890380c40300840c50800003540e6104807840c04d00c400868081c0000d4003111401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 947153552 1250 947152302 947152313
    0x12c0c03010c051b030c010606031a180106050703050c0610080d0516030c081207030e150606031503160305030a0f08070c3509030d09031509081b0a 65
    0x100640601a4020018001003410140c0140074550b125155070b82401c1c85420340e83c4007031069800211079038000740041c603151a0090060400905004c100c075a100c09081000c2c80d00d5903070401c0b0034440d1407082c40036909024049610340c0c0044402da003031000070820b503030180608001c0c036032080c860515000302036030900312144c0c02c4c89810030b5271204014061140144d034901c820304821045900d0700b043d4001003001e1821101501440244080c1a000f41081018050f015003010f00c81c2200d14042da0010524100b80c000d0048040c0e5620342c000f14240300146404100281c08005910000d048880c1c01c2c2e80e003082051000020740044401e0740020680d98681500720003080d140d0007290030161a1444c2c403060080078400020000f030607126062002d820900c25881d10440360702600d20b0421818500c950b440011075120b819a20301900c81c02c00c14000c00b0703100c0e4001e20b040d40d174007544911203641414041c1c801340c82154015500e1003000c00c0b2502c3c0b41a152982d030072402481ca40030b03021040d61810300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 947154802 1250 947153552 947153563
    0x1b0f020109050d1e020d0816020a0b1c0e01140a24081b04180803010305070e060a06051e07030809010605010302030114010507050715081b0708040e09012c 68
    0x81c50080904003868800503902c0c030304a1103103c141c403059005102c05800042c031040c806001c05010500c0c00a0b4060f07111a21400c045c402e00e0003a603401456030303a29441020300c0c0c82a01c500700c0d01200c01c40e80300a15180e107a040098182e03e204003f00e402a14102c0c0180041d00548840310451f40d515100c039880850042440741114900756400399807841c02032039a07110740809000081420b03010708582d040d50b0b5a640f100e40105d1641d1740400075a9610f03e09020710303600030300094410384501c040018004144100c00fa1180b100035015003c0c039032808406844a402061841c0904003091948080005894001e407010700c1c003036039448080b8108007885900b1039980d60011810503004200500000407031146840c0c5030002841c00c940c0d240710500700681408a160412119015800020b10445500c4844c0502441d110b101d050b00411100580d0240c601c6980070003402007800784010807a03590b401d0f1071654170001400011941090071a07030414004482c03038014081104c84400440c03400810002d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 947156052 1250 947154802 947154809
    0xf3c15181f030206030109090606090e0c01020c0303040602120705101b030b0901030302071802070203010f05040b07020d080f0a1e0e0c0406050a0b1b01021303030e010e0d060b011b0f020109 83
    0x110301c5151411500070072034610050040f852510b4845c01980108052540302c1001001070100030071415015030703c10b40e250610100c5980c014807400305c216840f80b8020003224100d44283d0020001841004184d502c25000048180c0d4103000c2c00403540038020103805403d50100101074282c094246446001d01105d020143c41d43c0540c15000041c00083d40002e80c50742602d40c050701d89503c041d005200798010b4801d0300342c0250507500300f0712001c015200f1074102a000b42e1203000581c1903503840b454126942c3d0111201c0f940002c0c000c8011551031003030707000829085580048040740700001405000300d0076a0354038503907407169540d21000011610611040b00c1092040f42d052015510704800150505254051034100c00300000315904e6410140451644901e2140c00039502c6412560500e001040644420703400711342040e0755008070390300ca035002d00341d24000104402603c1010b40c4552004205021140c0c5c14818400f4100240f152003c60745103280384140305003d0380110502c00140f17141d84503030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 947157302 1250 947156052 947156101
    0x7020f0a38010b0f04180504030306080a030503011a120f060306010f05030a02100207081506090a0b0d03081816080d0201050403050412020301140f3c1518 68
    0xe5414004088640300030b0445103141d4500d5211098156240500d100d0381e40811503044041c3c1c1403031600134068201d40d2103680139442c2017107100d80e2044619151140140e000300041c504100502190b6140544170400403045065103003032100484981603029804d4400344a468444020008646000c01c030140c05032040300f14180d110741c503042c0400e035224403200c4020301c54241c0b02110540a8820410301c0f0081400c10304440c01c111390301d0054003003501c003606d07250b002d849400009034140000740070718240982d01900b100c1449021380c5003200c82c130702e0151031a59001034030614542d03000010040d0041d01d000600c401d00240345400a02454042c026a441055904280c10000440d411000b03480c125074207003c080c20310105920010340100b02402c800c2604028a00a01030715400c00324040e4450201806890300300d01c00300c0da903c1c4d0070f904000881d130b402c2e80341c0c82003c04020344ca02031f03c10b8210360f0024402d918007010500080c00b0103203078108070941d075800c1d004100c1800118105d41001c4072004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 947158552 1250 947157302 947157383
    0x1180b151206012f01020c061003050d02061302011206080303012c01080309090a020d0f1a0a0f09090f020d05010903090e04080304060b120703030504050f04061d07020f0a 75
    0x11101c140c42071320302100180c2125803400d400300c4503400790100c0b007030803805400356031076813400c041c0c0580604070902082da4144116001d030441c1500029425014610118058103100100e5004485620300440b180900e50b864440010301601c0402c05140640300c01e402e41a820b03034810811400c46401c0701c40d1070400f0004507004000d01c0101200301c458000056440d0040c3d6510686400c0107440360401238100c0920300030580011190715070001c80302d8442031003031003212841c410801c064110030f030165a0035103000080c204800c4406500920099108060700084907180b0f40020700c008503211400d4480d0f94481d8215410150300c12041d03005003580302c00480385410544c54802c92400f005100910807541c03056800e40702d40e1488600d0301d0300000c02c021956403036103070700e401059600940718140c00b82c003070070346030201c5440d0078010101030f20300101400540e90049010740707c03440360142c024001d6004020040d40080300a03c41042d13170f24040e116000c2c0300a45806550300c2140c800b80c5110042d4500d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 947159802 1250 947158552 947158577
    0x302030913090f022e09061403060f01030f200706050702030a0e040f061e0e0703020708090423011e0603050618040c09090506010906060203040e01180b15120601 71
    0x580406914450301036039024112118801511078500c0300a403500520356040c3c3d40658900c6e4080950001d9603490745d80d2042c0081400c15165042c08240c03032080c0c2c012114800d800703e6500c654031107100340c101c8420120f00918403400c101c8040011495110628600040d01d0052096a01901790402e0a034802140b801d0182d20005101d80c0001070740c584a2610b80007910f03540d1809400c44000340900d805044240802071207503000141c84c81c41100003160385e080019942a000e40f0030b540c1410b82000c3d035a460556500c0420009044000a81c489209031921001c480c3d141030300d060780078051601c02c0701128007445030044000c035843c0d407002081500b424200f066607240d0380c01c81410441c407090004001d48962400001e000a240c00080c0c200d850400b680017400000101d09048840700340042060a485400c1240c40303100741d00a44a034803141000412403a0344c907440380305200d4000c070340004151340a94002020440c0311070414040340004030700941040c5003928080e410030703024200746200108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 947161052 1250 947159802 947159813
    0x1d07050d1d010e06190209030a0c060c0b0a0c02100f0f020a020f0606030a021806120105390703050d02090301021206040c09140f010203091809071a03060607051603030203091309 78
    0xa02511144160f80c010a41d185991410481c046805d4ad025108025460301d40100400f1114007003010b60f000c100c90030100d1000b001a108402660380964090000340701d4120003007000e0501880795082d04c03981c60310b43c0c0c180c8088520260180d50000d0740035248094031502940d1a291001c0d107004d120f5000204080d00603aa82d60a0070801c414804402040741c0d41c030000100b040c46515110844ca50811040200d540c0000c1451000c40600030030054800745040200685002950314401090f0800c00803800880e000e01c0c00b6191001588402628188400c00403e00766084480c881c0307221003020040c403003035142074010162096403d20b42130604600d82840035101e002e110f000140180c213406040310441c0d02c28001c565003a00060481d081e16201c0c024070350501c41044411019a008480f8080744103882800c0c0d0031817100c00c0303260b683e04503260f00c3d040140315440500115820b00c40d241c1c0341401880000850380046001703402a40e15040401e080c003501d4031718800c00594079072400c1c0c0070000141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 947162302 1250 947161052 947161081
    0x605042406050307050f040b0d1b0b04080a11120d0305011d16030c021002030c03010e0606030705090f01171519180c0c021e010311041d07050d1d010e06 67
    0x85003190061212514003022070003c0809040003274010f4688002e18007480484040c1030f90700c094802da000f03051542c405d191180c902481c01202c45c2900803000b0013000c513594919043c00c60000804035003092901c59262881d1650094180d80400e440b80d004204111820000c1e451a1410b00c0c010085490054091070400d1300402a95082c103988054200d90503208105500015900c14000c55490034020407030400394209100d451400038160303000401c030341400d00580740160259100c83c1d00f040c6e040d4040200e40403149805c070341008000c200144440d80c03a030b16503038083c10f415640c0030351083e1070740c00340300511000c10500c1c3c4003140c00d91001c100307144040303000c126200e1803c040058801e0144d2000c071400c21031000c019500c00a03203250000441c030000360740c1c02d015109807010840040720800114490183e031103a55040780c0414480382d00c05060948007940200d552920528082c182207281e41181c05500341400131030316958001c40001001d100b0301e01d00700e04400041016203000c40c042c80f0300c00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 947163552 1250 947162302 947162309
    0xb0414040f0221070303020a0b012c0c070b0f0a06060e030706030e0a05011509151a07030c02060c1b0909071203120c03091e020f040b01020a0605042406050307 70
    0x4800c240d90f10120010f10030340c0c0100c2a1208010b54900d0f40da2030900070f50303032011144140c4880c00b0f43d800000f04c541d600d031491510b012242501003890780320480030720340c0301000409180d00c4603420000030300000c0d180c0c444079100315040c00044070581001035130007040350310355080300052090300c3c4001003407a6000100c940844e2864940842c2c810458003100d8107001010800030000d40c24507003820030100302200c07034900342c440e8440100b0415201c3c1c0c1118481400314401c003690480c841562020307451400d8000c1034403038000c1c1031a0400070f00b030342d010036000c0d0301c0444c1229a54000e150a1030312071464180e0810720748001c0741e01131001c1c241040020b440700c0451154849400c611462542058041e070000d54003a080c0c04030401200c400d9080280c0600240f61044440c105803c403010200c030450039220b00100d80107080780c10080c0c914001e0100608050341440c0c1548543d09140c400200c0da4094584207a02c10720720754008039401c1100030158022a07106070100c60400205014944000511070f088 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 947164802 1250 947163552 947163559
    0x80403080414090601121d0f0d0210110d02180d0c05040f1e09051e0c011b0309051309060603140607082404020d02132103020601031502040e04060b0414040f02 70
    0x400d10030707c01760003555220318a0a00c1c0100c0c01d42032028080402c2038060350030943c081c0d400618510810344112450321541b101000402d000100002080da1b010704824a825803c0004200ca1140021102d0351031070800c458540e0016000e00082c1418010005603100d034034428000c42541110541e4400c0810070008046030ba10700340b03e428030000704441003401c040c01d803070030b0800341e0f150400756221000023600394082411a8403051821092003405046c00760165500454203082004100404807101315031840315480d5410b4a000c03a0b1503100e40002540304440200070503203ca40081d003001401042d9600744801c0304c2c10414405043c1710fa966540c0048440103111158210018009000301418285d403148046101c8a416440303800c0e0101b640c45c0404030b07030030b500746440c5d015059528150303000300141c1100c00100001084039080030fa0790201c2d490054141a120034003081005030465081c2c03016601c41c05000c40a0820b8400c420054560b01583c1e08107180c00d803102c0b490070702182d034000d00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 947166052 1250 947164802 947164811
    0x4020d0204110f130608091525091e08060112050307080c1b060c1513060c08010f05091003200a0f080f030c0717030708040308041409060112 62
    0x11581d842d030000020400503404140c480d90107404200050b0070a10035824464813842011481c140580c01e00d9100e02c4010001b01061404000c0380121120301802911007000350012030b4941d450706602c1810b507407c0681d5120b40591038201078070700d4450707070140348a00300721080024884844082803490640d1503000096000c01964540b807440c0d4881d000d0041e00031500412400c5044801182e60130714040044981c031544540b0ba01041454807460204401c141d103e0002d161890501c1c0c004503a000310f118401d1020b182c0151183c40036521424921400203110300b005000c0199404840340c0542019906181c0515040c403003646004850f00005c2c1824150540341c0c19041c0800301104c44444019110398031407555801c2404100f40f003402480f82074000c0342001c40d1000c8001040c3c0da4030764109001031100902d001c024500d40301c1e00c0c880e0700007540800c1010401041090008000443c400c8507810303942c625000d408145689000c0945100f12000410b2011030f80c0d121642074143d0520420006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 947167302 1250 947166052 947166079
    0x61b0905060a0c0215040e151f021c030b240904020f0d0f020406020c180c130806091c0804030c02060309070e04050a11090403050415090b0c070801230402 68
    0x1034030a80f842d240254030804492191503040721200140080b90409409011151207001a900c1a000d103501c4132a00070349c0b40d00641e04420001000303110305154500564000b6503800b40216a0b4400d11814a80401d8443d9071030b00041c108104405400f090142a91803005003000d190f030740502c01c1c82443e5100d141c0124000f2003a00e0030000725800025003000410000242e0351007031010b90411720944025000b9a054808641401d01681400c4090580388034100d607180304081c6800d030040e118582e19042040000f085d140c03002c014103801003010030b001340380f004054030788442030014900c500030030040e000c02030000181d00054800d068580c12a00715443c0d036211042149800703c3c9a2181c400c0c3c000c442c05010a0002c0824400300050148030f000f92446040ca003801255241620300400044080100300050b2000c5c94401e0610500c030310b403680c0075580e18803103c103198001d40544895604101410482c43d4424401e20106400e500c0b4112806124000000809540103201070302841004a198 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 947168552 1250 947167302 947167307
    0x90816090b01122d020f04090203042901030b0a060b03070c020f0d0303090b090d05030103060203041505040308180c030d110f030a0504030b0702060c07020f03010b030d0309061b0905060a 82
    0x101501c2c0e0410041008207200d0400f0407090140c54002107602c60721308001003014003240219a111504500080d1801e440e10800c1c5c4d009610040050b21804500c161000030368540368074403490742008040110255045041c815003091001d00303a41e000501d041e0040055511032000d4a601641c00d00340000ca0f40803030700208040781e00c0c00c07030030360740c4194403600c400f04058140e408290494000d21101c0f10944e9038103002552450411403250124206000401c000f6041c0c2e0010740d400b07842404040010050300c5010001d82c0d40c150340c2200403510b4241040200010021980303a001c000d1001171285000700c001082e240c410b100d011008120049249541441d810400061248070300011030741da6085481004000d0f42040c04101e036034852000108010b1480000c00728041c3d0000b400d0346162181680c00c00a5802010403a150155243d00c2e010075603a83c10700000c400c1d120349450100c0c9031209440d00008864561000c00e980482809981406645c0110a602510420b036001da60b54005900207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 947169802 1250 947168552 947168567
    0x5010c0c05030d02030a021b010c2301051303080f1017030c03040f15080f2e060e120a0503071b080d0504030c0b1611120102030c0307090816090b01 65
    0xa030144510743c1c41c114841d600000808191110341d0030303241c1c40d28081c0c0640c1c00c0c2c200402481c90008020000c0003000c144038600c400ca690240b503400800e041502c20a56081d01d0301116000d02d4156155241c6e4107164000b0300c41031340a2441d00c03c1c0881442d000c1c01802060b1010300403081134060041ca10240c032901002124003141010045035212070344c500c0d01142404281c000c8450400c69041e0031140c150240000500842e101100001650341e00360040f00c07000f00c031a070030801134461400803c05c0034051f0900361000d003515507035510b80000c1c12014030845c01c51540280c030710f0380d0029180c540801c90210950b402c030380d0300c507802003c2c2691004820840301074940040c0c0c0d0a0203110718440500380c10500900c112481382c802004610750701c01e00d00107180149600ba8410b01e800380380315000110403403040500c0404c01060b0024585503004035600320f800440d04591100c4000082c809901d8002c45544001c0c43c425005112401c4951020040b42c6028420700341d6143d05c800c505401a80100d04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 947171052 1250 947169802 947169809
    0x90301020d050f061008010b0306010e1807020120040803040308220b070501150621021620030c0310090c0509040b16081e040c0f0807150e010905010c0c 67
    0x90030b100d94109805503440c14101601d07114450410f403a20504018080d0403024100e5600302c2105085554841c01034981107402910755030b0011221041c0c2040002110800b405207029600010b04000341002e04409031006818245a81400744010040b40c080001250240da07807081089458461845226400c0c4910100f013501c1d60f43c19403008101122046c0180440c40c0c000c038000c1c031881d28000b580ea5a064403a0007404001540064a44507030005080d03071900c480303e186c00040c5400f0900e080b0f401e08840c000c0040720704180300d030f409003203010340c10030342c01c1404800310054101105507000080c3c0d030342c1e243c80c5458101c030303240c401010510115240110080802038040400c51400d40303003640206c902100c240c600c400c43e2440c4080090f20980c5054480e520034600d00245600c0707840320650b00c190041040314201d8038000049a140003204015005200e000c00a00ca002c0c00e18180300182c5144107807c000b000701c0308000480d2a80d04c02d0400c01158402e0030100c0d08c032096400c194145e00324581 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 947172302 1250 947171052 947171077
    0x20708010216110f0603250c021503041a09030903070f0e190905030a11192a05120a02121b090405010f0c1d011b080a110d08012303100209030102 64
    0x402202e401244030b1f000c1155040c800c1000c3da020300c4070060340d246000d0705c000f9400c0500400344034100b5280070020f43e0010f005409601c0404049904011000411202380312035030030200d000243c50030100000c20103003207899501c0384400d0811302c50b81004a0020300e0001c038051082c402100d005401d5201c600c5090700a400e59641d500b4520380a401e01600b9044221107100712096141d9094507250300d0038045500c0015280705029400c50000d02c80c5000988aa60048030314002580340c0d52124401c1400744200d016110092407030040054040700d090002c1c07881d41200302c1d15035000c032560211101e40c10f0102c940d400c10382c840d8103255004162100811426a24120806400d60b4100c00400810f1003e00e02e400801c00e101d500458108003491403111550308912580ea0000e44848080d0074101100d14020004c844030212103454061450000004141c103072006104140445410140481c9002c1c80c250441e8030440200340c0d20342d01c102c4c01c011403550100e000c002c1c5030740a4040751220f06244 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 947173552 1250 947172302 947172307
    0x901090b040e06011d012102310e070e211f050702011e24060f090f0503031603091205060108060610170408070f030e01020708010216110f06 62
    0x703504000807082c0c01c0c0d504034082207a8401140002c01a00c020760502901a134400008541e2003a01c05900a10a60140e12060f000d102c40400102c0e034038841401c4840100101c0d5a4003c0c0040340014400c207500401180c14101d0208012143c1044406100000503120750031104c404004541c00045417a0400d4000d001e4500000d90880300d81101070038207003141908104540b82c20105900300c40a203541e62780910702c11901c0c0100d61001c0d901900698074054080c00004107221642406130a5035009280403400c2d01789019205580180c8a0014000d420640b0700d504d81450b0000c0d47d28014242c003051101000c83c000c0040500c41c18050740240101101c2c1c2c60442040e261203901d0b0002405112000d00c2440006900c5180c0710356a00c4c2011540d445084545040c680c51131100d1500400541e0903841c10409040010f0880c441188180c1c003030364510b0802d04d4001c1c0024209a0260300c00741c6281e00500c40881c3c16942d220440416549c8212200e071a0132195020440c41d0308000074466101101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 947174802 1250 947173552 947173559
    0x100e15073203042a030807021207031a010e1506030a060504060906180207020906100201200304200a0b1605100e070e09120a0c061a0f010306080c0103020901090b04 72
    0x4070186028a1041d0401d0941281e00b14012000c40c9110349510400c07803906a080001c0342c2ca100007051b616001409a0344485110f966070361400c2c05a81c4100d42201102461040d003894801815016154142c0c3c04c0341030f8148055118480640e11095a2069000002059801080341d000d00024180038009004840c0d492190000601d194410f0151030b005d00d00e038021026110b0320890b11385660051a01c003113501c2c0d03201803003400d07a600c0403044150340d606c80711604881c40129a09400c0f03603a040c15030750390340740030320f0091107605038114100c0c043d00c62188070760000d41e141050701c810b03214002e0b03003c0d441e40384180c028000c0b98500b04000d4864020b524000080507281c1d04409440c030b002c03500b1103100a42c0da50244104103011075503004960484450502076072240f8000300001c5d0780601d0241c88075005512800d00301c45206072100484c0307009214500c0340b4145014007031070307502090a04119071898984156242c84528000504145d80042c0c0010281e00030700401000c0d240c0c200455032126107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 947176052 1250 947174802 947174897
    0x70203130e1911041401090f030b04120806031506180c04080c1905100c150501060305070f02030d0e1606020303150d020f0103051b0c100e1507 63
    0xc090707a45902c0c02e2408902d2034210441070060a591140306203415240514200c0c00d0020f2014008541e4100100ca02002424100c214601e0010754000c4451501e54140b901e066901d40d003680341c890b03050250b03040810011b41e0303010a103800310645401c0c50840301d40e11000010816007284c483c030705074000004103001d50000e48402074015074a2142c1201c0200310302301b0400504d100380f03005c034480d048082441882141401102c13050007019034201400c0d60b00361a520044e496040c05140c4501d03039a104010088035505025283e08001541001905002ca4600081d1207200c0e02c030040c001726890700041d4070b00707603010401e13816001030a05a40006070740743d138402910380d030007900d81c1c028980401c1c1e9010920b2801ca82c4d200c90803039004215101c407000b580c00560180c50010078207204900520ba4070a2100c840400900c0d0200c1d81c2c2000d0594405856680822a018120b903589590310020524090303004659255800039054244071035510700c6c0d45d0f00012807814950040140d00110141013820344c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 947177302 1250 947176052 947176079
    0x5030a11090402180f0d05060a09170403060f240b160501020a050a020f0c1011010b1e09130503161e03030b1f0206130203011416090b0a020c040507020313 68
    0x8200305d941c6035510982030b003001b0560040c503070302030125082400030170003010440e4008030195104200107a0140c2d01019481c01582107070303006849042d1039002d040b880600911840c800c40303400d100d840c50380304800070b0780b584110103a000354200084c00140d00d03040c0c1c000302d4200d03841c0140d002c00255a944002240103095030003a14514015124611420003007940c04540b0011020000d0452580400c44880845004810b800060059581c4e11108825502c4144041404008240454045101850038402c005000500095205c5a6100d20800052021040350303213044841607a034a6404032402c014828101c00044c0449600d103000940c820150150003e9520300700858100510030324810b20201c00503404084440142c000c5400581502a82060b459040d80041c2c00012039420f03000000000440544000222040b0032650f030b1042507004112a0141003070850a40c2050042c0ea00655103000700d04080c0e11580d2100002912f0703e1081003501c0110746650b6242510342d9a4405456120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 947178552 1250 947177302 947177347
    0x908070606030c230423090f1506061e0409090c0f0605090d140312010f090c110705060306010e09070c06151202090c1209060717040305030a11090402 66
    0x1118080b00052980129980810340031849206000103804181040300506152140045607402d401b1b148110400001d20345228000100040001c41e405030001441e200135003030b90003e200c03007110404c0442c0d00c0300030507149040407049624a829400e101c0c00d4841c4d01903a00200300b01440d02c0a08000d00c5844401c1104441c008c510040764561030f10340498a03403280d400d5241d0070120700300215001a0b045a00022000c040c4010740e8181184101880c00110089e840103000d50300021090019040d42e100b168400c074041d003800c01c0038841c80c85a1603202c4442d4403400c2e21801c1c01000183c80e503400703a101405004d40c020031a12591070030540103007002c942800e003500c8941c5019003068030b02050001b10400c1d2000c4d0174000c0b22203205542003040c1c02c100144000917001091007142c00c43d04800700e81d80c0c010001400a081e05242002006244101400001c4040c50000083c007010035040000c4903000780c410503010800c00e0000d800950301703200d1141210f81280c40096100d4030040e035a120521007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 947179802 1250 947178552 947178563
    0x708030703180e0c070b0a0605040c031b020303040f06050a150306090b0c0310050922031d090c090d06090507150e1008070f0e040603080a020607030608061504090807060603 76
    0xb040e03101d040c2e645040304115a0b90214010130884100400d4040c000d169002070f4942e0007040d1503440d4000b040036036035889030850200342c603007000c084030100c000300c41422111144021030461409e07496031500b801a8038000b070400e03991a030205002c1c00340c5801c1509007002d41100d501d007059581c94001c00505070500d098a041840c0b41c0400c2c2c00c5d405081c126405072032811008644e1030b042c0020040c02c1d0901601480c61091610100c1003003c11090803544440e000e40c4130608540340c49070790b181e031001c0c40c0103274207204903e020100702c54860300314141d4070300c0a010744050804040e180390000c02000c12040240141c4a451000034800c02c0324011011156502d640b1120181542000d01003070303d00c000c0b448c60109079560001011984038100340e01128125150000c0c8606480d00401c04603a00c0d9002995402c0c0c1c0000d510300038607010849960002803900e410024a45030107105911110003506519841c004681741e12800d03034864020a08032508803511580d074030681c0c6001c81c002d11081c44102c84 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 947181052 1250 947179802 947179847
    0x1308070b031501211512081b0a0b070c050f15060a06020f06040305091519200d120f020d05100803040b0919030609050a06060503070f0909050708030703 67
    0xb4154415024800c4158141c80100610540f10645038050050760000d001001c4503c03000240e2040455403002c5401d000d1840075588105940f141541c00d00f41b401e5061569100c6030441c00016104c03011254041064600f00c42c0c100818902079080180c46000300500e403007000300c1c1c0d070103c00340d904020b40940e808443d544207490b40d0350010b03a2214880d0300000400e80014000074040380c000c1c0300420345002c0c01088185441150100f244094100d0340c0212444051a803010030220703003259054040c1d200f50003070340050403541e003d00d42d681c02107199440200310ba01880060b403100960002034801780e05e4182036440c0c211000030030005200031503160507000101c50001509200102c100c0381591551301d0b12515000d40b480034080d81444130f51322181c454180b03041c0000440c50520a10714124418030103004011081e040140607642c2c0313034101521075000000304002c3d06800c0326048080302c828140108000c0316509220341000c038140c2c800122030100081000425070301890080003454049440c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 947182302 1250 947181052 947181091
    0x606020d02210c0a0807030302190c0206030414100c0206090c011e0309020a03060e03030a0b040204140f0a03230114010f031e080a030e01060b0711061308070b03 71
    0x2681c5100e20940c1281d0802400705000d200701082c0b0040807404000e00440303014a500f56502155544401e0081e80001d50105500b01c0441e07148440940030952440c008820b07481d02d400086407072002400040c402d80100407900e03c00c007402e01c00391103043e0051034100308080600300e0103034a40c8411201701c000c81c040c004684800e50700480c8440351189161140000c04480440150007d140303a060590b4084e10382500040010031034080c50104a65600141d902c0303040c080301c220282e91944001c02d02c1180140300622901454400c240241c1404072044c0d880340c212000132440c0c01c41e041c0c00c05041041c0da400a10784903506028009000c1e80601c000700086080544000c207901d40130f0003021207201016004001103403000740d416170f1070740144002800c03011325075854119590211448001080e260b80c140c603d81e050030301c9120700601041d901d00780350158030340e100040300b81c00c0c80d581c1e07204400c0070624516030b18058038003802600486044841181e1600114851a0401c0381c80034200741708000d411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 947183552 1250 947182302 947182307
    0x2190e04050709170a0203030d140a1e1d0a08120702010b0a05120f0d02240103020d030309050a1401090b06030a0c0317160807021f0504051c060c030606020d 69
    0xd10a00b001e50b1101c1c9000c0c10881c00e05003074416a2006015031044550030700c0566020300060143c0c1d4020240050f24a4140a01407092000100718040c1e80d464104200f000541a0404000109028100040300c41007480110034141c06010a40c4152242d84444400c2100c00001072910b200aa40d01049940d100740b0704078240c4226a9070640c01040681e002c004d24201703604100751006270801503811481011440318644540c40758101c00680c000a1000b8040040b03407900d442c101349c050000410707581180c001ca50b0401c4860f20080c200356444031510280803041c05900b0f5101d07404444010030707400489080780a4545404140c6580c003100022030803600d00000c00079a866448031850f0034071461601d4940b88070000c4510a02000170401124a100c1010300840b10014407030722030151650320310300600a0494500103000e548201154031882c0180e0000300351001c4510894042469200b82d224807141c580c45d2a400821560920009a45464040d04044151006030b400c6602088004408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 947184802 1250 947183552 947183561
    0x50c0405010b040338091b030a0c0509220b01090f020304020d03080901020409141b0c0303130609060c0804120305070c02040b030a1a0f01050307142202190e04 70
    0x1d080c020940120704912800c0311080c48004100031420341c210841400c01d00c085e01040f550064160006a0b200852005004071142d641e0002d800501c243c1e9840e44c0c503401c0f41e9203a401034034410f01200d800104141040a14a01100f0b001888940040603900e802c244803130081c0992400141060b001400b2100c0c1da02c2601d118980080421308406110385050b604000c000d0110040e9540030800410102c15078020301d50541c110001811903454005070403018074081c1c03000c03581031400c100075075a5017180c0042a2a0802014404d001c0d4111540c41c00034014030a500008045900f0070041030201a003004210b4403580c0500138000b2585040c1c1d074210101c038822a04840480d04900c2c0f600e0260502d503100444106d4058126111a40d03d40c0f51124000e812800c4000c021054904210010f904e844103180100707019001824000d00300804444101142d1540300e0040c2c6a4081d00d07444032100129031500403003c498215a04c01c116403145840d000e6460b4040040340c0d444d0300c007004504107440f4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 947186052 1250 947184802 947184809
    0x30a090501030504230307021306140108190c050d0b040c080a20070f03020d0314010b0c01020d06080c040b19090b0d0b190e03091e0a080703050c0405010b04 69
    0x11014809410100154010709000c1c00940703649200141400a07101e01c442d00460100996004544503145841004903500c0000c018101d00c0342841001c10842120901900c1c07440d409003080140703581e070b80840e6904003d24006002100303050103074500704550080020b0400c80701030441070018114242c01d1001355034860207010006042c1d0b0f40050468007080d40f1141c80800b0382c0481c0c02d4400364020040b5101e4108200c1034990081d0b000c14601016010860481408014141400a03000b000d46607607017018140700f9030100550001300c1c2c0f82c8242080d41203030503415003144100705654640054503a47d00350061014052450514507110510301007a41d0740350120f2807510064010b050407075060251504130745964001d01002e0b44000041ca0360600c140c452105003400c82c0f02106520b212030182c0309000a000301a400420050159442c0d1100b00001c01ca2103503000100081c1c5440070944c2c0c081c0f95804503401d4003483da404010081c02180e1081402400c030340900160b602c0d015403a420384034511 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 947187302 1250 947186052 947186057
    0x30e220c0f030e06160c0506041a0612030409050411120a0b091506100302071505060306010f030f02120c0a080106030c0501020303072102250512031501030b0a15020f010c02030a 78
    0x5001170910001c007488500d440303d0300d1801c0f1443c04c0040c0d0311a4075042c403d880c12100c41c144c11041640c03881d03011b241540d104808035900791150651401050b200d00c01d502400c0c4006454400050070b000900c000b46030040000742c50f42890010104040c2d4860081200c106e035001620408150400c01c000750302d0080c00c1108034240c240d40c0f54041000031310500007401100f8136400348800f0001c50804811130203440c0b10b4860104080c03810400301410504140c02034550b42c10320b4242407001c5030043e10424045907040d981e821185410550703d070301e0400030300340699104814030408600003406400550440b44541d680c80c844a03141c800598407070008613800700004410003900714502c62220100d90390101c5001005142c801251f1440034100420381c519a8040c412000305010408108031036031203081c1c0c00d24410308504012914032604601c2100107810140c90b0500030070165100c4200000510f0076401c803200c6210b01c001d019440e51000e0000c1c16040d46001210403205001104403003802a055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 947188552 1250 947187302 947187313
    0x260c0a201510150f0f3b060c01020a090504090503030601140c0607110d020a2103020405030307050604020a120804030303020f1e1c0b0904030e220c0f030e 68
    0x601e50007200040107041d984440b001e103000183c82e601000003602000010341e91192019107241016105404074a643d00420035080c01404040d404084540741c00c0e1180441000012200c00003035400b440c400308001c1c0e10010025940c0d400c401b0560041c0000744054403011445680e4508010440341d60f290003800907001040003032540d6101e50f9002084107020500681000c5c000220701e45081e000310340b0800403452803181c280076400104855408440d40f44024400b0000326901c505d000080703041c4401d502e00e410302c40d24040c28069015600030344000382c1200c0e01c464407800c200344e03100340c02c1e9021303805500301d41c80c041a00c02c079000b61105403581001c0540d01e801e10b595003c0300250300051041810580600c159840722000103111090344030301c01619910340805040c21021a01043c001e920014034241c42c04170241c40326600f5651150b00b604011b040c2c440c0680c046800f8809101c1c40303840e111540d12810301e190707025034000e105600455442207200920060281c0455032107081592456112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 947189802 1250 947188552 947188573
    0x40e04020904050a170406080a0c1d03030c0a08280e060d09150e0c0f010e04051308040b04030308070e2d0a060207081912260c0a20 58
    0x1c0c0c00540062080e41101c001c10301360380b05c40c4505502103250a20140000504206090b0700049054100034510300410907040c0e403d030b01801498010f5240d100b01060101d80000341d54081c029901288164003d40d6528040b80c90300d0407482d48080240a40c0900d0030000314090294842580c15802003526100c0b903012502d010005513800c0703081101c00c120f403100300c0d620010784c4540c060003040d822024081540c01940480c0303070810030340c24105801030001d070a07885881c1e07034414084496160b041e200040c454441080905109010043c094049000010b0020b0758850f035070000c2c4201c0c1c0c0203035103074500741d100c200f800c80384000a06a42d9901c50050030307103040c50764081040c007068a460319114403281c100318800b040c4d03000150f5201d200035801502080026800a016130f04e0048003080104101c50b4440d41c40c4e60110144040c00000c02c003101a0400080098405404811100ca005990036241c10b075408011903103c542d031000014044150f034500013600002c1b000d103803000f00c00540048580c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 947191052 1250 947189802 947189809
    0x30c070b04020d080f0d0f0e1f0204090908221d1e0a090c140d031d180601020c01030b0604060c0501020d060f03141507030209040f0c02060a0b0402040e0402 69
    0x1d001664403a00d201e000c10000750b000402040c18003030312000151034803040640701d4120380c0003121500c030150802290805219001c03415900d000d10101c01c0007040910b011011009028980212203003d141400d0f40b01030000644c06050f05e05c070a0402409000c0480c11241402c44507481940318400c1d00c00b00c15400901d081101c01c2d800408409403100d04d10040c1c4910501d81e2043d02c400658541d10701044080c06100c400e05c0c2d014107015490b000b0b8600d61900450140b000160002e02003141004007031041b05c4412a44c60b00c4014010150354192440f0042c41c101c40f4000d5032458003601c5074040003901540207000310a01410014a107d040c20324002054803c040340c00400c60f0155403c0265144004403449200003a12004112480305821440c002c5900903041c4068161540100c418407840700030260101d43c454958a800340c1c1300d031010004517004c0d21080049004160a005500040b994000f41e91341c410710084030203200b060803500510080388140d001d12491091140005005400e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 947192302 1250 947191052 947191073
    0x506160207120f0b010e011e0e070f09030510140708101a130b0304120804260c030304051506040e0303040f0201051209030304110103020c06040f03050c0f010509010e0102030c07 78
    0x41c080c12103d040f0203060b40d141207100f0030036040005035401c0c1c0300040c0303c2c919426175100c5428139001c0d80c85402c18100401e0b4010032100400500400030316005e603800c8540701d214008015903000040318100000001c40030302408640d8240c0b00e501100000141440b0300c920701650041544200c440880c5007048407420108186941c84a04104200402542c4003072256440c1d00503d401d143e11510307401c1034603240c00f2808a544881c4c042140c0e40d4140b2010600300e00c926584900301481d500342c034580d42e005443d41400b4103059850b40d404040104028400013280c481d0b84c1d66003075600f9081075580c3e0070030032086400c1c4843e601240e50040c4002400a041c0090011115005042140c1440e20701ca0380114102c0f021106c45d001e540011060104000f850380d01c0c08200542400c055091506450500b565400000c002a0203410380c000c011080c58041e20840383d110111b0030640f085c0c80000010103010705001d5903084625840d005410901c21810310070b580c010090015201d14003400c42e2114a182c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 947193552 1250 947192302 947192339
    0x1051f1103070804091505011403040201030b04020a1815300c0903050c0906060328050a06180e030406050a1407060603020f0d11041113030f0506160207 67
    0x8000e40404034444501000030380b003464400d0410b01e80d100d08082411060307803200b000e100041a0841c4e414015a130304544104510351036030180c40c2d01c0782d0315400102c2c0078000801140d0782061000900440e02603101d81c00c20002280c1180c082c0742c0e079a80d90403c0402000310846d800000e40c078042440f109109030607641b006c210780f8410404011180c5022031f011243c0c032880d03c20105480a008004000d010312041805c0841243d10764580d00e02840032581c0303844014146804140c0e104081c0c000380b804000b065100282c4007508100f035151121034100203044601500c03101c02d91038100c44541030032030f0054020012491000d10f040a10740303003090350355130000000c0d8024171444010700c2e1190b0040c1070107016500d008040100b10741d461801403000e038a07800405680508800d820300b1003c5440200e034500c04050940300015807400d51462405180580c560204840000c600d0010500002d03a1220100724040c03019201d140c0c0714803592203410070100c1c8440f00540c020030000c00549983c2540885003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 947194802 1250 947193552 947193557
    0x14090103060f1d0c030c04030f060f0f06081e030409110403060218040507020102090d08131205070e160207050d06020c0d1101060504060501020c040b03070506070b040b0f01051f 78
    0x101a02d0b080c66154800c4541c0004503110540d5500320348a04810b407000c0e07000009940d04519605100c0445080e5100d030b0301000d07117940203140000d010031100da0b001a084c0e4007140000c2105c04c8008041c00041c12140c4280d50062084030900c1c1140d42100e030902d6854401d2400452510303152000d81000341059100c2e00240b6003041c4400400300345640020910350380070200c4054176420781d0003001b0480300b0103800e2500b161310502411403161a03894901511b00d82000b40140c0790700510744600c0818100d80c00115140c2c2015100c0400c0000020700f25040d22403004400c00a07542d070203100620a07443d09403140040e8030002d0100100e080560035038050324002c45e0301503d02204070007a41d1400705201c0c0d4080c0000c003a00c0c0003d92100c400e105020161004840600015103400c00007503403a03090515051040351b492403200d000741d40801041009002c007a00701a04c45501d4280701802c460308a034241d8030f8602c0000041c44502d80c143c0b42c7c0707043c0c4000a01c105803a0415000600c200d142050b4904203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 947196052 1250 947194802 947194811
    0x9050a150203070209090c0a140d060b210106081216031b0b011401020c040c2f0604081b031c0e01091b051219080c030706050109020301032114090103 66
    0x740c0c55a01401d03110f0b2420030020205041f600d01441201410743e4071801c0e02800d1300c118002c5984d03681405410b4260004004284460300c40d000440707000c071800f4440881e214034082100c42d184190494821a00b000081d074108600b60014901d0b54403c007020314569682801044000178040d000011340162425150346081001d139990444d00d00c42070f0416440e2421a042c0300300b9a40c4d041041042c0303031800366000d0290308140c0c03002a20361641d80380c100c0c1c681c40e064030243d00220741d001c040f03c441c183c1d0201101d43c01c1c101801e100701d032544402e0b0203141f5080411585000d0a50002c11103500310115882c40e8040315107850301600402068050007001d5495030003403804a84211b920410300c41900250551191400d0204082e400c907507056141c683e00000c4500002c08802410b08241581084416589560380b003496030540c850348000425030303450480046021921580614141d03481030950007410042c1704940a100c0311550541000690080801e020415060000d4055440103040109 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 947197302 1250 947196052 947196067
    0x304031a0c13090501080118030915050702030114010e010b040302060a1b0f0b0901180b060607020a090609050a11031519180c02010c230307090b0304050a02010206060109050a150203 80
    0xc4012460f500c20104241c0724401401450000c0c454135481400c0c40e824031807940819a8051b0042e800c510407038060b11075403c61200018012011a80d00c0f079070040081085a850303290f090040701e02070040801d0700c00704a001050641142c1c04440551380c00030211420f0001c1824102c1d00700010b0419099036000c5c090000000813041c0c1026060b9511072104e00302c0c01d1403c1e011041c21111014088580c1c640c101e101100452005064150040c0d020342d147d507a594810300100d120002c83d5400b10b0030140c90100006400065940403900944406006001c010000080e25486001c02e44030110512204080c0004915241c00c14040d424200004110116a2103003401c500e650b1001405642540302c00790103210903420721520444007024285000414800000c441102c008188007104148001011980c103a0080304207d000f840440302066581c6460b240854940d41922000c80c094031540e0042109580503402d01801e0381c002510351102646000b01c040301d24200c20704c0d2102075020410108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 947198552 1250 947197302 947197327
    0x71e050319031805010b0f0103020f091215010602010504050c0607050d0c0302010e0a060906060e0c0a08060607020405070c0204110313030c02152106010f0c080703021501120605090304031a0c 84
    0x1c0c00300d42d014000006e1050154001d002260311600c840303c0c1011300c10450b507401c0307444c2d94094590761030050711120714266040d0401c91501c0071240100b03030100561000014904e9054004510440c030030700c00d40d2101b044160074003045000c2e031080142141c01ca900100741c01403107144264117180c080c2c0300119880c1c1da409060380c10a2000b04041d81c24548911850701030000714001c0800a11450010704010b2821042c4a070f080e01a007a406020001444045040c07543d8a0701036891182c0c0040040105090048000d800c06003201c0d4101e028900b4201c4205401d541c120540c2e120f0301c1041c0c803030381007400c0c0caa404403404901140200e9100f5801410718102c04a490040c00c000c0d919100144030407081004500c1d81c0701c2c0028220f41c1040010100b14103c04d034407601c602246607004000540f1280940f40c2641404480d16a2200c07444440b0000103034000d062519881180c012101002582c8440c10002d860348903e0001518203042c010000c42d17102d1440b104c0c01e50000c1d50301a09802c0221000d0354 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 947199802 1250 947198552 947198591
    0x61e0b0715152411070501050334030e0c0d0b061003110a0f0915020705010804140604290f040f0c0b0c031903090222110f071e05031903 60
    0x70844561818103891002d03400001c00d071040d1320060000c0150310f2030701c03000800a102c02807100c450ba840048807081042196490510361a07070324681044007070301007040180200b02810210102d44240c8880c402c0c05d05010b03016442440e00889003015940d2014248640c23a61000d4800c000c1503651030b0701d003056103040d20160441d0b501a41d24068180600c0500402401c2180c00189483c5210702164003010740014403881120b0081c00d007071440355510f041001e00e1103c0c040d40450503002c0e88080004111040860041c2038a810541032820542c08010300b0b1400340c1140d0308481c4280c160302003008200c5428030640d03c2031285804030040f644030b5160191a0300444410032070740e070010403d1041030001322881e14028050b441c040141c2c2141e9000184c80203a030354400c0c40000450500d1004100250b00944900c0c540c00c455903075514020100c1c03160303540c040403081e1110309004508440060149400700449500480254184460004003c0d808000c1001100500d0742d10350030031000100e0b4505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 947201052 1250 947199802 947199839
    0x20a020910050a080601060207060305150303070605070801080a020a1419030302060f0f0c031f050406030b09010e2b20060403030c0f0f0e03010609061e0b071515 71
    0x14050406141c02c2c18050b94a0142c0c0284416402c110700621605034001110710807070b00c2620f0003048075100d0380000750301507000308401c0c0d82500001850b2414800c860300091701907680c6a0300d14085a0340d841c485501c1d080181c400960000c003184081040340c440007010302a448000740460080800300b5a1034406046540c001c8000d43c01c44401c10010b9070780200b02c20740c80701e0340b50281240c1c2c0c50302841e0750017680300050850840880101c0c10315a01c3c801c00b40c0e95000b4010140c0704100464490803c003d525400700c170580302c658201500c0f1944100c0c0441d081540c012607005400240405411101030b1003108a81030041002c141c0041b1800a0035940104025403042c003d0300c028101410001c1c00c0c1d42c0c0c1c51035600c0910502d0001020802d51010140c032541e46545482040c0001410000f40906816407040240390700308013000c61200e0204c0d2a8411224010510b414141d50315420100c140c020400058403000c8a20580e008801d103d8001c401000d413803a94218000d03031101c00c1700720083d11209 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 947202302 1250 947201052 947201071
    0x2040f0e0405010f020a0c030c0c080f010227030607050c0309030303160f020106051f0905060d1407090308070209040305120403050901090e090a1b0312080601170907090c020a0209 79
    0x14007050190a2140c08040102100f003540340294020010700b200000c12030040401616200a00510201c02450409851182d040d555245c20315080c442c041d401240d00b6207090858000301c5220301d030380040046075110001e0b01601556035000420703a600d8010000014990000300114081da40d800e000452107809201242d070a9104032007401002110000a65425a0314152043c080740e500d08500064800e183c6610150940c0004001c48904410790b0005410090218110a081400741c2081000c0d16181c1d0f6402d03070301c2c0c0e100f14040f601c0341c3c800e01c0003074690f100030440c0b10054100080d1155006e8040c0c00e000703152450a00143c920340e04100d40a400091005c524160550ba0004101d001080b08000c045040d0074440d0b40561070302c48031240105045e102c40200150700c01d02c0400300e00159003044400911900e14080a4000313001240c801d1700140001d018900c90100301c03400c3c140030b00c03240e10042c0305d2282004107001c001c1000703805003401d5100c1c8100080040c0c1d50f90010902c40d50604 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 947203552 1250 947202302 947202329
    0x40e0702070e060607030c150e0703050703031815030c05070f060608060c071502030402010224091504030e2809150504051e04020109050607200f0a09020d02040f 71
    0x81000ba26268001d042c0d10311860003001490702007540407030084031040e00011034842401c031240c0100b0003003d44000094150007946c20000c144030001c9101c1080302c0c044e0704c0382c080b000d81c03d42402c11410b9460040c3d41030104170380780c4d03141303121300c25800408140802e007041403408520b5280c445000c00c00d14002c5031701d6901e0f200e007404001001d100150b0000702d40707460941044801c3d0344403c003100c40304002c048ad96074088002015a8401c00c140403150404c4004401030300700c841e0300c0011384d41c01204c1008261080c0c240409125601d00c1d4842d2049030199283d40303200d44088200034001070420400e0350180003440310062810703c2c03d44650024801103900041d500b8002e03114520b4802d99a004074883c0e4075000802054a0403841344203a800351001c10040b2903034032840107031211581ca0300100d40040700030400c071003001680e4a203400501a00000c4221103848281000658540c0f42a0190424140701040215500c160081d01802c422030702c0142c10a40c03034590010445045500204044158 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 947204802 1250 947203552 947203559
    0x3070c1b0e1815090a0f29040b162106050a0815090a0b010e07051e04081c0f0f111c0f030221060102031b1c0305010f0b0f040e070207 59
    0x30003010010600200c1ca403c81441c16444441e2101c0441c9005001210f500003110100310204040c1c20030040c001d03888070b8011140300c54420041204031821103110040a01149207003035400072000c2c100283d59560400240d400d030354012004004550b140003261074a40214403950340400c0e01e00a4280e190080c548010304050940c05114050012041500240318140c0450064691700b41541c0903030704584060b4860410444041c421000003943d0102e0321282d0b840c00095100040c012034003008225206050041580041d640103124140d0103d41e188010310001401080b022005c020f0300d003072150120640e114814280441000585c80c1e24850700c0c01c002219401100c0b02840c120180750031414409030351040d02c51251114141c042044403c000984a0381c401c01c222080c082c2c4c03504400c2c040350021160340d680d40a90304120288400300484a903030451103031107401d0403126075204104071589801040d840301d82c8840c0044004cc07904100100303404010f401042c0c02003c45500810705d00c3e14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 947206052 1250 947204802 947204851
    0x60c070201121e0c090f1e030501291806130e0f010f060b0c0d1b08120a05130b06100912030908070504060e0619091a030f0303070c1b0e 60
    0xc0180000510105050500403031500b00e00b00419a00503040071f8440800709408000000510340c4000c001d5820300001541200c005d00505e021301c0590081302c140c88500400300540b030f500207080705045d46c00780d50016000e46044a40c0c0c040711600d0f144006030481240e0940c1d420400400d9941049070b4484031114000605403190302c005105150302e07903040c140209545600d0340342e4841000204a415600122640300d614034900c1c41e1030340100041c2c2d40b0300300c0580c07040368013000b203507091801c501d004000b885e0900003c1c454044523511184020b03469031407804100e80700708410415002c1082c1e400300810054032554581e00740c036000e40c1392400c00514221000b4503080c4d541d0480e0380141c0c1000f904014403240103020356048401103551f620000511100314418012651140c3c0d0414186114904509505815020b00140036801c0c1d441c4c940e4107080144e564072056940340c00145900c42e02101207405000101501c1107070b000301e1551950385003012060950151000c000d41d42003a4580d880307071003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 947207302 1250 947206052 947206061
    0x4020f100c1406040f0b090c0913020307050102010614190317070c0f03080a081b040b09040501090e0d0f020f06040b01050913050304051207030606080a150608060c070201121e 77
    0x40b981d000400d05850560344d00d54400c0c58a61004107010013060120b48140c40900001000c4200030300301090516040d9140b02d1100103d80d010783c0a801049030214007540306000350000d1754000b0314140c03104203032042445240307041f695030010140700d00742022001902c4c00340440840e1500079109501c07400b50f410080c0c0a000190702016024a12140400000f00074005a139044207039030805020342d550310b810581e40c04422882a01e03e00b10b00240100320400100c003d44490141524100500d0383c0340c40c0d00e070301150380342071051241d6880b100b034210701c0310721075114950110700520581c0c6021414016692600b4411b0b1070884491402000512003030509503481075012050b6040420619256218107443c0d12490007030a00a440700c80007981140740801a00005680c0000d0400840355034445450b11141c3c03800d41110845900c1925802c1c5428900600c010343e0041c3c2c020b08030302e0b00d40c460940510340c0205d00884c14042030311901460810302c6d11524000049030306d0071122083e4103025000445 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 947208552 1250 947207302 947207333
    0x702010509060f0a0e0f0607031103040206040b0304050304030b13030806010f0e040c0e090f0703110703120209010e030316140727021c0b040609061d04020f100c 71
    0x6a00d0002003107240d640020749030750844018100310003540c89039410070001c0d0401c080b24480f144504400c244034a0800118548a01c8450750104105441c6452030b1101e0301c020341d80650700c110300788001d10124044100554003e44100200c0345004d40d20340c1ea030840e542e01103a602c1041200b4807100e0080c50342103c500c40e070011091030031108091540c100502080200a19180555541d90652905d00d014080d4001d0707084000f010303800da070300d40550340c002c0c07038082154101c00190410342e5001d0010000d40580c0c4440350305495003444034491008860003034200c011a5410040051280445c50720140028010324801e0301c0b602d0003520080c20041e01ca5003c041c98060140c1c04a80104000e00c070038510b404d0f641034007080164445540c08480e801034080d4140c0e0319402181ca50f0000b10450346903019200380381c41a03805000e84c0340c0e1075143c9400c0f03a10900c0b078180c00100d44001c08150b000e004000c203a00c90702c020b00060b086c02281000c5000141e404001801140b03000d104d501c2842036201910140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 947209802 1250 947208552 947208557
    0x2131e09060c0f1706010905040e0106050f09010602250b040608100f0b07060905031b06010e0109020406200a1e1b0609030b040309090510060809070803160206040b07030302070b07 79
    0x2103c51000000d02ca2001004903144032000d040c003003007035a0321030325403000244401032050228644201c071450080c1054800e16101c1c030011110040fa81c10300c40307a414102d4150303030060200421040700c50f02011400002141001512aa0100d034101051000e000a0500c40c0c0e203000552520801c1680701041c1c1e80c00810f140e405000040010305420421203081503032052010a801a00d49001b07880c40c000c0b0404689050001c0b00e05401c180070000c2c0490484a0079103180302541d03a1861b080040348103601a040c00039500030191605080442070208060003c441114506003190712400246001b8a9040b092205a08110380902c2030841c80c4060303028070714441c0c1444501c0c0c09009409030a03148402404001d00308001001d040c0a000744000400c001c460501c50b0b460800ea4000107001a400351030f0100301d1200207c1c9043c08000341071002d8801c0c0c58021071030100c4010f5911161b02074a60201ea00210402c80412010560005452950b1103030320056100d408600c0c00fa0070444c40108110f04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 947211052 1250 947209802 947209817
    0x506070206012108250320060a240f0501090602162601020a0e0909160302280f0911030702070909081b0607090807050603010302131e09060c 62
    0x1020103200712900002e00c0b40f01043d058032030a10348005140105451500f00201c468000c01040c00c00c0510603690a200782d0f03800c2c0c1507400c9032003401d0a081041307441034165480200003e040c0700d09a40003084000e403424400000ca10081d001c60400b0305141c00000c0d6a409120041099507080507504c405001c90b4009424006410015051206090311800302c490303504420300d84207a0b072410144a061243d440095550f03a040e048042c100108850405016042c1700c030002c1c0034410b000c80c01c08444415070b01d96690040c9190200006140b6071840c45038408542454440d00b081c4c4500b080d8014400c600c1503819907031611501c0030444618540007088500c04008000b0311030b5010a04509031a03910710002040d002c14140050701d802a4400501d03507941d00c10140203026400104540301c0c01d9980d58180c036081d1902c0d070302d54403030009110310758003c40180018001860041c030f0030084005400030000b030441d41e0015507500c011401412000c43c50750741c40c000c001d204040c001c0c498859044c0c2448075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 947212302 1250 947211052 947211059
    0x1060501031109130f0b0a030503070b010b1c0b06130e090d0302190f021006091a15070602090f091602060f07080103030e13020a03061d01052b0c0902030103050607020601 75
    0x84079400d80c681c150b190245d41c0d1805401c08405ca82c4031a80581000d0030880006860f4509656690f101c3c2e86c0aa1b1442254030001991030003200132680b1005451020403d990106440c10340500403c1e40d110f64013100c2071201c0443c0382e45021130f00b401042040e055102c0382c00d03c400500d09201d806010b500400d4010402c86c0031381c1c12000f2420b85400c0305403030b2596240640c500c1c12400d224010b80702000160030080009078210503a0041c442e42c142032400301c000e503618003041080c0b5510004c04c0801400d01840400d006c00d85941c050700300008060118091b84c1030641c00554010001c44075006000f0803840010300d1613904012a50f800001c661342282c89040c11000175202e407005210041c02c0000e120340700c0c0b0040e10384501c402401403003040d040d52a902c0158015020f0201ca0140c1c802441e0171a44507114840e103541e8240c101c1320064034071000c0307101013407001000d0403801188000c840d80e1044900300003800b804030000189288100142c480d4150b15219040400103008441190f01050061 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 947213552 1250 947212302 947212309
    0x4061505041509030b04082205031015030501110301061d010813141209150915030c0f041409060d0b28060902040e01061805040b01050c030c01060501031109 69
    0x1241602c50002c01c806014030040400c40d500e2080360802031925048506000402103104007510498030354003100329080052425602c903152803842403e0345580042800c3c141260743e40e00482c1d10340b290492600105803207840c0c0700c0c2035032000300b81c84c0182e4800000410140b903103c1c00b1907034800000060780c0a03400c84440000d1642001400c0c440422540d054a50200081382180b191a000c507001070f1486031908592520f45034001d041302da0b0054003281102e000344d0001100311204010000c0440000408507070094200b40c000926035840c80c003040200f5092480260050001800c0038030440c00c052000e80d080c4140c03a54040c104030700803001072915000190300d070507036136a000403142040000508a011840d648045107012110207500d03101001c2410380207600103109032150404585410390b61107108032180302c5000c4401e4180005000140070300e15003504040980841403614504180c0a00d0400c0d00b16070114010f04810f03995a1402c02c01560180a0303031100401d0010014203050909020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 947214802 1250 947213552 947213557
    0x20c0615150906090f0409060e0f03070b130f021c110603040302103605060c0c070303051c0f0203090d08010612020306030f0a0f061a010509040b151804061505 70
    0x302403003400007140030080b0b500ca41451507801c6800910a20030f5106e523003003420050802003413454080c043d1000000c90110000b0403a10042d5112003004819070707807030983d44084020224122600ca03240d07003602015a6030441181e41909400c0005400c0c4d0031607181c8400c0c120850303066180108024410400407940203d01880058081701c8049000c0d0901070342d101d000b00003031515210b01e141041c0341c0b1842480b1034041008042c8141c08880c010b8881c0c0441e1880d5010304086a6159844030070148002071092005e0446486c08141d14002c5100440280060350840310707640060b1507003c001c1121520003085000c00034009030800d141554141400106008a1441d42c00c0c4e025400002144860b06e0402c8031103000340c03608099920843c294500a0007224600f001a60f4007820b00d03030425001c0b500140b80801c031500503144c2524020150042c0b0004d02209411507a003c3ea003215002441000000103100d6603650121100a04000c90304001c100c1d41c2c141c01501310b51070120121401240c02c01c04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 947216052 1250 947214802 947214817
    0x40f0519111b06162c121e0c0405040b0105010c0f060f1e1b03090f0b0a0e1e0709110c0601030c06090915090e1c120e0f06180109020301020c061515 65
    0x250482c41e00c460303030041418005a4800c000c00c0e403050311590358007c1d6007038001190414140c3d058a13009413500003000280c500c1a64064000c05080004002e158041c07000d00c6000d0b84200c040340b4814000d6100c00301268a062040d010480d100e80310616201001441100f04034451001000a180c840c0340708224a00303441110b07414141e5880c51035040c40100548070391003030750140d10700c101c1c0c3c07409100f03100c00340c051551300c400c80e445a12005a403040b0a88000a4101001d00c01401c60301d01d068203c102500c120b0a240c800e515041003400742c41501804218045c1d8001d140b040d1000346040743c000c1280000340d1018400700d180c038a405443c0c4003440d45034401c030380c0e4000c800b203009105c9200701420807a40036004424030303c03910387d43c0c46803079006120101b244441c1d41d8100910905040c0403a19070407008000115604044009419072290365660302944c07001000000e0440915808a402c80e4401000014107501c1001000702e004081c13004600c540205460950f809028824a01c034036008901 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 947217302 1250 947216052 947216117
    0x21504060e0f092a07020409050102040501140304050c01050901110d0c1209050303180f0d0605010305070e010b030a0f0e0a0f0605092e110d0b040f0519111b0616 71
    0x540c120581540c0710145c40205070014003c02484080c3c0c50118003e40c0f140c030440780400c1814020360212600c80313040e03034030668101e8041c00c1881e82030b00c01180d0a50040e24107030305011003646a00c070030342c0040103074030198100c0e51031b00d4006124a040c14034029100528104c200240c0c03041c10302442c1c5020003074901e90600c5003803809204000c43c0000d8003602c40a0050f54108060b0300d041002e000103600018103c0e0700580c2660141d940b40c1f01040640a42405804034a21080000c00c1703079204968040a64038081601c0091015002c1d4441c0341045104d9400b0741b0710841007004102884864403482d81c128000c1c2c0c0042558102e400d940200c1092401180f403070b450b540000710100e10600e500070241d4180e2040d4001c1e5113040c0c000c84503000b410030061250040b0b1170318a4882601544d481240c2c001c44011020b1100d00c0b00e0242a000901a0781c03610341b4000e582030050020115581c508200100c1ca01000380240d840c080780ca480d845046020031204001e01042803000b65261018607a520727040d5003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 947218552 1250 947217302 947217361
    0x209090d0e120f011410090b0a14030f01020a1706040603050d2115031a04030e060c0a080c06011a190806030f2b080f060904021504060e0f09 62
    0x40b0340d62420201d440760451015420400c0000c4134005440807948150a02c0440c01c10054980c150b40c4116409040c09540100c0c0d9005c040c0b000c00900317003002555050003011214208162018a401d9070022211035021609030b0b0034100c098840000c07050345c002400d0b41e04200d1940b42d51182540c60203c07044c43d4060181c1e1518401026040b0008101121a60740003840102c001c039801000b03c1455100c1650580314211501010850b03061543c0c2c003941c0c040da03c0f072a0107203020040141c9030b4000c0324503090501c0f0303002007140001c81c540040c2000700391400142a46614007640c000b41c054024032100103415040101800c40707045040800c211a620f45080b0255694040c0400e11f0589007040440c004d22580596842402e0000c4080f81940d5100440c0743e00c0342444181910100010384a9005420900c00001c80504100650b603920500007011b0940c02882010555160b502c40e820590004010b440742d8004c5007407420058568640c266810101032500802c20755904d8000d420700450701a12 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 947219802 1250 947218552 947218579
    0xf0b040212060d0c17060115030b030606120304080115050f2d010309021c0311010606050d0203070201110c0114070e1c05033702010c0210090812090105040209090d0e 73
    0x1d0300e280020b404072117520940008909101940d0304424031900c02000f00035a4202d600e20310038080d1003009640a8010b006079144c001c104854004401211310300c512060200040000f42400340c00c2d00821078403810402d20303003030a0510181d200e1840089002c0c1c25050031820300702c0c8005100418405650009e007003042950001200500901c8a001c6c0d031051002043d80c207002640c018506041b07100c1d4680308a602c002041007030030b03189148600804214103011400d501070650b001540c0c460420f01c0002030211401e003926060350030180100f24560755800b003110f011440290f03681d0f0044001c1c101000a404000000740d40001103c0c2001c5c58689800e80d4201000000c10948483c1120214151400704800e101015441080e07141c2007022605900021f444a00600c03910f0186440c0b5030140c0a00000c0140b10710107021103080413140c80340100014a541c8040c0020342d4060300d0080008207460400340100700f00071801500d450055008200882c064582010014204540c1070b201107020900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 947221052 1250 947219802 947219813
    0xd1502040f03150506040b030307200a060f020f010b15070c0e07050a0206010b0307141b011e1a0a120809030a0f050d0215180c0d060f0b040212060d 65
    0x50340d001d100032a040309000301c10407101c2d4900040c550745204080010f50351355030030401038441034001986c06420401c88100400c140c4049042d01c520700801e109400400f103004560488031070350000001494051403903c645030b0500151510741e01d824000c0c009107810b44001a00d00500035842c8140e5040098110108803103100100000c14070707d08044c60a2030440c00250031036016000c018014003401c0d00100741c1c1d00c84001564060b800581d554514070900d0080600140e02c28159031050302e034011100d0302403120134043d0003419210642d01300c3c0e02d420030000007810303101c11180e460300315080482400303120740700c2e40c144c04212240c0e2039030085e1402250a210101c1e20490049603018058440c07110103002d9150702282680348a0360484010340c8800204130b80b44c0c028001c004401b41c5010002c20694560140c080680400d0242a58659814080090410150503908035a031940701c1200e4580151103204542101d80199002d43ca0628440c1e41c112030950000c0c513040c80340d18415540014003d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 947222302 1250 947221052 947221057
    0x81603020a03140f06030f0a0f0209061203040308040f0503061e06130905010207020a060212270405040302060105010305130201090918080304150507050c06040233090307140d1502 79
    0x408007014030500d0a02014134020302030b040700da140c0241300e41036140750401000120001e2443d0009864614403120740d08102840b040078110ba41d01481d04824050015810b00050004500c0761042a40d92894034018009a00042c0d1001d4840c0c4c2041d000c204880c407207219030410f8500c0542010035283d8603e00000c502c0c00c111010302954528128100040200550003003c04130300031100c6100b00b996030314049030f49500c1560ba00e02a00c0041c401c81080035240c150040050344440340c0c11b14400082c0b004142100e41c12034068005130301010040005e96050712403640c0100c01d500640040301e00c2a00042d120004500c070740180e40340d451801d04e01144100c0041107205034489820343e503a06142c1040d1010380b043d0b8211481162420380030902140c000c104590002002c2d00c058000e954450b020070810340141412400800c1100721030440c00407190703030364503a6507501c4481183c650403101c06042c03610380c81c0d40208180c441603049941c166500e405a50b041c642d03200b81f00c000800780d4116044e0190 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 947223552 1250 947222302 947222321
    0x50105070609060e2a10050403120323040605010e07021e01061d07141801110a02360714031f121109150d020d200a06081603020a03 58
    0x14064011400c49051900d40c214400582803170520718018141e00400c184100c00480d008049441003008000080780000340c46100011410001442c2a41c3e421800b80c840b00000003003e414000d90400041001503c00c00c2d01400301a000d23001e039032601200c065581c12581c911f0115600103030807000c8004000f5017107a000b40c154000c600381c43c5c4520301030b030b40003240302964928046038403d81d18881140c1b40c4000d0700c00d014500700900e09108000c0c001901c564201811174549070080d40c0c06103016888014281a21440700300101d41c0d9943d9590300b01c021400c0394050713800d4510b000e038207006065034000d50031465000c649105a03030b02c0d201d85d10281080c0702284a0b03d06008240000080c0c14004603200a018a00448201c8607510209041189404044408906201c50325003c9030003070514034200e4130414030181054080c1c03200380e00d070b91020520000c00342400c50b202c4035500d0068108000003500520f203134103103005641082c1900202082e151070f010410154045030244030035100f6046540203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 947224802 1250 947223552 947223581
    0x100e01020615030a141f0e0a03050c010b0d050709061706270a03020706030c0c051c030e0109140d0c03271d090106060504060503060405040f02030f1b090105010507060906 75
    0x4111750380d80c0317071950901c50580c8009001c6c81c00082c030a40c0240241c202c4184e01c030780605014421641c080e0b480b5007180d01a0b80d441d6580300810020340e2602004041d809004500401d10035141000000650b080f580012403003100702880340d03a100c400080c04035008041c508804c5c1000075030b03045600c0c08440c01c0c05005414403078003800d18181038001c10800161082c543d03050102c40390350041600e041d4400c0c0e1000b0002c0d40082e600810026403080302019503413440c600071460b2286400501d003500e001c0318040d00c012845040d042c0340c10750104600b410101190410100783c3e80e15840140c00c401c00180e003004000440c03064551400041d604007005450030440d0742a0089201e1f000d00c1c1010b2007222150401d62a00d40040f54a40c020300654003110500c1c1d032028a03650f22034003400081d040161045803000020748426006076420700160004021f841d0040000c1036098203101c01e028070040419005000200c014001640c0c444100e991150700b0050115101441c0d1a10300014040403100c02ca9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 947226052 1250 947224802 947224823
    0xf01140402150913150b03012601110d0e0c0f03060106030c020c120d0e041116020d0609030804030e04110711010905120c0111190314070f060605100e01020615030a 72
    0x21458007030b40005a45d2101a0306a04111b8031001d9030540da1100780a1140132170b11403510904101e00e03510703103124103540403000070560340460881d4026070741082c01e81e8000f464940d040704905a50802c035810b02e121040302c12080304800f46022940710001030140108064481115003231090003004072041900c00640416105e6030002400d9840c0c1031208409000200d0740b029a10745480c0030f01809080703c41c082c0035245420340741c07040c00c150815500001c90b0080b1044040101042c0780d8841c040246010362200d05003482c01c0c0c60000c218004c0e841c6a54415480c1c4090b82441103220b00070382e165103a101106c59800a149001a103c00110398007a650040399141440740241010880c040000020380ba03844040da8040a100c0e00e50402e8000300408031b40c0a10201c0c04288602c42c1c1640d03a42c0160000b034a00000f6403500110840c0502050b1884c6460311401c00c05814101c2c0da8040000710341c40c00d80401c0303002000003034540f10003810408894162580d0400951340c14040001000c0e8030410400c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 947227302 1250 947226052 947226079
    0xa0b090c07030f0e06030a0e0c09100e091603080d021209030414040b1f091e15020f070e09010b120c0f0a0b0a080a06050607050f0f011404021509 64
    0x80e9501680707048000542c1078280e8407006008028158182200503c02e6081d03607500042c2800030281380340d48501c18410400c1540c019102e204005020381c1842e82601100750a1540214600380060640049076110100704aa540000d03c48402601d1b880032215940e8403284034220040d01508486001060b010710a0004170f4400100a0040b0303044104500314410000003003004036268013011582005503003149003804011000c0501e0f4540132402c0c054441da85a916417000c2040c0c0e0b110054100b001800180080705a000d80c0010710010307440104081c0011400a5484007840d21503c0c5c0f0840e54440802d000460a410039070684801406840c0c0ca6002818415507408211225600135050301040108070b0401801c5038080e01c024032408c52500d1a010000c40c0c942d94018400910305a5851001c11f0556a003030041059038011002010210349001c00c46040498100b100111030b1701d482000b0030b0064002d00c83c11750050301140c210044107411030101150b44540c01e03078107071311103034000150 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 947228552 1250 947227302 947227321
    0x15041d0a12051806090103090515040b01150f0c06181b0504092003012307080903162006070b150306011a090406150225030c0501080a0b09 61
    0xa044140150301c00319545050000550b8544036640c0d01024450705000310302003a0030140c00410302d50b0010300d00010b04855a0b19654105410070741c10082d00e4805074180000e100700c2d01d107a20301600c038210750456280591400a0f04400348240e0901c24455400d08620920000d5800070152450f5621020900107261a040c1c00f0003440180180d03070517030125404140c80c105031140794902d6500a8848814140c0c0300c62032494000740b2290547c2c599203c01ea8100303040c580c010361a8a803141c0c0625002c030f070b0518203406008a82700405040c0320380d10902140b100c03108000b400d01041504000300c01d8020840c080d5070400740a003009a1900850b00181c15420096000306071440b03500c070400b01d41440c1d071f84031040540303826080c490100d040d500e101800151350140030040c110311200602c002800e541c2c6800c007103000c2d1541c80c0c40502681003424010002c134005810001c4088106d0304140300c5500b1075460001e211400d000740c504000324100050780d65000742d403180f114204020b10040c414034040314030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 947229802 1250 947228552 947228563
    0x70f021f06050102011a3109030c120f0f0507020102011103010e060a0803070215030603100911120616181823040f060509070e0a06140303070302030315041d 69
    0x41d00d00661901c1c141c0322004030300c00350258810000900c41b28140c0345040f03103c441804c10803070f41d140c41203020061180c007250501c101582d0309e00c2505c81043c440000c0c1070404041d80e480d000101404401c05000f034145900000c241466665810801e0304c1f44460300040b40140406090402e42d80301c000004141005140711951180070103e07501c1d0612602c9015968690141c0e0000070f4001a039013400d41100c924007405141d0001029040322683c1524444880958000d04019203114003261242590ba0811614120621604e01c008040030305000110442143c0704140d40410490810148407030300e0901e080d07042c01070900b880c1d0f569440440b46031040007400b0841045604100c803441000c00d0303d200310f40440c411070f00500301080c410b45a84800e0040c020040c01845240a51440070502d0190000024000c6280d132200040c00c5090801e015108400f10244520903481401100b0000368008201e90b801084d03c04504c402d03900303460102c2d004d0022225800c0d00d00d106d1001504111600040c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 947231052 1250 947229802 947229809
    0xa0e0304091a03120307051c14040606080a0b06040b04063308090616090503010c08010e01091107031b0f15050a0b0303040302061c0905031206030312070f021f06 71
    0x11a00180e041c4404040e51890820040403001c0010300014446c0382c000d202401242150706080201e0040c080c1001080785c00450004008410050030301050010350720800004e042910000c1500001a032118001c3c00c0004003214804c0361603080301050341e2150b412050050140c850b8107485180301080748514140d00810900761461000311441445201342405401108008050005601e0b18007064000c8100d031100304050011031400010f060f2001d1143c814165000d03038030454554145030a4801212042e07000011490400181c494180307600411681781550508201c0d030401310a500009000201c081d001d03040850200111050110006c4a21604041643c003080203940300c0605c90101d40d4a000601d415500a02013400141400c2c40104118100c07801d80b1580d41c04000c506d0310a80d040001e08503016000490000200c80c3c1840701d11390000400c4005d94184580c0e4110304c02c804900820300410031541008180f40a070080c0590601c800440000442a802e2041c0c1003018005521 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 947232302 1250 947231052 947231081
    0xf0307060209061209070312050405090414070b03010f0603061208040b13030605040321110415090803130510050301030f020d08120a0b0a0e0c0403141c030c0e091b030a0e030409 78
    0x804c88c46286d44520200c82c2902c0d402031044080342c45035124000130b038044c0131140150b44945a000309a107280c0c8005503008001031a040c42d03401c0d0400d1401015901a903025400c01c07002ea604490019803070740c0503201681c030904481500c5140c0000040418140d552001d4043c518201c2880207040d0300500e00b82e100c0f0b400b4115042c00d05401c0d06c2c000112490b007414608690010b0000344095080441404584042032408610203a150040742c0c1c2154442c0c00b85403440c0e240c032030040241c0c1c109002e4682107414075003000d17415585982c03281000f101044200134410110b6544070002c01202c8400c0d0780f043c8060081901091a00c02d2804000388110184184101e203c8400000c0042e40480140d214510500c0401c0c00d0600e546c7e5100d203030300960010003600303015000f50141d1005200440f019031005540e008034812410000142c50407485000045c0208c800c10b0401c880c02c40042e0034890202c03040400d90359039039186423540000301000d1001d00243d010025000900070229000245a2402c14 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 947233552 1250 947232302 947232323
    0x2030a030b09090d0e041d16080615041d012c0118080306010314040c030317091e340503030307082a040b03180f03070602090612090703 60
    0x100503240504031401c980c6a405110f44140503442017160701c0e610403002e4400306000c8008110812508001840303c03809501050501548001c01280d0070001c01e20b1001404443c181186000684003140440c14021511907210010341840a01c1816190100304020400c0780010050402e0300640b030003d02e003400c850391010440106040c0700d130382c2e6600d28007040c4040c260015541c030521600010003a40c14190340d8140120001500f684540c40785104a60300600b0904500d00689406140c160001c0d18040d05820402d03500400101400300c2c021903508240300e041c641198601d44041c1c41c4030240925090240f00c5866035841403200307506080e008034204170507101c5080c141d880c0411180280001c40200120303650f0303541c40b56203146280b03104075004a10f12102220034042c0e4810b6001c1d0588090000c1000095000c0c0c944501a2f066035101405488000910b07880d81d0b80a501d00c040d001c44da00150b4259a5a103080c102c4a43e01c40445141641c0c0c503080c01180d4466905100644004924 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 947234802 1250 947233552 947233571
    0x70309030207080d020c04090f02120a05070618170705040e16050303030c0909220c170a03050f0a02010603060c030203010e010e010b0d050601111507090503120a0e01120c02030a03 79
    0x101303a4180001c800da009003000000c100130440074003003000d01038070911710b14161107000d43c9588850000d001074030780c01002d01c1d8140703251003458101c0e20390040d010003800034400311501c0c0d05d908206013140c0031501c20780f401040301c2407028200610740d071010354480c0ca0405115014100451812946046c581000344d00d540d40300d0078941c0b41c0c40100e4481e00b84803400c206224151038103c1b08075400c4421000501c0301c80c0c3c207042c210040c1c1500050141c84500b0000000c100701c03d14032000901103064003000e001035001710390340030300140105018014480008030b15100c1c183c0c803d520400040d60441014040c21b111700002400a41c03083c068503400b13220441c000b1411021009481d0b048804501c2d2080c034003c0b002e501d000c02840060009410401d4442200028580401010350050b00320710300f62203e0708001030007422040e400d80c0854000e4000020b0100d901d1003200c2580c030600c1d00360504100c80c0c0c1c400c9004aa00c28541100f001d00103190901b111100c95000000d002e06107000c1e141003062900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 947236052 1250 947234802 947234819
    0xc0a050d0f05040b0915070b0a1e022b09020a030f0b091b0402090418060e0709090b06210303041a0604090f020d03030204080d050d0f02030f01030326070309030207 72
    0x5140140000744c00308001c1005a424143c10807078203181200c0030142011000e950783d12201a054a402e420740707890314050041c1000d11414090b0440142508600c0c01c1130f22000e000d43c000807022042d9082c10f00307610240c0920819004008955401070142c00300644a2504884043e00c1310700964018044000081411200089101101842207600385181e400300c010400070b0f50050141d1504143c0340e03171003441c4103080340d070100710b0181c460f01c0e000c5810480c002c8494500402e81e0b1200e4203280c01d01c11074030081512102121f0704140140c401914022240c0000104440540e2528056101c008200428405c0c3d0040146614441c241103008d103440d41410802517441c4450082c044100c0000654010b02d040401708850700e00c00d0030090309055540b00b40d03030708016060601c100801e10014841104680c0c1e4810f080200740b40c00c40841c01c44c02c0a201005600c0f00c14040201030181c0003c04600c0c0022020741c0c0840d081e01c0c0d05030340349a8682100c00601400403101c08801620402c0342c0440d810b134 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 947237302 1250 947236052 947236057
    0x3030a0b010e09040620040306020c0c01020601060923180a0c05120a0e0c15120604090c0302060a05090907170f07080c160204020403030c0b010803070206180102030c0a050d0f05 78
    0x62004000000c1c1303843d20b88950005100001c00d40d1050400c00201010410340300002d4001107000b80b00040c0c0721500212440d0400030221b681c5030454203e1001845074a40001e030001c20750380c01c0500c042c02c102004a0320081039603200300181d4081c0c034610301c80d803d1900f01d40e00c080c890904148240403400044a098956008842c266a43c603030822001031682031303003540454000710030001103403400074050002c914a000a0b040b203c150304800640c1071160350490074002c1e000401541d04106540c82505c464011604a0000900c2402c000454600091041003070f140e1020005020801c0d0b410084005813828150f2010400d8030340710100010070302004401c038103100e01013a031682c14180d030391004101c0090340090041e040b81440d02c041400980c44c0c0e4405007000c0c51280c3c540d00e01900381800c1152900405901010456204025060050326600141c40d1880740502c5511103106000e0300507801d40c000d105810301240b2610310080280f000000b002d1905480c0c60301c40418582101c0007ca40a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 947238552 1250 947237302 947237327
    0x120a0905042d1413050c220b1c0b060105040e1501030b0334090603120207051e010f050705030309100c03020a0915110f0f0705010309051b0319030203030a0b01 70
    0x30883d41000603e014030000c600d1620900c0380d803d41c0c61511070300001500350312085840e80350100140200c10380b400214412000208422259010540c5104c4658900c2c9000d44400a1861510401203044c51f4000c50580c1c01405000226030024500240070a5501e12445111400a801d101309545241008a2540507401f02005a0001c0495903000c214106001c4003905181940d00100000d03501c045104200242d0300c1010307010140c14506134001e2520b0180d400841c41004e0b06018100c04040c6068090742960342801c0c01100809420001c1d90180a542c001070704034000041007001e00c40c000302e10801003030340b0150104070000003003008400b240a40800d07000030408466040c01510079000c40d990241b051440c208040f01c10189140e41440c10030401a00300d580040c40e1400000ca0611800d00038207428601085079a00e01d4459660352030070b50321301c18002c0c014a0f0b800d1020b89c40910045100d003855250040000c041c519000b540e90b070044640c410400e1070182403400c1c40d072103150380c5500d8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 947239802 1250 947238552 947238581
    0x12182811030c1008010e06030d0c060e100c02030705010f020f0d0e03160c0f09020f0f0a031d1b030705030307080f0d110301050907030e120a0905042d 66
    0x1280480c0d522100400244940c032545840342000e12050360751406950f4090894035554071499526188140032003800c00340c0014801e40180b511003050b00d078092040c3d000241c0003103020851440c62003845051041d031310040d0f01901d00b02038201c0340054000004007812480f1344020090400391000300c4040303001d0034151900d510310410040109890305d411150070400c015090340d1a00c195412209400c502c6100304503410060300c0030401a61a99400040080c24820030940c80c1c41c01c0c03568058480d02c9103040350120354001245104000d40710fa84055842c13007102c0c0540c00000170032940240ea13486600080c21a0b404072080c122032a0401184c0c0c00100c0d10301400840c148544da54450750b4907000b228103082d003a0018069651400f51a019030060303102000780d603580e031354181801d000e1082c0c4000c1c000c0d428107042000d01f4000d20030024202d8446091010411b840b5181240300705c03140809a8409035200e410000b60070001c4034040c01c2c00100e200c2008000200700d0365001d02d20144c42030060081c42c0e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 947241052 1250 947239802 947239873
    0x706171302031f0f0f050f01060206040f03031802090a0f06081204091d06190b01030504020915060c100b0a0806070c0303020f0405040f0903030605030a02150706021218 74
    0x125400f1806020701140c0d031000440c120001d26150300444e103585804000240e05e41d824003400050800c0300328050b0042e0f01c00303480c051500362129145080c03004001420140c0c3c0d25026a42019100345000601d540200011501e0401d8012100545030811411202610303001000410b508005400751921100043e01420680b41440d1a0000c108800c1c0310000380c0d181004085001d401403185610800a030780d9440c001d05410014030080303500d81d0803218140f520301070910003d66504420b255100005100d8184a04000c40c080380c0740d4003c03680c019015105a2038501402e1743d2a030890007051005603444d0000365521141555100016940400482e00c11321a10021070702c030b6001002e480380c106800500d0030b6034030300116085400c04441c004086903142806001c059150103031400030002180103082803007072500000d140f001088080000907a0006c0ca51040101c07030380540d1801c4030114800c0d02d05140c42d00b0a00c1728214600d608445a01503030b0804026004003c1040c6868044540450b1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 947242302 1250 947241052 947241073
    0xc0405031e0109050a05060735070e03010603031d01021f05100b04080303100e060105040e220b04050d1b03030c02120315040b2407030908070617130203 67
    0x146005900d0345400407554031104208045542081038680051040700109590328081e02c001306401c0810100d400a5420100c0d48440c00700b4084040c4507101c15811001e480f901c500074181c801c800e04400c22501942041d0b40081415003058002580c5124a0250003c1308104001262100441c00ca4000b0743c08a2003440250641c1d541d2206500000802001c81d401d6107030b0554010a40113a40101090340c400810003d0780d44403040311100500c1c1c0ba0b212540d05042910028005000320300030510290f50340400a000803060308141d040007842104840307070345005818011080e0104840a80769807084040c0500d94a11400305448059401d000c40301c40400c160703400300c014055800c620710843c40b50710180e0b038104070f015000391f0103042001040071500c50440180015a004072040034030441d80c0031080442e4825405200d080c00700740301c0c007a42d61502c4620b001c1e03c0e4440d868108510383d00c40d520022903450707002441518581d42c1103415100640da940b14914441d0b50070400250150070489504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 947243552 1250 947242302 947242333
    0x108151e011a0705030f0913140a0f0207060905010204030b090a0c150513090e15150f0a1505070606361413020f011706060f0904050a0609050c040503 66
    0x501c1104a442c1500c0e01e041c00c96100d0034607607080582c0c2c4e000c41c04800a909034203460468411140b0040c0340d00244103600c156074410100035002010300d41280c0e162109464841142c0d41102e040035032207039040200160905290b8002d4006010032918403180801084011030006242c030f034030b01e90045a1941d15414480d800c580c01200e040c811080c040107010f03040607805004402d03005024000000107510352140c1a0514048034401c95800a0f4062800d226802c881c000450783c0414040e641d041c2c1040780800482c0c0640c2039030f4400c02041c0140340f017074010203034003100600c070081c00b900e8140301c0709458041030b00c6420410403105011500c403603405400c403101002d150341c8100006200081084403400386140200c5c04031010800816803000c01421464104820342d2203400070719000c0502260481c1e1241e8510000d041a44120f6001c2190821920141c2c2112210b410151003481103003000840000035106c58000d00f20030070708100014000300500c0003510225400100284500500c2c40c3e02c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 947244802 1250 947243552 947243579
    0x51003080f090111030d140c0a050d0b240702091b03070818190c0806010f0b0903121804050108010c051206240c10020f07020f0102010f050108151e01 66
    0x1581413102d180480d441c4500700b84060883e503440c0700340104070004225446448803c000300110b07502c1405120a240480c0e000701a10001142010000780e101e252030000b07074480000b038021141e04041d401f1013440d505c02c00b0014207c1544240c0d01c03001c06d622082c0d244104a442003000c0c1043c82030600001d0707466445200c003160802c215414038008807014802c03082c10042910900300955031160711100c20400c084100100404d021405030401e54104070460304842c0291145180641c004280c0740380342c0c1d03002e02c181032040c00f907450181d960381a010a40440c2d048040c00e03041c4200d180800000d0080018041c1c0c419100c1c16503201031624514000e01c0c3c00c4050003070300b0107400c10200b460b040011580b4030307140e201403032152900c540c403102003640082c54104010141c2c42d1043c014001000d0041c0d40301c0c00d130b4442d075038101c500c03140608031200101d0040000d245404859410040002080d80300480c101c000c205120311084543e960b000502c0303035800d01204e11900c981c610f210040090040c00c011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 947246052 1250 947244802 947244817
    0xb03040201080709031725020102121b032a0c0102030f0c0c0d1b090b060403020904062a020706030204030b060d0309120b070908060f0a1e020f090103051003080f 71
    0x404c1c00c1029102d4591440c4080c00d04440c41d95254009031b07005049032030a4002d0403401d090201f403106502d8950000f501d13882d030032003c107544103c0440c4c941d004031040e8040c4204000e0150450740c40310f54001c80718100701c48002ea4035645c0c01851001e04a40080402c148800002c1078004624040d0001a8103d01c0d500c21400c84126000700a50800d5540d140c0070503d1095000307a0130341c2400c1d0703820700080180b105554007040e8040c0c641004881141c03030310741c25034040300e0b01160920110798443c2040805803054160f0502400380341c00c10745403020004103081002180980c00c41e000251546070a9040303200f14003004d0500e00c0c1c500d001070558030345018809045403280c40c08101c0aa5102c600c002c448040e100c1c101c507801c0c030b0390042011581d44610740800403e61100100344c28100380340707850741403100035200f8003003152900b008080706140282071030450b00c112001150f4a81c481240b203a403541014a415001904002c041510040e07900500000d0302e80000b0124a0301d500004508000c0c0d11819 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 947247302 1250 947246052 947246057
    0xd0507051e030a06060302010e060c0613030e030d0f09140a0b0a0507020a1403060a1a0d051e07090f020406210908031302030f03160615080607021b03070b030402010807 74
    0x30a110780540b4144100f94015208440100c1e4003401d41c400505040f042d00c44541c040c1100348201983c0791800a600350b04015100d0b210449202c4609080300c0b0714012040854040c0318400400038555806000701041d401e15903610701c402500d519202260461203c0f20380d52021461006000081020303004200143c0e690030311514003140b0781d001c12503101859010300d80ca01d2200c0803a101500742448056800b503130071a130403c84140301582034440b013507109070018001c00000d550b5404102040004030030124640404800104924050660321656409040d00f91428900035005a08a50081d10103031080d54035032207030301a2041610030b10303102e03442c010700d01c60b544581075074000c2a9244010f5004401400390009115040e00625240032400744504e0407590080106c024419520844a11681c0d0311440100d107031180102030701101116900700b003700d40910300502c0909600056030103a521303075030b0f403148180d00303e08020191a40d4451203503448040c0200000340040d1f100d103403510780c014042d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 947248552 1250 947247302 947247349
    0xa05160509041401080610080102030f04061505060d0e10050103111e060f04090c0903110f0103020408011a0109060f170603030c0f0c03120f0a030e1513110d050705 72
    0x3c5090360340300ca00783d10004094004034240100da04c20101e5020241c0240e600961850500c0c58407090a214001d10161101e6510851000b0700280311940b003000348001003080b900d031203100c50f940000700802a81c80c4a50711171003513154103080302406200e049070f40040b5148a0382410406005e809441440d203011000034580040841e952402c002d07220111030405000d446600302448a003c031541001d04109002c0441010000103030310b0040e01d0030b40e400c00e590808400c0104030059020303000f1900411069400c0410b91810b0301300300102aa0480004d0361481d80180c2d50705400c6c1c4e00030446078030080010b20304001c0382031a40c2400d0629600500082d04032450031b01004019810310320304500481140d044a2403c44141c90208039602940303117103411a610307204011340034650341d02c40d50320320006041d00c2c0c1e03c80e032256020501170031918004400380c442c401d00d0505c8490521000a02003207038081140001d608140c28290101d034107841d8000c004002e0981050304200c0c0007010100606510700b500e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 947249802 1250 947248552 947248571
    0x30705090c1204080406110c0a05041d03031e1003050a0201053906010902131203181d15091b0c01020a0809010b0d2109091e050a0516050904 62
    0x4402c1e14841c40c01203910329101c50424600a168002116103002683c0c410028010550b0f6009400d1040354000c0760b0008034490090072550100c0c040c4862104140004002c1003a00f11103842c044105641490898849903100601d5028a2000e4003010b05654800700c1c0707900c01540035000905012071291200c1d00800c041d1502e0700003000800c0341e0101e2000304642c82112004007000458050a0420301c15030911855558486481100c2d105102c104411030000d5410306001c2c1d40c1c06400c075046110300307600ca02d84910f20b280c040310f52b849001d0700700c00c08007000a416004071844e0360411070005100c1100d82e19411003512000080c4041700c0340c5120304201c3c071624600c5c240300810800480d03444e44800d601d44515030508450300409114041c2501081c0c04002480e100210f00700c030307101404c01030078954041100710340d0541660854000c0c03a00d0701021080302c040c0a81d541012440d1548288207a50300ea9120809a030300a50700352030109402c003070642403103000b4030103081c0e8000081c0c40020f41002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 947251052 1250 947249802 947249827
    0x61a0901030809012c06030408041a070b0709051806031507020c0103052d07020a080d050405100e10020c030c16050321030106030b04020d060b0d1a030705090c 70
    0x20280d100711a80203001a401c041940c01040c105180c1c000c94075003503483c0c0d403951042c0c07070156008150a80324003030000001e020018050300b920040e10410104c03507201402c3c0140400725078045042626a11030140008660701c1c403411200b000c2d90300c05400d05030070034915004d20a05c3e50010b0051765143c040e050400340390404c0d52194034414134613540208a010790240024044580142c001c1e08001003a44002c0d9454603103000e0360a0b5030440340354442031075a07401003c90400016140050901c8030000740055030746000d8201a0140740200c040c1d4a1501c44001010101c0c0e0f120744005c9400d401442103505146099400f5013071484140e01600c4c50447d6081045081c5041b1040f0501820840582440a814100702080c9800d011504410301e2482d844541561404140300f070004042e26842200d41c0e984454061390001c84800034180011600c9038114401a00300b4000081c941d4034140013022001c0c44032a0603590484090054459182000140b14012000070710262001e041040790840841c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 947252302 1250 947251052 947251069
    0xc0f0706090b040305090a0608060f0105220816080a031d03070504050a23040c052704051b0105090d081b031c05070801080d0e01140a0801050a05041107061a 69
    0x9204c0d9580c240d0700c118010070489091030b40d420000c104059441000703001d40701d080c090200103c090070700544400c441021005284c11400da01c045885440400195210001448140e001e1000d480c82c107403a51a40060760307480e03604031310103070015004a015172008880c200c030010b8501405819251903036110000b01e0152401542d00000566462602d0b0041041800c8040c1654071303181c030f52100300d0405486183e00e020240c09220f01c5001141803240404908203940c603402d41480c00d02c071005160904200d0703141d120070000c540d0101c0305504840300940c0310702c00300c42000300018000c100f01690b07a15185403540101010a12170502042030100e0031030700700007418900c02ca00b03d00003c0d11001c1941c0c0710586801070022001d100e642c1c001800450b90100c5c0d400a03484c1345281074156502d40c00d0040380d4071100380c54403400c85400041d043c00900d9001e101241610003d92381c0603a0b143e030741c00c1840210f40c14010b0040d00d8010078401100099031030382041000310ba4404030f00c56040000700000f01c03c0e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 947253552 1250 947252302 947252311
    0xe060a08101a0c07050f01090311041b0503090f0f07170106030501020c03220f0608070201090213140c030c0f03070c0b07050a17060a12021807050c150c0f0706090b 72
    0x507000c65041c0f24040c0c1000500080c1c50103541d41680160700d000080c04450243c003000381000b0903400d074004241c4460b4040d0039402ca01581e110138501c003c000190103a407003610961881e0240c0038100004440c00240c030018004010000c10f45240392001651079046018070800c4035540b03401001000c50300c24009420380301c00d0a009140e44100100a03c152400c00304c14501c502e52450004100410740c07520076a0427030703040d814516290780c1c8032501203004101014000350b1040080d8000b0340c40d06c40d0380e4040c1940c80401c200c0c074055900c0f160401c11460004071030b40200c1031800c00c20350407100d03034460280d600403a0909200e0255155a13842d008000303402c9a003500000e4000c41d500740342c242d00500d44414520240c00d420003600386440030506d00c801030b004880382001c070b0022100441d1100700c104458080f00054061250402050080095000c81200c1d50940324072041d1840010440040e980034a0280354042c1c40d12a00c3e10311440b2a0b00a00400e940150391260180042421100a141708 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 947254802 1250 947253552 947253599
    0xe250f090e0915010608060d080a0201140124031802120f030c010f0b0d05150705070606120501050c03010e01050108060d080a0801060f090b030c07050f1902100e060a0810 75
    0x4100300f80001488024059101c102000901c4050010342d4a80c880742400890300304a22a0303841420b08020382c0500f05600b4503c0892111320000200c40c64080c08010301c00034400c1c0d0110340c1c03c0e00308000b10140c40d55840c900c41d103c48109600c2006141c540007003050403843c2d10a503144c00100b000e040d411904030020042c180c3e511183d008035018000d104480040f5400c40d0007200300c44050701c42d15501e545540d2401103804140c008030310300c28095410794210640c000002d204e1207440e51289010b690070190100c85640c200804681015440c41c241c0303060311182182c40203030307a10b0100111001c4030040c003e20b030880c4288400101007000c40c0002c045426080c2c43d00800c40d45810300003003002803580d4010040103070760281446868482c0c1e040300d0b04159900119500d0780403078105182444800100e0351418452003d44011410140e2401c41c072050007262245025425490144d40010402940d40d511900c10840f1001060060701c8480c3c001c18129003001c0b4480e00ca0781a07030b032881d01800c0031004c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 947256052 1250 947254802 947254813
    0x17030a0605010f140d050703021303080d06060c0f08160f0609030e010f140c0102040509011203090e010b0306010309142409120405060a050906040f0e250f090e09 71
    0x107540c1150900702045024074200c52081e403006541244c500030304001e5180c0580703e10206594921a405403a2404032545401c61411795a280c0130080da132120b02c807040c2245c1006400a04103006000e103100300ca4108240421940055039404125407000364081c40100901c43c044020401000100203254820700b80000c0d20429810003400c0a18090b440074104841480708542280e80700b83c2c202c4039075131600e51250321001051143c1d0702a0282e80c200325040002c41e8000142d00440105101940f4042e4940e4440b00c2e07169200307100c0660003409170150300b050410202d600365219500494409001c0c50b00040702c5914802102e041021400f4103603808041410070024420100c3c540940100d14000180310843c00e040455181d130040384140f074480c0c80302180d0540c84a000386c0484a0005004103016030f43c40e201d500c071112034000340c014200301d14044030000d080c041100d8010010404d402c60514603c0104904c12610303c01d44003020703010094022000101e00e1031010342140103c01c0c14001e0038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 947257302 1250 947256052 947256059
    0x3200102010e0c06041e0506070302010209100203070209040b130c35070e09100e0a11040506030601090b0a050411090102010e12040509100b03041101120b060d020717030a06 76
    0x242542c181c0b80010506411540c0b000195554000c201e608a85c0090209103013000550500d07001d01a00d07600946c1c01400000c1e40008040e410343c0200030034101141c106014620aa03002c81c0d903130044200080d04442c00c100481c001c04e00d92041186d000012604048503420310f541d9219101e40580d0118020300a2403841d90014510410001820b1003014082090b07120529415030740c4a08130310030310842d0402000030440f4450184480340303101c0d01500e000d1041c1c0884d90022075640449032829210714500c640c0030a120318040c09105c0c0117aa00400510050b400c02d961600200821810250700080d101d1000449840360b0158172199041e585e81035440d2004d610019081d1004610900c4803a08420b0f40050044d88a030251815100c007902c0d28040c595640d15420009421500f100203101c0010003000b08200c2603000e8201401c8080e40c03066488151100b503c0190b0f8440c2099036404501440798402142e001e41c045c00803d40211600b0020704900340c0c03030582650003640d05040e41034440c1408e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 947258552 1250 947257302 947257307
    0x110d020714011d150a0213060e030601060804390905040b06060c030a0c03090905090f0706020f0a020409080f03040b010311060a050306040f09140106030605102d032001 74
    0x1070103d4040100441128444030030a01e440341604c2c20b200012442c0c000c042810345450358160380c0c000780d500d04003031102a1503105c080d0032501d104540a20a11502c2c00114034648a080c0c0b240c02a5403002c0c1c943c420080c400000700580d0036100c20035000900704018110001c1c40382c1021f200500c042100005e050a040c107000c992030300300034651402900d0070054900549000412a03803500300e1490841e0304540c0e02d00c0c0c2200c11300c0e581c0e03002c0404d4030f0610080c0318821202054140c0410b50f8102160411a5580310070798840740074080020554118140402c00b50515402c4002030a01c038420f49032a002141901403142d42060fa000c1d40c0322880b00d0018400c06c08041d10340c0e00080c0003200c80303a0400e140d8010041c801d01c03005094a01854840b0000d592000c0c5540050000c04da120b421491704001108210b402401144000d4070858103080200c0c031480100413a0400780c4031205075601b0348120040d00e89280034482c04044190000c00e0b440040480c01d0b00401c1044012248282d00040d800203000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 947259802 1250 947258552 947258561
    0x3f141e0f0705090103120e040c0518101416080a0207050a080601140d02030f0703060516081006200d02011a062106030307142d060406110d02071401 65
    0x3012600e6200d040e091007240e543c0e00d0380504603980012540c40c60104e9200486082031605c45181c0c00074240f00c003251540b03800c0340103003a19814150382c040030044000c04024108401d03402c001d007c2002c0304c000b82d1f0841c040304000c103c0c01e02d003031103150341500d010340c1c03805115448042120016088154140103514010180b40c1c02012440002c041c0d80d410031860f400002d80b0704403601c0c400c2c4240301559085403001d0056219841841c002c2c1c4024a56030700741503002d070204a9801d5504060081d01100c0f080c010350360f840c020141c85418428681c14074405582d0702ea060100c44a6044d601c04207654140000c200000b48507041d40e00100d08411044105802c11848203030407882100c042c41400c002c50301003500a400300816a60311811915880007182c1940f0441d10080c0c4503449045010030381450000e00030780c1c461489452441d2a0404d203200041040b02c06652501941001001c1001b1880e01c0d007180c0b41824050003058600712100101004a81c441c0808980c210810041c644c4401002e118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 947261052 1250 947259802 947259823
    0x1406070c09060e06090f0c1b190b0604060602070915030c03080c070f15030b04020d110304050606010c17072d06062c09030d0e073f141e 60
    0x8034448942460020341846e031400070205040700001091000c6c07400c6554800300300d40c0315203400341c0fa5042c1c4140f044c1c2051f40400442694450450404501e003810184900f0085038641e50140c18080e0400c820000078006a1302c0f14049001c2138080440402e14404802e00154400c1042568500303140f1100b0341484010360064409c0f1030600c0f000c00c040700501d410794420102d28600010288c00c041d00240003401110066450a407419040e0641a8140700c019401140a00111001c40c1c1e25140110f0b45442085401408000c880c2d032451084c6520300040e0805a2041d92240c803100a07800c3d8100200b0703030401950594103903034480e1105001c1e40381f14000181c45040c1c0c800e2030b0910300303130381801404408024613191050307135034001032082c03c061050301e1034018540401c2c8107c40480d1040c0b644c4046d0703030003684150300070518a071161a00c3c43c0d40b030f05146000300000301c40d40720b080c5e5810342c86002ea81c0300c00d0320a220039058041d8070307480c144484400c40b00e00b842200702105e030710300d40c0e030345881960310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 947262302 1250 947261052 947261059
    0x506090a061a0f121513060e010b0a0303080a0b03150f070c030509011107050307060c1205090a0512010f1d07050a0e161202070b040b130b011406070c09060e06 70
    0x392002810740781e0f811007550290068404009400068400c149092045648107a030450303010107008252210184031000ca9000b50418050140440d04150890398982001c03507200ca00320304104006401403140a90080ba00c1c440001c005030703600d01003400c0c12150f01004450300c144204000042000c403201030b412440343d20300300c48081d405030303005040b61041c0c41d00c29040c0311007581c071074204103c10050440684006010b0311021a603641010342908a0820b04070f518007541700764035160074411420b880b04060000c000700c400a02c0d0105002c9004160204e01c44c095480d8800c100ba0b4042501800428844078011040c072812643c2c141810300d04075030002441811141c10070002030031101106600031424070740380341c80f10741d450b9400d5601070159030914400500106414080c0001800203a1150740510509000d65541d00d503e06840b216006000f00240401c0300140070195124080104089014007554070b041e40700e80394440a45a04c0d40402003940e11244140240301000d407000d5007141d8242d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 947263552 1250 947262302 947262341
    0x1050403060203090c0a0b070b0c2208030901090602152701150f0602010903021f0e06010303020f070614180f042c010c0f030e0c041409010539070506090a06 69
    0x15503410307946d9240501603002d482c50200e400ca040720102c103200c0760040f100281d03000c18bc0b59940c1e08035413680c101c100d14501040c0151030001d170346030010400003103041c0014217042c9942c0c2d8000c80341c550000b508200104142e190002001104024801c0c050a01032541042d62030f14a001d006810030340b03550b0000170859041540c6600081c2c2c0002e483d404806901401400c0f800a250031940109400218030445200d5100000217244d0041041201c01c02d080c025109165251441524201000f02c1d50310002d100c20082c8502c074186401010700c03846401008c0d05010480100040c0507641418014617201115500c41c03090401c1417210b81e031002c2e0440000780101c00d0380f880c001d070103051804803c00a054079030000f00703103d210500040200210060040100c1c1d820301d07410260088080300e5104256103000041200ca1a44801c910f9164541c3d13407401e5400031140f000c041203041000b0f92010315507400d10a0705d00003401071003841d2258007050b00030003c00d111402c1c100c090306d92010001c1910f8500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 947264802 1250 947263552 947263567
    0x4090203060f04060b1219060b0a11010510231302091f05090904081c06080f070b03010b0904090804090c090609231c03021f02030114090601050403060203090c0a0b 72
    0x68606036141015461220303001a940c0302607c4802031140320806642074600710300422070704060409450070f50340d56a500036000f210901864201d40e41560500b2103102506c2c0200083c111100410f44412001982c1d6400b401840c0e001c10b602c032030580300503040c040c2c01081c0000e09051001c0156000c10400c036150150802103100a4000d100d40b000c46406084c03400d00113401d11401008507045105003003004081c5c4a50f900d480b6005102d980500d41c4580105642c1411244002500800b41c6820a013480d01d580d1a0041441035903000c0307006650070070b40320340b03020011030300d40b4019000600310080f0104062498020003090030805030072503001e0140040e07091145082e40d48070300704e0255600c0800007045140c1d01c000b9010022121640609020365040d03102050f50224646460540e070f40043c86002e0b05940c3e405003640824003c0c00d409a40012075503506140c5004c01070780144042c100646030940301d48946080e64400c603605201d9500030340c9101481c0c1030544c014030042480d04840c5060a10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 947266052 1250 947264802 947264819
    0x302030703140c190602150f04030f0504080a0606030b130b0a020c19060903031508120a03060b16051b030307122c010f14091009120c090b0a08070303051c0204090203060f0406 77
    0x1910103809c01000d4bc01080e40c0c10300810482d0068072040301229142c241500e400405810180811101511844007066000440254074100b065014191207650703034030015420700a401006001c05244100318010800300c01112511141c039000d03c102258407051400e01030155000700c0d065000a1494100801842c0c2000c1180a0000341c07014086903900001d150407806062650403c00210100094102c190b500003040386e07020511410644020245ca84840c5400720301e1102280e405400410200000502c030164018803007096003030400c0280480c0a02410300c20b200404051021100040c0c40e10039a00500701c40c41c48515443c1104101e43e8849000c019400351000c206d028940e0b14091511507400740d241100039084840c3c111100034010b08006003c0407041c42a5811240740a103600e0142c1001c0810000384d0f200c800041030050701d95a0122480d03800302c1c80540c411400b0390000016111140010402812407103400350300c0c1c0c10188100203d0020728401c00340b2a0b458200100007181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 947267302 1250 947266052 947266081
    0x605070c050d0201233705180913050d11062206050601030b0316060e120c270f0105010206180613060609060e0f010e010302030703140c19060215 64
    0x401c00c050003500081540360700300c80b80030b0501b12082060901c5504015541c11103040d20112448a40d000d82a01c0c0103138040d910340c03040c0300409411039400d00481405041001d00c240d00044080d180e501c0110403600c0b501d04000bc8000e0180009010000e54001c514003042619003040010742c081101c5800290445100c034035950004000b82c4e125000104540c2c001c0d8040c89110380080c00340d543c400fa542004099a01c0303c0e0144d43d020030042c002080590810422410900d03070044014075094400300100801348803889240c88044201700060010848105074182c042c20090082c01c071154100380029081c420300034030042291031402d401303c28140c4000340d8035810652114200060342e80030305003400a0030030b98024032a03042c01c0140004010b9083d102c060b101d0369a00380422002c0c0d0300e40c1179202c603400d800c0c0b20103903144d800208240003060340c031428501a004a01c084801510198011400c0710301d010801001d502050f4a0030440940c05100340071003804205001c8440d40b5100b541d8180c400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 947268552 1250 947267302 947267327
    0x13090603062a0e2709010c02070e10030206070206130f031e050c19080a11010e1014180d11040b0105070f080306060408030d020c1504020f190f0605070c050d0201 71
    0x3203610100058500c480b404e0407038018040034002142d10f251603400140a040c650400c84014861070000240000780108810f01680400c034071023002c186981c0030040285c021031000c0c1e0f4030800400c29448180086841180207181d0031040500d50f034950b04100c01d0007180001c00c07110180441440c5800511301040305c060f84d00085070004100c0164034401e0080c0c541e150084038241c810b20b0080300c01e0200201000001c860b00366644007217200b400042c0320122403284050350220301e805400c2c480113000c40c0d0152215070315810400008101c1c000000d80d20480020381901d0507403200d402c6502c0b600b014007071200c0f00350f000c2c02d0481c6800701a995595180b00d40b40006080780d500400450b05a59402e400c17039008104140c00c4980315187c00e6407080003540540c450b0025807007010310f021100e121504010b4810750b0020700d0403d140103441c0074440401d200b0400c0e0320000088810205030b030040d10141c81c01505481d038880307841d4107582ca802c01102c115030f0001c501c9607420154440c0140e9002c40c0d5500007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 947269802 1250 947268552 947268559
    0xd090b0708370804120f050414010c061d01200405120f03041508010f0f0b07030309020a1e090209030d12020d05010b090310060f090213090603062a0e 66
    0x10040400c0e9016110450740703040b64049000d844088119500c2003500b0f02860250500848010b0025020340340b020841c0c80080104e0024001000449020035200281c0541030625102e191407a83e5680c2c1103611a000e4800301c41d8001704101c0280009100d081c0480c581c0741401341300441c800404e4205801540304562064041c400c0ca40314550040c0181420480c460045a842c1c0e612000e0011007050f10300c141200140f21348000044c14107090b1581c1c4110740860a2040300c417400c041150010b039003d104d00394145603c812030840141c89e02441d82d8000c1c100300c52995400f0b00511562110385202c0d42c885e000150050040c00016500818444030f421114107281d0300c2c0c59106004e4002074011000b4114000786004000100381d882c84000740440c02c0c084058500d041980300c0b40604491490080c0e01442054010520003004164010409050140955601203075940b6450301036071102e4000700c410f1520344100c200003105a440d106039010300f41c036060004000b51300c2e00070041f00038448402e21 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 947271052 1250 947269802 947269837
    0x150301060807091808130317120604050411090703020c2109010810030c06030504020f0613050f0105070803010807050a08031c0203130b071d0409110607030201060e04050d090b0708 79
    0x10300042c403034503c0444551104409840740a006e44049a0071014402954040481044840a568280121200b02e0150440c4004031303141c40b01488020000140129231003c0c10614600b000e5403041000c2d032007081c8983e00582e86d0101d1820071800c142c0c2050200d03400070801d1506800300741c3ca43d41501c807424030a1038450496a41c041c1e242032401c089502c05403042c00c1c1c80b02c02090880d407540005100f24000c1e500b2051441d480c000344011072280011802480000d05000d0056141030804154084c00501d05107040c016030307440f00b004960081c0e0202c1460352260300c00300405c5c1850340c61540140071a0020b1410f04941c100480102d04100009003081940000000c41076801e01c00e485081d40c1e04141e02c0141c0707180035000a0004c035101250880302810402d0124150703d41802408030b02540080104d4140072014140400354210040c12000d40d501c80c0c03008030349200703010040c2e8403450003000206050040d10101408070700746c1d03422206003039008224000200303141904844c8400300d411312440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 947272302 1250 947271052 947271071
    0x10e03070309150e0a0e010815190c020102131202130903050f0702130c020d120203100b03040f0203120304150b0a05010e040605060426030901080f0912030a0515030106080709 77
    0x9031049131841d192a40302002d11004074030708620f603580e85e040e5400001200d6480c0540c0c604007281c21812038403101070741510003020000c003a59801c4186101a2400051706003110001034040c1c120054200c140c01d4440c402514081d40340c000d07080025480945410014010a84c6005280d48184003105084c04000540b6400f19150320790038401d66100c03024208000000309900a440c0c0820103902400039500d800c440e230f48a8018402c40740200c4900d40b41340c18481c5083c220000d00e400c0180282c07203a0384036070955400760301e0600404004070580b4801d95900e180c41c0c580908860341c601c0768441307002c0c0f4040d4a5049a12001c0d42c40d0140c41090800e603129250030340014000d0f10841d0071468016801041c005200396051100c44084500321207905072800e8003c80c5c00740d481c05041032450000f51440045402c44400c607842c142c00c81c0d8210300342c5a01c0c441a070307840d4131300b0392003503414a0074280e484003081242400d814444400c404201c2c001d001942c40d06e8442c9a5890640c050703101a10f54410403032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 947273552 1250 947272302 947272307
    0x24180b091608130203100615030b0303030a0c03060801230c0301030c0e131b05030d030b030a020904051501150f0f02150c041e0e01080a0b132f03010e0307030915 71
    0x1e400d1584c0c0282160f128240c0301051b400076003041d01c0387c08805c180d096508000c06001e40541104981d0160086007107075078103030403040504440002c10301891380d0340c1c1000c00c4001080c00f90700c3c806101861000e5048010001e400303a204c2008050440e400d0303051005100040e03000c1c40c03010443d03d501c10440d8050b15401c0c0140800108404020440340c0c859400d03403551110034640078202c5504406603a400c86410100707030240c2e000728114550541200c0700c0c2c4401860305000035900103000b1012242c1400654550140081081e088103e043c1400f26112441c00d41c0304c03480c00b448a480d031600031200140700d40c01954510314524001d0611010301c000860307031150071081d18010841c040c4100142d140d8aa0700714204c160500881900c02c0d8039500201740280005a42c00760b5540c130502693319962448151881d55800140845119000b82144520034007807182052400880098000e861440f1030101400c403200b246084000c1d400902c000000310f50401171000031a0580780041c0512072524904 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 947274802 1250 947273552 947273581
    0xe0106050f1c05010509060d0b160915021005010b0406080f0c270315071d01021f0506090604061a090f031c0f0e060a0324180b091608 59
    0x100d14120b40d101d00c2e20a84915402050407100151401c18060715103000748014100c010802400d000302040210356407820003400700c60ba4004a24161250688966045020000b61000031005900030b0720380346a414014400c0c6401444ae00d84c1540c030300b506d480c00c0034010600c0113240c0716240000c1310001c0e00040d85141201c0f0002c000028680a0700b2502e4070000d001e11417524102d0085c4200c4549600600d10103070141d0180105464041440b0f11000d109441c1400451f9854114001c1100508800784441800e840b000c1d44258081142d251441c14040502e200602c102d02c07440c24074030200012100380d000c05080b0861404081e0350390510f0000700c6c60112088280c280c040c4221050740c1c400d6082c1c881c81d510066501d640b80312007d041960101c801107614100a68002010045804800c0c002c1d0300c980140d8680340ba104480c1c101c0041103603925461a0b110060120309015001403071a041c0c400c00c2141c0c8012241c050301c82c1480b01044040c482c259400100b40441580031900c8510b61812 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 947276052 1250 947274802 947274817
    0x9150c0204020f07030e0628030e010507080403110a022202161a010e0f0604020309011e0c0314101412100b010f0f0807180506070516050a0e0106050f 66
    0x2c0d90341d00003040c40c090b4280c0c400c602c240c0003d040307034601014070f1030583c01700d84404045103400d5aa4100c5680c03060500380e81401d100003416500e10007180190350a0103030300c0c0308403011b4440e00300d68541070501801d803d1b80221100742507000003070341000607500c0c1c43c225641c800f0107007510720020b14001003100003885480314000703c455192041d5000c1011529110203101051012002a070341d0b10000355000c1ca00a517046095040d181c0005011820203602840c2e00c01c40d807400215078140ca044581901208200340034120584030303e4444065501402400c107840001070070381c4038518001401002c56080b42c010807900c00302c0c0a40b9119560f40340c00140c7c0c0780c252070005031100c001441403000018000241c006000c01c600d103200740b01460064280040c02c450b59210445580e940c40300032202d002d000c49400351500002c4102044503140d1001070100d0600c907000400000030400040c500c10070303142c0c0c4064442d40103004107101c400c4450320301a044401ca42840c1d074036100449854482c5005550 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 947277302 1250 947276052 947276059
    0xe0102040b13051c0305071121070e010f08070b0d090203060a0207060b010e012712030302040f140310020703050d0f1d030307273503070309150c02 65
    0x100b001003100503919010480d601141c0c514442040003011109608000c1809400300d54140a91004510720200c0358690500041520505141c003a83d00e03168403c4400400e802c0d5030183c41c0901180000007682130141c840d41c42890364140c039040a195884405004006442c100410542c1101c0c6413034012031040303030740102610012301c0c11228205c002e400c4900d0a4803080c0c10504884829405204028600d0b44c2c10b94451000c152004002405a4840c1283e2000080c0100e80040c03042d65801e85c00640318444d03980035075074078a00b601030107007009103402c81c0f03000560b51128800281e0b4001000180c00d1403103080981c503400c5500301914503008480c200c2208505055000301c01000551103042c1400d040f11118100700c0d01d0001280e9a8002152914003280c01d0040301c0042c400c40c920910840040c00005890450721003034800c1050001048103600403900316a6200300d03860408040c000159244004c60800c455070f200203000c000c0c40c3c40345103221251a1550308040d03101e501030601c01500038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 947278552 1250 947277302 947277307
    0xf03050f01121b2d090903201203070507050f0d0c020907271d0c0d0b0f060c06090f06071e02012a020c12070324090f0c051f030e0102040b 61
    0x803103501820318041821821210f04d880b1000c5040c1c43c6600c51800d20f075070507640c2c03041218522315541d131202c881c0c1d043c4e021061188034009d081490340d031401988030b1480780d51291f888424a10f403981c40e103a800c20710600c540e001441c001d52410744c40605400315507011a41c40342e0f940c90b1407000303076083c0c64540e510076038110f054181481052080c1d581c44080351070034040c0040c01d210384030783c140280c0d40c140e4048003c004204034061700071689401001608034000c00c441c090210002c0041c1c0c19621a0344004a560415030800c1040318041c804c0041c40300341c0b04046d01403807525820043c021500800c40d80d178440440020050154403d40c031000480d803000c581044030307496102c1901e200c0600ba0b80300c100144103445024106003843c84082c602054854024082039041d56100e200c0941801813041c603009859020380c3c070b404050302503404a180074403000c44651615040980c045012500820301541c0214200302c0680090001003420303016910b800a01d502080701c02c0b03406480341e90310503142c20402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 947279802 1250 947278552 947278589
    0x2208061f03053003060a301b0b03090c0118050d0f05010506011b02040c23040303120c05160c0503030d020d0b01090b0403061503060c0f03050f01121b 66
    0x4402d00f800e8007102061540c010700d410902c000580b407004403042034120050401c00c0042c1c00050407004002400c411400c440ca1b071650040ea0507c58004405894000c00720710788500d003220080e18580900060b002c072501d9450030082c00f954a4144d890950704101e00e49640514945100d905403004d084020842d40b0000c03224104203901c100b211380151029441d110105443d50302802124803903440e002a01200d5030711680801c40206920803209040c081048105c251116480c00341d03082000040007003e8489040d41002480c2c0100e407012503410524000e10501c403950440300340d500d144c11521008007031485600d000c521045559100302c0c1c1611020800042c01c1c851303500034040d8811086c904000800d0540300440d42c414003441140e8008104200500101c1c000e074000c2100380e040e0a00440ba01c1e6605d030781d00c40c200c883c040e154100141100c03090203c0568035001c1c803a000302c10444410165410702945071240e20710403800901c001011083d110110920490b80e0005043c60450020800503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 947281052 1250 947279802 947279833
    0x27090911030706080105010210021e19020d050a080c0a0c14010f05060901060906050f0f13080c0f060a0c0f0206030f040213110409020d0e0a082208061f0305 69
    0xc1480ca00d4400e01400340c2c003080303882c40b44040364100c2e4030585c01000740619545054000f50311035020203141c02002007113421410342071030041c40b1790350121241402c45076001d840281030a841548020401508100b8904a2680003800c81d4101100e0155643d03070b4414008290394200968100418550015200c440d05584c190301c102c0351b4900c094400e01c810740d00d1804003c0c1c0c80409000d0200412603241090004910480180404018040c1203900d4101c0a03a03944031a504035900e81403464583c2c020502c03003180c2c14441c0c118800001d498082c0e9006284c40064201e000d095a00c00c20810b1010416061203003880c0100750454020b829141d0b2401d000100007030800782101e083e4091400000190409505842540000004100484e0404c1c1c14100e58101035130020046003401604c030344a483c01c0345020300944c0801d074410400180d0f180120701851500c1300c098050710244d80f003040e0040010306000b054030b56121540d490591200164144806581c01103a04060107034410030001c2c07210000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 947282302 1250 947281052 947281073
    0x32405010e2202130e0a081201031101180306020a2106150f08040f11060c01050a061403030702130e0d030605090f010501020d21020f28270909 63
    0x1e00c00e900b120500c141c03a00981101c00020301009420103464550052107007580c0d44104401e20942e406e851840c0440d03100d0079690742006a0b2070792045035082c01081000a0f90081c0300c1d24910030700b8180e05290841e0700d0568000c2d000e00c000390099400161600186201c0c140c1014041a000000314000700080000f50003031441d405010342003c142e440784050f003030042610b81d02e10806a510f41c0d071103690340da480703002440784080211005460301c00303d414680c1c0c502e009400c94008400c000513640c90045e00c501c0a8490f0780e40300d02d08000d1003544040054030f000c41100c02d03082c7c05032801120001c141080c500100f141003110380e098026091030f014941d07030540000048690031182d1050580307410b074030820580820b00c00c49001d0703801040c7d0750751028050140070403c0d14070889070610b40000d00d415002079900c91020100c2061000a9141c001103c040b8980b06088bd142004a900494418098110b0f40c09100b40c8003080501e203240c000810341c048001c4080c181860381030000d05801d252581106 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 947283552 1250 947282302 947282311
    0x150f03020f09060a17033007050f04090e0c060f070b070302090a03030f0e100c020108010f0e06060f0c0d120f14060f210d090902030c04032405010e 65
    0x140500c8010145a151800249000c3d030300081a5031403462800d64510300017100703e85540c00500007440511a100040c7d040940702c00344c2e00580c14a009141c00140c10008801014482800824000c0d1800802e501090f10706942100d1400210840b0080c151341c540540c804070380360b02c03040000360254002184805440c045103c1c00d0702d0001034448207826002d9010724010150800705001042001c0380c45a90080c0c141b5580303041130302424100d00e011440550126000d640810000c103420300455900c03045050040501c10508000b20742004000d581050000d04180c1c41074201040000a8a54a40c202d6a07910405800c03240c4140c014500608851100c40c5001c100c1c3e4034201c0d00c1c0781d10300c1d4980076500c80c4c1c07880810b0712882e954804003000802800c0b40700e1603800c0540c4283c69400107601001140909152400038650711000d00c40080c000c2041d6040316070603d0051003030041c05020b5100350b40030340e80e1001c200307005840707511110064003644552150307100e428200001050315010341c405016 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 947284802 1250 947283552 947283559
    0x1240e1f11121608072102100902101421010e0108011802100908161a040e0403140c01051602010f06080303060d0c052205060a031e06150f0302 63
    0x8168080c400c40d25410300c8074900e00b00c0714003045100924007040e048503607020710411141d17090188540303c040c02c40000b0300e1202007031565001c0540509070100241441c29030f403041e00b0302040c0f08990106015106e405901c0d0b00f8841580003a18504950809030f400c00c8403029000b00603850b0701e41d85005220310a104154803800000008190307004180205107100400128041010107607600b0b001c04805100d009000f000341e12080030580c40700c207101d28120804402c4c9151105404c284c0010b212489103034588103902e904110820400c405040159403084d018244200040c00f44d90392800030f13200c2c1500742c002c1c95203040c081108500b11802c4000d01048682c2c0200302941c440c1c202d50040380c8050081160075442400022071a01d01016080d44462041801500b501c3e80c80c03001c41c1016500e800306d107205080b0b400e08903610241a00c14554840d2080301c4d500d44a514607103821000f00000c002c8040032103844058001070020b80e41016a81c510782c841c0703507881299605800c9034107a519002c100d11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 947286052 1250 947284802 947284817
    0x201051804061701051b04120b0c04080a060e06061f0e15040e10061103041e080d0801060e0d03120e1509030702190605040512010902030d080a0f0501240e1f 69
    0x1c002c0b10003051f981a0b81c8c00c0a50f0725691050b0b1b48a0292101d0011301745851181c04000110f2011814848069030600c10500429900400003280f8102030000340110b020340c0e00c00350014451740107030f01a0312501d9000d04004080981c8500031450211160000c114065400a00012480b45c2c3d0b0455600c1003104000f00503015845413401c84280c2a41c0701001400da00900c030030b001850842d000030395800c00d2602101704240d41e4580c800d08141d0361740e200001242c03540d4010002103800207080340010008503114103000f94160b038050840c080742c8080040f403c0d682c10a20383c0e210401c200c0408950030707401e114042c40c60b05880c0903949a001c124100e016100d10301d0b61400007441030b0300070000e07201a611980e0406091005010b8290842603010380559202d914040c050389040c040da02c3d01980e01d81e00c60710f262602003064419600d41910694100c1e01e040010800b000755843e100c3c922000010380c02a60007005c150454809920840031030707007c1c01e4804040189500e030444907070004125215241c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 947287302 1250 947286052 947286091
    0xc031e03020c0f0a09230109020406080106030213030f031106040c17010e1203090a06110a031d0c041505060d0504060e0601080a0b07110d0e09090a020105180406170105 74
    0x869102a000854000c41c0c00704091040d441c046c1c1100c0b10b060343d41084001c801c3c144260301c03000c00301c003070f030041c000b256001500f8007800c1c0c0e002c1e103503502520b039500701545031840300c0150f0905020144005024000554603941c1050b109000301860240c450b800c0ba02c040c00d0a091240d00c8022500c2a100850700c4603000350031011040c012490b01c400030078003030040d0401803102c0c1a020350006001110034003400b2800b600040c43c51103981d0883d48241103190322903501082c00740840f8002c0b45955a84214000740c1d00c1e020100141e140c440043c00c0c3e0f0302103124500503161244101850300030303c3c0e00010219094015404e1a400503105600840e024441c0c406c0f01d03c28961244030a025280060f0000c00c081c0001c900c0f41411142c01501390b01c7d045a02c51290f05940d41840700600b14400000c082480d500050b14003036031100e82104420b00a44041c010640c0060198811000049441060300f40410703d207941c0d80d4020750080c2842c1c030300c0007407240c8505401da009240c00c50341060b2801c11000340c0e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 947288552 1250 947287302 947287309
    0x12190f06091505030a080d1107030239040b01031b021609020c0601120302102c0c060a0c050102091818060f0403030906060b0a170606031608040c031e03020c 69
    0x102c0c100c640190282440c4201354403071040642c0030340c0c0c81102003078a8858942e1001c20110041003010f0003a07001c1e0689240c0ca40c0b03a0404403400040c1401d900214100207040c01002e401822079219041b42c000416040c1c00b001680a400300080d92801d40d41c0c080341101c600c940100301280f03000c800c000c01d002940c0d15072260b10101d000700161001c0b9940074400500240e41c00052a520990080c011180c14425600c8054180e41484450108010252000080c049042c1c40c2e4002e002c20000e0141074070b5440c010209095004014010081050801e000340c1401029812960b0500005d4081640e905140041c4240c5440580c1c00035030b031340c0f102000d83d054290f02080c11030107070704040c0c12101d50381c07610f48044016100e480c8007502c11030b5840750006107646010004042c0034000741c540b1082e555032080c402104035001440c2c42d0141c2005c00401040c400e10f02612110000b0604081410751036078181101000025000100070700f4104005070740484503020a914000c0c031039421a0180c240c3c903002d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 947289802 1250 947288552 947288591
    0x120a050d060b040b07020d060902060f0901020c0909122802030301050312130603091a15040b0f03030d270305090906030c0901051c0506040b09010b0109060512190f0609 74
    0x15004c45100c14040c0310014502190b00b058500d0050310007180340181c2d500010345542c000c002d010b02400b0000f407a0402035030184a11230519004842c0710450f440e104100382d8440400e04004039540c18005070400582d048074a00e108002ca58040b000101c5c6100c0302c2c0696254000e0017020f00c2072162081e401042c00c03000089810700a030400082842c03030f00d0700d041500035000303401701110000c004420080d00050000d080340c1c414401c010070f0300084200c4406002c00c682c1100302d0940680d940a003203842c152000401c49464400c4640c000035003440005008010003d84e00c0a00c00900701c12180d030b0241759005015203a485021103502e81a03490329000c16079968910307a03005030032a1a55004200b40c1c0340520f0b148884a060b903024101d10120751340e81c2e40c100203086400305c0314040e0301702c01d0008140c424480c0c80c1485a080c2080744410742000806003a034081c8003402103282c007404000071100308621102c1070303046010950500c904041020300308090421030040c911400c2c078107811304070004000c480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 947291052 1250 947289802 947289809
    0x200d0c200d08100e040606060e0303040311060304110910060210270203031614120304031704060b0901030b090d0813020402031f1d1303090512120a050d060b04 70
    0x1c0c502035038008400c0d40c040c03400918055800003200400900018600050340c0701d81d01c140300005800d41424009808540c8200b4614060390060009000080c2c145214010b900030494030b00740c072655545084c46201075809401a00601c075202403240064a50700040b0036074200c1c0c1c09a40b02c03104803018540407980f1040e0082030200710b0340c448001da04092000340c0a0140040d007541c2c502001c1030200c1c40001a0040d08071051040c030050030410341e40520040c800e555118202c14914203040d2001892041e0035190b01402e480b900300400c0401c06140c1c0600d04020010380410340540e940d09181c0303c01e2004550801150040b201c0c3e04844500c2414050300c1080e0008010814203569000d21000707400c0100b00c4d5032240e1081440e0241c01c500d0501140040072001010100010818801980c0f5980600203900e0810f000008400094110030858203456042d107021004003076058100c0c0ca4844440740301014824000380c50301c021540074008081030104c5840901c4450790301e105d1881c03188a03520 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 947292302 1250 947291052 947291117
    0x80d2d0b10080105010503040f0b010b0405130216080c0f150919031e090e010305030c0708210c0c10090501090e040210031820090f0907030303200d0c 66
    0x140180000c0d801880907541080c0074000052700303440d265560600000003a086980c5114002c00d040106240010f9014400c048030942507090070450050107415981c14130b4010705d101d8000c1500c140c100020802600720a52400c11240e429290030a4002841004c1d150100640078070706404d03284404507c41d8402403940b44c4d0702c0a4070004081d0186803003440d42d6580c1e200b04040441c0002d0995205640d290286004001550b03840c0d0782103a24601e021701c2d136400a591500000408042e041c104501c1c80f042d000d271584655918072004854134204aa00081641d110803419070b55260180c3c0826082c080c1c4200b83c0b5205070b000d44581a51018003003c4400950051404512107180d0b0b00c290040b0343e02c1c618800159000303c00d560380d00c8241e8104035a0710000c0b03403610085c5800c0d51401805068000948620319512410145045d03070700d502c0203010140600da215074600d2107103040c60b6102c01e0300301030352400e5585502d0100d04c81400341c00c0c86603205000035034207001c0018001d0402c03107a0b5160b50004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 947293552 1250 947292302 947292317
    0x601030309230f1c0f0b0603160f03030e0103020d140103020a0b0408100b2205070314041a09030f040b07050606011e0e0d0b070e030f0118080d2d0b10 66
    0x1041000002c01c1e013001070541909960707040070001012140301d050711a02c110038125042c580107080c5442c040500c07204580c02c017046001040a0301521480005980d0980b030034082941000e030040c0c0182c0b044040d1584101c1c9460785010302405106000e0307040e203108440311001c041c1d0320300c00c1028034040c80c01500e40c9074000d007844165110040d403018104850207031201001021000e09080c00300f9181c0041801283c440041080c1250b26104d624070100f5506881c00450070170740c580e01d0191031a15803072040706140c800402c400020070802d86079101601c0821f1030b0755942702d510700040340d00310140449491040d800030410541c01080b046070f0440004038141e81e00364500750f04480032900d140b003280e00825460b1504010840b851290380c070554850301e442a0010103202030514041060700c1c0190b141c0d260120400c0d0482c00303020340e4158150000000350700c5d4449594400020480c06000c0b2030009012075448000089220200d1031590300c0400422640005100b0300100b52010205000068102c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 947294802 1250 947293552 947293579
    0x320010f1416020d12021b1503070804061b02100605151c060302030313080d081b1305030a060b0907030515090910050f090d020f0c0607080c060103030923 68
    0x114508000303040d00013081a000310b030a540b103100c0d181500e818a07000603040b40890a44005182030a00da061900b0342d10078005020780da06000031400091703c2401044400c0d804a401d200c12a004460103865036a40c5202c2d040c49080080d5550a1b00b414030220141403100005140c078001b280b40342603902c841c070403904c0e101c540070f440301800d440f0b504c6902410703643e030101101685080015080d60011000c8002d0114141a06240361490850000c020444001e003003114000c9040c0108545144100f02540c90350480000d21030030301040d41110390903100c1d041c001800e206207070f000100410b406548184187d01c0e081400c409850701100d6505030b481a5980d200c1340c0d800c010b803e641d4045142c40c1a1502d0382e9070207a9100940b07605688031000085080144104220b003803001020f50001400140303400d0001c4100756869800004403548500320100320041030043e03110440700300c07172070300d01c255402580c50f0700e8041d285404602480d002c1440c1103a11030242e4041112503410306400800c40c0e80d01c500e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 947296052 1250 947294802 947294827
    0x230010c1e030b0604030609020d051b13020703021f091502120c04060c0f03350a0c080411060f0309030d06170312071103040602100f0b2101060320010f14 68
    0x1540e020890704819101c24040110f04144421158400c1a903900420300d00380f0400c100c00d4001d2406a80b0020303104100c0d4000094700050210b14004920b00352413401081102c0410051070000340191041744078842e0002003860a070f00403c0752203508000045a91030301c95203000c0b580514002e071004902d0342e52000002c1107080301d44466440c440e00c0c0066500c0075030300081f4807808410250030000d81c5030407030180c100b105002c1841d900c0f0078124010004d00d054240014000c0001420140c40603606a0038003c0300e13191342085400d0440c4c45d0020503a00e0070a101d03080d660350710084a40b000c0c5440c106d404200c1d2110041d803e140003200c1c00096040518920003000b102e01b02810900a111a000d201c9222103002d00181000b0001d680240c0140d403100c600c4042640c0031891007401c11352170145101555070b03600704a442021100e40300341000105810303e45004050303a4002a00003070003418100024101010b1001801070280c0e21580c01450071482607960313440b02c40c4900d43c0b51100744244a01c664 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 947297302 1250 947296052 947296061
    0x10080405060a1b031e020a020f070b0a0e04020904090215180609100509280306050c0403050303130f0b0a09031b0c1a040b04030501050402120a0230010c1e030b06040306 74
    0x41c00485c0c480c0429101d0b078a08803c13640100d0a04001d07800c0103030f86101001040c80008018644140d07068500086130700f0040048100481c07491149a0129082000340c40e00c0e40514001c81c0d020b40b0a440d21283c0b20400040c9030040d07400780c0c55034520000101401c0c00c0001c03c1d5400458040c01030b00640c13000840c00d5505400c60005603400c903c55142600e03000d5101c1c913100245905844001418600358244502030351001040c1d2031405100300b108000250b0004116a8807081c90103a0100c01c100c54a020406041d10403400740c80154140c00380a0010300b00d501420003035210382c0b2941c00640d504070140d4038103041d0030000b5100c203602c03103004c01a000c0c0072078002100030303c00f00d030f601d142a840e00c4c1c1d18059034000703801c01c0e500f680d59003080108609156001d9103658290a006040c807000907400641801140400b40340c0303690309810501c00c6d04120f4107612805504200003401004404900141510301418183c81889035008030703801994041c0c4200c4105c0300000d8552481c090868841d030b000f81 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 947298552 1250 947297302 947297321
    0xb0d020d090209010906140108040c05010513170105100501030506010f0e030c030a3e04180b07020109170a0206220803011202031203190504060b10080405060a1b03 72
    0x9a1078030301c1540183e81d001a010302900e260200064864280781c01200c000c0c0d0800140e03030510905c0c50034480441c0140e60702a00312642460425035489540d020051146420b07808070417a00c1d1840081d50750083c06400031131003008005e4070f4030b000c907944100440136503600340c0c2ca60740452281601014610301c2070075480380100b005011550001258004249030506aa4050340d0901c1c27540c4074641c5440390b42040104445950b00c203040c0c000c4c040180c1d141c2c03045d0701c1d2512034410341d03070340d241d44e040306a40000b005416600008818010328141e4400f90182001100880e102d89501500c850003004178425903c1d42d00c50b9500404c1c040e55004000c00d401240c0f460824505105494007800140c500700c01140640840018170042c005140305142c94040c81d2441840040400e0040000d411040484810000360340c04020402b911181040c40081003030003c000c3d003100d00c884040500581005082c2e018512070000c03510160750b110b10000850710149050066002001b4000310030314440d1b04605201f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 947299802 1250 947298552 947298577
    0xf1e1505070203041a1314060a08060102011e15061b03081305010c0f02060106020303010e151f0f0e03011505090a2901020d03110a0c050c0a0b07050d090b0d02 70
    0x202915941d0810170401511505030f0042c2c0d000032105008108901c42500516076030080080010a44c00001c0c654021880d4807010040c481d400103406a10075000041001c42444001803114906801c1001a00d68859007101c0e44c1100340c4006001c1d4442c00c0c000415001e215208100384401d650b08035807120000e01070541c41090901c1540108100380310f01e8098185e540c8a01010110071000682003400c1680700d002550028001005164801079182e030384140e00098500480140b00002504078040003503c801c0001d520139262192a040b4201d51140d07041c61700c0318445a6003c20030035082c0e6500744507030070516111003000c1103103042041c100ba0f0040c4102c07801007031954034003640043c2a02d6040d160382d251130301020100841e503014400380b1101595071031b0600c0301c07814613604828180704010341c000820500c815a42c0900100b805602d83c00240240458a02543c45140c00e13229001a601a20706010351005861858024002e010881d8a17004400e400e0496040e1220020740144907030032170 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 947301052 1250 947299802 947299807
    0x906061e010909060f0e0a021306030507110a0606081b1008072001020901030e0309010e062d0c2802040203130f121b051e01020f070f1e1505070203 65
    0x1083d5003079015803030150803104000035441d40390810100110038007800842c84184100701012540c1d1030200d41101340d901d01e0801050689400704101e81d41c03403c103540718255001c1c2d004041c0402445400c91011182002c0403190601c551102d82102c8008419100b071b404906868030010329170090311915401f50880c20080348924a42440d2072002c19503540e5003004d654000350304081584c06100380b58124400100071814108110b0010b03101030390781b40820340304480c00b00300c201c1e04d00804c0741000c1d107807004160fa8020b0203105004540c41500301c0e405400f058040c4e1182c40d0411001700c03401c440011854841124038010039021700009600140c8165150448140020042041e841d00d42e4400761250031076021803c1e92501c014501c105000300e8458950084910901144000074072034031800034826072903100448000000c1c024810703244884822240424040140941c0c90600180355004e901c07450f45c03007000c511000e9004c074448800202541d5000300b400a0251495010b00d81c00085401181e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 947302158 1106 947301052 947301059
    0x8010f02030c07060f020d020c0703021c1515030b01080d0e1906030e15100807080303010f03030e0f040216150b0105030c0c1204120b0906061e0109 65
    0x3d003100e442c0e40f00317200b00c2101541152140300000c1000c40d03a40e82d05040550300d40c1c0052005030f10881c2d00303c1040100311451003021004980c0305010006501d9a242c00000902548412000080400710003100190202c0c40386400307440c21a00074448607201c1c01005000c511200b003114010480a240c1c2807203d40401c2c0070200382c0d4001d007000700c1c00e6102d680449181114410803010b560703100c030041c010f80c0000032209200303a80019040c1d40e4599200c1048941d42e2200b84624590143c0141c1c08201003445803d52880840004021034001e001b04000241039030069040041c2e8041c403948120100f10b40c803807220500103401c00b01400580780010001c0c2943c080200348009600001400b10b483c04014044c0c188039a881c1c90b6015101d43d02c9069404111014800896402014a0200305e440000003003042c401c0c030004211311000c950b1500c0a444000c06031300c0c524148800c0318800b2 = true := by decide +kernel

theorem cover : BRFrame.Cov 947122302 947302158 := by
  have h0 := BRFrame.cov_init 947122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 947122302 ≤ n) (h2 : n < 947302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
