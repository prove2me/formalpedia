-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1569
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:42:52.650361+00:00
-- url     : https://prove2.me/submissions/79caae89-c21e-43d2-b03e-32f0ea346fb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 282014388 ≤ n < 282194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 282015638 1250 282014388 282014399
    0x503070c02040204180e0106060f0806060304050c090a1e060308030f07121a0a05090601230405042f090d020103050604150807030c08070e18010b0603011d15030601 72
    0x285504407840503100516040c1c0311030071411002021090001030540301d102c00c0340d42d12802e0080d80d00420542c146a01c070f41580c1c5c40007409036a001044280200004000a42806802c002a80d805540540708014900b0101500c1014000707842a4020504210000e00940b0340700707101d6442160b07080100d440c210345541c1d01e4203a5004024001004001000081019044052007080d040c10840700b4104404083d90050040d41d100c982c1c0714a11400914041000c0c44e6001005150550728441e0444010040700ca5a01502d0046402558010386440748245240e182058440307000d2415600303442e0802984996894503105000c6450340103a41c0c05401c10055000307800094001d500248003280710400c032140002c1c45000750b480510558054582001400414021000580400c070058401c45061030110041c0940207000e2241402d03020369032016005080d4400402d00030000c02041d03881d42c0d0b550750200c0340703041030944881011480f0003103003006d40881d07040c0e0407940313016014145c1a80f814 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 282016888 1250 282015638 282015647
    0x81204060c030c060905011508071d07050c0f120406030b0d0c140102072408130b0f04020f040c050c1b030706030203071101090602073509040e010204090f0b060703050307 75
    0x40d402150050f40721712112001510a0041070384018444219095062615040c5443c1a0241c0c2c081d05009032513010060701081c40c6080d4960240743d81c10240e40d030317a03002090380f0b00e0030b2881c8040390103a01840d10703840291511100108210303403c45d602404049070610130000c0c3c505d64540c005042003021038003006a940341d00100e549004c81401a0f0350050303592035111036040b004641a41c1303013103a204895002942c216402d543c01010004560b0a103c030160b40d07480ca0444050104942e200040002408555400308912000c1c880030b4000d105081c40c12380d000c1c00580103074400002c507000d0302c40782c1c003060700c0c0d141910a24210700600420b041e0380790400c00c0c0d0096102a16180c1041f14180300f03e00724100900603403881c5407007040016902d0300c3c28180f121512560404c03820850100182c0c201510340c4008220400f24000d20515a580031f0780f01c00035005025209040d04a9400440c00003a00003140d440000740490f28081072010220000c2003101622403010300601080061010941c0c0740d115 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 282018138 1250 282016888 282016907
    0x1703161e030c09050301021b01060807030b040f0606030602160203010b06071a0a0b03070b091e030d11030903160302030d020d05030a09020103061215060b1804050c0d0c0504081204060c03 82
    0x10b42c10a108a16100c0010030b003640c2c0100280305075034040001d00043c00b002442400000c0401101a218032421030703841121103140507101602d440a02c1c8544e20500105038026402550300050031960354031a1401a4085110140b0030b074402c0d441c001c058403050611078101c6014035400320007143c51410b030700c00e46c40081c0405800351000710380c0c44184185039181000701070040c00c000f60760507031101e0030b00c81003064003000c130031480d040b41c901040c41810300d4500055000080c855410f141e00b1001550034030701d20f180900a83d40b6810300c070315001009582c1c0a5112581943d0003a0140c80d031540c440001680ea41802e40c0201000500801c0000d02c0e4400682c003c1428510514020441a56500c080300b0754240040040d01c9501001c850864500c2c81445800c0c020f08030171031420704003160b18083d542c1da03007003074079503103014039243c1e00010541300716030048807035030410410200b00700710308040000d005401500820416100305202002d02c90b4104080e603040316644e1b6a6101081071340c0d40d040314a40c60 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 282019388 1250 282018138 282018161
    0x130b0a0c0b0f07050702011808030418290409020d02090c0a0305160e0108090a151413020a0911071502040528062d0206060a060504031104181703161e03 67
    0x5841e0308c0400c2482091000340014100410001f40000f4441d0100044401d1005200c948a1200340540b04501c40070300c8030b500400b0110f40001c1e01125a00200b00348100c1c10318001d601240140400410a0303060015040b68007159500304103641d50304250304030141e44811a20007060485440c801250312400e02c941e802003003541a50b146540642c1da11030388450401000c4045901d0b03a260000b50303800c0d03c18840e40100801d11000c940b10441c2c020882911190240703a06050715038150000085801c07044900556001e244520121070311072846000390000d00034207100d400b180700d0341c520681c49101c14402151340e03d0a008100d501d00361040d115070080141d03c90703501d42d40440c4070030b140c10040d1480c0c91a02058010b084039150440401818121303030f40104080c4074003840140007040c0a41220803222500f9500007a80d00304030060400ca859200000408003c821003503014075206040182d801803000c0c503520002080841815a82c0101600800001541002c04000e20b80c1c0b00b50000c007200e41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 282020638 1250 282019388 282019427
    0x60901020304120503070204230c030c1b030307090b07121d0301140601020c0402072a030203060a060501030b0a0608240406030515071112130b0a0c0b0f0705070201 72
    0x2e55030150040f000c040007400352035a820110b003080030b5040c0381c0502c110b400c54001c404112000c808c404007038021409083c2e0070700140080005100b101e041c0080b100d0b800c3c044100a2072000c18000310507034a030310460b114000030300000300c00100404124103940720503900210715500d4010601044031441c00c9510ba2425901301c6e900d6031070894800b0700ca861034074201103851403d10300e0701320006441e085002072818007a0788100022404240f11910a10060848400401000080205c0072144805e6034101a600d40500014840340c036000703511081c00ca030390070388090081402800800010045521492020680d8078002030040c656001c10b0041110200740329180003007403580418100c50641e00200c0382907011406000040a580f1400e9502c03114615144401c8080324256a0315070000d011014100040401c42020b0601702d0100100500004602c1548030451000010820200c604c0e00f41e8035004403101141a0a90040c0c00621034400b5495952605040d40e0045554251100b070303030b50b01c42 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 282021888 1250 282020638 282020647
    0x201090302060c0312090f0307110604030215031501030219032d0f0b040204080c061c18060e0601061d0f090108010e0d0f020a0b190f0e15010f050609010203 69
    0x40e982c04000d880079030341400c0250740b100c10601a08009020250034116198054045a20071a800100320303461180e2088085030a081c41d000419110b00654000940c007a40d4415013980c0e4100c080b016600c550109800c0e260804503842c0113404a100340c540710b4084525802d800b54296000e90030044654032031040a446001c0e0020300e07900c0c1c0071591800609201e480d041607034500032060181e024103078001c490440ca0107107080300c1c0c655900c9004181a0080c0c4000c41c0f1450554146000d02020318601c0c001072083d610407508900500000c0d03c400c6540a02c5c00400c4100300b031000841c18182c80d120f4440362060100000c4100040501c4030800b40e114800f40c1840380c00d07890300c1c250503001b01100400401c041a40c0c1a80c582001d91841040301002400945540345603800030303030220a40c2d04a0200b0115854400108a0031041c0d84c1d1403100c6682400729018444000b42e10030b00070381448009a030300c01441103040111641c421b200c0c1c40c01c103811507103003440549001c1c0e008200d480d10500440380b60 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 282023138 1250 282021888 282021893
    0x302060a0e1306060206090c0a210f0c06032c100f0b130f0e120418090f0b070305011e03080f040f180b0607021c03090b0f040f0501020c011b02010903 66
    0x361a1540c12100051b08190148029281c0800c03c807414441d046402800003414144a001d01d140050b040a07001e542c0b0204000c02d0058209034041181e030451080c3c88440d0300c0e0b1101401420301c41060a01948440e5072004c10400111445401000c818001d001100c090050501c090301d074402e0b034001d501c2c1d030303482d140041941e805920b6484401c134014040ba41c0d409881c1c80508844005004d001550803c240c90341c407a01c0340300119400d0302c40041900d0f02c2c48800b1a202c2000303000a2100a0182c081c1c800c02c4000d100c0c1d9100660700c1000f1079a03044c040c9a072254140200010380142840c0c849d50840381c2440000c0f8260041e181005000042604243d9254150071580c078440d80100e08040c480b0783e040840041d130707000d001f01c80c0d0300540d512072908603c0c1d8040307448690943c2d0181c0611005280c840d040500c140950402440480c43d41500c5010680c51b0300c80760750042c410b8207110000d40c040000e0550011601d0401000143c58007034490b882c074010b03221404000707901241049402c1001000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 282024388 1250 282023138 282023141
    0x60504030e0a0f080c03160621020d050f06010203090d0f05160e0109110703090b090f060f0d060504052203050d050a02040303080702010b0a0b0f1e030609010f0302060a0e13 76
    0x5004031001c0d60320f1546418031007410003070005800c0d03000e5003090704e406804080004900044800500c0d1420b01e00c60b5001e01035400300c0802c0c0c03012240b28000592040e00b4031041c1c01c214003a0a04401c003401d140c9803140103903502e102c1c4100b0313260060240149000070511180008864501420035200c18200c80344c0740d0340540805800048a4402900c01407242264520505048030f814064091a040864030003411030500d0340f180500a00c1c0010300b001c01034a0700c440004c41507401030000780c1c0f07800d2500c141d05216044407034134401e810301d48040010380c0e15050245a000e804d039020458500b564080800030b80e078884c0d40069061240810005d02500c44034455213100e821035030300040e143ca0451500421103c2c01074800c40c03c680c1007000954560795207100d4042101c0044402075920024028080100c0c00355801c800c1d400c4807410305801c45040302d5802140714075411030301c070000e680e220403140c6c1c003a10035400060340041080c040e03034041c14055209035000039401806600d03041e54048244c1c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 282025638 1250 282024388 282024409
    0x10e072001050f0417040815061801080c040e1903111e071715072a110a1a0304020609010e0d05151b070609081201030f0201021005070c060504030e 65
    0x40001250410040c0148022807107400210905d00510309481c05000903520344080b158034200456040c045900365403801100c55514104c800d407111070350b81d1019400c1d107401c0380c0000f05000b50f0414000742c2d2590400f1805900c102e070030490006980ca000e460454040c060140d600010f840b841c184400020360200d45080400400e100070000a8104154480c412001c0311030110300f58064a006140645901103441d440340d03d615204894240405607030300284414168034800b1518525603e091140e007403100d0402c00410746407980840e036922913031454036038880c0340942401ca0a002140061519038020481e00e001403401c80b20544103040010840041e261007240d0540c420703504048140448080154054600b02480d0401e184c25411001c007817190b642c0040019982d05154800c001640d0140c81d110600945010500d6849261080d1a2100141e00307034098480c503514840d08404034040d59129080565503410201c1310740da981780141902400c200e080c4800380d801c000080d2200402c0c00d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 282026888 1250 282025638 282025651
    0x10b03030f071502122e06020a3201091a0702030715020702060c1f05070504090213150f08091b100201140702030a090819080d09081201030218010e07200105 69
    0xa00c540d0654105400e01b090880f01010207842040c080044540224454030010740000380c0500c50300090840841a00034110340001c0c1c088880b1060800020550011340040c0c0300d400f514484450003c0300c8500311204552000040e80100041000200349020f0a401a040031a0160130a482c80e070008405800480b00421340d60310084a0900c851781c170210503900001d200000b041142012400141548200d0042084440e000034000c68059041c810b004020030418010000b080340180c0c004155030b182980c140000f62229000c00d241c80704c08510100b880d00d030502c2d01004803280310140054080c0415401066550b203070050000080a103076451b11800d541c0e400b079039a0b001c16007000b0b40780080d2500301076603a034012010540c00080f0844280e5405410000d000e0b26581d5040181014080401000740103410125111209400800c2c5e250f060303900c222885002d00b04207200c0b68111010174030509003883c001d0b8022803003050060000580c0c420075200c110b42c91a544840c07840c02e40300182ca06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 282028138 1250 282026888 282026911
    0x50607060504021c02150a02070f0e0603160f151b03030509011103060d082803020301230d11150c07050a080f061b07050105040b09010b03030f07150212 67
    0x200b200310f01c1d04100e00c0c0341c00018010105442001031700820030044c02d0481002c1e250038009404148980200b2507100101307490012158501d40f1503410408044d0141c0714980240b003001e00343c03039107070800c01144015284103045042c801e9107441034102111030018101f40034440710b002c03001c0d01021030800780c5090500a0324003080300e080250040742100e6803a100d0051504090040c03280703d0780d860100711038581d04102c100352035205848806000d1155044400081c0034801c3c4081061078154003e141202d5402c00c007600c184101c520541030711045e03032541d298480c280c260358200007034a0f20201c10a040018100c00007507085041c40742c807280d01c405203440082c4d102c0030041140740f0f040b400f40e4000c2c02c601c0740030b010400340c01c086840c6d9810b006000d254007590b0072910849040b50700029114141d820100a00640c02e06040c801c140140988001002c0d50030000c0c0c48040e802d00200300c030001002e4038121482c00a40383c0311a5603000a81d80d00844042c0c08000c1080f032442400503e90245400e5100f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 282029388 1250 282028138 282028141
    0xc05060f04030e0a0f051504080601030f0302010513030f030c02070506040b0d0b040c2a0b160306061e11070306020c0d0f030b090c0304020f062703210c03040506070605 74
    0x1405040c259083c01200e00c95051010140030050612110303030b040f900d06860409416074400e000c0c07040b5000d2900305078014810400000280032100602d0201a40250000c000c035131200940d45102038101c0700050042803000b1004100d00e0700c170394010808940d8900c1075907003c41c4c030354002480c40e500980c44207008800200d142c0030b40c0c114510541c00d605034110b508100300301020030090a8003605000d41c0d4800c0d841c0708502c0c0184500740c507000030710716031120a00416150813030420240454441801c00000d00c1c0c1100070507401e0058140d05019440310366030100e01c1d4000c060448425150300c0364400c0d1400750031400000220140050946070031444050841054081c10040c404008c050100c0304050410711104a5a00d428414580224000703030b0710756a07542c450002c11031107450b410045421140015410307002010b040030841e01c6d14403a040312440008440f080540c0c4a01000b010000d4042002c0340c04414496070005241081c0f550007680d05240d99540026004e40041030142c0e4696102d20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 282030638 1250 282029388 282029393
    0x190602060a06050904031101020f040306052202061c06150306030506090601120201080c121005040605011706092503021b01090c060e011701093602060a0c05060f04 72
    0x366900041811041000314035000008640d000d0140024081c04909034080329a25000c8d01214907860458504550f501e0340d80c0b406000038402217980101c5070441c01c42740308403848061040c4d03001c03580003005241008401031003040610214081c203020380380d42e14400100000d0320440c400c81503109440001e001451400c215082501c0140010f0585d04400c0040c0300e400300c0401003403646502031034404000d540e504400040307489450450201d42c1e491b070b4100015454000480415a84203440c140049035075000159401109074164840700c0902900044403420907290b4a075021300d00f5600d249804008040001c4204d50700c403144030003c2c0d0002280c44440020300d00001c180c0154500070010108603032240721019550b40074110400401c4041d02d41c0980c842d42140300394238240310492140d940e44504000c000d28883c0003140c806198445100407100440e0012552002c20384030355035401c40c20740d0030411654002000b02050000d0818004085101000158400c2c0f5481d42080d06074102030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 282031888 1250 282030638 282030643
    0x5100e031611030c1c06021b0a1203060506070201050301090c0c1205090301140103020d150f020408031306050405030706030b180a140610050a030b040f09050a1505010b0a08090c190602 81
    0x1404013a0140140c07640e583d41e48601c01100e412080c0c0c0100006031211040c0c01b611080c20384107622901603200d030440c1ca0091101c60300082901c921706840c2082082d0752442803086500a141c406804504140010044881203420a0300c42c8891840c0020940d0b0590380c613021000381c50341c0c0700c200148000c6103088940c10300b44201041070289044101540d80355034000f0b254400315243c0103205440108000840704400d800c00c01c202e02c1e06807401e40d00c071a16501a1030f526084956140c2e0700180300c14000820304c0c0180d045900f621000b41c050000142040c3d000d60150000444841e041140300300d5000855100c0304205004e480e2110003c03c800c048003140030014400540024411030b00da03a00601e285401400300c1d00c50b4200342c2004940c40c410100007400500b9036640d00e83c855818100710381c003080000b103103c4081a1040300c0291071500b0030200ca4045500c24080d684140c00304005600c0e08600421401d9800b8150104442c040e40031800469181c0e2052620640014090310041c411075805 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 282033138 1250 282031888 282031903
    0xc1505180c0f060f0702150f070515060109060503040c0b030c0901030f111b07090203151c050304180f0f0204150804021f0507120507060b0102030705100e03161103 72
    0x2180c2c030b0480300c075140001800c43d21a4502c003484003100020351000315121842c500d4651280c0441003915006520140003103648402400c81c1c0b640035100a4000350406034000030700448041e50b4141001c0e08000060f6040d070300240c0160751218459600080c02c941d14030046100740388014895071101442c030000340607162600c0b00070058900744006800d02d030301c000085c0c906150303504040340242e0400b294000d007080542c0d00141c082900000421401420218051b142d40c181999030100e5541000301c1c1030b1115100c0c40380200f4a410030842081030380e59480550000b0781c038141d03001803400d004048030030850b03400003200120f4980200e403c2200300c0c40b1400c2e034046101542840203981c030b401d500013250a99801c284405040c42c140321711029070701c2035040d40e0200b94041002801a00d01c260054070b1504036083c2180c4581c241a41a0340552010042d2003106070701000400c03c00d0030412400000c2d00003c80d00d8206480148000050100089100b141d003900564801307020411150074107060101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 282034388 1250 282033138 282033163
    0xf12020a0509010f032315030f010e06090a05060f0c04050619080105010c0b0a0e0a0b0708040b011205031e0c150a05060904051002090619020607110708030702010c150518 75
    0x141c1509a40e40980720306003906e6603652540c400f011940ea40d5414810341c062440c0840e0188140e0040e0003554a05511403410100c40d00210390081d0340309540d45075900002013008209400000100b84086501820542c000b030220b00040c2c02d003034462012849580007600d690310002030000103028443d40018081c0e0141600b0b2a140c505d0006544420042d8400a4001410103950715114140408140440d000f0b035584480c0e1520103003422400140020800d0b00c00703440c0981601e0000515401d200c00744000181d10001030342c00d20384a00c0c0030640c5441a80d0a403443c0100402070f0b085202c8080c0900400c18071004180350403420407402d040d044560042c10180640303925800d00c804142c001454203802c42e07124401590700e03010030011444074042c040251884c90711210341440b2503500854600c0c8030b40d00640d5011114031101c11000c0d96003415200c1c4062541007001130b400903503c500908a51103001d202e113048200140d402c48411101c2c11149204006080403180c0b100c26020300079008040c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 282035638 1250 282034388 282034391
    0x300513061103071509020a1212050307080703090f081b061302090c0f04080d0305060405070804023607020105160206060108010504051f031407081c0f12020a0509010f03 74
    0x4291005065480c0300c0c0100c0030300481c1301000d24a900f0111307078016484269000e4140304401d07965a05420700d03018590000ca0785c840950fa0111900c5220308243d0f4410400c41c1c0c0e503101d85460340700c8180c1c014030081c401902c604e4040c420302c00100d00003c00408584400c04100402609405a19400d00340c02400584650f180350b94040007503a103500d074040c1c2050140e420165a06110a401d000c00e01c46c503403203031115000e20080039290542603401030b0300c030392401c1c0da0034001541c9440d0201d4803403404a50080d406440508851946074002899201d510340001100c545043c20b50505545104110f403c1d0700180c6d101d90800c6403a8540040d6a030001e4a140001c10741c6090402c0040d2100405019940c069555000007980303d01e0205900b20b07004171818405424541c590404d00d00f00781d502c44c4c44030890f200320388001403241000500140e1403003044410f200c0c0002c00300012910f03000d140300868100610020b520a5140d950301c01007801c00443d444596903000038a00244c02c40d8050b2180d0320504d27 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 282036888 1250 282035638 282035657
    0x51b030409110405060a201f0501051207030b07110714031903080604150302041b1e0e280e010e070801080d11030c010f02030a05090f0a30051306 64
    0x40c0c44a501b519031840040c140440b00b02c0c00f40215004031510100004050720032101004411200b00f8550341030415480414441c0c0da0300e520034484010300c00c00720355889038000e28040002c91080c0ca090342d001495840e1441d030488206811a2421819401c0710b5203040e40f500c0e91100a190403c20719120071000c3c1001c2081d0595138501429000d03005004a00680d20380c00103401130400d490034000919802041007001045040d401c5020140786801e65000ca508081d410b1140c3c07400501c1410301c40e04a035580c3c40400756030024092a440300d9600b820b080c0d0342d0365198200400c00310300508080d01110301d6941c582c1d858a0005290b0490281025090100303000c014080100046800042000582400e5001d00704190381c21385944a140104850781d46820020100082140c00660080b031540c07c0c00e020030746840002c4c4e621000c5141104805030300203040540060300c044c0703401a2003446445c5071004001c80792074104a80840c8088800015400540c4005c00641e0b4504640035045030f15280141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 282038138 1250 282036888 282036899
    0x211513020f0708040e06221a041407080a0e2104050a0308190516030e15030a0e010b0609031e011b0c1505070207180b0303070311070b030f06060a051b0304091104 71
    0x10351030040d201147c0c0341c0e100c408507000c200e1078460142d15558080c2003088030a0b400c285403203442801b81c03400000140100c1c00306407407810b00d0150b000c060750440c000d0020304001c10303540c81003001c01d0700c024212040203020011382c9035140c80f2524002c0d4080c0f0b030f000360b40746107003041c0482c0e040341d04981101b441014850b00102505284861135859810708100070240119030000b1008645004400e8503103000004014000c1d0681e040401740481c20300c002e10500c030a071b00411990380540300b06a90194046400342004208143d00714034141810340c0002200302e013100080140d2050b80d41d00700301007a15617001c4400c208004600142c0712600d44020009802d11840081d03e0b907002c0c5c850074036080c042c44c80e82c03189082d01e50701c075140210004044980d10b86041c50080d00d006c44078009100103005800340003c0300000c80040b2031040602d41d020601c1d60380c0325010000e980e0420145001080014040b44943c8800b0324407580400001c40000d60b101d600d000408070a88880381c2040b02015402c1c1b108000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 282039388 1250 282038138 282038179
    0x12919140c1507050702040e010c122007020111060a020a080901051e18070e041403130918021c1e020f10030e070b211513020f0708040e06 61
    0x8030742d488031000a026882d80c400454082c01040e402075170180c540140084502015031100c0300c00e03030b565118a0900455010454100e8014106000408003088034503400783c407088008140e030f03510505249981c0c88044594501c0c0100468201400c00d6000480c403001541141602e580101c00c44000e20040c502014181110702d0720111751030303071514a0b102207000c1c44840d11402500566200c1198412552b4a070034440b910350941d001d8503000d403000005140c207a0040115a0041101800c4030350151400100c031005010412102d0f503214105003c0c030006940350240740c120b01a0f804034803042c6491500f008071101001140c00c1c03070410441c0b1440d00c01030302c410782c403c00c141308112038a00c0c81009070607080c0c000d82a681c80f940341c240030b42c2002089540c500000762040c003c1226203d40441000c02c1036403010303901078134104880b02062042401038034000043c428699100c0341c0140c1028071020511005400401c0e045404003070110b4140007a1074514492a0b0003030f0200c0324a422408624000034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 282040638 1250 282039388 282039403
    0x1e091b0406030f02091b07030e09070302091c150f0518030a0207030f0c090c0503040c06020106031e15291c2d1101031b0503012919140c 60
    0x90040d01c00c0380000d10161030060011b0b14081c07580c4116a514505480c00400200600c17810380d00c2440c0b10004109064031a20a448001074090402003480c1d00c0d1aa402c8002501c600c002c850040b1000e40783d91440e80070b40103a0281c506250800300d894203003080e5820540101e40401d1310158002d02c045a0125030004d07034481141d0b04505241c83c000400c0c10300d0b038083c4280c0c0e04003c011500340300c0f41c00c0c4865400302c001c62165002d50914102c140d20b800049003070b10030307910010780741c01c05052003207070711962030b0702540c5039144580420346c0011300d440520f0b4241ca40c0280082c0e44800064010700000e8022884607070b00a5084407a0000348030343c100d01c283d1480030300102030700c0000340e000807484490100ca01541c0b00c440c4030511440b02030709458492048100d005e0082d0000e030a10005121210b40741844040010f803d485481c2160300340030141c009040c114880c0303034101c203a0465184240003c1001040441029000070740c603005c0e16a0302802da9a920700401e18880410042483c8540011030841c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 282041888 1250 282040638 282040643
    0xf0c11010c03020a0206040605040608090303040308011809020d0302060105040c030618020f070b04110f180a0f09080f041401020d051c020d0e0109050f010e030706051e091b0406030f 80
    0x200341696900b412403901100722002034010f04000740c045007950300600075200302d0f1040d41e02c0035a141e541e500c02c1c980742d000035200240850207150040c00b90b542d801004407601c40d11200001141612500020440070720f8043c01d07400350f000000140030030b0406018042048455007002c3c02034600d0104e8045198895502d020101c80d804510b0307202303005054084400c5103420a030401421700b00350601c0c5e080361a05001e2548500c4c008440c030b01e4039051400800183c080071803030140c5103685415468014019103415031001a030380d8848000001c00050190030f440107074400301b41e12142072115001d00440c00310881030540d0300c407500d202142f990000c200d814800510313131151052000107500201034001e80900c900210305080d03901c0e944a0055001c03119084c0203a04450841c591408614200d80009014590540041003102e021500b15040240c10112556400080040c01040c4220080c42a0386655464026429503510442c80120742c2c0b10401c2c044a0402c1814590380d1260000851403100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 282043138 1250 282041888 282041897
    0x106080703140c160b0109020a23070308060609030a030215060108010b1606020d06060f0207061b0f0f08030f070305011d370b13230a0e0d08070f0c1101 67
    0x1101c41c0d501d1307000c0d03d040b41d1642c0007000c00001e5843c3c0784404065002004034000180c2090040304020358803d402e200140d42c808442468030200c0d88040360403c500038170503a00007008105210f03154504000c0900c15031f001e035014049208860145414805000d0209410480d488006201800000080b00c3c901c07820143d00305a840340518180d8064016030762254529450220002036035034109140c44070a5a06a00380d5080310f494842c169480c108180d00c080c0c0058091020000048140415000e001e02a103400400c815155441002d00e9204460040b50110010107000344075400d8000c3c07501601080d0355070081081003080201e00c2e00002421200409408504030003035041000e00310a0107046819250924407154081c14080d1616004607805007407030300e600700e8504c2c59900c030380014602e819045410f1003011000410f2030650160031055441c1d40d4240c20308612500300071140d4800c489495020444c54801005802c001c1440c02140034090145c5900780011000c030f11a00c4419002d017003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 282044388 1250 282043138 282043147
    0x90618010f14190509121303050d0e0a0909050a110d020a0603020c0c0a0b0409110d060306061805072703050105091006211502070213050106080703140c 67
    0x56250240035000d210150081c40c051128941448101a00b0310419125401c038082074942c82d250000c0301d07070850310100d0582203807800340052840c18005080e40c6400142110342c85886c0d80714503040407800101500810a980300300b01c2c7c1814074503c1e0303030003d180000342081400440d40300c403901d480e14035000a10b01111341e10301040c240d5440d0a4080c1c02500580903980381d5403100d2020380294407490340031140c1e100320a00701c152481d069103940159003011a42e90b0030949030030304400c060403182440310840703001406010716595180c030910004501460b4080f07200c03482c005d00140d42e9070841c030341e0307400035070402080081142e0402240700d500c064201524424070600014103902a46540004200d5420003051141c5c400001600d80e0569020032820403250b56110b172401520032203400805001c08007020380c000490804103c49000ba250118054170302425940018140c40514010020b0565110018860243d011990903405902e0382410062003940c0141440385100040c41d60302c00050019 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 282045638 1250 282044388 282044431
    0x2240402040e03070303050609060307050a05150c06070207051e1c06240806130c03030806010207030f05030304061113030f1707050d0210020a1e02070b030c0406090e0906 75
    0x14003404100b0001e03000da0b6102c03003032880c00034050a8103840302446003102030041f4601749008510102210001801c3ca16620b24002c1404001c40d49004070b000041c206000d001540d00051001b075201e01c2c0241d0281811038103100400c058807501e45458007140e000c401201078551920701080204c1d200c44a44005000d8142ca040c00180a40c42c08a82d022161100c80001040d4914866800c0d20102e505a4555580b00f00300e00052045003107010301910960181040031900442c07040e038004070184192100140c507510750000701184480102d80c01d0780000100418000701344640c1d00c007008100400c034540003501043c9900304290f804090582e41010014904011940e00c40281c41d00301d16090941303405840c20301584030610b0009140c058086c18003d0700070840380c0e10031103d802c4056101d04d02d12107110741c2101608810317500018254480d603000842d000c548000614890880c00c411355550300e0030200e0013040c41c40303154000c102400864042c402c601c0c1004c500158080c2d00351058090700a142c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 282046888 1250 282045638 282045641
    0xd0b0301091e14030705030912120f041e1410050904090c030209090102030f0708040f05070b0a0306140d1205041e060305060d030f051c0203010b0a09060224040204 72
    0x15400204481500000c0100030b01c0903000e2406454092601d810072102c20a40d280c1c0c69200301240100284c004000ca260b503840c00c143c44001107940002200d0070711054021054495129003a4510710715004501004030340e4140d0003180700c0191900d00361010b503140c190010400c0542c0784405100f031030b0134641c804180e8415000c0c1c0e040343c00e00820601407c080e80c01c100c2d514058600040c0c1c095840c43d00010390b800e01c14001c0364081e1090103103100c41542c0c0c40c80100c03007a0300c01800c116034401041c82c0c43d1022460070840140a840c0d04034641d95540070312140501100d400e03074031000600420074081c0010341c1d203e2400440a541048500151840d0715408403002c1c0f04541000341c0303414903034078500740d2188000c06600540b03c40b80c404108680303038141089048105a18001c000555000100c0c050074480c002902c000204e074003c070030641c00e0000c80e0500f03a0b0401d800c4940720141c080f0b240c01c902a44000300400610190000d00191240381c040740d4401046c00c2c440708464407119000c1411034035075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 282048138 1250 282046888 282046901
    0xc0c031103130906031214070b06120109140c0f0607110402090a0f050109170307120e0a080f060c0c0601090c09030b0a05060406140f0904050109020907111002040b0d0b0301 76
    0x8601546240e00e404100f801040240015144004000415051140252040c864001356140480c0c00e0116603624020040401403a8a410032400801c000c1508000d02a203d080c0784600c400e03c45600f10350081602d030072850000c50784222450114003401e41c43d003104131410036411003c02915082d5102c08a0041e22544010641040e1600d6001402c99503104c05801640c409036a0000c1e011b590f0b4890b016090078442007807003160400c000d44400a001d10080818200d09400c00c0e034070103200754000845011a991090071590020300c44000d500d5000d101c116480b0002c1c501c40c60a0086030b101c0903940755014003601d1000c40c2da80c0384e5061000e0091003524000c680c4010100700310300e8160071400250400340d83c198055814880301044181d6402c0804440d040050950a90602c4980c2009a141005841034800c1e543c0c6e0724071400276845040380f451040c01a51100e6001e86013480c80700340f070031545a42d6004103920500c82070107014031244c11616000c1d81d040011801032000c000207401882c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 282049388 1250 282048138 282048157
    0xe0312040608010312030b0a0501050a021519180b040f030210060303112109042a110d0302040f0302010e010215071e080c070602030c070606080c0f040c0c031103 71
    0x1040c0024180d0380020310074160303841601a001807091030750058041d90203210005a00001344038081c4150f52188015242031500740c8102d0342c030003070322101c00c80c07046005940d40700380c0c58a504000750120100b40524000c8208a000030702d03218659484140c50540080c03c02040d0046490301d8030181407080004900d0321583c0c1000b004165540e1a0140404000b402030801c18000c40045030441c4403211203420300040134000e03003031410704040e007004020001090b0b4801c0080304130f11544150410070b080550b810310292a4889060059040c0524159800401808241c01001300340070311144801544200d0382c4c20b01f0004003021643d00140d0800300004a41041c20307180b0350400a284e0b81c01110b45440007d17a1000c6036091000800c1194440c10071070b8420b440003410040c4030002a00d50b4011684521080161340c06c02039240da03070006031025584400010340c0310020301c03071b1145004048407107059000c890811000066000c0038206604070340d0060309000d11041285210700c070038411a400c0c041e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 282050638 1250 282049388 282049423
    0x80408010c1206080303190c1103070b0601031104270e0d02160b040807051c08030a06030b01170a060b0105160c0f15020a08180904060504061a0607030e03 68
    0x200725400c01841c10046004008086007800c0000840320303404002c0300c3c01440e45102c0e0000b091480300340100500b400c0d111203010800d50200c00b011811041c000740c83d04e54071032084c020032424103100040c10b8591080d0407154000d0100400c00070140e0880014021000030321050980a109848a500921143c0b01200c45405400300400e1925404101090407840c22001c54213001c0d1104031301103450045000d690712540c04070000340400d2a010004001e441208000407216a03815603803281c0c03a030001e0f940fa9003065245c030401e01c10003c40008040c05084080da10f00280503c0000b86507139101c1098014141ca640c0e06101c8625908c2441101c00c200340c10840c54414092600e0096103110252090f000587d20303400021860850130700b41400402100d6000700070340b19854940c032000e54802000102c141818034060b407082c3e21b039034080c0c40c032071806018000b8135482c2c54140101621010f00c840b085c0010213084021403a558101039440031601031402d04042d21840700424544940114500c0900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 282051888 1250 282050638 282050651
    0x1909051f0207050f30040b0c0f06092b0306080708070918030e060309010905011407020d020c01050301061b0c08010b0109080d050906030c091917060103020f060708040801 75
    0x221aa6001040b0242c4103100700d40010000702c01103501c030744010440c01e030079074a6206480d00360a000500449414000c240042c5810703901d00c200b8510f68403210320701c1c1c1540c020354101c464418052008039440a9540301510145040021114405020030310100c84d8100e08151a070881d480780d400b55010381110303011241415200c42465a4642d618801d02c0c443c0307030401020685080388000801c16a40e4540c54140d1440e149404010041d040100140e000d996a82030b0000400d01c00d0044081130a826800c1c60414204910004d00380742542600000359400b880716140183d80c04401c0380d0442e4042e180076034100610301105400c11511403006030841080d11000f1030842e0040d481028004400d8848050a0350307100e000f03a40f030b4003400c50070401254041c8510b400900300036000b9684004070580c0d2900c1c108096001a1041052902e0304403540c6603507001340030100c0900300f0304502a450b00000c001a624582c0010030f40c1f003855007039502480012400c1c2d000c02c0703480804d03039010303110a800a01c40e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 282053138 1250 282051888 282051943
    0x70f122408010b06090904020409021909060f05011d0f0a0b0f03060405060d0b04081b060f09070f0e04080703030b0303071a0a0221040201090510030e1203190905 71
    0x325030440c003070854075528048072901149800302c1100c01d62100600f12034000d0755941c0070040209503289007660040c2e031f403c468000c8031000c5068a00070b000e0028000608500f0130740da6420303018880d00414180030801c10300e00d8440c1e40c000031a2040220842d05041513043c3d03100819000703812039202c1c105480d000f080501c41441c0d9903002d188103078800d80d8100b046580304e6041100d00d01000d100542516010320208000c40c2c1c030302008011040400d010401e5141d0400b0059281890440e085c90f0400360355000d1141680c402d005078801851500800c100030b5003007203d048400ca20290008100070300001c0e155007014020f8011940744400282929229440d604040400c421f0600c031404019007040000341c1e90318514400d0703502d0b07070385880900c100f0b518114802d111b030864003034010f0f81880744405000501e603582001040c01c503002c035500842c4008441c40e8140c54040c801c0360301d010a40b414001c02040040058100310111080e6802280000e102d0034010300f021401c0c09000c20b062a407110683c0c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 282054388 1250 282053138 282053201
    0x30f18010e0105180a0c0b0a0c020a0602390108040212010204120606090507050f0d0b090c0a020f0a03020a20061602121615020c0d060e0f06070f12 65
    0x450b0300f070404013440c1010b201464548a40740e826000301001c6060800f88280859007000d00504e054900303101107520026000203c8203525640224010780c0f011503140c50356a28089500861058101504001241d043d02070410490b0625201d04021917140054199a504405c000200603003a000b15035403902e4202d05946540d4008003170300c00c0c46c10800c00003038000062007214415945035842070b05140003803144440361340c851031010301d515071608122082c80d59542c414a004e03140b40c00360540c0d00c0c84141c40c007a040488405400303415421580407900420b4002c07a588a4481d4450404800504280074555044514190b02504043c000c070f0540c01000d03410003003625440c0202c540c3e03040e08000c88051543d502e60480002011101c207a410070550803580350003640009540152032a4100f0b03080412105420110181d0340c240d280c2d0300d9002050f0040c0a101000302c4124050001854160740207011500c15038040410030150600c01d80c85001c1c00d50040c802d08070000002045443c04a00134207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 282055638 1250 282054388 282054391
    0x5090309121006060305070f08090d1d040507090f08030909040b0709080109050d09140f01141e0910052811030c070e0121290406020c061605030f18010e0105 69
    0x200421200d41c00010000d01034010301b480b64615200400c0bc1c0c0c0c1e510b4908840b818016801006164803011502240350340703d00800c2d01c540c5e250b96981e000d075490030710919155045a401070011380c00800c041d440755200c21070201c1d80590018005800d46e00d921308203ca12402c9944142041d52a0440c2c0e24200640403c00d40b000c1050760b40c54413001c03500e4515000340c1c90300400360340c0ea004050701e01c180e030746500941d14801a07590300b103881ea080c120100755081c0c04103803140f00c1480b10100003c0d046680d107001002115503a480f03142042c105003002c0035803052890440c40314a01007104840d40d50196200b0441400c280c03482c01c082e03d40320b0200000c42c3d40d46061600484010b000101c0001c47d03240d80e00340303d501001c8482c030780d104200030301303034880c2503110407804206a40008559641001d19403060344940c05148074460044c1e442203181c041500b00b02c005400c01b800c6544c49000e1805541d444000e903a040200c4520726071803074540d862950041a074000200d00d046d4200a01d2081101d810340c400c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 282056888 1250 282055638 282055651
    0x6090d02030a060b011d01170709180b03071401050301030f0c03081204060b030c1507060605060c0d0206070507020a090c030f110703090506120403140408030d0905010f05090309121006060305 84
    0x1b0b8140b2400100352031900580c880c801e00280d41041c1e04902c41000e2050650000f1036402e102e640980c85500201d880f80094074500907003515040e14116508003004a00020116031182e907060301206000207015100620015040603420b140d01010300032480380007402558000001641ca0900454080c4091800c03281a03c04919100d0850f0341400c002c551110ba0030401490700b141650b190300c42101d10380140c441500c590b981c034440400c0c030340c80302c800812020003241d00a00c031b5070480180007454042e0041c00c01342040303c103003c01130051315a108100141c07080c1000100c3c401481440807001481e01400030031a2a00304804650032050420080c0303800f500941e542113883d0348550500070b6601c10b210b905c100f00e400c180c00040100784124141112003a80f03000c0c0074034050b0744203503582c07564126030b0342e07801d440f41d85451042c10004248901c942980ca180e005004500d4110300054403030160190381400f41c01580c407480c55001080c4050300c05542601c208102c01600c3d40802001080125006e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 282058138 1250 282056888 282056897
    0x1c030b0315190509030306041503050607050405240937090c0207080c010f0c08070c090c0e03120f0d06231503041e0f061401050a120206090d02030a060b01 68
    0x110201d91815004052003081604011486c544901041c800241002c403641306541100a402200040007808a5400b4415964427551118240f408115403055151000c800b240720290300c1b406c0405010041e00c200312000c862001046000580c0000701424151440c00b0380580c180c004004d800ca030018000903a1203020341003003203880100040c1d0341c400c11070041d91819402250010150f40c8540203449101c030403450b113450708002d907944002140c0c000d071400310344610200c88107000003206071044140503100380c80d00482d001d41401c08651a107891244c52020a0301c002032110b0b0f50900a011128440c084150400c02d4030742e21030318549a2841c0c4500001c00002001500595247c0070b80c401d64070b4111a602103280d520f031039407208140c214107120900b0420385181243d0201c1c1d5811402084030780506004903c4011880004582201c140c01140c4a400030345c900780403c11038001c014901c07581c180e035030303903502d0a522000686a025001c4001e52500c05d00307402004204160300306101200c82a2030b07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 282059388 1250 282058138 282058171
    0x206070f030915050c0c0f0c011209030e12070f09150518010b0a020a06020c1c0212040b1c020f0c0c01030501031a0414032109010c021c030b0315 64
    0x1c50580b201000007a1141c1250b405400c00280d255025542060880d8005864038071240c03030250610002d0b03180344100d90009034900b086560840101007000e06900c40c2005419802da0b000740c24036054012081c005c81002e003005503400d40810003180174111041c0203410043c0c0e20902d0034003514808070010381c0b01c2c011f21400152824900031611041182415140c00c0d6820200702031416003007110300c4800c5104214400303001c114940b0040c080c0c094040054802d9000f198541d00c0b04030f1140c400103045512007203811125034203480c280c07016a407901e46829507501d2070911f5802c080f803070910039503080c40c400140241c444070094010b16641c0300c1c1c1c400361004c02003d90300540440f07001344806010703031017070440e1310342142d4680c82ca982e032240c462040280d0920030300e1401c40c43c5800c84098a554400c2036019403600c1c80405200c50340c007003114402880140e400710b4009448501c44040343c1181c0100e00c1184211900070b4200f0040d421015085031071906185014013601c00f4160f5044401444068 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 282060638 1250 282059388 282059417
    0x915041103060f1003270204051b0d090302010b121f020306101202130906061403040503040314100c0810082b0e0303031e06030607080705070819020607 67
    0x181507902c2814020141d0b889070f082c0e0710a109011400d80d00550406690f510790001544540c081021300d0b400d03046011110440500c144801c4880282c55461880340f07680341618500c00c100200d5028054015022540d5045450141c0c05800705049a07a40064010303d00b014802000400c807400209083c680c807a02c200b04d141314401c80c1b005640d004d41001462440c00081c40c0035120070b80305840568001407801410400c048481080d0307070005081944c445808000c2c01d9030000b886240130540c28001c0d0300d18105555550f40d284034501c40103007503500c2010704043d00d0000740058507841c804074409100b4139076280c0f0003c1c01004212541422021401c00100756518001001c2850035003801946108000e5040d071510000062046a070400070342c100b13500840e84003400658054188001001c20303205000e40308011804004140328080e42c8204100710f0010b40c0700104a130824441e00709180c1c1c0341181e0603d03088903c1882c800c0705208400081100c0401d6000440d54800c00703442d43c44807801c603c2807 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 282061888 1250 282060638 282060671
    0x1b1d0f240a020d08070f0c03120e0c030106050103020a05030103110105070203100e1b2d0a18140903180102330105030615010509030309040c02031c06060c030c050705091504 76
    0x19180d1000043c85443c00c001c450f801038003441003481c080d0811034a81843c48103e001614031622b250002600090754501d4541424000c04020b4039013400e0a500380035041b03000510303501051002618400501c4104800d17640500b08440c00c140c0c0107000c2e01c6844e504a4030203006062401c0134040188034480100c840b0204644540a0395603000f440b0400d243c01000d524288000d02e050b8003940080d01c58032441c402e40d00c12807003000621075082810301000ea41183c0d4000c40310604403803420b01403c6000c10060341c0000c01226a0610040c000c0c800011840300100c0c601072422164410041c0010202908014009c40401c02c4206200d03144001c0c0c1e803603100789500c0b00019114a503400a100701d86502030b6005c0c2015000012014040301c2c1000c10100000e003e6a41d201014070251300b00143c1c0c40d800003004511110345044c203080c01d003d540c4ca00300c2c0060083c407c1a2018041240c03030303409202004001e000d07001c000c02008040c2015802c1034a0300c000c00050400344513102e94a0600300380e8505020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 282063138 1250 282061888 282061891
    0x60622140f0f0c0703050a080405071715010803030114060a05040f17060603010c020601050103090203030702090a0b0901080c0a060f1b030f181d13050708011b1d0f240a020d08 77
    0x36640f45410031580500c00c8e90481000351080301d56000d05c4c0c1d004180c201924000301003403028000200704907100b00800303103035180042e0040c4045810800c014031480c5207a5050b504000c400b6160142c1e500200c1c98100c1e401c7c0603c4e0172030b054584d1180030002e090f182010080d99000320201c20354440c0c1d20380000b010f08840d024044040540c002e000100070a60090780062903050000c0c090b00e140a5590340003542110b421a0b041d140c09075070b18201c07581410071010701405000c682c0020300d40c40b034500000444075412071161500b08480382040d022041e00c07907400c038450b8150021a6020b040020315025114400c2c0103c140c0000d460000603019503008603c41a007100c105a030a200e00901d5006c0d01107404200400c0944c0c1507503220607405c0064400c01601009002003800090b10002021030b00d8006610180500c04202e201c418032902d144041e0681305a2580455403076107501d0100001c641c8480d070300c1e140884d190002c0da07051030302c840c02c03600180a440c406500f07032445072580740e0040e5200c000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 282064388 1250 282063138 282063143
    0x4030c08040b03280c0c150e0f010606171306051b211f0b09010c0f030804150e0309040914010603030c02040b03030f0403030c1e030203070b0702060622140f0f0c07 72
    0xc0300c076446404187c8031217142021045a000200300b0b001c02a050301e240040b4034095007030603035541d9020070403994815134211842c12507410003005400d000011000c540d101940c0500107642d24004a0400051070b4686581c0283c4408859101e4450b00304020010300a88103049800000000290f2210000c540c3c070307000d5001041030102114100582006203401c00c41f222810700103010f280b1000303e25010311100c500d600c030341e5a0300d0741c0d441c003803038043c942c5d080345040ca014040c10042c0e1203840e000044156120300c08151000100f202c10f9042800311103ca90000e0605c4c0d52038404003006059202c462a090303240240e5007808000e01000c28140e480c81801d41d00040c180c003d12050001034417560312802c07070300e000d1a000c7c1070300581202c070601c8000c81c10f1012005070340001001002c003c5042c0c00150722484a0018117528508840401c2c1200c90402c030521615007945012a07456056034444044041c009104407a40d290004c0780c0d030701c04041680c1c000d4455211000191aa82c6064100d400c0f455 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 282065638 1250 282064388 282064397
    0x10e011203050c1005010e01091a0a050f01022a0f03030a0915050d020d090302010b0108071b03031d0705120633030109150b04050402060304030c08040b03280c 70
    0x10181d440c01c0768550407001400c4550f008a500b01d140041a0703000304c5010f8044032012192651500c44c5401c00c541544c1d550440d0300d51400c101054a80d0341081900407140305450404460f151403004030306088000071342041d603108900048080c4c3c04460b00348044e40c0c4050b074850070b1081d0700004040c3e990207070500240c00038405120030700050f6000301a0200c4032030305040550514591403001000c0ea044004042405960385403404140b5030f09026044100200b03080c040c1060600a100414144803182101c8880080403881405c05111358040c01690781c2c510385a1105109a2200070345603d45881031038441d40c1e0f000780c091503200010038545d00400365880c2c0307101902d90145000c04d1107035021003c2070711850350a4105080361800c6c00740c11100c1e4401d40324003460002c42c14844003294845144180a81e1034182004010b848003011650130a07014107100701c1400d61458460840e108a40058881003400700500040424181440c00d0907101c1c41068440381d6144902002241c000301d0344e03c2d0005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 282066888 1250 282065638 282065669
    0x50f01110a1409150c1603030206061509090705032e140a080601050108040f02040c0e09090102040509010504020f091507060c1103031915120c0503241f12050105010e01 74
    0xc1d8410380003840c03505c0141050320110350a580c0c2483c42d07000303290300a07030143e000302c0100080c2c1d10f02808840e1038002c440d4141d81c1440301500100351002c6000b841032042c0718001010a011640d00c01420014900c2e16a8202c0b40038805450070300414400c2c801c1d90203401200c01c2203501e40c41d001f95030b4010758001c7d400508903070380781000440e100d20007d030040e035200e8400003c140160311a40268801c0c0d0b100d0f61144480e00d50290140040c11070000e2109845900c103100a10096661040c07542c1181c3c42160b01680359041c5213507108103841010b09803a80b0103184074040d030290020350007410419000b000100251100300005684c2030070320545c880c07101d030010030004200c42e00902811a02c0c2040140020b4141d00b80461503030b101c003090300314004a2038810504420031400080d0100580003c2d00038180030403004d14031141c0f9144042c4403a042440c5a4001160300c0c4101000600f018003c1120f0040160b07a0444c0424114000340c2c00e9829508050010819442081304181259480b50061410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 282068138 1250 282066888 282066919
    0x9090f060c0504030b280b060a0c1103010c200601240311030a0e250605031806011401110a0302030a1427011206031509050f01110a1409 60
    0x4260065584007805000d01c004404603844c2c0107654840c90329911305106c030a00c8031401400906030701c010200da09003004100c51080d00c0300000c0d1072918261382044c0741610344501c0c00848140e202c451968140d071030030807900d11071030340030058010783c001203e4222500c40d40e0080c50340c5c548409000b182850980031508003800408101606464501864009171020f8010b8041d82580d0040c0c0d440314403035444007101400c2c0e00040c02145014214a0140120700055160b201e05681851160b101800004000509040e1010202003110401c0b54207640041d03844412228252107201042400904504d10688106200003100c90340c558240c1c00943c103010000c41700301e54490404601d03007080b500501105101c0d44101c0961040c400528400c100a4800d01000400d040000c4149214060074003800b080460f044214441159207207410104140466042c05850880c2d164034140043d071810146000a0b01c4810242c405050395903124103614101c0c00c3c2420f038900a02c01e10b1035001940041d01c212 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 282069388 1250 282068138 282068141
    0x6010e01120809210706020c21060609101a0301061b0309140301090f080a170f060f12060703050907050402091c030c05030a11070609080a020d08041a1309090f06 71
    0x1c0860384d4551102040d140c400000c4d0901c000d03503100e10f003d81d022204071111850803030301300300e00e03e06481d45800705c09046c2c000b0030b5580c042c00b604181c05030034198003207803490812607011000b0703180000000182c00340c90300312444a0f5009204940010ba41a4100a5400746400b001c0d400c5a800d55038000800381850200c43c5890254103241d5415903075080c41a0000b84140c00d40c3c40c3c128003d413182601c8100200c000b41800e9800360b0410b40c04580c20007002103840e00440000e4006034140e4809010b4143c075000300d01c0f0881404600c0c5214450102004100d82d80750700014407a102c0002aa062940d807002400103902a56a6640d4000c5864000c024502c002034005013070503002e032134911240c242c00d880f8141581d100c1c0341c080c3e0000d4070b80001c0b10450441002203200030300031444c10031407039890328240d03944405000400911481a003085030b0f00340b1000505550152528092450000304000e0782e03003803241c0c040841c0d8900207407907507400504e0102e244610074125821100610b40b550302c03076a230a0b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 282070638 1250 282069388 282069409
    0xc03030b0604050406120203122a031b031b01060b0d09050304050d03080412170a090c0f080a151a0607150504060e16060f0f0c050f06010e01120809 65
    0x150003007014003000410741d456005140003401000d00303a003010702090040c0350a10209117070070640e0040c00c00c403c0c1c40280e4a6207001c0045039040f0303040500e0030140c0c1d2440b819071244043c0d500221061130462181414084000c20080411034074115a4030440481c0c80d091795114071407420b107418107201070300f01242c568110300d50503885101900c1c41d0070f44440c00506072080c081410b80014110324100000c009466101c0c2c80c032002e0500740384c0720188401247c9903407000000d1613414565140d03071001d400c000c5c4070701a1a01814035020303440009a101c04045665506160f001d4540004251038604089118803d1000629410b21000708090742c078070a200b102d0744400c504907a4904c0f0f00090718003002051280300e001e18419503001c10017074030040d401d9207000408404415501d00b0204108141342e080381e0312039541d807200c1c14902d00020200d503080d45d461444c07150141c02c6014009a407101c52a0209029050f2491074001c0d040c0741e6210850007048050301d15000b040801d0400282c02d140c0f51492005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 282071888 1250 282070638 282070661
    0x62601090b0c090a1a0403140303040206030c0a0e0a060816030203060306060411160605100b0c0607080a0e0f0708061602030a0e060715090b0108010b0f0d0317070513060f0c0303 78
    0x4c0c4c0ea25a82c070b00e60101203013090010031544c4840401c09004129103a01c94810420705900103601710b04003900003407141d10000d0281000c4401c00a908040749000d8003007044010740c010004500c0c1c9544080103440c10740111040a4100d10701c4000b546114000c1c4280d07405036102500801c1c45658810500000305028407c1d103945d560148960ad1f00e40f0800503424142c0c503c158004201c6082820850b40305880070380119031135000c20b100100340b1105c00a40039a02c071450b440d003030165440d1100402c004011880e1b8030400c900030200010601c1400003210b10803100b403241221213958541005040c1411403000c120b00581041001000d4030303200b21070103000d11070300809a41c0b40081907540d6408130307811540e1140750980c80d0b1840b0b405000402d1500382c014840100207101c51500a00010006036407400038070720a052400c454800d2604c950400c0000300d04100c01c0b440305050a038805015038100c280c8200c0420b001210203e8a41d204800c001149551912500b4081d07495603401c0e4082c0c69800c022 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 282073138 1250 282071888 282071899
    0x6080609280c0f0e010e210d020319090b040b36030706032003090708010c020a29010b03060f06041413060e061e04062601090b0c09 58
    0x44070081142003040c124000a80d400080c94110060020b441850074030340034000e00c00003062101c1e66076000030551840c001d040315460b0048500800040f0300b0b403280140740000d441610300607000a50008003c2140c0f4508048407084001a500110350070251400740074440c0384180030070010140c0c0000544808800f02c0044c4920004018482c9141c8860f9051403c071081280840c4946007030500c0003d01410884c40c0601210800c40d81501c1e44042206241e584004000001841e07000148444009483c00d80c00a0088c801c04c203800956800c854070050300e80c1d008518254840400c10b003110041d0380b40b9412240b090b41e1070000e18245680004005030382042060f03494010319919200104060040d028941040d10a920248860b1403210341180340c9240c9800d40034403007510481c6406520190860b000e01002a04030361310000207880e010481d070842e007400004181128040680c00500f0511100c224110805c0c031000d50a903014024050f00342c3d21100d0101e075020300c2950003441c2d2103002402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 282074388 1250 282073138 282073171
    0x2010207020405070c0308091606110f030403060501030b100e04020103050720030406030b09041511130b0304122f03120a050906070504060f260901050105040e0706080609 75
    0x402d0030346500301c6250001458011801c402c058105c80000e0b00701c000300c0c00602c4216241f0441d0f08145d0118001d0000b0310040c241240701102e000c100b440f01d001151001e0b80e841c0c1d990f074030745840603100a010480316004030b50002800315407488651011200c0041c03c0018544031a0010742c010200074002d0720410031402c4c0c10300e00302104e0142000c129450394004658843c54508010110395404c000e0900c00c0d100e900c00c0c0004100d003240050981358128100040d0701a003880108a10f00c40d40000c41a20000c0304000940000c0c4034000d036106900a03003031100302c0302d0b6144046618103500040c040c404881050342c1404411602c440e401d41844010480b45030603446400740d0184c4404032403c0e56140e072100200320340320009001c80b80d082109030611600303241c105000031300120352090202040240e100088550a4546070030340b5030342da99400180c200c5080c0501c4c000e000e04001d015080c000c1c2d041541503101c5400024501e03045401c1595292440c0d200d9604000d84404040c1288500f00c1c50080c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 282075638 1250 282074388 282074393
    0x204080d08060109080a05030316032004050405010b040b030a090c05060c030433030b0d02040c0804021008060f040f090501062d18231f050d0507060f02010207 70
    0x155aa4034210340300c00d0070500d464000100091001e4018036910b8200d2841e8a00281d8000142e9800c51042c2c10b0701ca400b0b01444c03504034018400f00400196441c41c0d070304000c1c2c89451202c014016a08261014001607803151203c0c44113119074441c00ea0940300820008400740d00c0b56000c550524455090074024070303502c5c0e0020300213800040c3e16100640001800304400c0712403104201d0140d85548080502010a9401c180d00004c0c13215041c082c180c4824500b619562002005400e01e54002c1c0200a044082000109501c108850803405000e100007004001c0d80120b11041c46000300034a0326040c04165028070000d0507020704081261a286c2c400b050006d0800c3c01044040c00c061514a820f102070042c1c81c40f1480c000b000c040c5141964100300b400f031480e0b410029200410540808186c81065981c0071000814420f6001e500e000d101b010f01c40ea400b402c440700301e0b1000b4112070456042da250700402c102040075500c02003440e881154100f1546024840071006011280001800c08882d074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 282076888 1250 282075638 282075643
    0x3061515120608070608070503090a0503271207092f09090a020f090906030a020d1b080102040503060609041a0c1b0d090b090607080408030703030b120d0c06020408 72
    0x380410408030301da4040e00c000c1801140b08020043c0705800082c00101d241c0302026001500c00f500d540104980040011801c041c10420704041c0c981c030204a230b0f1381d81c2142e03400ca800d40309980c01214104007040c220104070702e40000d11000600641001c1c01d03185182c009580014400280400300d0a41c1c102241c0021002c004444102c0311400140b803a510340c07100c0208a008200208480b81091040c40b101031300401e220b007034170040e0301c0a03100600c1588580300020310f002581d8034001e52140c4600d4010081280012010301603401e18403c0c1d00f810f40d1612000390a0740038900403160141d116900041c00c910340790b6005900305015070782d039090032018000701c14114102100c003001e038043d001983d42c200848005818500381c013184050070704d02e5022400103100143d10300c903450100344042810304d410f940c0c0b18201c1710603503400a9800d035510780e91200d1179125000301c0019004627140450002c1c1c0d0b4144013032040c41c1c5207490005028410a152000e494200040e07001b912255406e000104500008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 282078138 1250 282076888 282076919
    0x13080709060503070509040c050609011e03090b180a06020d060b040308091804051e03090616050c0301050412080a1116020f060408030a0522060906031113030615 71
    0xa040007141080c100b00c1894608441c41d44824003a4103a41c0c100b02c086070700840090150307a1304030b40c066951044100100c1b500e25000070002c503036849031054240382c150964407964001e032003404203420580c0d4031108940c1c6030075a1003600c140c41e004038401e840012803603402070003a000390100015265455040524072070700f00f500125040040000c0800842c5084c1510705e1581c440708076508130314030740341c0e0368140c4400010040813031824025102e0031000100b0300070344907640f00241c00350340c90b030300100b45c0d0340309101c3d15800568040c001d0b54483c102c9801c060140510a076040003401c03c00c200031070011500301720010070740e03515290f82d0080144145060802000f000000041d49a031000c03290041060908144203014031420041004000791007022041c4c0b030b042801403c24039181c102c1c010300342d280c1004c5003414200d45510082d02040c11600241c808003603078800d0b5000c101c2c805c58107802d10340c0e41c8140e062488590461070b04c01c200080310f6130000d84407000d03804004051142e4542030401c65540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 282079388 1250 282078138 282078149
    0x307020d020f010b060a0c2a05040b040902032e050412180f180e0607050c0d050c0703021201021c0204080f03070b010501031d06040303020d0c03051b130807 69
    0x481000c14441a81c1000400d00c0400070900030440041c88900085152042c614041c0500c810304454005020b40c0142d0185001200b00c140e24001d020030b217603056030f581c840c042c03144100e03d13181c80c243e01c1c2c1c02c05200300010351f80c0c090010081f1410310001c0176803810400001e508080505030381018480c0244c0101030003144225006100f4100001c1c0140c00c22008107280003d080e018a42000400342c00210101140c108425044c42803901e80c441d0b0014000b402001411407103800140580f40358080700901403201140162a5000034810046455104940c4180311592115009101510300051980100c02c151000149006520508a00030007298400c8498480c0c3c00f0604100040e0140f103007101160000000d1403030415541c0d99180c2008060080a0400d5034400d81b41c05c0c1100100b05840308001541c0844106261510300200a0741c04440034406080c01d21644100b003d00078000c090003440351340b04d4048042c201103040841a005110b4041c2d06a04442002488000500c9503602418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 282080638 1250 282079388 282079393
    0x1170f120904050f100605030621070305010501051e060d0e01090b010f0609081005040302030705031201050f0a06021506270f0f010b03160e0a0e0f010602011a09040215030702 77
    0x100303501c01c100c00c943c0010084019402c5034810002c00880011a4000b075a03518101203403a0344444002c11840809955100031015150528101d8200d0020309041141d215000071301850303880303401780112491006c1c440403e0010000759045146043c00107044000f4440d800003c074403652182c0c040c20f50710000d0b01940c0c000000e0303005219000001d00140050441c07802d00c080c50510b4440000e41d07405404901c51240391b40d4074045010035100348100d400c1c1c02e80240c00c132500d488604080c0c40c2401802c0c03181e148180c0e0680d070450841d051580c4100101c0300c113500508608050303181028040e0701c008002c0b1354000c1074814060703090407010030720746981503148a501e4020701c1d25282e0b218001802810300c10001c04c00400400c1286405022640d1080400c2d11011400070304810550307020486a000950119418801142940b501c20403184644400300281140d40d90f6448240c2c00c803051a14040180c03c1c0c00c1040d42c405080080d0701b250046c1c4094080c2c0342c090004ce1259110b40c000380c3d145401078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 282081888 1250 282080638 282080647
    0x6050c0c0a1401030c0e030d08100b07030206010e06011b0206030a060e0a02041d060a05131515031a10050708120702010212090d050a0f020c120c042301170f12 70
    0xe584c10300c43c5800f409180e04041900c03801d182c0000743d40d40100700d08501001071910008038141c401056410050003006103032900d488007894003a45688003400b640c04e43d0040c20b400145198414a1070842d120038948207103c40e88c60079024800303035601c028103c2d8980e82e255000000d1845085c02c11038410f491483d40142c83d941405082d4095100e100b0010400c9a4102c0a02ca040d80e0340c0e01d15041240d400305e0360148606000e020000103007107060a00004007090100c0001d104080c2c1c3c2c1c104d07a0721491560304000442e0501c180001d0b20b80c58076006500030324071414150089025000034040d96002d000101c0c02c040001c940700c40c000d5411290200141d4001c5100740070284601c150300e401088090145c40070035003200006181e40118101c200402140b1041c82107030030b0013480b21940344c4002806126146074804e40241c0d4404e0780e0740040e40078502d800380c5050840345048000d500c5202040c0110304591070070048060668284841503401c0c0a03603003d19500c186c04000e2405445424581e00d5200c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 282083138 1250 282081888 282081929
    0x80118230601030f0204080304050607030c0606080c150304150e010b09041a0c0a050702211b1905030303040f02010212030a0543211505030c03030406050c0c0a 70
    0x9941c9400c0c06041138900500042c0324240d0040181d07400c1d40c00642cae10b03a1f00d494160034121b40700803024402900c1d4525150b03002c2014500400d001a0a28043e0344608619000503000e500c03502c400c0750042c0c0b44003160103014400c0d51554206101e0100c4200000c910343c050140000d91400068808858641102d064036000041c0c100402d40c6c0410001c068905010301040e015080344212140288198000c0b8580701521100390310490386540b50108070780c51030b0b100c5401c88440924203981a881000344580d420001001244200155800030300914110b4449a40700f8050082100d403c13070550245e404621000c0724182c2c040d51040940b00340201d06c0d130030300940d4008520b07066092180c07069081002c05101c4c040d0b45442688049903203921107001315103000b0450345680482d54469890740745c801101c2a0ba4504d8000b541d03409495038030103031403542c0d4104041c0c1e121110760714260182c02c28042040054050303c007610a0034480c3c02034402c1459414000352410354a50081c021080c615185181d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 282084388 1250 282083138 282083141
    0x2041707080304030c030602030601050415050307020c0301051003030e06070b07120e010c050f03090a050d0513050a03020d021210020d0e010c0e0a180605030307060507080702030403020108011823060103 89
    0x10907030340e070286142c24150348030314264420b280005800769800002082d103517407150049400034285031202c02c00b0720440550041955100b500c4007401803041c0414005545010700c202030246a510305108070302803540d03400b81c4100c51003c07284d0fa40f05a00740640c40114540089941c4034442541c1c409099900d404001d03000c64802c0c4030a2007030b40c1c1c50301710418a6142c0200440da00742c0c043d05442e503120341d940030030381f4075164200b140200789008800710f0402c1c0b690048013034140c0d210b8115004140c1c030b885a050003030704509440042e5109031440c20711070150518641250728542d051058500000f05207810342c040c0d0340541170320b40d00c00d60381d403403508070084080c03203102c880942030700e130141800f4082170000710030004130b000b16032001c0d171003101c00102c0b00450341c0580d00030030003e41900d40790b80e40c50400340000c00c0201e44590104000070001000070744040b045030b09580c1e058541100603402c201020b42c2011910000c1c4403000d941b489101c20780e05081411130082484203110200c2c0b454031500040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 282085638 1250 282084388 282084403
    0x1110c0a1203061406220602011a041e0b1c0b01030209070e0901150e030105040c080c09090d050306041d0109060615090b030a11030c0903070e043201020417 69
    0x100b01890070700306121030b1440c00311076116480d088641c00d4444006141c0d540c0c20301400b034249643e83e407946100103210364040d013140c042054500c1380401c0c100c0c110010700003a41c01e40405070405a0310f80c90074000c40241a803084d072800704040d066aa0350f020001340051021482e0600755901c500c2c244c010002c500c1c000f02c0c442d506c9412807400740742006000c03020a9503031006020b4103044003c90b40e07140d01028460040001c0d84070f4010020300135810141000c150350315081c003401c0740e10700402042c0e481500300740c1c074254042d0f000a030040840c84c1c0346601c11141d542010780020392058482c1000509051300c1c8681d400301000342c000000300218549400f1086a69950011502094405d60141b2644e00b141045084884d081e014607030300d81e01d03e9001d00080c922180c2480324003401100f8041d003880e1080140c1401201941110803480d00c80c1d0401c40c651008440c010700d002c1100d400c40c0c21100c0b29188050391000784080c462003084140c4070490a9030003d411412120107450b04200c0c100000300240c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 282086888 1250 282085638 282085673
    0x403050a030203031f051f1e08160804050a0f020616030f030c020d020706110c040e0d0e03060103081c0603171201050d0f20130218010e09130501110c0a 67
    0x245e0180d03d4603010030580c0b07084050b0a1028811000b00d1798181c2c3c01071030303114401d000320312180c00801c5007101d0203441110706a444d1000080500320b100000d50041c140ca602454002000305030000103503a490308010203802089800081c18069000410851a0b6004109100e500c892510003c2510000e00705c0d0070100060085500000e00c0104c416004074030725040d24901d280842c181e01c200c4444518140d40e05040a40181c80c10000489001340840e0a8420380700381d954565458000004255584d0340a01000d00b103c0010064120340091200c10a10b05800401000c00d0580d039a4585049042c50366904c0040c07604009496124204180041400740c40102c445110840903901e071060800303a440c90042c0800303a4001e1120b80342840d00d0030000318400041c01c420000c0e5181030f90101a4000c1240d0000e072800c03210b0005510f601440c1020b003404005003910030199507803054102000c030f0790708098809541e14040c250070300c011180200090f820a4005081d00b00082c904060031401205d4403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 282088138 1250 282086888 282086941
    0x3050901060f060f0318030504030308090d0f05090d020306070504090b03072105150106020a0309050102030a0e130624090608040b01090b060f0d050a050703020f03060d080403050a03020303 83
    0x2e2001e0644061040140c40481c5807413051043c80140c10707801404900c204400041811010708101544400213000342d0340300340e950381415110849496500c5da1068038241c0414104a4a0001b10344250060124031f00020100c0c5405081e58000c01c2c20000191020000100005014450050940580a180c4405800500c07001c0d01e0f04003031000d40788483c004520030500020400d400d025041000d10442e180008100d4103d580d036540203907580700781c18422004286a400001115800881178035141c008584502c800f0008100802c030464140310642044107540f540007180c0f88048034643d481000b04407070800c1842841c8000031706410010b82c021010040b0603001c0200040350494014116441880041151004c4400145079070180141c0c4460a20020522200c00003094110600800c10101c04211a469000080302039105100340e8508042d4100042081c900b01900c4198003c0d010701e4010b82055141e0355890704043c000704007500160b00200500901050f504264004031008049 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 282089388 1250 282088138 282088151
    0x1b03140304060509090c0403080d0506040b040902030307141207050106240c0605060307050907121d070608190c170105010e0a0303030930140322080c03041503050901 73
    0x3d04074030903c20514007924984002c00e10203461a0292005035038028402519846a90140d20003064110740c1c25200b80e0400000003268101031117112040394025002e9482c3c85043e8490f5106541034401602061060040d090810442036000d8400d0314800c0c5d002003182490110160801d007030540c5510310351034803480000403054000070a06c0c1b6550744a003002c80e8613a5050002410491260310440e0084000b43c100000b440d408400b03c2114004614100701c10b90109003400d410407403520071000f840e44881000e01c80c141c0903504e4141e00168040d410035003030440c1c80c2c01c030050b580c107450100041241001e02e480030380da041505a000d4031003840d0242c100d8803c0d80c00070340ca1174850f1001078207250740d441c1008144000304120390100c8600c1c82e051540018040000548040c040700e02c4000510040484090205840c0849019484420055001c21031803244402e4020580c170080303908000400ca0a006c18605001401c010301543c1d07c0040004030b8100d0180903035400800a2086034504034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 282090638 1250 282089388 282089399
    0x130203062209060203101503050c3c070b0a020c0a0b0a09140601061101110d05070203190f080a141501090b1201060f02030a0c020d06091b03140304 65
    0x29007055608180164603415401c0c080d00720001000820301c007521032400041000113140f0b9501c82007040780d03105190103102c1c0c0b580e000c1c00c03002c4039016180407140410812a07241c10050710002e002200041848038000ca0207800d0810002000e1841d07204241b1001182c60014030608074140d6500c2001140c06602e028100c0d0f15690700c40c0e14040004011a0660000c2514102140d05c80340d0340c2903000340d2052841c80d80c4000d507644c40c1401d1080a00158424080503881441800340c0d030301e4005d000c85aa41003900c0040e4440c041c1c0750090940b01141301c24818502d00880c030014040c14540c007501d6400811107a01c01c011f080e41002420464001d0528140c143e140344806d41c0303160700c901c4031485103480d024440300485c0c0301d6543d5803240001003030106450a105411814550488800ba01c3c0d40e1000a9405402d9840e800b401241c00082503000001c0b802500f00310b0303d6404414072540d000205000745603101c4002411751402143d10b060b07801c2c810310800000010708145000617400440c2000d1a18 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 282091888 1250 282090638 282090649
    0x2010206010f0317031803030406060305011503110f06210906071e030c090801062715090f0b06030108011a030304080706030f0e0708240103080403020409020d12020a0213020306 78
    0x11a01c10140c11002001500501b105d00c9200c05090161090f2a074905041c1042c10260440e4007054856518280d00c49440125542e800f02c00c4035880038003401848000400c0054409a0340042c54011804100140b0f00c186007158540c05400e013407c01202d0b50429040051604000a00c4503051010300038040c08110408049111707418000c0c600452a60080c580868026030940d0040f452982848400704e103424101040091a00c0b40a100070007150748184000283d03007400d405e03410031494548040c803195441d074000e10035003a0006004190314040c000446c3c105d030f0099210903003a9640d90024035041d200d03ca402d0502d031108500030750078541403103e060384411161190005051383c1f440b05014102e480d0300000d6a107001e83c1c040e94840c41c0e40e81c808549036200c14410022054040100e030040300100b02e681c906070713030700b00d4641c0741003034203503807d210051240320b0040e030b0b00000401c0214000f4610700302d0b4080b0411180e026044141c903a07c180f047c0c83c600b9503040440140148100640364884 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 282093138 1250 282091888 282091913
    0x203070516050f060a1a0a050a1503230a0b09060303090d030215040302012408120d150f050f061e0f040b0a1d01020d090501080603010b0d060902010206010f03 70
    0x540140340304180c03a460198540503014440050314004e107000c0141401455100302c1c001410603c1480700710302c001c010802c08001900520340d021904600510004420740b50b0003075204000d0400107440100c5207001b0764180d42c8812407881380150281044204001c50040e009083c900742e8500c282030070034100190f107a00035081071500904600c4481000c1c5482000700040c004800d6910034414241400c0c002c0c081c00200c100550400741d0700c410400d8184808202ea0112420303a0080e2007212030401c40409a0703404986440005070321b401c100003038403140000c584000c210103032600503842d142c08203210711401503089444c0300705010702070610301000c981900c0351000c01c2c000c2510799a8204a4604040c1e002d1138000d000a01c0d8080340c41820550084491581010f4108980b000c0f008104012aa01c0202415220010341034002c2003109500030760000c0d81100005001090000780000440c903075101980c81914006c0d1111404425541c05100c024050f003281c0465403070300d90a40e1921b541e5a0389 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 282094388 1250 282093138 282093157
    0x13210201090e06010c150203040204061e03080d1d062211090714030a0c090e2208091e15071703040507030204050705030405010e06070f1b08030f04060c0302030705 72
    0x1000b400100030b03a1081c41c2c103202503035000c00404820841c4085042c001e400c02c9400700d000d1031030040003003003004002074043d030001d90002c41c41118900396615a9403a4008005000000d82c8a41c0219030f60305001007034040100d94407004103082e1a0400040d8000090080001440301c00254503001190103401a55034240d410345021065441c0d460040b41d80c0c0400c9040013034142e00100c2803002c00400d075084882c04650036601c13600c1141e281d410200c2c81603c1560b110101018002101d081c80180c010f031891140d008084241c248800341c000304040c0c4400d020302c041080c00c9901501c000d8034003400700c80c0c405526030036998140fa0755136945100600101c0320000c4503100200018003001700c10045003014541c090807c0c01303203050080c00944a60419581200cce40d500300b10324001d00c480d0000e8014807400c0b0740d0b991003038a161820819907070800102680c00b804030301d0303400703150100e80030301c008602072409030200a6052034181082011950305402d420201030041052142c140c0e8003805441940d030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 282095638 1250 282094388 282094409
    0xb03010501140f25050d0f0c0b040317010f1809171b03041203020606034b0a02030d0f080105011b0f1b120b04061e021321020109 57
    0xc459402000103402602c09139518414080264100c002030448007a001520840c101e5503020200c480548001c0100f41646d000908468040c101090202e084541c1041c040e041904070320403104032104e04a0b1098000383e84228012100300902d85c0c0c0d2007014002a0702c44c040c10030007000ba075541c3e40030030581440d07030410030080032500404610a2036020744000347c07010b0890390788079a50700d61046206451f440503409401042c002420030309001c1940010100390000311507154a03030000d0403100b00c00d0309448100c5450702c066544095901700510a40548810b070040c44000d200788101860903160100190400000c168424641500181158151902400c01800905030300c1d00f5680c40034060319000d09030b40a0700b800f10703060003c45d2010b24814800003d4401c0c02e141c88403100d8007032900a0304000c7c40c0210810001e00031402541c00308840c000002d034148410601c1c000b061081c0e03048445044103040d91018204009151003d40110b4981c09100d0541d41025640020385004020f2041d94030700c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 282096888 1250 282095638 282095647
    0x501210b0111070806010501030c0e090a0e0c03251505040e0a0905010c0905040b030106050307030b060609031f050f06100309140d0e04110f0d090309030210030507090b0301050114 79
    0x9a02500b0810307405960401140c12150340c030b004030ba99480c400c2c40703414046840e28040d00001407089078100c103541e00150124a00f910350460080041c40300d245024038900a0329110030042c0d030184001d1b1140c0a55411901d1045d50b070400944030300c10f07281c1c4941d0071b542d12401e21008058101c026074040342e544d211026019a186030000c00130745a1400c004020303510b803101c07204041c0c1c0c01030282c1c4150f40041d103003080b010003248149400c07241c590107050340c50b6100710f0040001075202403a8550000c4080e0616050003210404640b5040c15a06d642903103031107244682150000358812182d02529070f500c04465410014045007180034101d60400400d82c0303c1050034148844005010044044041195130b4000b01c854001e0011740c0180c01c05200c0c0d170a1001c0d655442c1554000e072000c84c00810802450048800c88500003442205d40c11400e0024041c00040507a5601e00000000003268802003180c0c60503500007440c44c401900001090001800140a00d03644003048103c100302480445669 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 282098138 1250 282096888 282096911
    0x1802010e2205190b031e120a05220f050405040c05120f01050703091a0702121803150702060601081f09020c0f010e03371e0206010b2505060403020f07050121 69
    0x6240c285000c0580c110b400091810b8990380c008014444401648180b0009420305000c100012915200380517412f22041da0501140c5001d40c40f4030341040c442d461200301c0c15550310100d203241a800510105039086814a00c032081c03000c2c0071b0241e0103d420318003040100aa6918100000e01545405507000780300c0001a0001d802009400c4244001c903040c0d64803880101c154040b0750b07001100450103402041e140c5140b2020849815009071165006042141c1d2118011a4203d030002d01250100c3e40401d10340c0301001c5c0090400e070241401e1030016a80c0d4400300403591804c60b40341c9800d02182e2421003034443e090008000e40b081c02039401d1112074200d005008181004410049141035040107072103074403c0c19045519400c40c0050410802541c2105070b20a03a101d8900744105100c1030f90402c018141c5000100d003040c800202c50035007124842c1e090702d4561510a041314100c0259001044802c1d601d02e08026000c000c1a0901e00508803298011404841c0c6203131580040d07400e03440301d80c22650f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 282099388 1250 282098138 282098143
    0x315090706030c0509040f0507120e1917040e0403110f06161214040203070b030106050d09240e06060a03030c02041a0d060c080a1802010e2205190b031e 67
    0x3d00400810510840707601105440003002e003278403000b0207e40441c0340300180d503459003d40701c1c040d541080580140c5240d0715811344045c80c00700c021184a001c407001c9a411141c0c00340a08050071720f010030503016240a14000e02800142e02c030504140d8450009200240f80000e0700a60080340480a500380386003800d000c4d581054244440d417022410101c0e014032924880031010300c0351b03008a003202e0f005030ba940142036884c88280904000104100001112a0f80c2500941d055520902d030000100da0034140c66022980105036000103592100c80684480c0420000f450b0403020071205a40729501e142d074058024044c12000a000e1500c642c050700803007145c0c426040e1100c1e03016120b070001094504c2e01100515200c490f0102151510f804500c0015241c4100a440c0c00700601444411050b50010364201102d407504136801040c142c0c00c3c900040741ca480382c2988414400011a86040803081c40e280000c1804481c19528542a42100e00b0780d00000c0022505202c440410580c9020303544c02070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 282100638 1250 282099388 282099397
    0x8030316110d0806090f0f0c0a0c0c0b0a0906020111270604080312092d070b0a0c0302010506030105101a0c0313031a01060206070e041512020315090706030c05 70
    0xc1c1c66000d48100ca003540ca0300540768500c101c000311094a200d5585200d944a603c0c4251540d40348480340f03c0c00210748204a400809421040341403050340c0203030344c0c1d84902040c03101750403420b000c40001c81d040103499009101e44c0080c1110f40028014022481d11300301a80c055081140845441c2400c80900f00c61002c80400b55032202500c001c0d03450351203456003036890303200c1c1914107050031010001071441c8201251801d80c00002c01e6518040c0c031040c10510b401005c0b1105290400c0c0a24240007500e0f0b80c4410052022501c140c40c0c4103004c3d141814064211070740102000e010b03904000c2000046c800742c016032000c0d00d07440b84240300742d15213000d2a0282401946030003c06444005203d04206001448040440340301d40414544504049404032650f4808c0c8520b0015070710840c041007000e8028104111f0507840a807001410f40d40094440c01c180d1400d038001d0740d420591982910540c2004e22061f20b00a903001440c0c0014100007021517a203e40d1889082d040558454005841c14803c00440e0f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 282101888 1250 282100638 282100667
    0x1050906130204020415080718030201020c06090616030f02101b050a0210110d050109090510050901110301090609240509040231230f07050c0d120f020408030316 71
    0x35410785d1101d0700c00750a0356008e607030380c030013083d1a982d80760000469003001006895041c0c2c09040c1c401c07401c0b014080b03c1d400c81015150700100c01e010500d01c4201c009c4000111354000e41d600007400381314902c040d06020000520342442d41c1441c2900e142c601d11311403410090121482d2465444213540d00c12414107014504181185040c0300001a1206407034000d41152842410304005c640d984030035240c100d522000c4001c1064200104040340620198041d55101e1000780020420700d0301c100510b0f000350b00980246942591750b503818400106a445200d00740b90360b48a00c4a141c0000c03d4010301c07548400e10420344203508450002c1c085498009408501c0d07915501c52840b070241c902c0c1c1041d180b600000c00c0141103032401c08420011a0040c04510800c410411600015114004510000b0030010004d009100d01046845580801005032450044003035490380204d694041444c000d99001303107625030010380144014082d44801200b1260403000701c01901e080341501030070039500d003845108032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 282103138 1250 282101888 282101909
    0x150c131503061d040c060302121b130b07110301050105060f0a030f060303020120031509040807050d020307060b0a06080a0b040e0f010609060b04080a030518031c0e03010509061302040204 82
    0xd44000e880c2c1c40c00c1e5a80118413890301780c145141c54450807400c07030080c40d4809003550107040200f80c2c55089007207041c9110b02c4035007187c1d20b40014203e070205210f4903544019030742c010008110041c00b840a0720705000700300840003070145525000000380c503400341088409004600207940d103207490280d0301030354142600a85c1803140681ea0304010303000740460600d400071080c071804020a014004401c40b881102d102c40482d60010040b1709202c1e004030020411600c0740404c228401c0800d808000f20356140803039600860b81c481c1c40d4900038040d18188401c1c40e010b6440103e00780f080d00d4201e401e46902c0009008009200140309000030007410b60322010750368600640002d85040c18040d0043d500340c03821300401380007103503840004201611507442043e90369080180b1100000b031260004050442e0b681c0440c501c850521400a4241544040030a0140d583c0030760690003e81c21404040c2140030842c000c1141e07141040000d034413040c00501d410b000d0039000c1c441408556a07541031341d010b0800300d2031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 282104388 1250 282103138 282103169
    0x40b0c0d0612120e0105030a1d0a0804150201140402091e01032105030408040303030b01180b07030e0d0c0504110c0a08040603060b0c0706030b0f040509150c13150306 73
    0x44006908910100644144140c140303806480c0307000d02c40049080d41d046c0e4a0500c0e59903190100001010701e009202c6405540714035031000f200c2d04001d5000d025000b10006660b8034034005c03914404000b42d0036660b0175a41040c401080c02d80300482c003103500540641d143c1c510313592044484c23516502591503020039000100004024051100600407906076061100c5112803260349055400e80021200201821010481071001034400d07003001048c1601818150240700240b0580d8807030f66415000082d42650200b040c50505074882c18044410200740c40c184a00b0000d40c4548440d02d180d4000c283c007030fa8a54508801700840401280c0300b6251b10010b607400d2030401c1c944000ca0394814424400041e040c00340218100c80c00c1c20031204c40c141c4103401001c11078503010040e0301030180c454120364440380e021301c002110307140c5026544c4501041c0b000f03032140007000041086910030180c0401440c04081c0840188000891000c100340c454000c0b880c0ca07103404030b10084014001d15081010403000b041c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 282105638 1250 282104388 282104399
    0xa0e3c0708060f0a0308091905060315030d03022703072312061003030f0216030803041703190b0301240f15050f09030c0301020c0d0801150206040b0c0d06 68
    0x1848a03000d68003c807802428412078034104245400780f804090032808003080366082a2401144041a286003c1404215107030390300c00045064108442e50001303000c40720010079441c50b00b8801d007401c41d5280c0c2400c40c00c2045003c04d9101e8446c3e90101802c50300a1400080b40039601044400001d01c0c40c840b0702a1005c640c3c4206200c02101c03610b03810301030207400c1520a4078410200c1c20314403e5507800c0d90006401c0c03039500d00f203c04c41405213034042076009154403400704c40400b8040101441c003c03841c0c03075039904017450841c00b100c00c800d803840b40b280800e000b404150040c00d1510000f0155404000c10318041000010740108050103210440030b002841140041e0b150001b031008496000d0071400c1d0065a030780c990704408040a17004400900c003082401c00340707150078016206022001c1e0481c0e802c1e8011340b0109003240d020207503e203410707441080c1c1c0f42c0d03126500500c0503015082c840e06c0c030742c060750b40340074069a20040a80020400c051b0351000a01142d5000f0940382ca01d01e004c0d200b400819500c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 282106888 1250 282105638 282105647
    0x16081b0d240b0912010c0c0305070c030209161b03320d06081507091203180603050121020f0603040f080a0903020112051605030901061706060a0e3c07 66
    0x303d0320980128440c40da1040405410301c91040058199220ba1043c2040c40e5011a013652101c4400c541e031104e0b001c00400580c0718084000e2049485005a100590f02181c001d8640d0080d038000401204c0c5031070000e400680e111003a0000c2c1014442d4000c0700c1c0303162041880c410700c00240c83c00c00c400340200b00380a0340d03101608000215820f180c143c4500d1042d00351100b50321001100d049011030f00c0541d0030400c03141c6500c403058449001c0d141038032540d0084101d601d03010f28150301c0030000039121001880320003130070491340070300040c6c41810910080480c1d02080c920098484807500c41c1f1404400038040c007007614056080c15901000407990b4281c848000740840000d400181d001035404c01641d000a10780740304140c0921058000c03124000000b200840b0340b86d0008003092807030354903850005140340041c00c0d18010403115070302030085842c2410038450f0302c0c6001d2b800590303494000810721007400c01c4c1040c1c0392001d040c4032460303000c132298640524401c0381d00e4010500c14880d00e00100710895922 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 282108138 1250 282106888 282106897
    0x7080f01140c040e010b1e03070305010303090f03211b0b01030312050f061e04020d1a03060f190b0a06050d05010803030c09120a060516081b0d240b 65
    0x894000d0340c0d0b40c0756505490711602950040000041894005008028a55015121080c50754803019100700c07030722010182503001a2440f0340442c1d00c650061040680001c0d0540140c06906401c040d014a10b0b180d5400e0b1004840000010803900094101e40d1885003801c0d1080020801c1040301c403130081e16200c00052824030054001400701e80002104a446015540c001c10401d142404c52b1f445500410506007003503491250305030070503d0100040c5d25140081c0c60204901c42001416001c05680e05030b141000d103400034842d400050800940318820b01c1d0b1190401d400c1c1a00c100f501400624a030024050f082c4415813045c1084400100c156020300241480700c0d80344800e00460360303a0183d0710741c3ca02064420320300d80c400501107610a4104444c0c61450981420101c0b441d803201e80e1950b500f211010742c0c1d00c500c0c20604158400d1000c0d0050207464211320006102608a40300029120290040d40182aa1103485a000e0001408600303910000002aa409408501c2c1e07030300c0c11174005522 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 282109388 1250 282108138 282108161
    0x120d09030b070206130201050901020a0204050108010b090615040608090a08040f090c020a030807030b060d150510020c180403030e01050901150902070209040323070828020a120207080f01 82
    0x81e600024588520114006004000103004100014216401982d50f60000d80034a41144074400c03003200542d40e1405518024045c801c00010700391051380500c650f2120040215000712405408242d47c001a41c01301c90450b045031400c00003a4580f502ca540c06c11131441c00103081f000e0049808a190b0017100c00b01b9003111641e03842007149518003c003d90300c4048029003c0c0110345d07070030002221140a90050240110010002441c218000b00074100300d0b50320940101407203944400c00d00040c01d1807200d03123520714440c2c001050741c10912000203012088a050044180218501040405000381c121b4002c0d005400000c2c00f2525024a1207030003000582420854100320b01c1000401000b42d01c203c1e59001c0d009407031280c00e5982c5840581d42140e00c0c4445480d00d8020b60100000d640d03039000036010051141014a9032542c0034140001c01440c2c02e4605c4201500306102d490140340c0024a28000c907071300a03c00d1001c0d0307681c8a816810f00c0d00300d500c604102d000780d03601c8a81005041d8040a1180c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 282110638 1250 282109388 282109403
    0xc01050c0a0815030d050310030f0f020a060908030307120908160209070c08190212120f010902030105030c090406020c160e090601180b130c0e040501150c020609120d0903 75
    0x59403c0b21011441c0101842640c154202c480d0a198071481540115404415044003040035a5240e482ca0740f80072400d9000e60b41400c03e8002d0034114a40000d650f401045030b0b141c0402d00d2810301c0481600c03440302514034410f02c091103c0b0881000c90301c0d040302c080036800c106041c7d1103040004030302d0709590784000101d11400c01400001e1000d8041c02c1d1403410960043c0c4058140100d5100a010040302c0c2c00002c01548104001400c0c0810840300810b00707903102000da00803038149000c01c09072030304040e0403015440340103000501071070700e00090b004490702e011500d04c01f094445044c454001e00c100780c1d4401d06800343d02e2103800050180d025075000c540e141210b4a405a446808264842c1028021100d056000c500020101c4249800c40400d515000300748004920001d0005400c40c2c04031036040001c01c0341240807a2607450a446490b00514900c07512540b02200500010004a150000280304100108480706c03d6115010a540c140542d2803c942c1c1420400740040c0100196110855441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 282111888 1250 282110638 282110641
    0x302062b020f0720060a180803040506160312020c03071109100513021207091509051011010204050405040b041209080304060c0510110a020705060702130b060c01050c0a08 75
    0x10480340700701c403801c0c001d4404060400550760740d007025a0444100310489250352002848aa030341303540050240c2c0c0540c0d22410030001c1c0e028040c40709000c040c2e10143c0940c2050108101caa1246070403035882c403016001400300c5060074036080d40d04510391000000002d101040c0d014888a000004000e158001d100801203061250200b0482400413070718030060181030b400410031410482a440039a52410001504084056081221410003102c000c0d000500e081000c000741c0395403042144070303141189002896903003401c000c03414200c030040c00e99007042400410b021102c0401e6041c2c03400b03040000c2c400e00060510342010034034440c00303030350680d00c0301a40c1403180c454a00440d50b510031203100368040c608040c80c0c040107403440458940c4c02c0d01c842c01030a803c206103a45511401e0780741c4100140c1c0c540c5070340407800001c2c0303403443c51340000d40503500810048002d41c2e40c1c1301d20700e21907515100000c148005084013050316130084842c60719956082c001030005080500780604278030012543c83c808903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 282113138 1250 282111888 282111967
    0xe0a090606031203270209060102030c030a0201060609060f0207060e03030d0f0f1104120b0a06030b040f060606050405010504030204020903030403050607080f220b09160f0807060306030203100e07030206 89
    0x3480901d140490040000c01801001407c00a5220390703c81d40500540b410f20f443d01c00260b0440c0e10400340e0000503550740b00e0070b201e0642c20104000c040c001602e4074503075072441705c030000e035548403580158810301c00317031701c0c3c0640e05994200101c07880c1c204c04400900c00102c0744541c0e007000d49003584030002c4039402e01015080502c6c0402c20380b022a00350300500440c03043e00d51140e0703c01c0031000d00310b441000d840b01d0004c00402d01d0250641c0c082d6104040c000c42040f0346c0e041c0700c0219450703500100c0811808200821030341c0e9010307007602d00703698040710016520110707103000918522541d40000c00600030318040107203068000d64807034803a0508903030030151690340910b007140002c080300b0011a4003100710414000b103050300b4402c6611100344001c43d50b60808a044054651075554400a1246200f00c02440407600030304c0045c3c01400705040500c02c850071a4002781c1c1b1103440701a880d98040c1d9980c2c8201c000d0750101314800040d5005443e159403004e0340e1040000881848030b85c41072074912541c00084 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 282114388 1250 282113138 282113171
    0x408010e0705030d0518210607030b091323060c0703090e0f01030602030402032a030f0606010c02220c032f2b020f030414060106090e0a090606031203 66
    0x140302481d9590300e00d0142d03071b084c910519410040300c0e5a00a2100d2200c1070000c00b0481c44101c1c07022020000345141e1030b0a45008003a40c400c2d01009005114500074130480072038200e0307a00502d1703911114200c3c2281c0c46400000021074540406c515a1140c0d605101d420140720004000b007c3c020755610400c1d0751070341c2d0001661071080d0303032282d800121607004202003007080c3d0165400510080075910900168200444080f508500100c200b004115003280e03580360401482c1003520000707003d031426140c1180040c00ba8400391801030f0146500410341c0c0d0540140e0143c4a8610340701d43c20820031a100c000c0d000700107119841c0a0f1501c84100000042c01d40307100c201d1101401f6601c000185030240c800c041701c41050440d8000060112000220544154280060080245582030700340d240d1134182410883c45500a072142c0703042e000760b40180049580300601100f6210203905046c51360700c5200e2140000c1602c080041e0116245c24070100030819089a80c030f0030750021344d4003441401c9074000d5400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 282115638 1250 282114388 282114403
    0x10b070b0606070303150602071d040b0106080601120c05092d060a03020f03010b070203010c1d06070f0b040f030e010f0c110f1c020a0603020a021009080f0408010e070503 75
    0x1400c051040c0c00007201c80ca0a1001450b0aa2080c50b02061640120004400d41c3d4201c1d086100035070050141070004514032072043c032080c8145018003c090410742c0340c1e4080f1072010b0007960100006900000d00b540d000c4c40d0807540001d11a2010072070840e240100038584d400043ea00c0e0700c41c1c03540403038901c007035400301d50080c0040c241444268002400da00800401d40c0c04512200203140e024020426060301c5040554000d1135045945503558031248100350855441249902c140a0000f40724401070081000143c1e08482c00d5070304560314030b906d050480c03c1c031001e140c2c0140801d000a0401040010750014040c03d18070980320f01c100b800c80400103503075420301108090b00041e65440408081520904085a00e82c805030044803803850410200f4a81c01c413501c0e842b507210f446011100110f0414048410007012a8602141440c0c20802e00940310710348403c4014a02c9e440302c0d541c0c418400c1c05403c40d951035124400160f603661395080d20b10f002e0448800a41564001d0f01000105400c0c080f8030f10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 282116888 1250 282115638 282115643
    0x309060b0a0e06130f02040b030117032109010b0d03020307020a090c1b080d1803020f120f09220e1606022e0c171b0406140702031603020306010b07 65
    0x103041c40c2c0c3c0c42000380030003880710740d035403046054542d00540c0b045046403004001800d140350304d081d643c0d03050240c07084501020004949069000304003c10641300700d600b46180c45005c2042c00440f075184c203507440e80580514458260b009465000300380800d41c0000040981c0c5e07209030342c0ba0301916628100700c402c0710a42103c00300400c44904608116a807103603402c0d2040c51140005908110804464034100c8001c6505050003003403a8060078240361b0100480000040800001d0140b984070001d400e8582c014020400d00d05480071540202503078032054000114480c04256020300d00c15070a10318041e090132115041140a20101e6420708030015845800f9100340d90010280d100030402410650038465441441011400440284402c070a00075011208103a541d4440c0741e4441182140711610301900c8040340d21010310b12040d0035101d0b8010f40e821540e2a043c03a10512054580380815032017074aa00a41c98052251100c1d0080d24459659080d0380c001c0e811200603a0300c480e8a0120b034030504070301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 282118138 1250 282116888 282116909
    0x3f110d02030402010e0a050a17010213060203030f09060c090423070504050a0f031a04030c0b040c0e0f1b0906040b0304050a05010c050a170615120703110f04050f150301060309060b0a 80
    0x1d01041c0f141c00b40e0442140c9c0000d000600c4c10000142c11800c241c01c1c0c3c3c0040303005070400000d0000ba1500381c02203036004092000900800d0508000300802c0d0310039411241d0042c1c1c1c0707607c1c0072213002014860040d11f81c01e13080d2401c40305281c0608000c0866016005003031080d040c4e01c0700480e0301080011540c05603580f0561402401d40b20a40582c11610004d1080742009031015088000800890229008038070514010300b44a003840d00c1402091001031161500d240c500c000c000e242e0242c0c007940c1c1d0070b56590480c1a541c0e0400640412941d11584d040044911000414403040280c002800c10a4600440080001c0907040e1000c60b900d11a610381c24000400380c201c074002849500308180d0308a42c00510f25441008224070000003078000380b01750884c0b107141c4070402081ca0381500940f50f40401035901c0c2442c0a00d048100c101e180190b01605000e100804240982500c0791440f03252079594141d50b0365201e60752a0300003806403071240d10031150a81000789038a00c038104019504103642c1064503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 282119388 1250 282118138 282118159
    0x14220810180f06020c030408010209040615020a0303050405070f0311090108033f0705070b0c0406361502070902030609060103050a1104060f3f110d02030402010e0a05 73
    0x955090090b0400c0c801c0ea01180d08004120000d5410401400104100c00001d0385a5a810042200302c40c0198405103049580d0003d0b121001d90100d0742e0399625a15040c001100c0d00c1c0c9003000c9140c9500e0f41c02a04000c140300e0000700a000d880c0d40300c010810421030b40d02c100c0d40e89481070b8648030300400e0405100079400840f45c8a5441040b685045109001d5072050035040038081c152910300000e4885034046440002d0342028440b0030040c00741c0c40889010f10502d003c0c9001401801078168803001d00d00f041240740600030410844641c000380a0664103a034210540b0b4000c85070003c5000c0e000341025100350035001407442e056000b500d221f01c01c02460303000c440c0c0d80ca200540c05040005c1030101c0c9699142c15154440d410703200640040d01065440b00080c003c0d000b0023901e1000c031052f8410403000409920301c0c02c1e003015201e54010815014591a0500074030105101500881c0385509190601140e20503840100303034069071145001742e8038086c0d01c0e07100c00207010003034050307005140d00703c4030130003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 282120638 1250 282119388 282119393
    0x3070b1b0304270b04050a060302040b0d0210050a0c0f0803090f0604030903080f270307060203030907050d0206040807060e0405060f031b06040504140702010524011422081018 77
    0x441060801600030f00114a4a03050701c002011510221101d1110541e2690f052095050034842d8122f049800d54801150360402d0f00010300e104143c0403940d003040340c0000c124444c02d115546003854280e002824000d140d0b00d40c64102ca85400440380e216061040303828800e0200b500280590003950135840e400405402c584030203003280c2c003800310100c8840c82084502070300100000c00f0f00d9400342c03c0d40c64180c6190038004050516042e98040d4007158401d0040c8200040702107812011188120b40030481e420641c80030503524002c6500c400886d0161250015820b0f4201ca694804110100c03401c2103142c3e00c2c031041007036002c28806400d03095884666086504600d6098105080780010f103041c0c20a5074990015003a40d02e1500e01160751207402e400e004503107809001e1030b0381140e040000b41c3c0310001c0006096a80c8000d141c030240c104420b024510302d89220013022598040220460b1103038940d41d506e095410f02c146441040c255100d8802c207018071000c41d207e02c041c00903041100f6114441c4a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 282121888 1250 282120638 282120689
    0x1090e040b041103250f030312090501061805090c010825050c10020d050a0219030f14010611060c040f09091703090a031e0f0503130203070b1b0304 65
    0xe00449907a15051100f0203290307010014803849120400700004840340f10f480707614580c011607100d8030101c0800d00040c40081d400c10301e2040c000d10b4074800003510a5290030854003511180c0e016080011000c082d0a01c1141c440d005a8403480501c4110350702c14a542004480326042100c9100100c400f54688034010495800071241c0f10b49140360590034115407034269810300c0080b44c000c03280d03154006500d0034402818000d50341c0c03044500d0070450a01007800e0042e0f080e82e090361400d50800d40d560041c2c815003081580b006c0038810701e282c400b00196842d43e0004c0d1070013603c8440d01020b80f05140000c0c1d170072405182103800392080740c0c455010003480c1483c803002a011501040b16401d052116544008141e00051842080c04030010203120300d0508018221341c9406461032500d845402104125940010383c81880d025180380c40c90362952807005041c03407450810002941806070710800502000c0c4e40b03018000c4c0c00007400c46480490032a0140340d649104a100f03100c0714402c83c40710b1214040c0380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 282123138 1250 282121888 282121891
    0x807030b01020f03040b07031d0f060c0a0f0609020913080904110c03030a02030f070302070c03150b2d040504020d17120a050103030311030708061315080d0e01090e040b 74
    0x41c01268a0f21403103003421400c41e04140c0021007440e9010520070103160348100100d01c2c01401d004002d01c140d01407001710384072840089501c1c0c055000060307004e5031700d201000360fa0326080d080391024801041520f421006441c031418180c0c030a0b03142030041340c1c07000644180d403035046922503801880c1881744014030001d030888082c100122141448803001030201440258402d600d000001aa40e00d46481c44484400028280c601003507c184042c00000740d0180005060b650840c3e015185142c003200c0c094040e000700e0305225001083c0c051584446042039014141010300b042e0200d07500c404000030f11048031400c440195003c44030794003d071301248103000c594802020201c2541c1c9840611010844050030507114110400c6e03a41004005040d03043c410701c2c8000307069184007851400e114600901003c00074104600c18401041d4806120b09150b00000d08004100c141306140d9a03248840e0b40c0351035150702d01e040421044d900c4075000e50301c903441c0d0006580f0300e00c88001c8d180e00c40d5150b06652550 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 282124388 1250 282123138 282123161
    0x63002130e010207080408011508070e1512340b07050f1c1202120a0e1c05030a0501090e0706032408060a0c08091b0a1a0301080d0906080703 62
    0x580701c501c100300d6007080c001021071038020a0307402c0d626413a00d01000d00311021031281c0348041740102c5041c0400640880c12804482101c10f2101c4652a82080900107500c03510081e5804071080008030100c800c00314810a0340c442c940301c40c45014003200f002500d41580403c900c040168100010300100130706101400000d4001e00403241c1450349208051300d805043c1c0322813890190703090100d16500c3d60240302e1025011008100b1341c01c000c1c81ba0200241d2000c0506913410281d154606c4051107041001101015000982100300850742588090010303401a92a640701034204000458605594010090000040c0b00100421407070290114010580650240c102e440711180d064400c1603e140503c1c0500809405041c15084c601e40c8081140e25451003281400703003040030041d440c1c5002c6400d5960400c0e2030740081c104a2440001030584036182c0000040d292058070341d002c08a80380c0c01030750580f030000c1c040380c00c85018040181c480c03070000e104540001d829000011a00c40c0b00b0340001c3d04001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 282125638 1250 282124388 282124391
    0x90e0d120f020301030803012907030e010e0411120105030a020609010f030902100306080d110d0e15030708010602071d040609060e010507110c120a03030203270106300213 75
    0x1101d015100240c1c0e000780e1041e184040040014014444600c40103003481704400d1921225460860a82d0443e000d40080641404101c0a424425074000c40740c98100d0a40200200805400041014103640100d035941c140c04a8142c000b103403034140011207a4000350002c00f541e007414600d10045400001c1c4212103010182c481460071700680319078240e582e046005440205c0c0850070301403850303c0c003d540308035030040007010322180034482c8000c1086101c6e68001e00d00660b0b04e82d40400850b401c62081d484010805100004208411ba40044581d042c0c0705240c1c01d0704c0316203644980301421410000380e0101c4105680340070400180c03440d072051010512840012400c250008010390855500301c9a440c0403030030704034110b014201b061040608103001165810f960b030780c0c155462a540e26014100905040c1d002011072007100341110303072101501d07039405010356180020107640e0280110340b24240100314820800844070b00c94a10f000b0a04c01070180c14800140780d5000c11000008981e00d24001c103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 282126888 1250 282125638 282125651
    0x18021302090630070c0b0c030c070b0901140615030109050402041103091005010f121403070b0403121b0f0f18170601060305060d081809071206090e0d12 67
    0x1072070f5200c2100b030350080c449000544641d210a66482000008204070100b20030020000002005802020307000070000314400d440343c1c0c3d89940300400d84142c00010704105400d80401a03c50015000b039043d807096042d2141c3c07180c0b5860144094172880344000c00304644103100600c442032845d400694410300081c0003199503a0a22215020b0b648165104d17401c0385c001c1c4640a080c1059030246900404149400043c000d1a0411214074640003800043c8401038000740295403080c01c1054608007904400d415806041074980a040c83c5111001450f09e2402d04580c1c1420150b40420003201c02030301d858be140c203c0e40c0210100e03030700c0803850308410500102d1501400000510034844d4050403100400425107864468607900c1c08030140d12040c01c16042c6000c0003243d13120741c0b407401c0359140e001584984802103c1502413400c00c446a0264004500d0402c003c00254800e141803014801400100701070398440d6440c13400e0714001300e8400340e568842000122a24030070980c2e1031485d00c1945000695 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 282128138 1250 282126888 282126907
    0x4030e0d140c030d0207140a0503030406051b1c0c02130203070e01200d050c030c0d030504150c0509010f090f0603020703020d0306030c030b09030903120d180213020906 74
    0x4091180c00303540c1e40d414107940c1c0240401c204a85810900100c1c0101640202c40700000c6d641d40c228003c8001d40e42503400e00401a484222840024010080a4035190358035118014895000006241c40010340b1540c054100203004c142e0810700544c01040b40076286440c0810b95020040c02c20482c0c00c164658013102e40340000e480514000d40d4140c3d100f4031503034045000108840c00403107208a44546200d10007862200c001b6034a01e50b242c0c642021511021420701c001d085000b40d41d51182c2c1401406820311b0040c0d49a40228801c1d032281042c0403041c1c40540c05101211082c4040c8004600100b100742e40540c0240608024a100c40c90300ca52082c3d140d5041485024003030f48002c020a4012801c0c030101901809007002c000e446140400c2000d01c0c60b15031220036105480064100e50001001c9031341030302d003482101c2e0300710b0f0003500300c444030300001c440c0c2400340e48401001c6507803a00c2c00c901c103c00c2c06200c0303080310f135a00d40003006000c10860005254000350b110441081e40440308004010704c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 282129388 1250 282128138 282128149
    0x30c23040e0c0f060c101d03070308040b0c12190209040603080a0923010c0204060306050709090e03090105030f07091701020319090807032f030913050601080f04030e 73
    0x1070104420207000e80e0303000b003028040d070028100e0030380784950010300030000201400100c403921505020400f06000d407a00a08250214a0100c506501e0000140e540185a00000031038044c0c0d100e464800c043d541c4400c2201054003550901001b4159200d011a03418600080d90b02e81644480700b00600c2c040388400010102c8a8075801128a84400305650382080d0304405500004c2c1114886001c60343d01e07590741c81c40e00e00d410607440340c103005804850409540f102e40c03100010b036074400f2080140303081c2602d000d004d0500354400c01600340c0c2440c080c3d40c4482004415071701035141c1a181c450450712490420700c00715400509940800044403c0003c1c1c0302142c201300d880d280800c00005a43e824107018021440c1054030401040038104501000013603e9001203c0320160545066000440f58806050f019480e0801c48078a0440040039081d00c400e0100050080300750858082d05510922828031050310011189a4042514100010054907070407020941c000d10a140010101103071400064 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 282130638 1250 282129388 282129401
    0x41e0303050f090c010f120f020a0c0c090b0307142419080402010507081e031008070f050604120c03080307120c0c021e031207060507021006030c2304 66
    0x100000d448009214040c00b41c007140030340101c1101d001d09001100f000018000b031810003182c03002c00c5040720755141c80510b00e61000c071311500850820365803401442401000415411800d9459011080e000120b071102c81c810750600000113000351a01525080800d5010700c04001c9060f0072001070750b00c80c9102045646404507a00710100200d0701c64030360030061a1170300b0101401c1400d01001c0b809100260380c100e0180c0d136016a02520481d46c80001b0f020700c4880c014a000c6050140d035001c0140a00b091200c0500b00030b4503041c2088440c140e540365090440b02000340300d41500b0943c10441884003258104506407824042d940e08040d159690ba502051941b0460b0100c000440050318440d02100a00a0318062251403902c403001050540004e00105000c030042d01c94a40001d44402094a062240030340044c1120f000703580300d40c40b5042900141c4000c03651381d001400343c20703072071400b6000302d120782403d494200c1d03a144046801c1030a1101e080e4800100304010304450092a145030765076000300e2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 282131888 1250 282130638 282130643
    0x609050a230105090112030203070f121d1c0c080d080609010b27121c020115030507060f0e04050a090507080102210c0c0a060203070e010f08040209041e 67
    0x3010500490003980c1c01e03085003060000700300d0032001080700395292040359043d210b20042001841005240c1603165105440d4024111569003201c40d00344100b00b800701090450b00d80b07850460301e0320000f00801200b100c02023203a11a240c1c9030142d4490010240381c00341c45111f0b0508401c00c5454890407442c0c0111020000c1c0001c842d10204040303802d00d584000d00400312152464140840040000e6140100464013600c05c4a40f4030003010f59034500e4000021015500c080d2401c0c141c2c04011540218040b014240140d0f00f0000405003904c04490b680c0c2c2282c0c3c005025041c00703400c010f011505015050560300030408240340c05950341e9618494180104034844000840c44018542142000402c0d80640c1175640b0510168032000050804950901032096032052103a5400b100c1080d20f000d407910074100ea11451542008100d9158021405102c1c0c540310034a942104500448040c6810080c081c000b486200215005062450055030050b1081c014042c0f001c0102300da4010341e001e0800203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 282133138 1250 282131888 282131891
    0x120b2e0e090a1709210c01030b040903080f1005220b0906010f03020703050f03130201090509060d0b13080309070e0112080a03020c070305012409020405030309090a020904020a030c11060906010b07060609050a 91
    0x381b08540e0503116105034040192400d00203083c2c207441c003a00110340107188245002039100005c1241040d00c01700c1c0b0180070b005010900500c100d03060b07541c902d00391801a16240c0d181514540300c51802d02a41403050105941e541d00312945101d003180650000c0b10f04400b48030041c46440600d074500006940304043c440182c820107021b9000040c003200140d4060b0f40940c41850500102d038880303900d6041c20742d82200d4840c080c0d441e2071445003000d0f0410140544100c3c8003006001d003001d00440c0d80022500c6070140b100603640c0362500b101c24400c481710020554542048003000aa0003900a040780f15250750643c1c03a0540c0d25202d040c20b6860b03d0044004070001540c4400540360b51885540240000f568110b06240c00c140c00320b0380d05d06c03658103068468a0403100042c0b0724071064040f0741200002900a54944800400140160a408008001003416052500005400015124130030300c84080101426464803070102800e600c10f902c1502c00b40c0c0c503044081280300050041e02d0007680303814070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 282134388 1250 282133138 282133153
    0x7120203100c230c2b09120308090c0a0e0925061b080409020a081510030c02030909010e090c0604120b2e0e090a170921 53
    0x105070410800c010481d03082032800346000001c550100d550766024102c0d00755103050858100e04002c0c2c0e40640480001c01d4403074400080c10100050f010550041d0010013240500914003d003521615007601405540c80800c0d130360307003010920400142d41c102e0b0540b41610f1407956010040782c0d580030b45030419603240c00011300780240300d5000c101d12034960b0041042191030150515030006103203241e10a05040101707a4506805120020910300300a56015007480e41d42c0f0307540c0170361070041e4006101c11004607800c440003074940e1010f0180458032400080404080814941c0c0030360003040c00c041c142c8210b22090201c04513a4a950301014060100d01c207200900d803502c49015854496201c0046000c4c00c5c0a00c420051404070240ca5a165544281c140807140d407004c0200305541c821283e800c124800d000c1e4444181e07180c01d080c038016070345c4c1d5512001303080e61030f034400031742e18458140000c29190307400f600b00400d00b005401921003040c0040c08035142001d8044d841121181c40c1c445840c0a420403039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 282135638 1250 282134388 282134393
    0x91a310501020307020c12190602070305090901061d041122051801080f0d12020a020c04090609050c150d091b170d020604030915020a080408010b01110604120c05070302030712 77
    0xb00400103031400f100081488e400041084100080303400c50080442d900403400508060107017050341c0082d040502064800c1d030303640d0307c010311900c911005103808a1000b24005854205806008907040f41e84480e946802920481003501c0001c549201000303001c058030206a03541c900b4005a01c84d0150380c184ca0095050003406810400022030300c003482e0b4008880345650503005000701000250007080140c0314004404160705100510700d2180e40300789800d40040800c5402d500c0707480094020011a031190100006122990810711680e110040040c0a4444465050741101e188a442074807030340410b69000d60448801500303600001024650a08444160300040000d4580c4094610081c0000d04158a000c0c1ca42440c2c0e020b95003035601c2441403124841d000304084007405910804c0c4c9a6202c1d0b40c3d82426000300903034a541c41c0002c0165481c0d00e01a100050414000c5801402c882c82480c0340c40800e44100e205080115410700402c2c00000c0584c1d018400403004044410340311070b0029091 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 282136888 1250 282135638 282135649
    0x20a1205090d210902090106030c030c020c03030409020a0c0f050a02031c1205071e02030901030b0a080c041508010e010b090612120901030905010609091a310501020307020c 76
    0xd0048440c0c0d400079000440240d030183c00c2460b04001034032036044910356861184007070032800001a402c249070000000381142e0581c0881c0705512156000c0160801182081380c0300c0100c03040c0651b041d0702c18001801070720240d60040c03840341014213040155000230303500c4100003004070a00740c455412148182055003000d011003141c0402d404044d04aa413401c0002a146e07a40c045080d410b481e40c0c40340052102805040c0e47d002021029060419581508100035500d90010300c1d100e0020341424254503182c1025440034003902d0010780a080084942030900009049030109554803d054007400698400c4c00c2c442c403640f5020002c0003044011104050181040010b0240ea01035468001d03035038140390021030707202d018031506030421f56603c401c00e00480142240700e4000d45075528210001a07a00c3e6154403096006200d82d00030030300341034403a450400301d020480b1031034400e001c014055030b61284031122403a01d4a400c801401403800c2107031107960898100b11400000341c0c2c414181c540e442d1038403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 282138138 1250 282136888 282136891
    0x302040c021e0a0c0b04030b0c161a010501030608030705060a0216021003050103030f0804020f012706021506030a08040b03060303040b0309030918090706082d0103060c0306050607021207030501020a1205 89
    0xc4040d03031b460b1030b02d1640d07180c01d51003004110140480b008650141c074554114065829990050102920228090144142d1080038400c10340802e2a04e8400165210044161110039800102070301441d03503950b41d030760043e6002900d80001130300c03078854141c0142d030307030040d60000000140e400061960440c0b50103040030b5050000c00381440160b81c100001a96040c0070408402001c3c039000303070760900040540c001000b08100420001a801d100070400315400a203203507445002d5106180d4a44581e014191981190a400b800c100001c000511000703064200564100401034212071400d81c1e21003c02d442500181c5070039040d5000040c480025141114400041c0c6008405002e00e43c07e10340401da650382d0592140b6000d10582100280410000e59500d6014401c0c0c40381d14000a0b4004149007070321142400708841d030a20784825a019144a4820b02e011b039100034090078075003001d9808000342041401014441807183c10b60110014900f80007a144d101c02540b02d51949200c0b008001054940 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 282139388 1250 282138138 282138149
    0x12060118051303032d02070b15090718050405010312110106061e11100b3a020303190801171f0207050304080f0a032006010302040c021e0a0c 62
    0x101030521040750701c0d5290707182ca003d5150900207488144583e403048003000130743d032440b490b04c480542912480160340080076214407911014849699950380308021401d082e16150308507100c5000201d843d40603a04511600f4105107001003020b55443c0001e080c0d079000d820032540c043c0300c101000251901b055280840c145544002e108603402d004008006000341c50f056510102d0300080b105a02d8050001c4c0b82a8071001810f0310100d94103101905d01801c01011043e0051070101010803c0305003903560782d4003400e004210054174212030894960080c01168042e60305020400c4904150001d140c0c290410700500e85490a481d80360141c1596500b440c0c280039002e641200d404041511000e082048041d41070035001622900d103414503034a14010317900684214410401c034600c80000015031340c4000c920994034103880c0c42001c081a003d482910040d000950b20201c014401071030240c0002043d0b125920440f9050915400210880c1c0c492040c0350810360410ba5502060004082d884400b600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 282140638 1250 282139388 282139391
    0xa02091509090712090611090102070e0c12220f05060105030109110409110307091a0a050907080403110a0803010302090c04080d1404030812061f050702060c070512060118 75
    0x2412900822192140100924104492070315503004c040090750042c511036030000350070001d400126003c060568050000741c0d0141c440c0c040009820300e40c07003d20b5403040d8055201942050300c440501c008031070313002c0c04c06088640f83c0d10703054010b801645540443c1c5d50240510050b42e0b540c13818000c0c2051810303000b43d402641085070041c0481c40e410030b00c10318075000340d40006010466003440400c01100c031404940c035018013200010000b1280d0803030800030b0b00c4c0441c0c12040034800c038100000860780b0f108803504800020002070030140141c0076035074054085e05116500d00005059030781070400080c4200c51a4130048018015030414051150340700d50344100e214030705810444402d13a5803a03010380d0401000340101c4000312109612003030728002c1d40e000c0c102d583c407070039892405111510100d481500071004451280c2c5a401c00d0464401c0c00310064441c64a800619000d1180c50381c801c01031030341c0318480c1c4100095180c035010307644030304840c45002905071541020309016145128040016000307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 282141888 1250 282140638 282140647
    0x1504170d020a0311460801080106050406050f01030216080a0f140403050703020d0f060606030222030206040b0c01060b0c0d08091b12011b09061701120605060d050102030a020915 78
    0x500c2043c074600c1c2d507100d81401085d66050340c0d010002420b03000782c0d003803129159800003034540300707403c1449903041c1d6403d20028050315803180c1c140801c03115980300700c40d03108103044131044540d4017030ba005001c1c2c45c0082c01c00d0b5070f80c0c1c24143c40f008241d42c090003607034001403c1c42031640e42c0030750310601e12001e100202141d540780c2031541e01c03100e0f640e1940c7d000183c416542203401400b000010418200c4565101406210031a6240e40140080d0850000151000542c488080118040fa183c450540398010701240c10241401074201c01d0741c00c40d2940d4000766503155804150740407102c015200c4a603c0713500401548220b41c0e40200130280203400d024590b44017646100d500c01c0d18622080c4800000d603010101000c00c00782150252440c803040700d1041c04208200d02e003141d84090203000b40c035426258000005003107202d0404c00c100921914291034060703083d150000303035035402c0781d60031110042c440d40b0903c0207501c480e422030740245c980001d800e9001032480c0341070900c02c00c0b0505401d0031031f102d03c1c05e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 282143138 1250 282141888 282141907
    0x4150c020a05040b0d0506010e041104020a0927050f061203031005010c0206071b030203281502070510060509010603020903030a030e12041e080303010302031504170d020a0311 77
    0x1841c540c0a050300c52502c4451001c85612a01442d001064200084844035651041100010705040d5801e4900d070382d11542000e100e040600807180568200ea03113518803a4079213110a4210b40c01c40f05255940b1511945001c140c07412401180d000c0c030465140005142007031820040a0700c3c28507041070554100380300b0040b41100c24000e074412102d080c2030820f0382c0d03002d034400200c0910030140010514110b49140c4141d14020000315020343e882036040b07410000b90081c11000c804a044000c0040b1243c0918481c0020151030116030a000d00d03c60260419000340d4910342004502c500301203260b80e40b181c08201602d49043d4180c010440c1e8281140751415850100b1f40fa0310401284c0c03024143c8038201307100301904c1000300c1040001582d0440c2e4840c0c0d02c60345c1c0c0074403a800451280b0300030035420300d0210f60faa03008421a41225401001880c00784520f0702e49a410301802807082e2400031000f080c0b1004202444001d2205191800c1d006a440070202005011214544501c512201e03003071010f07022 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 282144388 1250 282143138 282143149
    0x80114011e0e0408071505042402130b0c07091b090f1505130806012d050d1205090d08090103180b0a020d020412050304031703070203030c16021504150c02 68
    0x40140d0400328540da100c006041002503602c4081200450074901b07c00c01080c05403000d261410b50320302e803c40a0350000c4042000080e4001c103506959036580792181041610303e20030003091001d6101c2c00392088c2c960b441c0c8142c0115200c8801e400c104110103007120f114241e005030742ca40a48013800c1580412400c045800b080ca450b01404c1606008000400c0c491381c00506220f0802441184222480d660b121042c46c04101e00343d101030404000442c50ba880c00302e006141c00f006941020f00f0790356426505c0d4844079860b0100489001c11300004001d0b101d02601e03461840050180101e601a0340c44690400050440c1c0e9030405000d0844584030581000503540f2070310940140840401613141e540004941009100c0e90380503c40c0d100d000c030380d600104240031002d40f048034082c01e4009812181184102c045100444a100050b0401c0000824200c0b03603802038254281201d02c1000001e040e0b80c04150040400c0c00c2e030510042022400304207482c1c00c01c000701c560201e0352914040d082c200383c7c0802c0303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 282145638 1250 282144388 282144391
    0xc0203190c12150c02100c030204061106090a021c0b0903090a32010905041d0f06071e090509190e03131703071703010602100c050919080114011e0e 65
    0x708044d10392409103003aa108001d881c0884000340d40400401f41e07c8040903000754024401c0901243c00c07094020000740010a10a2149501602400180015034208284040c1c16419044075900c100c180d040480e40c400d02440c071445012001f5030303441c20030b036042120000c09580910800d0f48892100d00841d815a203481000d1224050800d004074030500069030840c065801c0b091b04245400d440a902c5804650204c0c2000405c100307560344401500a015142c075011148240070500303001d400940580400708000c00041e0624100000c00e4407a400514110015980020384620444510310000301c10700c51680e0680311a0002c524100c1e1401710b840026140e4440c120a03400c11842002c140c601c10b100700c03a4855442225030441103424200c0f0f1a85410a000c1e000040c4a110074580041c40c03030307200d00d415912243e2112410715108504106400c5103c101c3c80241c0b1481c0c0100040c000003d01072200351920b003419003503156062004d01e182c1080810b505c0d101100000b00300f004185c0030320021a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 282146888 1250 282145638 282145673
    0x204110a0f08040501020d0e1c0203030f0c090d0b0a0207030206180703030c050f19060b030106030c0302122803170708010303080702071d0603060f061e010c0203190c12 74
    0x200050b41e51800c01174024010625044441030511802e0818500085110807540d048034014400e00d04064408a0b920b001c02c03600c1c19038044114004c12032907280200603008070f0f200100707501c03010b444035a140c100554082e10004101d64010905804168050000c95402070010032400e220907140010143c0e07425443c0b102a051008040c00901882401c0c8000844a5030040403110b10700380c41c0302c0c036001e002082d00007640d40c2890110142d01924045c000c2a08594111504070826411a001c0008600c1807042d4801326204018040c03448200380e00d29869003040740b0400901c00c1c981e9081c00750043c0e06801000c040f0000c130380b041000700c540040c1c40b02d0543c0d0305840c0900c1d5a07580c001c02686004d5880d0807600706880c044800681080180e040d06200c1c48082d01076580b42e07101d0420b4480ca090082e01c403070341d01c451080103107440400921442504c0c0c200500d042e40d0340c00c065402003805e103485d0105402c140004034a8000038400d404594000800bc1d01c180d10300710040641303d8001c2821841c842 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 282148138 1250 282146888 282146897
    0x240909020c010905012d1404060b0607050601030c09140f0a090c0b13090f05070e12070b04090504140d0836060a0c0306080303060904060603140a0204110a0f 69
    0x15016415000d62001c01e036251302c03200802c0018800b00b000300c4442a40c506080340440310342c50320280540240104d04010003040221a069129640c0712405800582c1c001900000301348002c1c0d0208004104042c021800790312480a03041c101400304042c1c8030039200060100d0196014044242c001e0502c5961141c650386000a010304e0500d0000d4442d4000e51000141140104082100504071081201180c030103240800005850301c549409445046844901051b1030f603241815904216000a5401c2444400e07244019111071900d9840c0e081a0003c0d10303131a6540c1c0811080040103014004004101700090040e41c20f111402840d8a1004004000241d18020b098241d0030312070300041c62007800315000c000d20b024001c20b12031b618082211b14451060400d252030002c2d50291084000703a960f801302443c510758505091003656a806442210780940d103000010100320b000b140d5524400d030701c07400740c46c204625004210680d10400503000f181d60042103040201900520070070f1005845040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 282149388 1250 282148138 282148147
    0x1103010c080c070f081c050115050d0509070801020403030306031b052110020c060a050c03060a09050c04090c0206070909182003060709030b16051b0106090c080124090902 75
    0x81c030784070b411400240109005c0d00410160310840341001e45018641c420507080045030307a180c0d440070190f8003a5180340b000ca50104030f2000511b150380c0007183d12075030301c0b01104c40d82a61030448508903445584250b00182d0340c0c003018400c01ca03404114080c012613000310844610709200c0010007103081411400103a103800e42c084c020140d82400f5016103101030b001c3c00c5449408100e851503d07450129807641020380b512000601070251a0300f5280103845c05001e18612904220110000300030203822001822003e01001a0030b070068011400c82e0402079010300f082e41015400588042c0490304601803a070b00786229000711081c0c0002441d5020b401101210b80380a80107840c401e0b40c80b0070b1400f1034040c0507907401c1001094120140604907407245190b0b240701ea075209210070500401390f62100025400700110344058660b54121500300741d9800001038007590b1808020122034800c561070000c10080401080f101020050500320300c200c0c905403440034401c0302c0006041d402c0b680102c4211590114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 282150638 1250 282149388 282149393
    0xe030709020f032403011104080c03060c0f07050109050703050d1202190f1709070611010b0603010905090712030909060b070b0105010f0c0203010501080312061219030309080a0c1103010c080c07 85
    0x501c404500c2005d03000f00910701002400341c803150301c14001c2070b03102d10851742031414500307001440c0c0d031080000c1c40100782400410b070060b0072140d20200058030f80e59210b40700c88001c108140400001103128000038040e602d01440058494840c00180e1150f107841400041d0040034600005421182180b0704540c0424203100c0030340340d4100400809032001d01c00000c0280000001400401380c0e0a903403034610100c0b075165815801da40c20046450341103c0d0501c01003185030700341c0d04001d42022804041c0d83e2071a49546030208203410f24001540000c00c0030100300884040791040c0790182c0014140345207042c219842e1880c5150b01845a681001440590b06c22040d11a045140e07000303074010000d2182c0c0d603480e00460b40e60382241171400d0060f242c0d140030851910b400155410b020b044040502004c0008a1170084030000c07418080c1c0505171035405101c0000d4680c130040113092040c0d2501c0744800200d0400200b8002e0800d1003601030b03072403d094180e205410840d0035a03c144561841d9030b40302c0d86031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 282151888 1250 282150638 282150691
    0xe0306100603150b1c0f200901050c060a0b090105090702030720060d0b130e060406020f090409050f0f0d021f06030609080703080a0603022209120e030709020f03 71
    0x4e030b0000740421404156886500c29154000408420892003880181c0a0345c200904685050006c2c039466801032002c0341c0c0309144036001e4210070005040903410000380c003401c9400d18804640821000f9070742c105101c51407030301c0050113001d014160349141261801c241c2c065607912a00320090b0a03551400803691042c070301085d5134081c000020f441980c9030002c02d00a84040c0c05841c1d10700e03100310843c0710090120b602c0c3d880f85414040070b003001000b180d155625501c0095200c2241100c6140c810045140c90361181d000302c00041c0e1044008041d0074044692541c141b02c426803840c08182c01280142c40403a42c0001d6541e11075120701c1005034410089040c078001851694401040242003003202820301c40e10310301800d82180262a004507560303d100c0007400702d5505000017940706c200b101440220b10340040c209010348010780e20002e015480d5464401c2c400524054010005035403455958a0b4142031042e5401802c08202c29401c0c03641c60004400c46020060407100000018000110500f00c0c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 282153138 1250 282151888 282151931
    0x902030c0a0320040611010b0d02010e0d0609170c0f06040c06030e15010e07140a090603020307030f1103190203011511070f12030f0c030e120a0212010506010e0306100603 75
    0x3d484026985035a2480080c240c081740e450610010351a0028208250800441d420006a4165500702031201c00004000c00c10350100425a44246d82e2201e110001d00003d6895015010245100d034035000401c0100c1e10703082c803e102d003000c540c0061050000041c01e45110600340d0b0b0240c200400c02c400d071030a442e450001c6003440391101c0c801440c000103182c4132030030841d80643d855a84051010310b410510f14064810040c0607000510010000c2180c903100f5400385421444514003c541c405040c4001c070143d9030b901c5100400c50b200002441141040f00710031b6030100340d000c4c038207500790341c5807003074520603180400140f50610415030307200c805600c1d05201820181604008405440e81ca4140b080c0c803149007105d044000c19000c2c5240d2400034007408442004950541e2158044500304080c804043c480d040600c00c1403152076034440050352503414460000c0e090750000145841c003100014811540c9104080c002c0c0c01c560309020086443d103040906503001d40c24045981b030081c0f044003600204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 282154388 1250 282153138 282153191
    0xe0604090501050406020a0306080601030c062f0c09060409020607060c03020c0f1606300f11030f060409030c06091e050d020f06010b091201090b0c130902030c0a03 72
    0xa8401003001704851603024020710550799034200907468884210569803082070001502c02e4040e2802048030364442e040d0440700c41c7c043c1c1201e0010140340002030b2045c08070301c880005140c001e14840c503c103043c218034490f8803007011541032050b21000d4010842c903106101300580581d840e800020a4203002c7d404440e40c6c41c1139442142c20600300a0103240d207c181901284444540300440010102c1c456050107200410991035002d2004880c4d00a00340800c0300c60407400c0c01351311142c82684551861140c0040d45407803005041ea2860944002c5410902c000c04071807040385086440404207a101c04948200c40e441480010b000e01d45003000100d13000081c51350095010407040020402c640414030034107490440e02100d010080e0502e1103912000240100781203000c050003946002d14110b4841001d030300b02c1c0c100000360188142c6031150312600c200c0da0307262425000650011002e0044032004014203540714110b0a5080a0406203060301c101c00c2284205600c0d82c2091141d000b41d550300001081c3c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 282155638 1250 282154388 282154391
    0x100f35150a17060606090609010309022418060703092601050c0702010809070806060d0c091401051914060705010f0c021e0c06070f05070b0f120903130e0604090501 72
    0x2542d480340451840085000300c841801090041111820a00150b8098400042030340d800d188a070001100184007a80060341c0c4112010203034842e240e01d14800402010040c0b1040d40c1d124406103400c1040c1612555040c050441048038001007a400a410b105030380198411583e0918001f1000100c0452140c020249520344824819980740200041c42d45034400e80b030f00203240d6510143c580e25031400d40714054068021500080395450014040ca040303503c500c00414006846110010443c1c0b1035810902c0381081031401401a454801c54015035005aa0b0a90301348904001e0700c6c04800019907081c81c01501e001c60102c08101080d00f04040c1580e046c0c8040162031901c5000035507944c05103605a12206a551500925001c0410014110400038142c145018038594910590404c41401500c0c603008018001c114040d503c00203004041e85c18550917191040d288440c44000c601a08121107940f080090314103041c43e01c40141c0031500342801000305550703194003240141858500081165 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 282156888 1250 282155638 282155659
    0x30406050c0f0a1d0616031b140a020f031b040c09030203011b030f02130b0901090f0e0708011d041202010e1f050c03060d060515100f3515 61
    0x280d901592511030064221881c840121003503061080746e108a50b04441d68000b613a10240111b4001d0350322a44138503000d1190403031501d69231070f010840c04110081d802950012070900066240600d92000040b0048018103144400e11031014001d0415024041c001c0342c442e4520b0b00818020380074080159000b030001d0015040c0310070a104111842c00180340841c0c980101150107e000c2d1080e0303402c40380c3c0306a0711050242080071105154002e400d019040203448a4041501140e400c011001000b1411807040f10b420803400c00740410030305070051031003868001000c0620016601c00160882d81105200c42c9603103040c0340403805011060b103007010078807400702c0203c00d23442c1d40c140c4400d030000708100400136a2141d030a41c42d17841c8001c0c4e88469000c00c5110301c040114805a129a801c82c09902a5500801d050004a80252000d18100340400d02c0313120504600d0350450400c42c0380000018207039070007914484c1e2038a6075002e1540b01804024800c8001641b11114441d0010724240040100c2d044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 282158138 1250 282156888 282156907
    0x12020a020d120305100f0306050a0e030c031c05040b07050309120f09010e0405040203030a12091509030807020105040c120c050910030c060203030103020a030b060f100201050604150803030406050c0f 87
    0x442e40c1c41e40c0000c0000c0d1800c800180010310301202c1704150b511302e1a800f1036181c51500c540c0050500604007040d0b60340d9580d01e11030b0049042000380180e5500402a60711070038402a075080880c1d50004490f501414001000000303802c094803158499503505044c1e4591f2986c0e8056890312290040c08010380c80009014101c09803603002401546409036509152030307000d003091000342c2e401610b000b0b41583c400d00c80022400c1c05424000d8150a504100082056054541c8010421040e0b04512090340d904111030506038490721048d44608140000d015504080c1e440318030001c510720800101c65101c020820401882c016032000402004081050318140302c101e181e120f808a00c012030b00c0050034100041d41c94004025a8100d0780c00401d614102c0d442c5843e03030051408010007080c1d00103200c40c440d50480ea070b96040300c4036815142c0c2c00000d07186480d2091208961410510151211f0310344010031550400000701c0394090303400000811541c450104462160080003403590b5081004249101c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 282159388 1250 282158138 282158153
    0x1b0708010b0f120309061b0a0602090112090f0605060a090608070e0106020d0914011205040f050709060506030402120f06011d1302060703080405070b1308010e0102031312020a020d 79
    0x161004102c40550000d0b00b10410040c03001c0c0c000c059100300c0c0e0828000300e406850300d01c025100c4411031030140c04805c2281c141c11420400002c2040f00c503682c1c082108003072075a010700090340d800d003060000c11503103900392964528a103541200805072600e07100040e1031510f500c00d4104c02000b080d1024003d1603100e04150313403a141c01d80500c401e20800034000003601c61001a080c0314180d4140c850002842c28056074901391a20a900e46040c80712807100003030045801d00c01c8510480c095850501442030380d03d00107040c103429900c03807003400741001018015580d0701c0d0116500903504641c0a0a01c220002680303080c56030704143c0001b82d01455000140d00303440040301000c2008000b0381101c1598036103220000b10458410003035000b41e420311080d40064051250540c201d801101141c0400795600401c210170703404005004c082c003038007102c2000340d207209000d00003052039450b0080d030862902c108030030310040d290b6034007070300c002d40e20340100309210300a001150509401801080320b43d20b15091445 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 282160638 1250 282159388 282159401
    0x307020d032307020f090105100507021807030f0c08011d0a09050304030b070206090a0f08070302070801021b0c0f01170a0b0d0f0506070e032a030106030303061d0f0406021b070801 79
    0x9001d03032030700e12504000c0e203001b030682e506070b650042c1201c1a030803249104550f03a8020346012600150355050481c2850340c00644a480f071501c540e00820ba621600a4540599010041c0201070003049001401281c261a100c1425070401a42c0950300e5602e64820034041c2541070000340250000044c04401d100240101c58400e070499000c4801c1500e0704941c1d1a944d40740c1317040162014088004074800201004000c0c000b0314000d04c11034a070191036141c550700320f900c44000a56601c15584210b0802c1000b0300c1507460240b400c48840c025400c0d0980080d082e035460f0642c900c011514800001c1d4145459803201d82c40076005484050300811900d0455030500802c0c8081d01c00e44074410010740803034420114503401e802c000d0043c000800b240494070621800d82300e5022146c0700038909100e0107403000d1040c0c8c0000c1d0302960300440c0240c0350451080e80c2061504094242c004d4000030401050700c01420582c1040d80903000607030340e01c8060034008009802d03607081fa1140c0565003002502840542013030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 282161888 1250 282160638 282160643
    0xa05120a0b19030203030906180a0b03060a080c030a06020a1b030e130203090c121216060c0f0509100504050d050a150207020307120f0b090d090f080307020d032307 72
    0x500145000b45084001c0c40c12910000350715910801ca0b41c4420f040c004068000c00001084000000042e000024040d00d100e8104801d50034003c020401d8074509001e102006121300710141204203501000f20741c4480c026540600f500d0780000e0f900c002c9034452080341d200418250541000e150651800806000103035815901c0303121b49440c0b80610104a20840740182400001022026200810311a0240c410105500c107801541160040d51001c0340003420390045a05c4060b181c005503191000498100151600070041c2001c5c030706030307055001001c807145041300329201c10020340700880c02c0303905204541002e0307000840706030110204100014441c4000d48560138000003081d0788141d140883c02039050296040d448001e040000c08100401a0000c40c002d5a090040030220f84503090101d10545006586602803005602c103d80d0000600d8040c0c0790304039100428a19007500e403681e83c002e20174007911910f07580c0c000c3e004245c062a24011715210708c00c026440100740700241e04e059041032006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 282163138 1250 282161888 282161899
    0x614150d02091312030903021506180c0d0906020d05090a050316050328030b0405060f190e0702060f06060703050a0e0a090606090503100908031b0c0303042a06090b0a05120a0b 77
    0x288143c00049e410920702c20390002d08008c015510724806036911100c09072440c600380204100b4000d40c0030311801403d110901851025a07524010b812400445000030110080c603086008041e00141010080b03480c0c23461040501c0280c464941002c2d0f09501c9101542d40305080d901d40d40014840c0050003203e02c04405841c104030024405091009030f800884105034404500c20011419281104591803201c0c9013590304008651550302035103207a00c0564550380541d004500700305081010003412544402c0039242c89042841da590040c080f406141040400d020300b446c8000056191344907900d00900b4412800e0140650310200a8503608240c0903a90080c0550800c000c00041d041c05418003180e0f104003518074658a044504c0268407004e0f1070018040ca04000c0142c050308100043c40c0580d00a801c1100c250440800510907070b8206010340a000150ec40100300f1283c02030301c14000c03148000c80380303940c83c40804c0d8112014403034130500307500d011805020b1100340d2a4961040388002000c2e100d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 282164388 1250 282163138 282163153
    0xd080405060a1a040c02100510031704050d0206070516032006042d0315060e0702060f1501050c030f0a08090313050103020f0d090614150d0209131203090302 69
    0x4541c0940d40c600c0e980d43c0b420000b0141c256424106940003a41c204e40a01c152051044080000700642e031081d214034990040306a03041c01803201c2250903081d000c0b06901507903d4280381401052042caa803d8020388600008140102400800d024540d005072000312001e220b00c0d1640f4180681c40c60311500c91030344200c0e02d000b03140e1070f041290072502070b200881408449440900b010100280317150403040c803903020301e140c000700103981c1d0300314440780890003107001c980385060920090350001c001b001c01c011540030005201c0320011aa180d81d400010402141000c0740340c0b0700040e550f610074403404003180d1100040c0150034200100103000d4103013050341d411401c0e44500c01030a580703002c1c41c11240d89403480b00e80200040e6021764000c03c0f14045000483c3c0c248400050050226a8a110160303120f07034a0307a907540c0c011061800c841c1e070710a151a00481901c5088000b04030700300c0d4111002806001c4400200c0c491480700c000341040d15a014450250704414030030300801500e02c0c40030031405840f5001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 282165638 1250 282164388 282164401
    0xf0a1203090f1205090a08010b0102011112040b0402030c1002060604050606030103031710030c140f0a140d17041212020d080a020912030c0c0f0303090916110d08040506 74
    0x1c0c03841000d0300003603103004020075612260f418844540c0d01c00c0501c00208100c24698640e600a0380c0102506000014480390102c000790a6500380c02d8440b0b2400401c11188440300381c40c005850300550020540798080d6160300c04030b0302d02248980f00940c00a030890300c0712265980011031601c2150183c03414809030700c0d040244107060100307010041c082126440b030780799080343d10110300354041401c083c0303813440d2a0b80703854201815006400c150000300b000b40000b966800c090f4003007011100d05076012001549412031000781000304084151140d0004207500d4240903208448161040c100c2000944e00d0350780e510369104600429a0441f02000307400c010021b060300100d400c0003240010303103a255055a031b4508110003540800030032a44256400c200f4107580c0410805009200e140c0320080503460400001c02140c18050b6181512952041201c03440545410380c040b5001107103003044010340d00403200d050b0380019032074900b001580b04000d1f041d248641d01c03100c054055406202550019111007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 282166888 1250 282165638 282165641
    0x5061b010605181311090f0f090a15020d0623030f0123061201050103060e120702242101090507021518010e0717191a180f0a1203 57
    0x282e42034000c411003c0001150400e5410044044610420342902000744000004140303150964600c038011090004104012303030840d1005422041c0ca60040c01d000d0619a10b451a6121140e41080c02ca50003040c011242ca4290f0404000f900700310381010001d0200007a0b1006103c440549248284030f00040e400b195001803082c41c184030310484402c41080c0507124080750ba030304090545500300c142006036010140c028810103020b144101808501c41c0c4088000c2071414141456100b0200402c01800f8016680e41502076041c44203030741ca0a50300c00d039000081c0d840d401118080d600c5401c040f00000c20b102c40382202c250607500c04800402903130b01d5a80080b40d403040440d03648040f4894500204140890413008800c400006000110301c5545071701100b0b040c00741950244426450100030880712020601404201840b0a030303000c051031209407140200c07804041e011283c441d07050380203d06404010f040074020a01c618045810340ca0104100359035074102c0c95015509080c1003041404158030a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 282168138 1250 282166888 282166909
    0xb071e03080a021813140108070602100c0e060a030f061409070c02030c0301060f0513020c06150a0e0103030f0806060901020309060f0403020a031527060f0605061b010605 75
    0x181d840781d0301559480c2c01e0200951141844c0b0302040c02400c81010150740f004848031107600e5024020508603007040d0100480401a04800281c0d0400c100601c2041e074002442b0002c007005210100e20740d030b0100c006680c9202c01561907a04203500080040403260107410032154400d5005040060300e5036015a15800400c11030250352112581021912a070f103c0c03009400954001829540301d411446c1c0000c0c01c45000750f00c01307030f80d0700c07100d00c000c02240c03034800b95080c841c47c0722590a514201c203d080854840c00014041d0301d0103120741080e413000307484007036811000d0100080b0302004c558407418042d020342c0206078050f0001b0148000030303180341030003404e858040341c068000f50700700110682002400c2d0050400c0940d80ca005000c00000759894441440095002d05481c04041940100c980309541070301d0318214040000f2031140005e12104400380b484603410540014241c6402c3c82c540015101546c0074540c014404103e104100820380d66101310910000000c2000c20303a50820f120100f00c4c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 282169388 1250 282168138 282168143
    0x302031312051201083d0f090b150604060f090e01030606170106080d0507030e3304030203061303030f1b020f010e0304060503221a01050d0b061203130b071e 69
    0x8803101c4ca41400c2003109403080c014214054812462251010f46d60125100c080002021680740d00004091221845006410500ac3c20444095540c0300e80490507502c030340e2082c00c04114183c100444107a100d065070300302610200742c0c4003800b540d407401c0c020003800d03460140108036695501314400b000700510070202150303c880c019108180c1c40b100e0540d8581c0001e0703410740c00d00052420358030141e0344140050307240c0c00c00d00c10216150140f100c510340e150f9001c9280d91206030381c204014005a41c0004507144d12055140200b8003a0b002c9280440242c020303a040120028142280140718045140c105404801142e0031581d482e410001114242c5000c4001841590802c10051003014410401164400f00460110031300d40201441c4070b00d0142403910650744090045516841010040006401841c04584058901940e5140d94001c0080949054801d000c2a5580e040300c003002e005585591880034444600e59950743c240c0d581d0365118100840d010450304518150b0303108640c0304840d0154 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 282170638 1250 282169388 282169423
    0xc03020702011106060a14040f1404030206010f03050a06090f050102030a0606021c0905120309030708030d0501051203033c01030203120415110c0901060c0c0501030c0e01030203131205120108 84
    0x43c98203840b1407441e411076101f01d070481c1d01e0307610504d50010303e4000c0150583c002406140d0b51702e0641002401d10806802c14882c4002452041000c03440002d81200d0302078200200248600c4a0714010008903c1840c0040003075002004006809801e584003a044481c40c0c3c00b41c60300088291200403034850080c0450010070401c800600450425a100100050455040301c2c41c01c2e82960029103406501c0d40000015800000d0703201c201e81c4240111801440c0c00d032508a008000300d2980ca86900008104041e00010303808650f2006510f19903040c80724019105003000d11460785100c00161800b400f05a00034800d600d04803105111160403141210410000108443e480d04000c44264224440b20380261003104180b040966801c2d442034001c0180f526031107504540351805d28046c04690344a94181454040030f0640309420013220400f0034000d10b4011303669135403040801201c25080c80c1c06410040308050154a41d5001001014040b485142003c410303aa86c007045540e4203e060762055400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 282171888 1250 282170638 282170659
    0x605091e0603070308040e0a1802010f0e0d060507050a03051806060d15020310080c090c090f120d02160906060504030609060209030619180c050904080d0c0302070201110606 76
    0x5180d04940507000700d002025070f01c00c103a0f01d8881c00c0141d00709030420b911035060042400490360142c4a00011846410701222244c06903800182428880ea80c0e000b003488020014041035a031911002c032342096000508014034200310200620b40c1d0085050000030901e000c0c007007200300010ae140c8941601c111002003941d66039120500030b041c0021a000c403081c500c4541c10125050050000d1841600c042c83d507400618540310343c4900d4203102660450084030103106016000c20743d0012544c0c1c500c0f040c0c40021503442e055010807505ca2116054900c540103007048043d00d2540403500031401920080040ca0442e01c54085a04699540c819200841c000300b00401c00120b06401c03034103802d8041c1e18014200800280801e00b0a20201c804040f0003800e640c15a880086511581c02681c5099551441c50b04503a038403000ca141503409a07a10805103000010104524801101c00500aa0100344400c0e03440040113006500001c6049000c01c0039a10081f030390540005120303120b00c1008040700c284 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 282173138 1250 282171888 282171931
    0x41d01020c21090f060d020a08040b060d0b06040507050403020621010b120103020f0a081b01110309030717010603170306100e0105072d03020303040611040513051f0e0a060509 77
    0x11301c03034100d03030700b255007400a185000001c0c8040e01014020744c40d0004985040d14000040030700c0240b0a0f8803950440400304007144031410301d076621100554000415032030705001920b1501550784001d5001d000000c40c06200c0d1101d00000070003241c0781840d030171140d89454200c80399000e03040302500540070080041025103040b046905000a01605400d0380a80743c03081d072800c140e076a8900d00c0e1a450707031088a0041d542d1010060341d60581c544055414003020300c00280d00d460491103400843c02c81c5074480519290298090302c002c0d5406038550300c40101d1507180c101301da0001c80e1401d01c1802c0c09903404080502442c41d6900c00c071070503580c0901c7d0585c01d59501c8001c3c40d4130b08e0107400c0030380e5a580c801d03040444c4039400180035020344c009688034030f40b610700303034003503a410154084d0101c0d001d0000b080a92100044608903201a40c1c000c209a650f06a211405503200808003000400c0828006009040c020069000788034040051180e5910358007400407900d82668204001d035980d420880070b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 282174388 1250 282173138 282173149
    0x20060705160605071502071a071e02010e0c090901020c15160203090a0b03090a020a06021b03070b040608091f0e0d03060b1803070e0406021908010e040809041d01020c2109 75
    0x21061190a444a540d41a00723103d504001d801c84040380400c5c020020b444401c06106002e8600403485c4c0b000b44159800203000b1511860042031460140128101081c0c0740c0c44290180c40724a030300001150b440807a051002412214181c43c1da00070b41c240000301c041407a06c044119010150080c06007010b40d40390069002c0268001419200d41e40a05041400143d5861403507000403da00c0d8010021000303044150329040d60250401c5100e40d0110078200159120b1b02c0544080301c44608103021150359009815080c1401050403e140d0541c20f4042d20380030780283c0c0100c80e00c00c6090100d60043d90303000c20540880e04c039030040d10035458040c010200b96510803c2c0e2401100c8000d400d0740c0031150385040709045914260380c101c60464010501402c003c00038801d0007014410f03842c0ca01859407402040d05c8208101610250034500c000031302d000d0544903030b044440f008a1200d0100700000c464407016000390880740940c0d4040c0160901e0b15810800054500d5214040f124007602d00681d00301000f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 282175638 1250 282174388 282174397
    0x7020304210611180a0e150109080a050d090e090a060b010309020402120a0c021b040c0c0b0a051506040812031012050d090603020a080420060705160605071502 70
    0x8049007216a840008490b4000e05403825250b040301138942203000c041c9140c007000c010003240110120001006450a652001038020410100c002c0f400702544004842c001c1d415000308580c3d10070344c0d140714100314000611030310040f09951411001034847c081c0d42003410307003541c0b1501c444d0300141804d40410042e40c428103a02c40141000640f5009a502060030303030f0001a8090506146942000110b0a80e4010080121790030b102a003c3d40c3c000003d01c02e0080500d42d44c160003107544180007140c0328080c02601c12a035070001103500251900c0c661140c0544001c1361601000c8916902044c01400c01200f41c40c195200d82d00a00005090030407003a1035900002d10001c00c98815500000d4101400f03000800d403580070304081d01811130941c401514842d4103510a030200f61041001c104c03010b9005c804540c01c240d000501c0e1452100b8100c250510041e18484e10342d101300000b0b1844200000001c0b0300c080406da01242d022410780e40c000c141c6040c000e41e174024160003c0c08528001c2803c4550060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 282176888 1250 282175638 282175679
    0x206070e0301021e0403050c0a05030a1515080f0d0201060f0504020706111b0d08071d030a0501050c2805040b160c0b0d3c020d020a21020307020304 65
    0x18201411444d010010000c00d0f03080380e5581d0300000d01801448011701400c03414840545030182d840f0702c0c0c0b1000c695038031074400002d446980c2c0040305142120385604580c901d0182c5442059443e42c031400030f5516142c010025001610414140700710390703801070207100c0458182031003603241e191506007030001070740c040c0c201102d4040d40c0e00b15a400700a902c40140070018100b00c1c008640015500125103001944604002403002000401440c2c0360700048030000130410404001004400c9000701c0e10300124140300a1065080008006105031340d0f0340500b80101004554203011010a200201c0c40c01928062000044c8204000d114419000d030041c8034480290140d04c0350b0a860f074403a802210a142c116101d61200014005501c0829000b2401c850094001043d100141e648041d6404c00c03031403501c405141c2040c0c5540038441e0a42d410354007a000a01070a56580680e4030340149010100d000704845100e072070804094000030303882985d10840c50340d00214602400e205d2500c2d50b00c604050907 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 282178138 1250 282176888 282176891
    0x90c050c060906040c1706070c14060109200f0910090e1006031d0a030e03190c0302120303040b060d08041701060513111207110f0d0f0305070206070e0301 68
    0x4145800100a070510407400031002d002c0d40c0c140341c5003010643c1500e40c4801d113034802000c1c0ca0302e040b1070003007021508945242080300541840b0704e0482c2d141403240c480c50840c0d010b6034000151092243d004003075248100c5a038100d1841d25806d000c0454000c606c0c2c1a10780328030034008004035040468544108501e54200040300542c1d035901c05c04000300c01c8942043c0c1d441c0420041142a40502856030140c1c01201407900c134448005007159902d00210000e4100701607554080059242800040902030340e401980b02d030034a650616100c140c07a64803049004115800ca103012409010003603a0107030b80e111148680640381c4404014800f401c010080d5280281040000341103101101c020300b090001900204000c0e141c041003000103d2030b0000b11102e603041c1030038541640341407009c42e441801e40e0190307501d80e80c031049000c0b143c2100c42c2c030340c02d5424800d58103151441c0100045107000116195151650070800d92011000d4520960340c020150b4000c0020031034003030007880b40044da007134003900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 282179388 1250 282178138 282178147
    0x60f0904090813170d03090206090904030915050408060106140304110303281d03070b0f0903010c0c05060a110d0905010b1003060e0c07080412080c07030614060a0609090c05 76
    0x80440d52911142c4c001c20880d0400f41c1420003100c0d007481403440c0b0324040e0038100b141c640b80390040b5043d881500e942c9071040d000e000001c7c04060007000030002800f201035404419243e9524042c10030307030103130203080d0051090780000a40248141d083c1109110308801090031501c865481507800d0044034800c0f581800207002140c010008200c40010030f41400c40c8900040040000180c9440050148812a2042501d0501c000e031000a05074040b114001038546c0d848078140003840350790050710740d515890f50912144220144c1d0040043c8001d0b8020b00903107503940c4401c2410400c42d43c136055240c20003a030600092080c44460b0b03100401c080d0240c000031030203201d404001003184103c0d000d418042692031a0501c8054801c1800a40c00844c0c90003191402c80d1036200c1a848e40560b01c00d0070250004e0314141e104200484080e14400b070601411105d88607224a41407029001e044540c0340700f0700340d207400070300c49240a050540071640ca641300c1280103428140074402506413040d0403020310000300b2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 282180638 1250 282179388 282179407
    0x30c030e1801030210020606030d052508131e0501050a020118212c0a0305030a0504051003150603050c041208030604051602071e03050d0f030605060f09040908 70
    0x104901c00e003000e40c1c0d8001220341c154410403400c9051464140c045501060800c0069180003c205140c6c1c18039060440d01d40740210000030080741040c00309142182142d9482e01040001c4000d03205c02003c0c0f180c400c1030182c4460510b0050881000307044201c4100050400455000320300604000b90700d44004644072000e45a40c001c900c51044049501410345040150342d40320180c039400300140989042c0e0a1107143c05085030203034030340d280c10780c2034420501140c800e260381da005807200460707000c0d041d261a904a51006001030b0014401c0750f00510f03811301180a45c030b2180c401c0c1c94540e0b40424800c2c90060400300100c00401008080c003069010800010800c1d001b1040802262480b54502a981b4a440000e10090701d0002d4130700c0c0080d00c00100d8859005401182100669511140e40214038048010b882e101020703543c40603203940550b20006900c1544900108481800703500c0030b010b1241d8500501c28544070f42420288034500601c1905000c5c0b400b500004d030070500940c00c1741d04188050307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 282181888 1250 282180638 282180649
    0x302040f1107030c0605070e090a1d0d02060f1302130c18030602070c05040213030b06150726030709091107140a110307030b04060c0207031e0b01080f0307030c030e 72
    0x2c10040d000b094031910b0f24020418903016456101d0107926100c5400d010140c0410354921010300f003607180310b8884501d20030351a03540030400d110084240071560282c00101c0f019484103004d48922800240d0400080c2d0385004034102416820307400f82c800c03203021250a040d000204084040700c401c000003110412080c030030540f08200614040d60300140c0d1005e030740c6400140c007619a0310041c003960042c42504c81840c2103040100803650008140081030f9111000550b02c0b1045480c1110111400f20303148041c401c0f6139560011600e80011410206e08060300d013044079000403214a40000c1c59030307905000340d00306500f20501c8040114845800c00d800f540d5500542d260040d85400c841c0c0c4040b41e00000e00013103072000401c07907500307034060300b41340342180c8032030003254401807020b40029210b650f0090414401c0104100858104011507107628045010140311440f5540c00c0d511303540510004580030724045600c0c00d100310460000c40c070b8030380240d03020740d45107401010540034002000a0b01e200c41d1201c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 282183138 1250 282181888 282181897
    0x50f09040b130c081602030f030a060e040606081b101b050a0302060708011202060d09030c05070f060f05180d051f0f0f0203190b04020c032701020a08040302040f11 72
    0x40c0e00e000c982501d820350010000b0303100400360b6420480705440121110340110442384803e014103040760741c0e6550142c020000d42801d500c42c1c40191360312401c00042c84080d0f1320503015100c5010a48110407413041c00390360701420000e002680941e81d403030060311250203050300d001c0000d001e0b420300e40c00e50300984a8904100441d01b00382c02580103482042103580d80811420701500b000b035508000246c16401140381c81c040d40d1500c00c40c0b80c0d13440d018030701071501803112000200d41c44411a2007458698503008118840351051101103030345640c0d0001c0250140050340e240c0026a040c8100203000701082000ca003404942c180d034140151010b030440c0d00320380d0307081a00480f50300c1c00100380154030510080c100c5407440c044224052050041c400c44113900a401c1440d80382c000c0009c2032030034814000034000e100310891681c1511002800a1280240c00841506a0414403200280108503001a030312803e20007001020800e080005000614159001c0c02e01242c042d10002058030603c01d205002c3d502 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 282184388 1250 282183138 282183169
    0x2120c0a030e06030f0c031003050f0d03050a021606091e120207170c090702070b040e060f0405040b0c070507050a06050d1b020304050111120723030a050f09040b 71
    0x1110110090640100900786484800e40f011465880c0c403004103a0028409014804418000000320b41c0f00b492144001020715040807d035031504040811080e6180b44070700741907010a040078001007540d4450320a94440064450905003034a440340d892000030300c18610216910403e0300600c002c002c1800d645280e003d44500f0301202d5010740b803c8082e24107126540b00703601d5109030825540075000c000c00c0200c500c0f0070580c0c81440c25100c446040e03051420035081032542c20804039000400e041ea0040c2c0b24001c60013600c0c50002036194506020984100303c90242414140300c0100706280c6480008098060040c000d83d4061511b807000a0502c00981e84010009440420515004103d620400750f0401186a044a019809100181d00c0340110f10441b410b105640f101081c1800060211960070400700c0f00c1e00750b4032441c51a100d008484c01400341c0e011590b00011000303047c80000102e496040e0709444231410816140c0c0650015808103498a400548401c00302c2060303120084126036015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 282185638 1250 282184388 282184393
    0xc030b100305071a07140a061a01080a0e0a23030d0e0c010c030f1b0503131a04051305151011010e06040b07031d03070c03020109050f09010504020a02120c 68
    0x14a1820050f1074006581c002c0302000c011440007103440c030204800ca030b18556100c0c0c8400240e00368400c410341000418113010300799900b062040c403a07502c4d002115250441c82600c0302e41054032038101c500e04498904244509991110b600030010690b039036400c40034000064030100400812620950035908880250300e64039888044280c0c8101090004604803242803801c0c040401d80e1ba28010411066540c5650a0000d29810082540054500000465004022203681c3c2c804e04403100c25009207480f5805c00c0702c20048000300031045410446089410041991180766114044000100405415142403142e8545000c81171b4460240c0640c02c0d00b41c1c0d480764a084800410f9142c255603400e003002c030294005504101c0003c1a488240e0b13045140d903c1c0c0082c2d0000449884803014101003400d680d00c0c03201140c500c080042004200080d28800e90390043c0280d41d035001d0042040c0814a0709500107159030060003542065400750680c582c1078030480c0c40d403007030980c112402644601685401038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 282186888 1250 282185638 282185671
    0xb03060d140705150c06071d180906090a0803010e0a06080f070303110d120203040f0b0408130605040b0306101421010501050306010f03020a170a2405030307020d0c030b 74
    0x602d4131425404480c40c2400c055850148860340039a01e59500803d0f0390140941e0908030105103403512105424600080c0504005c20344a80043d0321055044842d05220320480c0000780c00d291010800e010500c2d8025240340c00c5900380f907600440070030b00a0440c180c0d01c0e0f91f404002030f0840c1c00c001d100350060580c03029011050450800404130640d0a05c2000c030f642c810200c01c2c0174180e000308820003800d1103d80050b20307512140782c501184e13540207134050003880020041c00b0600484000500d81d14109400c606145980c8240540b000d014a00c5480070150003880000c05c0f508090940c3c420004543c5800803c010710340d060b903032440c1c0110140f1000c0200c2e89015030307282c402d00b00c01c442c09000242012400c51805400081003583e01036003c00405401042c100e50040c01230180203d10a138420304c5014510301000390a0043c04008400101c5651094098005000303000740d80040d0750010b07005e1032415950b6000d000c07215649a008940f0110b01a0000002c1044c1e850007a016911001e007680b0170 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 282188138 1250 282186888 282186899
    0x240e0d12050a090b0913091b0b0415031a060325050a0201150b070f1104110a03150f06050a050d05040507060807021204050d0204020c0d111212010b03060d1407 70
    0x1160607401c031884414013003240641a42d51031030160300c0e442d101e00303001c47c107180b25260002d030342c0c408003038400007a400c07092021038440f080b43e026205030398540b00c03078000c82c2d09030f00b00c11000d460848055200c0c8450000c0600201e0500000a540c0b003501d1035010700f81100c4246940c540092081170220005030045075034050150f084c0144000f1112103200314487c00d08101e0010407510407840010002c1a10f4030007070040003000410b90660f030b40020800c01a41420895440c0700307038021001c16000910749003080761141502c503022802e484007400c10354411403d101080d03842d680428090b50601000740840c10500c8d0346030050700d10840c82000030780380240c03030b001c005004110040c0011040d034010400e50381192034070509490803a0310494000546502c0390021400074851003e0b000740c80e006420b2164035268000c01d401d040003001c41d084038030110900c201c000540c0907489016106001201c010080403030801e0145420031001405403442d110380390fa4002c03c0358040841c1d005942c01c100320030000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 282189388 1250 282188138 282188147
    0x31101141c0e10052413020c030301260c100e0918010507050a0c0303020f090d03090f05060a050306090402031c030603120801050616030306050607050705040501240e0d12050a 77
    0x701d038650380343c0030300143c107000442c41c10304005400805200c03d116500314441d42d40340303100401d00d02c078080011980d4030030140c111512079000340a81c0c0c03503a40e00ea00b961602c503500e80c44082d25034840400603103d40d98054007005105015050100208116660007017860340d6010040d0f4000e4040d510300300805158a0607041c00c2d560004e042900f4048140803010003e03810182e00d28040d91305240040c1d03900002c0342e0a8140b40610440f06411a03880040d010806410408440036a02d600d818030709001d6403142044100d209241200000030030505c007040b043d041200915421500c002d0a4503c001841d80305600040c0200e4041c000181e2100700030400d001ea0000503401620b0185081c1c107907581007401244080c03240041070000744280d00c43c035005040c40707a441407000c1c01c00105202e0350b40500d400d00c1540e8108900030f031032103145401c00000b00328501111814421802c9d481800310302c001d1000541c2c00c0c08686031900e4128403909500340c0010302117440d04401400c0d980b1615107400c5804801032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 282190638 1250 282189388 282189403
    0xa0f14100905040f05060423010308090303070b010b21090a030c0c09020a020d0905010903211218060615080c0d02040e0c0c0634030e030c010603021306031101141c0e 73
    0x4c8004e8010100c1d01194251207414a041d02e8201c40d40941e40c115510200ced103103208582001e4546154030b800892412001001072800c0da2915044062200c41440c02070f8040400f40c8950707520380d010f5000702001070700800e60007100030f004510315224103540311128000e0f64030102c000d17401a0081000803000301d810940600140000380390030500e50303066030381f800d00c5451012500a010940c14a150700143c0c810000d001540760300f42c1c02400300845400d150502c0c200c0c00c142c210303005810078101240e14011200490840d11456840000da074072070000754015940501240c40b9031a408100104482c1c4420324418095174107200d8882d620f001242d4540c3c240200a07160124400000364000c1c1100d070b00c0c80c90702c2184100e09002400805500310280e004203001c0395404118000402c0695941d4010742c800400c40e40290391946845c01c06003050300072030302c0d98000200030344207070281e48004c2d5216902095100d090b0710361942c0360024494040c449498123000a04405444800040034030b14240540c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 282191888 1250 282190638 282190661
    0x703061d0309150c030d1407121506030c0c0c0e0612061902090a050a080604051507050403060b06070b0a06061209020f09061c060b0a0f14100905040f050604 69
    0x7181007489030b10015901100c2000f0301c1141180c085840002140306108550515900c0e580c100701900c02c0c040724607808141215018042506444001c0c44083c05004607462902c9030b02058554038101001a40209040d5030f00b00100410b000e400d000007070000d00010003a080000040045152030400c2001c1d2050110075407206402c1034062107410680ca0310344615030500000b000d61502842404154541055484a584912544400528840040346940c004c0340144240d44a007030072802c00d48000070b0103403155400103004000400100b5250303070140c00c2281c802080703189040800d1f195110511400e0f00d03003094441c1c0d1541e04100e40c2c2c0c2c00c52202400c00e00c0d00d01c01480a460300d0340004100103454034269005092040c0050826980d40c1d456014610902c110b0750702071101828070b4401010800301040c09660108400324401c0038000101040b03134814002c80e41040ca001090140700090050110241b01c003100c80442c540c1c1c0c03a801091005101c078030b40000d071032510104000c01d403407800096 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 282193138 1250 282191888 282191893
    0xe10020919052d0a090e0f0114070c05071205030c061b07060e07120c090b1f030b01110f0f060a0b0d030c050a0606062f030d1d0703061d 60
    0x1082140c82c0c0c80f000b2540d00300700708559403062403403419002e0086096440300e513111000c094042070100d465803002540c0180e6200b00d44641c0c001c1f003041d078220b5442819460b840300e8448006642c2c0b41c8903440d102c0790300f803040c400d0700c0949a90301c61b5031402c4000c26008441503000070400004401082042c168007120100f4070785403000313201740f07540c4991050000280540d0380701d80b50104081c800f0400140108200002c9140d460810304010705141e401d405003c4410341041b105c42c9035440c2c1007619031004000740c0140780c40015500c1d404e070020b20352008910306020190072448200c3c0780500c02d800031064000e0181c4a2024070701c11132420060020320a01c5968507007902d40c840c0d912081550844079a00d42814a00e000450074885d241c1508104001c0c40075050520103e0065400014185504041c450312500c850103a4003501c1d400d12600720041c00782e80280002001c0f0b9101e600652481d20070607141036002c560021500e0304161301600150390407a294031241d040d90b000c000d84802410070314000b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 282194244 1106 282193138 282193189
    0x20c060a14010e01060806090601030b0a06030615180e22210503060f091302031e0f1f05040c1d0106020c01030614130e100209 56
    0x140752841681040000388041581c2d0b40103040e0f601c03035101c0d4115552850309200c2018001410a81095292000b44a050300e403904280c0140807190390114000d8200750480013030390f018030300400c00c101e03000c031181040040d100c0c041001c0c1c4250b94000950340d11055040306201016110419202031030700304600c2005403000030010728103c0388403a400064414281920303d400700b221000e410941d223107d0107149140c8520010b41c408189070300e0101c2c5c05460340119281c40816201520706038540001100d8500040085852003c0400700030000940d503030100c0d0741141e82020460000e1390721a03000c00c04000d1042c142c4000380240e101c008404c1c0703001703d5840300954030038880c0300b004d40240c00b0041c0c046d500c00d01400040d141c004540000440070b034000d101c0d18512950044401c95074608802d241017600303004403901e00240364000358035065107008008450000000d000d8140304180d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 282014388 282194244 := by
  have h0 := BRFrame.cov_init 282014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 282014388 ≤ n) (h2 : n < 282194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
