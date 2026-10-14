-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1557
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:33:55.196176+00:00
-- url     : https://prove2.me/submissions/5bbd74ea-ffbe-4c98-9d3f-c243e6562bef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 279856115 ≤ n < 280035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 279857365 1250 279856115 279856141
    0x305090f0603070513090501060c080d110714060f07090e1e010b12010b09011b0c091b12060b0405100e0a0303050a1407030912050a1208011a040b09040221 68
    0x5e014540c00302c000209401d14036202d098143c4007180c8804201e50425180c3d0200f85d000710f0140c40d1560780b0b070b50031000d044200724003401115204000300300f8184030039002681882001000107008002c91401c211549074000c0c110030407114040c400c40c0c5540c44100200790141144070b00003040409040c000162000c6440041010804002d040c0307555980301d468508080c8600554240001d600080c259001c0c05100c0507804030340d06c03030b5482c2d0401075a0303502c01d0010341d60724402e0260103a031514000000e9540015000c042400300b081c2c00c000042c10482a211b43c0c0c0501d000c0c2c0750140b502c0403041c200c058010643c41d201c4032030007000707020080e83d20700d001801540071542101c0014503080268a9000104098482003580b46e1111701c4190f0070b2001800c5c01e800001001c2e10580b00c0d004406001c1061242e14030134031140e550301d580d040c0d8101841c1112540b034000310507050311010002044034501038400d8403920075040307401594480030340742170703414410100e00d00c85000742c1d00b07505104940405d85 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 279858615 1250 279857365 279857377
    0x11030c0d09090c02060c090415030b040602090a05010503060901090c020c03030f0712050304050c040902010512040c030c1d0a0908040305071401030506180711010621060f0b010203070305090f06030705 88
    0x2c10240241083c0e143c0032a29000c0c103035000121544103200e46003061074290014030401d900e083d00360607000d590f43c03900b4904500946068440d10360000b010005410007100000107072400782804c034a141007480120b03120000500c50810010f994114078a80d40c0d00c203000c1d140d80341800408a0b5110505003010038200e502c0340b00111181088881c4407042280203a06503482580c00a010b007009842400c03d00000c0e00325000100d041010404c10b40503d0743e825110a80582d004101000100e8114500001c10b0344094001781da000340e8000c1111a20521011203a44c0006900008280250145081803003030040e900000c0c02802420310102d0070086039002030412502c241e1303061203103480c1c09042c0145c2c1003007890030390003058400c00011040d500031020910161203060000800c06d5a40000c1104080d0501c2d040d1a800c0d08110180c0500006010710810808401c104100034060b50002079900d225660008092080102d15040141c0d501d0450066441c0b01a001554078907000200920a9001c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 279859865 1250 279858615 279858629
    0x50601110c011d0d1a060f01020d0f05040b031e0a18140f06011e0f060503041209090e1e03130e07140d1d1f18080c0a1a040206030711030c0d09 63
    0xc240011190320f0001d9481c007d0a1040e0050594103c4c0000c08641d40d14803440801c1c00e105d000c100014801a07010000e510426a5043e180c80034803030204846080c80b0060030b03101080e8103101a1002d040c01c41055802240d5018116401144010203040e003020515038030402603000e044000210707800c18075280b401103003c0e507900e4494281c5402101444c3d80340c1c0d01035080014008d000140016842d04040d8403160b00600b0040d14032a03542071040c0944090100408503900001017030100018105a0000d0140c0034070040c50411004501811000c525031180e5101d4080c45000b00b030215020f0340401280808549000381d5982c003420030140501461820210000d13058050300288402c0030640240103610121110782240d0707041404005000a80000c140313800d58031014400080000c00108103041c898005004c118160341442d01c24100031282c10042020300c501000b006a0741c0508580d401101030410000240c145034610b45140a4411080c41e107210301400c0d4403056411034181d400b100c4074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 279861115 1250 279859865 279859913
    0x4120303180308060a0e09030304150b04060b0405011b02060a050a050c0a050c01090605072f0a0e06040e060403080708040f06090c0317040b0d09111c020301050601110c011d0d 77
    0x10b21b8004000540d030071507400c451600180049400a121048102401d6804140200e0000344020003d01201e00315802041c88030000641042596040b400300c6010b10221202e0022400c41600880e44521480c07807180200302e00000d0070f020342c1740103c003910188100c2c4c2003161040e11291a20959503403a100034540480c1d07401000044091189007180c4055500a0115034103440c407000000c50654103804500c42000d40c0d03c0540c005071650180c07403000300854020070500d41050307002d000c00c407580225400501d402c0300702080007003504040150b4120300d8618003260307955160f003086405084d100200400300f50600d10007100344041076150206490241c08000d2040d0840140350b002c51199206103907640d4020300038482e015020f075100b2020395000380259654650210001071440703065200400b02c51347d1003452601542805d2113000e40c880305c2800c3c40341080f196010241e66404540051504000451a0307510858132040146107254902030b010f007200c10b00d94a4580500b6031000b12000b51012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 279862365 1250 279861115 279861119
    0x70b03040c0f0806072d180b1224010f0f051e07021005040602120c0a050d0221070b180c091905251404051f020c040b010504120303180308060a 63
    0xc80d0f1405140c00c00106d060003190460f860700c0507520100e4540002c03010030109040000d1031550324006016902c00444800804c0c900300b50711050f50300e112240707201007890a81100c1000d981020301c1e003070a80240d00f4544116960503a0460300c0b44621034802c0c9500034907682d40c40d000701e05034029094003442101c5240d200c40d18640121074501444c45100c005a10045a01e224400290005d0a01001e82001d80300010303200e459031864004890030050040e8008021a00f518150b01c00c490044104024070a2078121662107010042001400f00100c2c9aa240c0d101450b0007c20440c00860b0741d00906154118509491410401110040b211120a040400051290307112642c0309000001c9918108034031a40c20300115410f840c1c0c50340001500c04204400309040d40d03032184009506c210aa5116400090254024200154006164055030402071300c01c0861781c0180550301994010030002d05601d10360b080490140603d01c0b4010f40c2403550300c2c44c400606500040b254880e15050304d00550300d42e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 279863615 1250 279862365 279862397
    0xf0611060a0902060d1a040e0a0b010801060602030a0302031e01090c0e0409050304060e060c0a0b1b0a1d0a05040204380a0804060b060c0a050c03030705070b03040c0f080607 76
    0x90b21440d00254080360800c115004a1242d5200c0401840c1c0c90301c02103124100304000c83d04450302c0c10200c020507407000b1a6001003204102d00940580341920003840104c0c50808060358134054288910289038021001602410300607070b4241c3c030b01d070a15a4845407035950703510180003801038064400014103100141c4d00941014081c1c1c0712f07002c2c1d000008501d81441d0000886920341b000240c0c40d1301c0402005900100705041201e85003050154051a900b0709000552103140e0b05001042960340900f4002074401d1a040a01c401c00103103406082090396860000044181200d43c02c4160312510104d40810450070040642500000061902150110034400100d40c18064284c40d64440390401c0314a40c424455032419401c0303803103000c01142142c50785001030229000194160038591201c0d420105006042103030486004090700910700e0000765803909601c039007407401104c0d18900000085420400c0e0170800c5401000c0d039001c0d150a050322518034648440c001c1c0c54510010b0941140303d1581 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 279864865 1250 279863615 279863621
    0x618040501170616030915062c06010c0c09181a0103172a0c0f090610110f0601030f060501080c0109031e02150721090e100f0611060a 59
    0x403002100c000d0802d507543d2526801e0250106403061304058071004d540d40003074075004290ba6420101400426094184200d11072040101c0c2c0c001841d0020109240880941d808000c5420030740a00e025808105141442c0000c0b0725540d11501100385400300d020100140c00c0909058a480741444107141d480c003192411b00001e00b8000900314805240040d000d40c40041c0c000c03c5880b039400d40e41c54410042e00401c00881c6040c03031005d6103541141119440c02c0c5412007100603111811654203041d03061840c00300f0195100e9001c020140000101028490710b000c01040041d03c2014088818568592030311143c2c0185100302204d07401e0074240003043e184004100d031a065541a910310b2400d40c079684610100510a400042d060341c000e0700c1e1440540c840318050072029a05000305940c502c0c0e42d00d8802c080c4101c1126192032403252642d401843c0b80d0041c0c2400c2101c07018910450f007512400c2803242d51400c03540c444200d40b03880800001c1c100303400202d444403c840030003d8903429503902d0309a0043d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 279866115 1250 279864865 279864899
    0x70212030a09021f14071703190b120705120a021002240609072604080310060212030a090c080d03050a0b09100302130b040e0606030c030a050d0e010e0618040501 71
    0x1045c07a0a0807031800d042443c01400400b4015400080e80c0c1d00f140703075020026401500c00200003038801d8461540700002d4051008032160603260104540007004007151500502c0c01403500c140400b400700f0440c15020404419681d8009019200300c040300c540281d900d101d0f044094400c0030341c17007410b0b00c8001002c042180c8500720160504000d640c0359034003100c580092a400c0c0041c41c900c1c5050344180380f03205c600319202d01c1c0716001055807810440140403030103181394810300445d0300403403400c000c644901d0b055039004032a8000204118290b40707000c0d4103003000c54210070601e210f50b104540549905401c11030103990321410802134000643c0910202140489895411601c04802000181000c40d000743d41407101d28000034013a1211400a0199200c071440b030260755002005001c4a03103014884074a485a0860003444143c540381c0d1081d80b84d070654501501400401e00040040341d001e0001480021001024250b49404000c95135040c00001880030303000f02d16000000c2a40c22030381c41a030309 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 279867365 1250 279866115 279866117
    0x7150806030a05060c0f22140d1e05030906070302012a0519030608030d0e0d020a0b0f0403020a12080a0507090b0f090a1203050307030f1a09070212030a09021f 70
    0x4c01d50b99004103440e515400345030b010064140170007907426541505000106203d4000a280b20241d2410004401c0c00204d4245503110744161749144000440a20400b0402c10118170a42d00f0b61040382071640c2140510900c55401036000903038801010f40c194030a101900074500c12111054208840c0d503001f08000760840c0c08204100070030304024140f000c0000c2c0ea0749403403802007441a10ad801050654100300801c16455440c1c6c0c1e10a00d140105101030640084144003d00c018101a125034100d0200502006900034145010409042c805d0040500d103030781200b0010026a81c0f20002805000102c40d103490444ca0100444c42540c400c40c4100201e528042c1e229041c80c03600d40c4400a60f034000d1124a43c0712505100c00034036124107960101d00c0c1c0b8000d0304c50ba602c924001c03201800f641d45280040329282d01d000084200c0d02c003071b107a5110154a00743d6402c0000d9032840016494548052800880030340701004102024656410030b1a0b034501c01da58200c0841c1180451900303000000045034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 279868615 1250 279867365 279867373
    0x301050f100812030718091803021b10050705011103012c04020f01030213030c0623040b07030309030203120a0213060c050a1e0804140405150a05010f1107150806030a05 74
    0xa641d0782e202d4492501c401c1140040109141d070b803020b03a80100c605010100349044503201008c0c1c1456011301c480300c0000c51001d0b1000d0510445c50029101c1c40e0138514800c10720901040d2017003802000d6001121200d14015a684c0c1e80d42c54001880507903025540301178442c10800d4142d4100f003441c00031903024030303400340c5220b01c052445030042d00a50400729503003949c404643d000101080b80050040001c01054591421201468014000c0300e8409400d04040134010002000600204021070701065014a000038500c074072031500b00d003140704140c103000e084240101449a00f040582c02004100c0c0420340c0c0820341c03175540c0401d0b0f0307290140e4a000b0741260405c0b0104800304010390100c0c49651858080106501e6883d0740380141070f04180c00030724480b02044410001400c180c8582d0360840001c1c201136102c21070300e10019407403881a0096030f0420800f0070403416090301030031a08040344601016100d66944a21405040c222140603410000e00e0f4000410944c0c04c01144529070750740c0000280c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 279869865 1250 279868615 279868621
    0xf031b1e2309270a0b070201060e040c1a0c0a0629010503130804030f0b011a090d1704080f0604020a06050702060301060c0326090d02011b120b0301050f10081203 71
    0x26910208000310710945482010501d01c00d0030004e11011944a00c1601c032029582088040207084a19640244001c0c440d25424840454401506d07501100c0000c4000d4202c1d01492503014081d00641d40700071014800d120000040200a81015654100b140604424401104040d403140c2d240d004010340465000c20100e107055524401c0e01c58158041c2c1203103440c00d980c07039480f03c03150015620291058607400c4018003d18504a04400c240c00e01c004d00c460818441c3e03c00580d6003000340100910000c00042d03044000f5482701e094800030b007910400e4500300300072084030b162110301c101d500302d109049120300812000e00034810344a40a80251841c0c1c00e503802d2010a88d803c4464000540502c019011003000e060701c10600031410110301c1030341c62820b041400610386810100b2041d0015a41030460002c80c40080700e0400c1940031702d0307240491129810030310400080400302400e07a01942444200700a4840c4010418010810116082c0800e0344d5050307429281d0b0140200d410280c8810008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 279871115 1250 279869865 279869881
    0x115060926030f0c010f09150c180807030b0606030903070f06060306110720010e21070305030301080d030b060a1d0909010b04150f031b1e2309 63
    0x1692031a01141050038071007000580c4401d2442d0415035502450f08000502048407050a000700303019500040002e100315900c0703945041d144e0b41c880c2e003500c4100c0c0c2e0380c5140c0c0341094031501c800c8240800c120a030b00b100039140d001040d00ca100602044e224092110040b070b245007000d4007201c7c42941e00d240a141800d44075a6052800135250300c0036a400b940721240440030030170511a90403005422952196900d00524009003850101c0903e00c501c41111300d003c0f002c1d80d070405207160303140320106c8400d4111000c4408000714a00e105501c11074503c5030840c04410010000300840c1600d80410441d5840104081d084099030468020190018001e0010590a030f0123036240941f0b41031103000c61529949454041407030003408481640c00760b03449498450183c20a845030504407000a221401301c00d09000590391910b08602c4014020f040300495046d0441c0803142d110003810450a140960309200300a001d00f0404a0007001044c081c40750b411000049414070468039200c002c0c142042c50754034200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 279872365 1250 279871115 279871139
    0xc09010501180b03070f0906020613020f120a120207051903170c030c01290307050918070e040314030405100b0307150306031a09060c0703120905060901150609 70
    0x1001d4980302c1d40c00c010505881032400303540b24001ca955051080001003100400708642d80d48000d0a540041f01400528203500c03c45c0350b0901d8055513071030b00d102d401c0b0300421044a11020000b8680c0900c1801e501002181c0084465525140c1d00300e6100c00d895204100180c0345502c122421311000c1d500802c0010301d61141191402a40f42116040441c003980c6181513500403585003100c0d941d903002400f040600030010340e00045100100030180e88008022944e02c1c5218083c03548100a0880000c258000824041d21050703079100a0700d28179a500c40740816031403c11384089010404407040149940403400c02d8901c2a90004010031040889140c80c00092900c00c400f1901806002c4010035400d0580300c0f8180071428980e400642c0b203280d030914514042c0380b447c80c481070309074860510220300310000c0e030b03079030400544420156900042d1034180c41b40c64603449401c5d106410402d114040c40740c04141c0c103208000802c020300520600c01030060340341c58a1f004403800315601d451305010303900c0044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 279873615 1250 279872365 279872387
    0x406060c0303090515010b0a080709051c0c0f0806070e0409021e120717100e0d050a03020403020d0b040201020115060212070309170c0a06050a021207050c040507120e0c09010501 78
    0xb6a203d51405c6040c05110310381c00d820110f04e0000004d2484c1c107482c0e00c040019406081890075000141c1841c00261140b45200c1e01d00ca4041c0c189807481090106510b04071000f4100381e4501d82000c1d603103000ba81d4886030304a131528080307664a102c00030f0f182464080c0500040d4014030622340e49a85191001c2034078030520186411440307040c10250003040c01c100000241c0003492040c140e018031805501d191030107242a20603280d040c00c620186140c00010a480e0745074050034055150080c42004900a004541c40a03502064843c0e1802c2030104010030ba600a9000ba03000384404400051040c003a0059131003410010381c40381641103001415500078000b624800e181c060101e03556040c0c0c0d1146142d0011507401c09400441d800c601c1f525264040c00c0c01490305042c86030401500c50800794582e90260741c0c4101305400002d180c81040414402e0541c0c0c080b00820801980c24080c4000f01091708109030103c4071460800403403020358000440001c0da800052880c40160308140044503803032005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 279874865 1250 279873615 279873623
    0x150507050c0d02100b0303040e0a0b0102100c031b0c0c03020913140c010e0907020c061c0216060501051203070215070c0b03071701050607060b01121d0601050406060c030309 76
    0x6210800c4600030034404141880720b182e004041c0c84030304041d94012103175071071550783c4654401c020420150030441da035258010031022001510552400041c2d0416401a0642048900d802c640100241d0107a00c2520071032680300640b01c42c0341d24200c2c1510903d0345040040c00410041900b0401407a02036042c5900100302c010046116429582e07000d540413101200c076140c2c0c1c000c14180052545c0c00020002c0c1400100d55641841c00c140350003039100d8212602c010300070940001c012407032000c21103100c0b640c01624002155590300842114540700c06004048660724101400082c1c0c500d040454004e00c2045a00a9403502e0540e600b0461080c0400d40751955a500601c80c0e0404900b101741d072500144142d40015039213240180c0300600c40f15601d0b501c0d6030818900c1c0c0050110b074075510141d815040d80014002592282d990041c1c0702c40d4940040081103600b0304841d281984406071281300911100d0048506698840042000b941c0040c003400700080c2d460a04403010903ca81c202092032401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 279876115 1250 279874865 279874867
    0x60c0a0f06060f0f080c0103050609071b0206070602030a0605060c070e150904200117041506080f01060609080f1513021c02011b0c0515090303130e070c15050705 71
    0xe102c480004583c501d0707006510904000d502003110391428800e1864203402440c0400c03951400c8030005e40c1c90240980814200403000407103006d100111a100103039160001c004036207807101841c040c03005e980115521002c5a0404a0009a40c107100701a105c0300c0c00f102d03000c0c0c40418107100f81090200c1c0d00030300c08814000900c84030030158542d5020140039500542040106014040362401048022011507042060040c812401c0e080041005504641c0c01449100c85107a28030300321000d03040c1500002c203103010380b80b584034454105600c004122403403038540c0301e2201c0e5030301c454544412211415541a0300014004c0c80000304068034180c0c8500082280d0a1004903074000c1403941d1200c1e16125001c4142036580c201f550707004070940284811185800750b4413500da070f66401c584a0303648039403800f600d14000c0307000b45081101d094440d00032025040b00d460303c1044c030215102100b148900c820501c1c1080c0408c40191181980d09800b0340c02442034124011142039000c01040003c00020130400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 279877365 1250 279876115 279876119
    0x1b03060703020f040f03030c1a040809010e031c0f17090c0f0d081204061103042a05030105040b011e0602070b0a110a1505010b1c021305090108060103030806060c0a0f0606 75
    0x580c5103002d1700994080c0d42c03254002e100a01d0301c41d07010b03510106c1c142c8511801004100000f05030b00111541c0e10001c0c80e00c443c01ca40d0000209252189041c010b00c4403441c601d240c10000f941c401c02291400d46030350359008000b0581d1101040f40c030425200981c0c0b5802002c40c43d4100d092001c0507a4500e04054a0b990b08040b090701c8454154006101305814400d00b00180804d01445020b604000090707502c4042c51810300b9924003524444009941c06140140c1d0080068940f11000400003004098001c0c480c520309807400300b000354024083c241040c0700f140c51060904503001c0012058a0850b0000c040060511058000d1a00000040301c10030000d0740c02810380202c10311440e91040c0c841c0e51401c40081d604d0704904240d80b0305810140c0c06001c1030202c00d83c40c2d00b450051640d01c866050340141d4411105e0314007461a406508250303048007801c8000a45420005203070b0b41241d010380d603520010340300c50040100750310408040703141031f6200c40214004181414040c101070f62154000061142d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 279878615 1250 279877365 279877379
    0x40b040603060f0f080a020904080d0c0302041a09090403050c0709021209010c0f090302010305130b0103080c1507410405010306150c080d0e0102030c030103051b03060703020f04 78
    0xa849a000301001988480c4100b142d111440300c500c0240c01d0010b40310224a0a1010039aa00c480000c030183c0b10301c02c001c0c08581403040007011074039602407003402840a070015160142c043c0d4098410401701040310005000000b032032005894081d007005048012036103c0d601c040300e41c0d4010800203500d030300800c40d000a080d411031004004921040b0740240c110303e0003509482c21108000d99440c28001c011043e0051240e10010341401e880d03090800003066126508817555071742441c1c0d002440b9034003900010081c803202001504034501c0807401c40d902c0b02450311402038245e0040d6903540200d18007900d5040e9690302c80c45a85200028051302140401c640c0350b884030031110380e544680420030300140c24001c80d64503000d16809803c42c00c10740d030300c446031005004000e101000340c094045075000c41c0c40502b03041075030000c11240c0c600030003e5480303007010444030f500c0d64402e10003250907210300c4440261b000500c000c40c44200700010302030019507031019000c0c0d01270750108000c1740243e202044086815 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 279879865 1250 279878615 279878617
    0x5010b0d111305150402070303090c120b0c0c030d0b0f090c0d1413060b0a0906031b1d07050c07030f0b0a0c0c0f060b15030a05041203022805040b 64
    0x2080c0140c0c0c1c0000003145503428405000d0684041048a6080200304020f150785814a0070482406031801030391008107040c120018890144018451014400c000413848841269100e072a07000c0c00c0d0700c401c3e80d00c03482e900034814440d5811a60168000f4480f42c002003141d42d0104170b030b440018021046456600d170001c0c403902c1c4200d44411507040080360f2010306460340c1c82448124800c000399510383d0b0504407041000e10b0038120005100e552120f201c100c09854000440c00280242c42d014083d5640301d103803030b507030040a19504080c144038a01000a00070706a21a00e80c1450a0101045658031007460490700c5070320580c114000f51140c10380000029140340c6075641c5060156850300349504203140c0d00c10a0300c40754030700b140070040d0036484040820462030b1001001c81d440500020700d0a103843c0840c141c0080074004507513200011041100034070340340c0c020341d12481c0714a00d17501294040d41d100703408900402540e040c404000c40d0703680035820380482407904101c049041c01c03810a40da40c07010401c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 279881115 1250 279879865 279879889
    0x18080105040f050f0a032f07060206060310060b1c02090a080c040f060b030106180e2a03071403040f080a02250e07051c020f0403020a050d110d05010b 66
    0x10a1200803000d0082c000c040c000140384c921010b01501904845031001840b4984511200c41068154995070090403000311829210b003a042094034100382c1c0c4c0b5500030303417610802c4031440d009001d540b40180c0441031500ca0b02e0142c1d403030548800e04242c145d14640c680c0c61905020a1b481c1d503400c100880c0155102d4a00344c004294a4000f041150000403e000588819031240361134541401000e0240355089402d4070f064480514110403808000100c0300c180c3c0307002d03030b1005491034021024000c43c1c03051080c0040000380c070170b0030305402c2081c500201c1d11355100498448000800c49600e400424210900454109006045c91001d11080d40c0b2039040a9010781180c2c00545e05c50a140160020856075500907c4000440407580c6484e044002d0030f048002010b060030000005848401c0300340d04150b0590900f50b2500c210744412444001d40782c0c60380f1030f00044e4032540d28444005607520f8100c01222a046c0e1000300240c0a11824050201601ca07100703048442d9500d4001c1c04070640c48101030240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 279882365 1250 279881115 279881123
    0x20a08121c05010807062610030b100608060f030a08030c031009060311040b030f0f0102040f081c05031315020304060c0201020a021b03190501020a14070f031808010504 74
    0x1d9904404560300480e14120228482040c0c01d0400402641501190401c103d400710b0810003121140400c00416004003007102d01d648810a00902c03440096010304501500c1c8225541d80c0f081d01d13003480e000712100c05449035900151310b01001415a083c0810700c1944554050120b401c07004891382e039894036410499000408900c08410400c03021944240e5400600340d060081005d1429074803104900c6686c00c048901450301c8000010a5450400810002118007804d9455103210400170038007030344c0315104402c06410540401700d442d0304049140d40c0600581c82c0c45074404201c0320002c0d140c1e42c2000388142145c0e000003085101103100300707a01d00311304960420010790720706d05850044201e541040f4080210381c8103100341c069060300060310505101d440c3d14085402004640060300c0d1007402000c5140152440c0c01500800405402418505429446503210b508801390354141c2070040349805070030030f40c3c030b590100c001c24081d844090402c103034850f000d8120303a2160115800d507076050710222 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 279883615 1250 279882365 279882367
    0x3040b160c20150412020d08090303030f0403030506101e02030906041205070608010b0711040204050d0b0a0606081e0903070c060c0303050709291308070837020a0812 73
    0x41107440c280f08040d1201c503074402a64101401c00318542400090030500900600c5034181c10b205018902041d00e02402c8000c084030b54078540403001c010b01144c10740e4103c012908001c0030581d036181005450940c1411a9100300555480304400c00003240000c09810642c0001c00c210306060701c9100c01400682580100c1c24050301c001c0c80c0c07061074813045610602c2007002c9040103004020070f01b42101c04140d023107a240400038200d400098002d00c00c03640a113510403440b1a88008024408501920031650010304100165542c9019124000c080303a0700103034038045125000e050482c0c2218250010462000ca03030030141d00f55520007900000c0c0d04903001041da10742280c010540e041c0506e561001c040e05d0b02460b9035280441401899101c001e00200102111030701e9049101c0030015610351000c910b032400f034140d60740c03262540c81f00c501d400703642101d0103807002c8084c1d1040020012055414641d40400200c240981c0500b00c04a002c60103e90101034028005100407042040d039803d552031006803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 279884865 1250 279883615 279883673
    0x706060915180216030f020111180f040e0303060105030405070f061d100905010e04090c03060c090b070309170a050f031b0c060409181b1a03040b160c 66
    0x81d040300c680501c80608028010403034032168561300300990081d1a40350801250702052080705030f024001038004403030683c8011881410300c2d51401c40324000e600050b10408907104440083c0410f070341d1503003180c0c40d840c0d008000ac00d4243d4440d03001503070300a0042003600d01c8aa09c4045405841b0b10607840000040c10418400d11004e40d2060000e4914000300c07a00310824100e08005086c42c0814400c0d6410f2050155008000cad85568000d04076443d40040d1000ca038544034500400100b00081042002604855011507143c04800803926607542549804125034540416600007511303180d0015a00d000e43d0450700001023082001251029000000d140c4030175007a00403101e4071249601c641c00f1688403001400240d192641180d09942c0000e00225178551046d035903040390700d2030141c01400300c03030351491070710088011880c000d003598001800c01d0600300c00d4512000403400306a0300600a80440b4011a11300842416030b44000d80907403c100075010940d84030000480241446449205020701c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 279886115 1250 279884865 279884879
    0x80601030501050f090705030702030c06010b070506090a0321020910090608060a060815010e1804050c040203160f0e030d110601080106030302060a0905070e240301050c0901050706060915 82
    0x800b4094407068495540c1d0740c4001d000185164400b62503c410b2141c00004103500d1807081c0100c0f0104860802203c0c201d50b0740d0152152203910443d8107507100c0c0146008610640c10100b1074281c043c0d05a42caa440014007a895580340d03101c284150801031381e00f002050106d440701c001c4060b03415600c2c5c960803400c0b0b1511101612640d00109110320481c0d2050050201c3c58101901139000480e2948188003c0880702c01684c5c000071001d115a480b120a1002c0712480e00c8105180340302c0e40c498010f84a48051207010b100981c0415200340c450b03200911140e1241c80e1103020004c0c0440070b07038a4080815224000070a08003000c0700030210004140d82c8845034410740c02c0061a0040440800030000d2600c1e40c0c400075150640909040006500ca0104205212003008800d0181038800803403101420a280b109100c404044601d050b1100f840044813164601071107180e20500d2404811441d1041c010300454003a400714104813281a910440460414a02c0c82640912003500c3c034002d10035410111 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 279887365 1250 279886115 279886121
    0x2090f09071a12090a020612070f0206041a09010b06040b0409060e04080415020c13050a15060e040b15120106083312010510171207030c0f0b0708060103 67
    0x6028460007042c1e44056858481c81102c1058240e041010995114103055500f0503010304000780d44000b0104441c3c07900c1e4500d00e80c00780030703a01d9074413030f101c88224000301a61118022500542540c51000c0744140200c00c40c124554400441d1000141c55011f40001403069045604107078513004000c2000d000446582c41490003030490040740c0c1400d403809540d107840034440c80c0589100b914800a0740e50102c0d00070020000d80041c02444041c0840c2100308202c01040111070b035021031820003c039410300641ca00d61040c280c48503650341c803071a20840000c0c08058403d0542c02a00f21600c2c90a40010200510103000a44041105c4d0b120030b5150020007000c0c2140a800a101d054000760240010580c502e4042c201c03150003444645602e50b21400921040c0300800d004449500b80810040b07250030901e10b83c410342d0b000300d8204100440201d119035980e00c00d01c2822031020701c01c01c402408039004840c1020315600c5054052683c41c0c2599801d16520b00a41c0c070400883c900809000700d56070140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 279888615 1250 279887365 279887369
    0x712060b091314340206071e081609090212040b01061b110402091309150e07090b150c070e1b0a08070908070b031006050301050618040902090f0907 65
    0x350280035461803441c00303a0280f8405014030500002890500a10782c200c0a58040b0090156408225a050110001e910740200320f42101c0060301841c110340110302c02c941c60348140d46480d980c961165881e0b80019210508848140c024007004880009107003407070780014440365850b143c0c141180e00b0640b070403010060b01030b00710b0030074020070705103010a00c01012803021001741c11090100c00b8508110115009200300003480c1d8104e040e510b00c0c00089440354200031003081c0300b4515008088400c0c0ea040c1e04803000c0905100c02d90b00a00801c00400c400e0341c00c40b41d04024010300407084850b6180d02e284e03550707110204403c107a4006403800c200848074160710fa903000205000150184d400020002d91510410b4159030a04c1045004181c034148030720401c1002e4900201101d64403501d0710039150482c0c10844028514140455012491034495400d4a04880014243d5424018210200d03a151400299000c1c1c000d956100ea80e005655040c42c020b00030450312404822034200040018141511a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 279889865 1250 279888615 279888649
    0x16031101030c021203060d1406060102072321150106030c0c0c06081f080a06290105070305130b0711030c09010618080708010c021005010612050712060b09 68
    0x20700c601d02c0440e008160181807071903075411103a6943d1110002100c0454500000c0c209000112403000001c01c0050303018082c0400b40c08071503031035a0340c82c1c42d21480c20108000040d402411170949500e810401ca1118891200384041e95441500808140c5003882ca030303207424114100800100301e5071b5014450801d1945140c030709a081e91a103502c130207618000303520610301005280000200308460648062250b841030821400b0119036802680d0faa80100b218240c1d4070500d000001d450001c0188020058004201004030743e0088440064825400143c01034080c05810441115621051035a01010f4030050700c109856181c507040801c1d03c08000e40340c03980a81c0c030802c0441456a203071001681100c12618042d0f1540741c18200c605040849980904200e21450b200800c21002c190801400d100c03541d4212100c0c1780614810a055810030307c500c00200b6070280c40707421260081d8101035800b101c281042d01d110581030481c103048800d03e9010242c0200d001c155214203180c00400d4000c90020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 279891115 1250 279889865 279889871
    0x1020a094e05100605011805101704120e030109051216080309070e09070b07110d350901020303060d030e060703030f0c0302040b12040201111603110103 67
    0x4601c0880e030584000c0e035071a6502811200c1d00c04100e0444031003240641000ca0a92071000e8a0341c9007040c0e48441a0800f101014245400854154454403d5459203082a1900031407107261505006288072181ca42e90201704640a2007900702600d40740702800b40340310350780030170500c5802000102010039101c541b40c03103641008a01030110b000042d078140403001d070080f8290fa40f117000c0c0c51410301c2c01c4081c0c1c00806504020081241c01280499250101c507000e2011301195601c80c400652205458055448000002d000440104450311480344100d2405003004506103480c0d1640481e4808402080050441d50030385141e281d080d0300010100300c0307068041c507802d02d50b110001070745170301000b8502800b4411a00101d405d041c8254600710040c2005000c10307583c0c907003506004010384150451000020309210480b203000d8480c0c802c860858400c440e05030f040943c44a4411080715001e003050341046806640c0c0e0980c00001e0080c10302c0a085e41002139410713495854003078000c1c00b00313885c080d05043ca = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 279892365 1250 279891115 279891149
    0x504020307050a081f0f051504031509060b0603090d0f03022706120907030c0501081308030a06180b090a06080303070819020a03020a170105150c15070201020a09 71
    0x50001c00352040000141809525035543c0540c580e040e160840c05c401c40c00300b05440001d0625912040c6605482d03040c1c40c2c65492403400641c0303c42d64401d51000900745e03000307801007000701c290340d52004e4440d81c4184004141154100009042a00b0580741e003030307098000361801c0c850960840640c14402c0301906041d4288141c00000307100f00f01d40d00b01c00c1076612a074000401d040c4c2d0350303070380c12511780300c039030080c15052814000191aa44c40060104452405200d40040740c41c1d805071007018800d1761502019001c0281d280d45000d455000502807101c103a80b100701c041100641c28024400d20301038180001407640ca03c404000c100c120180c0355040091505009110714040401180c0d444030703187c00e00e450240c4134000079281048088658880d514404242e00f210a540b6030020007000300c99a0fa0002110aa020342c1c0000390310a200d8268045035103500350f40100a0316026200540701801541e02c0101c1c0400200003411013250349100503540055880d4120390001060740280200c200860074044e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 279893615 1250 279892365 279892367
    0x1090303020a0e0d0c0512010e1905070602150a02090120060703060e040b0c07080c07141003050601120b06090a0306090c060903110108060d02060c060103060608030a0905040f090c030503030a060504020307 90
    0x6018029140211203102212201f00400d403c00361280d5815002c030340c580d0852030f101ca9008108007004545074002c40d000000d841c1e100049690003114480c2c0b0f40d41e032540343c030007100d002540032302441c0d41488150303071074003007024104601141c10b480d2403030150100d031a1408004040f034826400c580285010141848003091000940680c81041001c1241e56002c03e800e041e1000c1c0205400c00d41d0a1040080104182003006030707038400c4078015160341800d407100c00402d800b034600454640e0b002404c641c5c401100444503400500c40c00d100a81500c1c90503507040041480300405070025100d45455444170300420201e015447c00411451518020007401e40d0b4403c91050b440203401810002c804c408180c81c0e58a10424101441d4010a92a0398a4140440e2500d5240910080c0ea2040c600a00050f4020011084a00f51070081da2610b1b5900d040c20200030040412920b44030ba40c554407004000080c00c1309680d8000755000300001d648070f1034200510010348410307802071342c0998014003e02c1162 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 279894865 1250 279893615 279893633
    0xc121103062a1e1303140c09070309050a020d081b07080d05030103031710050405011205070e0108030901050c0f1609060518040210030905160f12081c0b0301090303020a0e0d 76
    0x1041c1c503000c2e00c84d603a5043c444001c80c00c0d0401d8201030710701c00c0030229400902400041100003101c003541c0c01c0d900c40da5260015002c40c2c105420160443d0020021b00d001032425501c0c10041c548205645400c1c000300c0500d0300c20b100340c44c0003501c409911040e0103005030103040011038001d0481d0300c0c14510b59070465600400035200012001c0c3d030528080e01003103241d20301098500c083d20029000300082d41e540c010344062042a010195207a0048101c0030640109403080d6a040e10300420040d45030102c4032004403600d0384840840f907039500500400c9202d0038414880b5120440380011400d40007401c020b82c00046800c90f610051040da107220900d82c0949a6140c01c80d8059011201d404400c0f0745401c040d005007004101c010041d00030300200d0000c2480c3c079106581a5a11aa801c1c00001e440f4258039a5404000340301804262040c050818132981d041031246008140e5100814403503c000d0109096883c072140480200b500450140015a440344e800504003408452103a2465410345404800d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 279896115 1250 279894865 279894907
    0x201020613081e0712120b04060e152106180102040f2d06031a0d021e03070f090c0f031814011e140609040c121103062a 53
    0x1064602010b000e8920f4451000e07146440c0c1c02c41c81154915109100080c20030a650240c0e80d04103141c040800c04905181c41400c0c15107030b041051150355168401c8044140e240300c84120f600c01c401c40076440c0c481544840d0038280400d60030082409080c54802284000840d109207e82a803040c0000c01941012110b0f0b034080311200c0740146c0740c545501494003000c3e170031409020407007100040000f0380703240d150f07105404c0140800e00040001e00c0510400203a0440c44901035406101c4092041290150580552070148020111034600359200540c2000500981c00500d8266441c0c103d80121078001080342c05801c0b091600300604202040f42821003003911201500030200c0004c5582e611a00b54812411076845501d5030020600040105014007e08600100d03c001000c011500034240b224280b40100e5016090103a05414181d119070340c198000c0381030381c1042410482c482c80703880510400d40182003407011480380b071403054032080310000100080940c2040030081100804033340e040e4070790 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 279897365 1250 279896115 279896137
    0x7050304120f09080d09030203010e0703020a0504020d140703140106080c12100b04180e0c0a090e01020702090a050405010b010e0102070e150312030f10051503180304060903020102061308 82
    0x70001040703001110902080c0d0000d101d00d102e1001603105d0590032020b120101c9100f1002070241d0383c4031000c0b20351165802d1000940142800c02d06200a25058026180010081000113803131200001049680241134480c0c42c042542c0705601e0b0008081039602d0b41c050006d9041c60061824105100080c07031042c24415401c2c10003101c0802c0c011030400480600410703482944a4640d80c4560000b60319140784c00300024028580303041c100002a0103e80b500c420100101221500307460408030300c0213410001881e03000c2e5582000010700590b02c0d10103050040c0c44070b020020f10b03032a0030325141d07084503503280429040c4441d01079005a03036a4000341800c00d07078a0700210140c194483e1184002c40c000c0030940e41d6498018a11600340d20b15210740510300c81d400801101210741c0b40c1505c1c0c0c00d2b842c8040d000c1c650f002038280c1c0c2c0d04586020600c0056800c400c003440c8030000010620501425608650070020010320b1a0504106540c4c6c1040a60381210300003001940800300c07507075080028401c0c081c2c588 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 279898615 1250 279897365 279897377
    0x901030615050a1e0e01060c02010507060605090a1d0f060a09020f030d0f02070f081005190e07060212160f0c0b2113030807230409140705030412 64
    0x1412070040000a280107080140100c4031030b545426162000141110400d07000803200000016800c6252181c603040b96143c0c0c980b40e1041c1c070a0303001122607a1040c60180c3d262600d5140029042e12a10003583c070920004000044613007101004901c6403540c5900ca0b5102d40c80300c000c69a000d80f003c01c07541d400c40c8113884006400c4d07419101103850011000b1704d40d5810f00403003060361899038000c0c04403000d514599080e2280c150b1228418424000301c1d020300c0031147c0c07041c080314481c0d4a4a91101c0d400c0710340074095061441c0004c403110140e51414100d201150050081009861740400500b501c07209002003030307410810201e01c84540e191610502a280f010000007900038002d084072080c024051000119aa48800c074400e044007506d81506004400340800000f40d81c040f840c1e0010b00c110341c1c590b0b0742c1001d0351620303041140e040180740c1c0c400610701800f88070201e40001000040c8000d14601401240c0320000810510b04034100070000c4c028004200700300800104800455603042411342000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 279899865 1250 279898615 279898631
    0x50712030b030a02030307060b01091a071209081c020f19020603040807021228020607061a060c102003040b090109080c0f070504061a0919031a0606040509010306 71
    0x3071814000c2c03c4042c0d094000094400244100e03038004685508080e240c070500300399103400321880030720012500f0900b02d0050203803000041c1c461040042040051429401346615880e98500744030100e40f40c8500081c01e10b142800003038050001e92a0018544003600c404c41c90607200801c003111042000340310b4200007000504006002007500c24040e0040d1040174008191010295a091000001c0342c4413402d40e90000f207150908081012901e03800381c0824184013a56849101400364190140c1c22400201707410005d6440d25405000c80581c0f01c8020950000d03a00b4041d42260032001910f038807600c002c0e040c0c04800c0400f40c2140c1d005540901120440d41d50301c1c4860740100740500f0b004016940000d41001041300008080c079a45417014195503505940700100720886030544500c0984410240241543caa44400a810b400c8409007000e208116200c9950100c040715410032261509407c070f6154840320101ca00552008044d111140340505202c002018a01d0521008140341e03160080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 279901115 1250 279899865 279899869
    0xc0c030a031e1104091b0f0305040201140c030a111b10020a080d020405120c03060a0e030415210902011d0609040f1a0105071101050c1c0203130501050712030b 70
    0x140c4030030b02c1c00d2801d00b082142550a181509a0f12901c1210456810150b100c5c0c20340c41503030066000006c40d03448540e0340e117240050980203000c2c000c0003070341031044ca8801c0040b0391200708020a11601c4c0070020b140c0d43e45644102401c48240b00b6840401e82c0e2010b001500511103180600162107822035609040100c4032808914052031200028a07110000c240c400484080d50003030706c01d5030022103968185500f0f120256a580085e40d8866a00d9030000000c03600314043c1d030b030260303005203440010769140988814803d0b104103019031030301000408070412000160707949200300c9024800c41c00240b00c01030481c1c000038414214481d004007041c0002440742a541c0d40c1038111042c2c0c0f10060000c0c403590a0300c0348608020003104020441c0111500000c0301e4643c41041183c1600b98801408021500316400440ba1500100e640022500c42c05c41c441045240000743c0042ca0700b490303030040d943c82c0406030304c1082d48226503020a042c00303c240309400010745070780701c4c2d1000315480c2e1500140e83d42c02500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 279902365 1250 279901115 279901151
    0x2116081603030c050f0307050106090c05030601092106020f030601021207030206010b030a0905010903020d03050705041d07030213091e020a1b1e0b0103020a0f08102301080a0b0c0c030a03 82
    0x1060030303117510000406000700201074005c0e20031035604130400c01102e00a410140e90a20007182c1142c00070307554110038130205408d41c005595015442c4450f80106c8070307560300c96089a00c000c0303a01d0300d07460002c01041081d42c0c1c1080801c03035031a01281c1d02420013500e6500a035441806005007845407802200050803240c0c0d682c403203180703241c005000b0b125000c200d09020b074035010342d620100002414900024021070140c070442d02203903e80e104041442c0f2508450300c511441c06003024007010b4013040340680b440041004e40c4003503c041a0002444100c8404101302d0b9040800c642805a00600064805170340040d54814102c0d524110b02c1c8000c1e5480c60204501940c01c0e0100148022201165092141507924681071303908c04e80e0041d00d51922250b40c1c818882035807141204c03c0d0304c07654103203403540200e4102103240d80111602c28200b1842c41d080070303d90780f0240c014109a80c00301d0400030038080515500d80e004080c2411982c94a0070310300b1032544038840c881410050548400d44000d100407054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 279903615 1250 279902365 279902383
    0x10030f12170406020d050606031012020409210306120b1602070906060f0e0a0f230a0308210103020a0b0f12011512140103020f2116081603030c05 64
    0x10a4002549401e14010f0300940090302200300c204e1034200002e0b414201682120300070007042214003041803408413070075581c400c000c0c0103e8006881b170109400158209a501c030b01c542c1b641c1460551488500b50050854000d07500c07110201491b522440c0210307210801281c0c004403414813008030902c006509a00d401c201c1c0d4407004026142c002c00060013948006860021041c982e00c0c0911408204204043d03900e0341e0081d0521480d54080c1008220078400c01e4010021011031148000700d0903000040f80d03146240d1095640c284000740751003510600b03200717440706001aa4104170781035040d030700810038441c0b482c0111074240304005442c50800c452013058440c545464000c940c00c07982c440c540705058600c114108c0020440e802c088050141c00c1307001d01440702290700c01d08244c5d030b031840e020498603001d00901c842d01300408046c8080d1040300c8020714440d0000c4132004010000e00321034251580549588003001c90380258031035200686070310744228102c90700b40c50070000d0383e505400c101d42003070481 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 279904865 1250 279903615 279903647
    0x60f0a0c0203100f180503040603152c0c1306030e0a0b150f01090b0a0c020f04020309010911060a020615120a0507050108070e010e0d060b0d08030f10030f12 69
    0x2084058003a8107241c104d6a00459103000034480a42c0701c0c00c1d80c882c00d180424008000350000c0c001030000380d10030b07805582270380705494640202d15a034504900400c3c540c11106a21038403203016004d0300c0043d14004a8000b02c07403100dd14076040c140082c1e0b481e1701c8100d0054000b05526607240014407641000303c000100d802070031a685d01e09000c1c50828590100d81e110602502c4c10b884500250342c05909068110340808410745e2801445030300448859141c0300040b41c1c0101c40071212003160b00c4620245214107001c00002504503030505020001d0503030045e06034454842003204035185a40400c010f50400014840105d4807010388001802000030554610158410700e00a00e050080005040c011160281c07511803403901da080c000c48044100d111b156001c20540202c5d40ea084c10b068069000c06405000001243c40901d000584d410350b1802080c0c405240200601c00b201c99046101900000c0d1386c00c990810300c0c03650742e071a41e00e8920128068280c400400021b1006401045000c070101d13a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 279906115 1250 279904865 279904873
    0x4050709091109090f040209070f021c110c1c02040b040e01020c06010e0a06050108040807060908030a15080705090c03101d090f0105040203031902190503040305120306060f0a0c0203 80
    0xa0344442c000c1c1c00070700e070b10381c41000d460b800314120310b2000d5425030042d9000380c00019103550341038040d60610b600c40103607807c6202d43c0202d1554205440425103500c9000c2c1d80d0002e034010900d18440c0b400214099041c411007081004241043c2c8007130b000c03142583c0c151404079282c10b415000900401001c1c500342c83e01d5000040754801040c0c082407180c10b80706000107200e1707543c54402d615001c4841c10300400d03021a10070300200b40400c06101c0034001c000e06c510070210f10070465540c2d2035200e42069410070015511465100090042c1003680310141c0b440700700401100c2e00d00b02c00128a83d4000d800c04010b60f400001048070025049011409009441c44006100038201c4650503e510111203040c0c2078013030200443c842c0b0f2010300a190080340c00500450925010030341c05a44108810841c03415889007410010a107021600c1c03106039503014001568503249181000d82c1803a0f0f102945e0340350b0354410410050341d42c0d103003801d9808001600304680d032034004492080c1e07880445208041d6040c46 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 279907365 1250 279906115 279906131
    0x2406040f15090906031104020d15030b01060e0105070b0c070201110d0c060509012d1503120f0206090a03030b01052124010203070b0417072a0b07020405070909 70
    0x300c0d8081c00d0a02600039a200b202c034a60342d1084008445660000600e9004840b400171b04510380f51700030b48144a41e4920000d600150411034908a0034a40d004842e403404000041104a8200c40311031031040382030800500d050001d079100c0328100c0004001e8820610003065070030941e482002c04054503041d5802303c4000408001c0702400c200035246048520f1400c100000b15008018040c282d00312180c0c1103007802d00195844d1006601418550242c0b25554622101c041e0b528410f4104c2c0007580103222011071101d80a40c01070000030264412800d551000080c009500400505204469090325000520090020048450380300b4035101840c101c0d801c101d41d641c070702c0701a100c65024400e01d6603021098034950003140202140012200e02680080c04a000404e81d09401d059106205800240e0220000d40002c0341a81280034184c4007040885a00761014003811840060180c2400755046410311345080000c8620414000030301072512003001c503001c6805002c8080140c810031a050007092 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 279908615 1250 279907365 279907379
    0x1e0d0b09061501080a05072102031605042907080d05070905030106060e0409020d050a14060105031504030c1401050108030a23040e150d0b010510082406040f 69
    0x844240c5090845004000118102c9011038030a640410810b1310b40380116900d80c80c90400600d0300500c84014003c090b10600c045150211031000c20112800d00143c0701c0c1891150400303004e440600e6002880000c220901c04548007a11003007103612070002c2e00e803498a0b00044c05034107010b4401d0042c00d60201089890480c82d00c0d800c01c5100d642a5500c20983c96615002c06080c2ea000d0300c260004640350322002042410150400140c581c005050402e002c116079079410b1510a0300c410680b480d182d18100052445030601580f401000110020010307109464446064444c014200605100d013020400d0100948200d00181c20b4040c20005c00066a40d115483d40360740c44051440c0008007180303050500660400003801110342c00c68990782c101420000001400d043c050880610303101c01c08520710082d41c03511105a10b442c4210300340a1079514090500c001100d030718011200340881e00c803c0201019404001899000b000c0c0000d0020307407040740203c1c6103485507070080039440302d6001001c5115 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 279909865 1250 279908615 279908633
    0x70e0c1207080613060f14030102070c091e05040309060e010e10050c0115080703030e060712090e0c2b060e0a02030f01060503040c0b07111206071b020306061e0d 71
    0x4003c2900ea941c2160b60303040c8a0002c03502e603401110810211901d00740800d0b006d51554981c21752000e0001441d00e400c40d1201c44c00002203034400d100c0c1c2500e0780b816030110f484103414103070540e41e40c240500440c14259800b816462250040104004074281000c1d402c0e0b20a0300440108013014000d03e90102040100510681c0620703c450000c0d824446140204102009070104403890302000d8146541542c0e0205c0d0030b81285403070554482018450b0f000492020200e01a4210032a110800f66620b01030306203420300e200400c10003100c00305002c1c90030050455450382000021544403400010307410b80001c1d009051517045201e21240240030040508881d5008500408140002e924a42c5c1e907400300303c1e03c0344000c0750005c00d1540d504c1010405588043d02400a641c810042202c1c031101101c08a2010a070f8000d1401c455444002030003003840d00244001480fa8400c5150410728001390042683d030382300035250f20b000b00100c0c4860b00802401000c4100080b000401080e11003d041c01c0c03480203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 279911115 1250 279909865 279909871
    0x160b09060601020a0f08090a15121104030201051b011b020a0b1807090218040f02180303180603040f02060703021e06010f0e100312020f010b060903070e0c120708 71
    0x51140300080741c4150300009208140c50b40c40702c1d90885010351995841d200350000071109800c0f249805002c58090b900d003400000e5204075039186410303007100811840a4a01c004c40c0d02e11140c800700802d20150340e01404a60403c2e0018008403c00354807038522500518000011a1109214140c082803260b408a4200840c50080548900e03607200e032400d80d41c1c0a0080c65003210321b039005150400640e040c60b000f4040e503d0048981c2d206421841700801d003600e043e00e400701001640010765041c440003600d06012200d10640c001d500305070600382100c5200c0700000d000340c4250000300004040060340040b400b28180c4c0580b03160f0302d130402440c0103035540c0306151080821003a004000707900041c0009019040351000802200301c07520f42580d80c506448060b0420007541790501022011401201e042c10030049103900401c03a81031510041c2c0d0841b803400a050388941d904100c851080d075800564001560b0403200a01d0942d201d05929100e1803007880a054442035414081140403078100340200c2c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 279912365 1250 279911115 279911131
    0x5160c0801180c0f1511190311061e070e0406050a0b1b0a020f010c020d170414030303010b0706230a020d060e0603070312051c060906061b060203070302160b 69
    0x301a166081c0d080300c44490302610404408030b50072405030511611114400c0030404007515821071454100c2c03c40c1d611f0354a010707008221203043c01ea040500402246038003a040c446c1022001c0d00c40b5140e440100d01c058040803c1015900b2034449030f40d216130098000b80002809410300c41c1d9907071040c0c14680c010300100c8c16410071040b4614003805020130a11403030703507004119002c4c2100f82801520709640445059821508075001180002c2cbc1c00340000041115050391a500ca82c50800800700b1103801110590182d0401c0c001000900c1c3d030340040e910f11036808940402c001c03c1c06080903071070f8a1000807072010040d0340d00510003c0e51199004069094641302c0c1800b000b80c035442d1210740307828159005a0164400a001c10100e880c0c0c0c003141d80300c4d911601e011841c0082d0003007041300d40030030410645800d9a0b0742270100141c40c0e042c4180d1000380100c1c00c03d0404d18017002e0494003c241c0ca05000780405400000080c0c0c540e10940c111116400050b480c0c0c1c01210160a0454a07114200c82c400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 279913615 1250 279912365 279912383
    0x1b030c0801030b0103020411190305060415060203030408030c160807050c040c080a2d0e0705010f02030304030302090613030503090102100b2b0804080a0b06040c05160c080118 77
    0x2900552055a4140c1680d811880c0c8564070b92a41d0f09200061907002d19444003214248070720b2000c4854000c644540c01480da90108480c00d001040208079080d078802e00082c0c04070600100111900441900c1c0e01a0300442082c0e1650303aa00010a8103106820125504071910a00d5500304120f2101070b0034018041d0084450340d0207480c081c0303c210760310329403101d021a284100040c428840c070b030091b1400306d51400d140940d40c11040707124240d00c80d1060352441e0141e10f03842d02c03540359141004820700404092030080071241641e800a500d0344806031014040540014620301d0302c0e01d99800f03e90344000e4121050200d0350f5030f424450780b250420b02c440c500601540b060131000110314013402c3c0401400503d6007540c16450620000d030451103140606851003030b058908003141615014100600403007000e411881c0140c50710100f00c02c070013413565206601e450301a001da80c0e4810b05032204202c400445039680035090404a44211003035008103d10f40c24800850348031144030040540c0c1c40c1c8038110742c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 279914865 1250 279913615 279913631
    0x50c1207030b13020c120d090506060d0b04080307030b13050108010b1009121e06060626012114070603061a0f07020d05070b040e090f2e1b03 62
    0x12001d681c0c02c40c0415622030403407180c50590000e140d006010369178006045034640b0390131850041081d0040758401190641c4d6180f004140501480b2050f03001c04100c94890352030a541e6100100c1007405000900014004800200303014000e0340941142c00c002403039074260405160025000c6c0800340201006542040082c104604041f806600d1706c04554075a0000c441c00c0c641c0b81c0c4200102160b00b80e41021070b1803020703420309140454510382540500c1c404221181040405819013204803100d0003045e82c034142070441c0082440d50b05041d00c101c0d51440384010411507461114818018014003e0103505c2017400010703500081450407203081d910140310103a174406058018103031106841949000400145c06043da440740103180b02d51008129141c401c0c1d10b625810325202e00c640040900d4040081c06101c003904007241c10b40d100d828a4020841520341c0700655440340c0d090900b000d03d00d400d0b139254000c02c03001d000d0004500f00d107049003000009889903860180c0640c41c108040480d20382811 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 279916115 1250 279914865 279914867
    0x10f020a0302070302271801061d0a0c050c011a120703020105030c0f041701091509050a0201030e250e07020601061e2a0311030c0c090a020904050c1207 67
    0x5040e5030640c2540250545902d1034082c00700d00506110b540301000e002503107030008181e510003030a0142c0c1c3c5842000b00c02041800e03c280c2140c841d500014184140316a07905040941280301590025100002164407810b901c400c1d030b2140141d9000c0000e9509202c818524002e14103444501c1c0340c02110002112440c0c2c10103039032554224040130b40090000c20016203e50030400c02065184881c840091900d550341c00e41003e454850115450240d444c0c0501e00180321065403501d241032940312040050250b203940b1039580e0100e03104001d051584880c242d5506010510800300505046850ba4000c01d080b989a05035140b101c2c05292103082100300411005480011200d050310340707a8480c240c0e02c1c0307184030340d014200020a0b040400c02105140d0940703078420700714503581c403007000f40701c2c1e40d0058542d4500580364240c0c078030300e11101b44d00a0120300003070440060700e040505815681760701e0325165085410043e2182e0160590064244014843c00f5455003000b403980c40d0490208000a40312118 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 279917365 1250 279916115 279916123
    0x61d0901060501050c15130c0609030302010b1f0c050c04020d0c02060123150403060f050f130308070c0201050408061005032b0e011725020102030402060a1b0b040f02010f02 76
    0x740079490f0300054542c4a0380052030142a00300104100307407c465400c95880d98102001c6030000c2c0c0c00507546420800406409000d042c02c0520111a0295054034504a10078209504250b00c020041c1c603100701d5082c80018440c840d48403401070811b641e6a51701d880040701405a46a03d04010b1003404000640c0b00001c820901405110408000f00c03c0b5201040000355640001c5041e00c1e00b108000000005030148030745070b480c584145020030189401020090b0014004141900c2410f4051001000a9000079031a5011003503040280d812101d0380012074160003140c00444180c405e510a022410303500040d89421100c6c100e0031245845205c04032800c00100034980d00d510007400219152b041402001d90541c9400103150481c051103000c018450407100c00d0303c0340c5900a80510810051900c1c41e120042e0140482c0000c1d0f142d41131aa01040461089220001c208411164606101b01a044005190503001003118003a410141440c031140000b201c8200e011884440c3c40004090000c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 279918615 1250 279917365 279917377
    0x15080d03050f0c0901050c03070312240303110102090d1b06050f0304080304030309020415080607030e1c02070b0c070e280504030509031e010f0528061d090106050105 73
    0x84090581d2520f03c0884220380107090428180320003407105201105080004c0e03c0424002d540744e40040d607151b90340b907007254419100505e80303404c41540c80325032003000d071507042c01c5a83c140b42c00e0901d01820300e2803a00a002e541c00707141c1e01c000e65441071410711002040304806039030180c4165501c140e40b22802d84445c8203400840101e800c00380f0024012410031005103502600900700429140000d40c000703021125469240000c00a00c0f10042c0b0090108101e0310381c0c029603600742001041441c0c83c00542d07400700d40c813009010f03401c01002144050710034003103c001003100c0058592150946481540c99410a014025500d801c4600159442504c10760724001014004860070300c2d0f403c00e401001c0603000051064003806820405050700c2e8030200107418901d03e000c0d4108000c500c08640302402d4a02c4101d030030301c185052809100301c942000001c000400700145006049020f8000c0c8103016281c9688420201e40c0d61703c4440c1e00c2c1c00000100f9074441c0f003082c4000c1003032a4803130b0b005480c0c2d40654 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 279919865 1250 279918615 279918631
    0x203060102190201121b080601080c0706090c0e0708150102010b09070c1b06050702090603011407110a080412060c020105040305030105010c0c08010e031306080105010c020112020c0115080d0305 85
    0x182d141091010001c00b2030840e14018500f1030b000b14a044022400c4e2031803000c0c14511107041042c81c0030903540c04119140c20607002d00e4400705a040c0450750076801c0c001c54a000e4586540c45084400b0410b80086c0c00c40241000c000340201803800c042c0140c00e100040381e04550035418600090441d600c10700c601c0ca2040001840d0100700c3c0c0351014100e9001c455004126044103600044030320110030000d040c8020041641e8813940c60b08140306012103082c019050f180a0307130408240300004200e44144c50341c848071500d0007299a803540000140b40c01803a07030000c1c0c1818400540400e0360365a040541450703074041e0340280158180038104a00700c8804403070181c0055028030042c0030a6100e0704001c4040303400303000743c01006611103460390700719501c0700790f041065880000c60142d03107100c1c480a10002c0009080140841d8948000a015105008002410802d000309401245030741c81c6e05581764030721f80e08001c01c401842040d5406060400340200300ea00e02c138026000c0301e001e1290240602c141c42d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 279921115 1250 279919865 279919873
    0xc08061303050d02130311210d0e010c0c06080f090a030806040b06040f1401030506030a0b0c1b0d0c0302060a0b06040314030f0703090518060108070e030c03070305100f0203060102 79
    0x89901e0440e4282c21508418000603020004c51402c13500310800038000d075003e0295141c0f00d94000f0100811155030500d21a13010061a00710100c030600480c80c1c40c101c42d00d905111208951304030040b40c7c5641079080043c80c40028102c040340465029030400e00c60000c80a84114645820040c01e507904804103000780082d0891000a4072420213411000080c3c0c0050041b5040617107a101a858546140e08410000c0c242d0040101e41981e244c042d40390408010740c054040c4015545600303a0080c4000c14001c18201d000800309021800000b001200c401c10b001034030030601012000038040d111400050340107228000100702000800d10a4450b4041c0061540b4a0246150784141d0180c5960001c002c0314007007031000d8400d4141c0100105041c902c0b0340e8030700b0f040c00e00f0403081101c4003074a006000380d100600c07002c0101c030340d800503c400d810001504154846a5a0a00003403401c040145000d070580101c00700041000320028034032200c2c40903618203000103090007100e50100c0c00f08452131030042e44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 279922365 1250 279921115 279921151
    0xf0b12030315031e03032403120310150f030b06190c17030106021e0619050613020a030c030e06070f0507060605060315010e0d0c171e0601030c0806 65
    0x1400e242c0c0548030b40300240640e0704844400c5200041a000b0300c00d1510303180c2001080041340195903000c59000a00c0391140400d0051410110f55a0001001318510356a00003020032180310190101c0b000901c0c45a42d0324040c1d40904500400b040300c07107140ca02c00300c0c0c1000401052880e017107042c1e6080360902e81d28050030707200380b1a080b40c041503540000c1c1d45d0b0b4000142035040c40e1030490001c5011b414240c00400803a0000710140c484000300c120002d002d030704128140038a0400d2103040208444009001041caa100c1100040c01007a0301c56000c00c000c2e10000c1c803981640d401d60402d4040310002d031800c00031580d10182003501ca010413120300b00080e020b02a04418075008d98043c281d49402804c000907501d407a4804a03a07203500035030b416440344240c40344600d081e40c0d010201c500668416035840154035116a100716480c40079014218a08591504102515104120007411198045c03404c21103014865681ea8840c0c901380010748000300c0e02d15002c64544000507642d4064254607041e883c00132 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 279923615 1250 279922365 279922381
    0xc100b04051e0c07440c031b010f1e0b0f090609040309090624051e1606060311090601050a1d04061805070f0c0507090b010216090f0b120303 62
    0x42d110420440d00d017000000d5409016840b00512411a5000740106040e20200500300120752041c507902c00e0708400030040070342c2d003a07808416244c1c01070140c405e1a412a2400281e0f50140c81001e15030b51460f403520013814584081420101800b00d5a0403080044403c1041441b04d00c8086040194010300c10202040c0302d400c080300040ea0150080c98a5080c1640781d1520f030054410a501004040d6400b1450040c20b0790794280c8200a0390150520500e80449641076104841441c0c81c0494010804100754002e03422100e0f400c2d6807180c1c003285c1005002c0d200d10b80242914040e003080c4c0d004940200024007554010011a40300c0b600607180c9450700d80c03c40002280c070710304440b101c0c2d030026103505c2e0014010000070700500321031f04005c0d03004c6050702d0300c41e40081c58008600b40c030303504201114a00300c1c086440400c411081c0c07500c1c1c20700440e4075809500103030700d40b95a400214090703030790340c0ca40012101042c0e404a0969902070301c2c10b01060060008100000980d5182213000384c1081002c10518 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 279924865 1250 279923615 279923617
    0x9040209041703040804030b10031e0c0b0d020d0e0f21040512010507030506040c0f030f180309080d0309031d1503161b081902030c100b04051e0c 64
    0x14424038840005900d2100902c8180e04240e800700e6005601140500401010b0441168409590b114001c0d14a155464121804824078042e828003241c83d001c5500b4001070a031480064290402281e036544800c40c907040082d444089540b000d18549a0004581080441c0c598001c0c4d001200a08040c00704103a80494001c52183c008a520810000064142c540c580302209441721100001144d04d8403102c00380c00d4550080070700e84254030340407060720b04030342100900c6402089481c0c001280d031110394a81c2c004140b44504078601c03c205005038010103a1051250741611080b1050706d07090100401c05030305542000c14001c02041d003100d02c81ca004850305800d600b00c0031004092202c44001c0710003070b40320765000303803000c140300c10384554003401e11a001022411000a80040500c2000650300d500342e00d4015441a50300d02d81d10b00100a0f41540f08206884500211505540070180540000b800619280c2100d5000f00d0030b100000c2c007400e542800c2c0d005c2000c0c005514003200d0f81c8011800b401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 279926115 1250 279924865 279924871
    0x90b0a030605030607030504060f0509031b2b1101140103020411070c060306260d031d030a0c0c06110d030e031c0f0e030a0e0d030e06030f061c0209040209 68
    0x201690348078000703020343c0c00300405030203840c00380c0380051541060b080c2901640e030798000c003008450a00c024800411400000c0799011034010220400f4090a1a84241000880f842c0102d6180901c220750306035608a44224200d0401901c0d2625615400070301c807400c0c0c07a0f40f80c1c201017000e180700c0e00420250400c1c1d00500b28420041800305c0c60301006075280e03502c001d426002940000d594040030302007004410408074040c2940c04851040c0c13070005190a9590044001d0303001090340710400720680c005608807600744080020240c0703807200d00c13101340105901401e007403e03912149180030019040b40207200c58034112070568040c2c24409a500d0081d005001d0000c501401c521042003c100004403071140c1c10020302c424031012610400c9404c2c00310554140c059081603c2d081080090051500b0043c41c05200006070b4800030625024203096580500c4540650b0300004000100a803076074050342c842e8440c0a00b15000d25000b0140340c0c2502d10f03031302400c5000303400000c143c011a026186c240c0c0c0187e4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 279927365 1250 279926115 279926117
    0x20d090819080f03070903060605040b0f150403080a03020c010c0903052518150501020106050604180603060203070c170408151f0f0306230406020904090803161707090b0a 75
    0x129140f8014007850f80c0b640f080701c1800010b500b03803a0500c05c00031180200070051604131418800c0f980e0441c00038194181e08481b5900c1190125400c0c0907103c0d614080c1c50080d44c1001060380c030b0b00c80ca10307405006507202c0f0b040d4414a51134800c10303480c1d1a0068411106884c2c100b00105042254600b000c403c80c4500c0e0400d4200400580c800240e40b0f4541c000110303084180d0002082d055203040b0280e040341c1d21078000314156410314030705201070b032a10030668086407070701c000d41001910090002401003407140c00207401035000004100019401009003e04288210700c04141010b01a170038050a00842c054800f581d0040e8045200c00640c1200746500700041c4d5054404004030903140c0002000d16a0010080300242601042448014800e005d003005480c041c02804403041d640078800407000900060126502240f1008a910b465104483d900c1e400303122241d81c1c0c14004a1708500303160246100c0f00041c0030003201c0302d1036050251414010803050300c400c4409410b103180700a1a800a02000e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 279928615 1250 279927365 279927367
    0x15020306031614090c0a021c05070507060e030606030a030e0f01110f0604050609010903050d05130615080f120403030819110a030c020114071b1b06020d09081908 71
    0x2102d0a202984440040060150003d640c2418038103120003810010141100400140080c0480301d80105110785841070f180b26602c0040c11044080c0c800e8000c070007014050744a65000880c90b40c0d0000520608c090f4102c1c222001941c0308400c150391190d07408002800200c81c240c403c0e2b0107080a0a0f180d40c103c80c141019841092100c5143e450107500710b14201c4260300c00303814407080c40740c24088990000340b10802070200c0400350310060900e204540009010300d80e12400100d0101440d80402c40817644400c060094015220204c440c100c1e0034060003141d07008084030400114800030302501c00c018401110342c146413450300d003600d00f49002005000400501014901da4001d18450050700c02c41c0040071640310035041c04006c0c00c81d01c00244080c00e582c500b004007000351300c88420700b90303003c0880d181c47c0c052030000005405d1f4807588200c005140c6540482c20040d076000329a0b0000035240301d80d08981d00305002400031100040311344541a455041103129007400000311004000c182e00440400e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 279929865 1250 279928615 279928633
    0x30510030b1f060807140f220e0105010302120a0903030b0303072d0f0b1005030703080d151802090f10030b030f06100506030a0605061c05010f031502030603 69
    0x300c0c0e186441182c08510707480500d2140c040d509400140c03107010f810280761185903440c01d410041d2407580d40c1c00c3c440964900c00f041000c6a100c8031304c101e03420501035640a601d008000d140218030705030705000e03801701e20301140700204065201c1e2095034441c070461403c1c1549900c40d030300e41500a054501054040544407191f208039a101040204541e603c601c1b6440e4a0740c042000b8401c00054a95152000d1030145080710040744010502e00c203001d800200c044880c3d202c0000a64105115601c8240c050045e400000b050103200409010030400b8100103000d00d803d2640840310400103030244421540320088445810f25055001c3c0c050840040c203054400030b01c040010714095030004200300001c0d101e038030b0980e60b4102408160a0181d90b04000e120505011400c2c600003481401081d0040d4004000204400726940000000302070207050180e8070300040d65035074800c0740142c614408141c201800051464404580310040b00d810880d00001d00c41d10b030f0308400c0a9031016100c1c1d64544100220 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 279931115 1250 279929865 279929873
    0x1b030804030b0f0906070f0e030106080f030c0106050901030503040320040f050115020607090611100c020f1605010c0b0705220501020f0105010e060108092503030e06090d020103051003 81
    0x3400a10b000c0e003051481403030040b03410380000000400700049a04000140401c42e42c03c81180c007290f500c5070070f1074440740e8100d80110f40142142c0c1d0210b8981c1c030a0240700078070030201000406d999000b8274028400241c0b18420b0180c064000e1200802540c010031041002c603104200c90440b190110529130319480c0c118000406941d4810051042d0650701c40040001981441c24a0210307842d60024101916286101910300ca06a01c01e0b8410300541c00002003100c4170520020082c401d1b4550100181d80e01c441d0001c0da43c40c001c0e009084070788140004400c402c0c501501541c12035405030f68070005030030b05566102e141c000141c0400c050020134000e081261861403a0413140c42e040c440c0c480d000c0c1d49040002458030000c00c900e540075900d810011311540314101403e90f0300407000e013800c0e012500d400c48510710302404c804c419201528402c1d5030003c603910481504086901903521124031560550030849148030b056095075200c019a00c843d80154002d03000036074000480c8041c4d000307240d5683c903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 279932365 1250 279931115 279931117
    0x5010306020d0501050301150e060a0e040b010e0f01030c060e041107050c0f1503040f050c060a030501050a05061801030e0c120309040e01051902090a031a060a211b0308 74
    0x208a40c41034011400782d01001d45442070718014181100240b12040c00f100312551860f985000c0e0150f001c0403180015100e80b01d048410006021002840e0001d01d818206080b012600f0300868884c0e00c81403002c5840ca074000741003181600e801220142009280590603a0304405070304034640c00c03544a561100200c4840c2c800342c05041c1c068409491071080030000c010301d450b0529115441104004c00380c5103185a22020381c0d0f03000c0c4c0c1c0003c2c047c62965a03400c0c481e00c1c0c001d602440c0c581c00000001c2e0b10031001d5140c1c002e141200d10680c0d00d400c44a0b15a420040180500b0540403200e5030703850820304181d8440d412400d00e8202e00003d032100954500c0c085000c02100300785404441e070002501c50014281232050b0581c40c03090700000c000d51306102c0c91481c5000101c0412103040d54021031400c40a0b0380f4594014010b5a00141d11125000e14004221003d0003c0312540c0c490454200c0c001134442580c21980c6116501254204031103810380c3c1d5100c00c0d00081c08200c90403010707014000c40080c031000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 279933615 1250 279932365 279932369
    0x30807051e03031b0c12070f060b04092a03060c17010803040302011e11060a0902090601020a0c06120f1d0d09060c0305030c0c100b03011a310501 64
    0x4024061541a80100344010041c2070007414895004204012810158076441034140c075420550f180e07100c3c002245285800c81c1d21401c400c0080001030381c48204415964030944032881b81d903040c0720809090301000202c603403069010b030421100c0030000714001d040100094594a00c40e0110300d9154a0307455490480e0859803a8401040c50440c0130700100c01c001c00b03060300601c00440214541400c50740002c0a003c542c1110340b0407200c0b8900140d48490003041c07100380040c01d140443d0030518152051902034170454405a006000c080042503003544080b4904c60142d0300484103408951070008115441094601c0b900189540c0e088078a80840c40307400785000ca807112206546400c084c611071107040020003040441881001d90f802c1000e140c20002d880740300d64040c01d109460b42e880d21542031242c860381702203c400d40181111840c00300300c0e55110020710382c001d80c0200280a0b0260009100260800301180d201c99407082a42d02c9080298601c01c50115030102c03001821030300f80c00001518020703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 279934865 1250 279933615 279933623
    0x603061807030509070b0c121c0c02010b09060108040c05010e0102030c060f150a030b06040f090204090c091b09030803060102010603140d171510050c030f03010510020a0305160c030807 81
    0x400504c0000380701005000003410b07903510ba807441c010f0204201c580d90400352169a01d011000300d001e1442040c401500c00400306101414442c844007014000d000f080c0386810140b0078000780002c1402e552160700e9071846507070301c0300e00b03100c0d03650604005540340009203040700d0443c40100240c40c56603500b481824040c0c000400b1650700303030030880c036814440307254451071900501e050b22041001c03d400102071504500700ba01c0004420040303d200c0c002600300d08401a401030700f0034080404100001d0301c900304441c19008100403440b203003414104007010219405000400d140c4082c000f08003240000e54207c04140000031f1180d690781d59075054001d0840307003690301c1d07040b07981d044110a07000454007409034a081c004c0441ca06e01841d002c00640502404580a1422444000d4015000b04126403242440400700e80d100d20101b0300c07018855000340a0240120141d56400c2d2030540001110740c4d4443d41500c44074100380340f204030040c0a20380001d05480340c0c03441e16400400f081d6002c00420126000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 279936115 1250 279934865 279934871
    0x12010503060601030b010912020d0f11011d060915221d01050a15030914031804021306180b1204140607051905040905010605040e0a05010605040302060306180703 71
    0x581400c041c1030840041102c1d06060a00c200c0441c240e9101d02041d0a40b101c0d04580e81e0340b03809500102c1c02340c120303000008100302c0f81e1040107002cbc0001c03002000084102684c03403258007800090262504140c1801d800d80181c801c0c410f42c00c545c03070481082c070000212022028100100300c0040f0b40c4000090440c401d640f40c4000c070034801c050b500c60320034145081e40345100e101949030401140246119124503446403044032507081c42540700e41c01108001e604800b42c2401280001007950b1254040b54032144490081c014010040c2401c1c000d03203111404008480301c41038a454420380d0038141100b410010307c2c15900000c80d024031078601401c5030044258071f080d610726040c0303880f4071210140621401107078451010413280c581d0050495591b0904400f0106100c080c420b8140e80394040e507004031860f903003054000b266155001c00500101c820501703403006c00d80c640d84109c50440d9020b005600004008000c20310250800e18021034000c480584082d23580e000c00f406106910302d0035243c2c6c50001e52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 279937365 1250 279936115 279936119
    0xa1806180c0b070503030112140604111903050c010e031002040803040504060b070f12050d060b130b181017041401050106030e100e010902030601080a060c1e030b060f1201 75
    0x107003080303036440036100346a1403501c2c1402c2a112a41d6a0105201c0c2111010701e05040b0700411580016503900710319444102c4003141040c0c50501040341c003083c1d07241c1c001c04503c0040000c0030742e8903441d10104d0303400901401d000040c260045a43d41d40c1d80d200703240c151003446030100003c088d5200600051a141011315100ca003010200000c2c1c50483e07210f004080e20500c110004506441300540300c45a0141c1c000c0c00088880b1030503580e90241c0404141094984040010614442e500400c13240911112003140341c0d03100c00d40300c04180143c20000e0350050746005481083d0401080682e060081420301036500e94000700d8513204501d00300c0342140c0d26071b042135009096180034002d00d0b0142055040c00e0110000e901d01d6603984500c80c00c005418107489040f07000311f8450a40c44001d10359001780903a180380d0384404c0000e64a80c026401103500d0346c50702903600c071558031404880c42856001d82c0e201c541008003182c128080d00101d20019030000c0304110640c1b0304880ca50042462090040115440358 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 279938615 1250 279937365 279937373
    0xc0a0e01090f090515040c0b0d0504110102240a02071202030c0f0f12070c05030a03080f011202010903020409380c030402010c1506051e10090e0a180618 67
    0x4003011400d1142c1424090a90000f883c0450380c8454211320344690922607995042003d0f207061264040600484001428540b11503180c1160b03202c1c602070134a9107500041c04004907514551030010301c80401c903c0401440d681f00680390350381c1020240c00e0143c2009039949036803003060003028518002d40e10010b6480c01e400d0f03003841a00d00c8410114058025030048544080d19020f41c18003550885600107881d40420200380d910f60007600f0060b0403a85032a01d14600a045c0382c9003658000348a00285000040e10038a8280d107041c2c650b410307034491111928503801c1c04090880c6103803c40741003244500540f80900e01505414403c403045480a50854000c1c9401d0300d030003c00b5003034080500041042002507600840e00c80f40c02c1d03600107850810900c420304002d00800d100c0d0803040e444003100c00d590b20419500d841c60f01034401c1c22100400380d01c0700b000080d104500144580c2d0000c04215000405522059101030280700d1701441c01042e14805a40708400c840d80c8511005036141400b001100748 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 279939865 1250 279938615 279938621
    0x30606110f0709090302031908010f08030a02070312030b1915050301050d140f060a1a0102060403080402060901030b0901150207050a0b04030b0a090204090b01031e08040311030c0a0e0109 82
    0x2100c41000545141811207440c0c80c2c40d20054043c06400076264416070081500c204202c0f008081c10307040e802d04101c0810001440002e003885400910781503c030000c200800048100d400b60803840d001041c00900c1d5030b541000c000d24480c20030003407680e201e8103c9455125100d031002000f60a00001542500b07140b02c140c5508039016000040000c01c0c4011300484e190784424940071a0000388540203001d90024007454004813156007900d074040d140501845c0959a04510915a018019400818840401240c2e6200121005030000d010f20000c0b40150400c18018003454606140c0441d891640c20045040000c00b13034000080e08e20704098070956a6410b000540180008558180c40585400143d100e24003450102614561401021698050950748903400b019400b0f031090048045500b41926102030034401542d07a407501564031030040c0440c00c001141306510100351800c141c19900d07495059202820741c0c2d5054414100904003664500d003000c00103043c283c000d42e28a41c14190100c082d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 279941115 1250 279939865 279939887
    0x3060915050a060303020a0206130b0a02030319020a02060703050a11040b07020901080105060d2d050c091f09150914070207080c010f0806150a0f090e0c0f030901020d0c030606 77
    0x2c2c0d140900500c002503001c42c014846a4040318074a031a220071203000c0410000d00e07401004840d100080940840381c001c000703144600e04141c07840707030343c011140b045900740d110701c8060340016044000012a03150290340f04580002c4500030001e40c0c0059032060404c20383c403030b40220310103a901080759411441c0c00c03c0c206000d0b108460091210b402c051010030003824206030014040a450481410040259407020701e00300d5101d14036411003885820010f841e40e08400c2d140d801815484005080203800d8128040b1001c050310101140c00c0c40e0400340e100800004600300c1248140c4031000804200601800c480305e01700d201980c200f4140404040d02d4250180d12501c0c1c81e0f0000c162810301d980c0c2141580c5144406820000000d964200026407420740c5441e210100030004500c0442d407550010043c1c100071380784d403100d102003900c0304c0c0001902507048501c44001c0d40100700520401c14490065900465081c00260805030035101c444250386d03000680c040045ea44001c02c000030365200c00f40c021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 279942365 1250 279941115 279941131
    0x1050607030503012601060f0312030605060a1d04051005031606020c0108071e020d0f0e03070308070314070b0a050c18040b03071806090e0f030304030c0201090306091505 75
    0x3140400d2540c010340240014414001c02c00100c4600d90b44001c038000603580c04010807802008859140d160728004038500f13000039151110740540d2286454064400c401c1510f10040645060204001040700d010300807a2045103501c40f202c2841c101600e1340c1c0146070003565003450035020107040c0801c1c503150007540404002422452401000015008100b001041da0281317060782c0305507201641a151100d07406c501588541d581c5007403007809540400c1c0010f5505150340c03910101c900c80c1000325100c100c003500d0300d80e050b0044802080001e907044010407607644681850f0280c070441c224494901d030040c0b40280e030424044001c00144039001d209003a80202d00b03c00850034a600c045030078400340c9038016014091551820754842d02d58040080340001d0511b0480c880505000e40d07800c101502561044940c01802d24403441c9080c01d0103d038480a003407411000314150742d00e984080310300e440194010b0303050003000ca0010001c16030701d01030103034594020042418038100c071086100440c4c100a100c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 279943615 1250 279942365 279942367
    0x1021b0105041119060302031302030307150b011403010b0703020106080d0c0b0703140406090302030f1303050106050105030c0703080c13080f0c09060a05090a0e07080604110402190f030603050d17010506 89
    0xc92152044c40300e000a854007450010380301d0b0b80e0044c094900042c8810080d41c144004100350341005888124100d00038003c010034407042521a0040d584c006a001e142c2500c80c0c4c0070320060102501d00710180c10301500910002c00c407181e0385c80700070b410700d102c41c540c41000809224008052040b0b1062640d0054428601000585000740f1101783c00329010b04002c00b60750312259080145482003040d1780e010000d100659669a040c0c151800a0b81321903c000c0702c440d402d1030000500ca60041c1c0541e07219031341001c8001c1c42c0c015590f5048071a89001000300001c0a028403a020000c02d10240040141080e00002c195003202d05c036032585001101581d0300c0c8120040c00400081d41c45104100d0112882070fa4156016202d01c03191101824040d01d07520f040c1c0c4955400002d041900048043c01a4010704040c03c0c0c055030201030200780c1c4160981c2243d0281c0500511424911480241c00d0b000c0080c600000e1058880d40d0325400c040990f0308000c0018801c0126990707000b40e2014290040004451803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 279944865 1250 279943615 279943639
    0x1c051f1401050a1d040204060e0301060905010602190f15060602012409020d060509090a020909011a1e0901080601050109051804021504030b0702031e090108040b0901021b01050411 79
    0x1c0c00e510500384060100080299490b0681c0d044040c6130040307080091040d921903494032401044c10b1200b50703046100307600b402c2c800038181c8403900c01c0740d0581da01075020300b804000902038013040c3c000303c01007281c00700b00b5500e500340846d040700000c100a028902002c11160f01e404002402c3d50380d801c1c02084483d80c04804980f40d03040c10744200b401c8030424a00540c8a940100da83c4e8014146a8481c0741c20070b11110400c00d065a0206020024901c02c462600d041d03100d480d44103003202e80320310342407608542c551900c60703591502940345030b03c02100c424001d10250103e00481c580300c0084e070094000c0c2d40801c0041c4020341e0005404c8002d458141d8905003035003c822284008414040c0000c2c1c011640c0f04c2d0190f88c030071040c104845c06541c001c210b00e5103d0806050003552640309030021319511368440c08803000d090482c001c80381c40c0751059403030030300c3e0362030700e443d403402d054000350203002e16650030840400302c4808c0c1404850846840000091540360a00741080c01082d400d440030302c03c06080c2e9032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 279946115 1250 279944865 279944867
    0xb1014010801030b0a06090906091a070c020402030c0c0f0a0201030b030a0507030b0921040e0601091203032a1106010f0e070309030c060504080d0b0411040303051c051f1401 76
    0x107141141d07003100825405860b0401a04000e0400d0b4010340f100d2410300d040401480000d0b00030303500d40380c890781460030f0711a803803400e03c100107400785c4500000400d00c5000c14007507d4103401840e04462080c0c1e415241c8821198800d11700320100c020000c10f9003040507580113641e050302c10007080d104258054040341c107151343c50580f521024003000308400408030200d22404d1003044403202406030400c0941180c68102c1c0c0c1114250031600c1902c04507038500e000a08254864032920f401c59070520254100e0b4001e5030313001e401030007a0000c00b510b0507440d9504010780f0010120b000111038040e454602c412444610020704041d0140c1094461442d10b5004102e5036550502c01c40d8052281d180006107c0702c985412911041c010102801140c100340c1488180800341000301218080380e032040215146000c00c1c031040d45d4101002524440b014401000464043c00045c444610441c10804841c188017184000700c0c0c50507a000c00c8561079041c04d4081034003851000b00081c00c071340786c0c03d66000500200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 279947365 1250 279946115 279946127
    0x72006010819110909030d0f09080a0e041e0c0201060b1312030c0206130524042102030105070801080d0e100c020112050f09010b0d050613020303070506040b101401 72
    0xb40040240c2c640708520280f00000041869814009001031180d082c034003a50b564070f0b000302c4401004a46032031005581c02c00ca5105141c02d065010950600f45048210f042e5160120180003e4001d40c4500c2040c004126001844004985000c8001803a141106000707007120050b401c403142c03030ba0782000103580f129055180541210864408002814254502281d480fa546000250008400726542c1c01d11203c070300c644c200340c0301d05a42c1010010b4130301074000c4451441c0081c0c032001d207004001c14891010ba25a04081c049014002225907141079030200b400c68000303c40100000303440000500900030b0902508036484500e1400785640c0c442c030b40008555505102261041c811545014802c59014001400001004040400040c81d04200d0082c10000844062084e03519010f014250b5290080841d000d19400c0002460141e82389441410b03141081c403400c2c1d074544003d0050360300082d010089144070358807410700d078122800c0c21500413000c030003103411524800d24021a2400d03503990003d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 279948615 1250 279947365 279947383
    0x1c02040b0d0506060705010e1e030a08010e090703020d050c0a060801030c0504050604091e1704030507050d050316032106080607080406020d060e190605010c06090c0e0720060108 78
    0xc00c00003119228640042c4e0203105549004081e9420140c10f5030581802184a41c40c5208861a024912040c141c02c50780341d115015a45020400841c01480401c025400255000e81c16030300f1070380d6540d121380024010b0205603604070f826030300103005080c203402c0401344907000741300b142800701d02d03035041d0f0f80d0300e40840c08107001e02030150307564100183e080c0d070341c90300810007082d001810400411030207810a1040c0800c90300507030301105040b00c8005100900421103040303d0f0000d01900c0c05a003410b04000c3c498034a2201507aa0744000c0c0400e00c6802c0c2d0301111681c040b0700c01e03200c08404003205003110080f903140300a06542c0614110007040090800b1070400d1780200d0a281c144503c1c0d58601c0c1800083c003d41f45000780c0c0d180f401401040074461841017034042d10b4100002e5051140c44a4281300f6180355000319800225190050400291a0340213501035074410101001007a440311480408a4022954800003445c0c0d41c68021100050401034900002d424000d4030035503040095481d5109505 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 279949865 1250 279948615 279948637
    0x50a060b0910122f0108011a090f060705030c030a1b0b04020f01090e10080105130f0b04081207050414040e0c01050d060801050c03180a051c0e03010c051c02040b 71
    0x15036840c0c00f000b044424120b0050100d00080c08810f03042c0d1900444d28640307512040c080354120002080944005041d0343c0da195903060210320780f0f500c0609211090001c5020190080402d100341d40015a062002d0322040f03d140d0b00840e21648928001000384070b4440c1000c0718601030000890106201600c0d2690107501600c46690913424840100c500602c135504c07010f16140f80714148031600850400c140100c4100000a01141c1c56480c0c6c0304506214403035000341044d42c00d10000e800960314030480c0d039102d4012843e41e42001351261a80090460888000340002c0740043d090050000b422b138918200742042d24200b0031462040c503440c0d501c1c044003084074144071001c40c0c0b842d0100c9454000c100039042c086c0003032046040400081b03046400030b860820003540e003604040c4140744006110310f405a04840200314040951116289a080c00c1c6a48820805c0c0c11400300c0b4151801d00491000c00100d42d03545540d14126034000107880401d4140842c6923004000401045484400342d40c0c2c01018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 279951115 1250 279949865 279949889
    0x2130902100915050f1b01020301060e0901080307031b06151706090c040f06030501060f03020f190303050f250506091b0f0402040f0303120b090c180a12050a060b0910 73
    0x340352190b294051003100c06d10442c500443d0400105040d00554100c48a50301d5045024079034900b001360381a401d00413504940d00c00c3c002c10001c00e01c1001c0400310b61071001c8020450b45141d451f10000da500d920207520702e000645401700030704182d08400c800d007620590b01030100c034100881003075100c0d070130441558030a03520750b0800e0f0911400c4d64864001154860b000b086540c2d0303200b082c030714064828482640700380c01404585105051149640525130340001c0110249420341d60251643c1c1c20001024140d40b00900c000500d01143c54120a84100507562240d80c1c10150b04c5d05510740f01e001044842940c1000c02500300c840c841d5118140c080c00105d40c451251022840403c009000da58044c5580500441c03000080c141c1000d1840c0106000b00020300002c40c25805108801d074042c1d410560702142001000360990f4450b0b080000184010705c030501d480d9275400903808100c00c40c10b081e074054110820000811020740314150410350182d450b14040d1030726810302034140d1807a22a860000366 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 279952365 1250 279951115 279951127
    0xe100507050408150906070513091802041157190302010606020102070209040b040f02040c12200306010c0809060703090531020c01090213090210091505 67
    0x10294050310060501c2e80e044985980d0245440d201e65002500d5042586c0035103c08200d00341d101e03104450314040300072a001915407a03d02e0b0032004014500c120500ea410000302c480040c1e490b0b000e102c40d070f081d8440800e61550051009032800055480300040c050485601c03040420360344d054014058000e80d0710f6500f410312180103007410004598106e40d034a02070058800703c15901c1e40d03009121140650300800000e52180d00aa080b03100c0c00c140a94041c2042e8001400900c0c0e406200d44e0243c450211400c40a8545d0b01041c10348140070160004030300f40300c15548180083d84603a82c08910304612101c130a1400c40d0440d80148401b80200381000a03055090040c418448203d074811040641702070303135411603410000c1c000b8003503000b10f5100d0303500c0034111015120b52907c42c0f180180e00b40081500305182080000c003c0d405021140c10355500d800716080560b0715041e10900c0000b80d07480201c0c2c060070501c100680340008a82100a101440c2414010b403a406030103841c0510040c1081d6a0300c0d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 279953615 1250 279952365 279952367
    0x506090f060d051807060e0603070c0204140612030f03010603240806040606090c120c0e030601090905060708150618130c0318030c06020f2511040e100507 68
    0x62000c8164100c0030000342041d841d4010b0348903d20407164000c40c000c5104e42188031070344030344541c450750000900007001e9510b0b41c58200001c542191030f500345240507071105d50218040e00c4010b00c0c228000c202200401c01e040c144001c0b4613008030115000b46180181e44c1c0000c813007600040c02506d003015522840c1820074100022030b900100c0700c60741c1c90820140e84240c0c403130340d0301000c07282110300742d013859400034052000b402040c54448003500d46017101d2003d52207500051502c10a000200aa0910205a04e450500030305020305080d910100c0d8410f1941882403902402400c500100320554041248aa49101d01c0501050044400c990b50b1036000c5024000c002101001c1035111000030f41c0c0e0003210110b644640d120f0440c03520144a18515480c0011010140600240c08240391050a60014495600408081d000b003007200d4105902c060343e01310004100300124260721141101d201c203001c02c0b07400c24003150f40b0880d0140035400d10fa03036146445403c104240c14076251500d001c03035001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 279954865 1250 279953615 279953629
    0x15071b050d1103070f150e060408040927020f0402040f0f1509120b040f02091303081f0509040519150e030a27080d02070e0c0702090f09011503080705010f0b0a050609 73
    0x11f500c8038000ca41c07075400c041c1450704542e403003071003103100381450408400742005984690b00086d414101c101c0381c100025400344545901c292141720350280c0c0c200800f203816001050f6a1001d060400034803030b1414185501d225004588102100602055240401c82034054184c0010745aa00840049042c0c8561a201c0c0c0d65403a1a0b000039440021201000750200104a200491900a81d0388a00c00e403101c14041014181e403028814135050b40c0301d4140114180a0300361500140704000300c1d060100807803a4000c01c2c4040c14400c030340710041b00003007809545003800340c4442a064a000340d45040e15141c1d020f4840102d02e958050350400c00d981014071090304241c00070040102d6400d032900000c2104009481d0a0240221110110f08070b0115024070300e031805441d4120350280100780e140d100c484030700e8104207004040001c40c2d901d82ca403558480700c103401070074015803150002039107400242c6401800d48002d0181d02d6020b07842c1ca140206580d460411a600315501601c84c180e0300e00000c000304006c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 279956115 1250 279954865 279954881
    0xb0d02040f0303030c0e040e030301060c02120604031e0306051c053a0201090506220c060f0905030109020a1404110f1305011115071b050d1103070f15 66
    0x3503100141c0000090540582090118520680e11181d0002c039110411048805103c0c000703a0a0b8000e000611841d809142d46002c01e40c0018400f1107620a41d882d081c0c0383c45030031035003100050b0140910300e0341080d40f00f030700c0108047c0e11b04040c4481401e100200f4850803880001d480103004142404082c40000d000d6240924403400303144c20042c038140320614101c0480d8109c18034024640d0341402901e0b1040c4030341c81e1819800b2020b01150303100c14a03150382c0394542c00140c0c250084d910300746000003100c1070750000081c10070352940c0d00c07013101c01040a81803500903801140242d04014240c8016503600c10500e007070b1808010034040e000b0780e180105000386040c07555103c4290b00002c4400b80d040304100030700f00d15603410000b22085921040112400c42a0030214220f5501601d80c3c00d0341c4e0b115800390594412403c2c038000d107140c02c06051a18140725010300903119900000c43e441020790b0700681000b29412120011440c1a01c43c0e500c0285404085101504080d0303000d0307c80190460681011758 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 279957365 1250 279956115 279956129
    0x20f06160c06020d0203070e01090f0b0f1e030a0e010612050c04090503090d060b0301050a09080706020904020d020f030906073204050d0b0f0726190c021f090c0b0d0204 74
    0x1d101c1c1f40c400c00103400c00700c08008aa0101c0c045502c0080e42d03400c450308800036140c1c4204030350700341a00301075000c001d900091031101400100720856a000da00240140d0b05c25040d02c103000c07900042d0f00c803445007112a9900305032510300081511384085000064881442d400588000800c2c241c07034180715003540250440158058500d40e285414021581c124102600c0304400070080398882550000c121100c00c40000c0080c4014040c0c81d01150882e806040d030124040c01c050b28100e04401081c007241d11020000b68600b00100510818940c108030141d130000351400d14100301c0b40e01600300034400341c0310749680d40c2d020000142c1c00e08a091a009139402018080d000900b10940381c42d05562100044940394001003010001405440c070640002d4001e0f06880d0304403818403c2c03920b0340101e00e10700400981e05464950303a440701080c0f1500c0792200c030390b00c180c0c085c1c500400c43c04c0086c00001000705118851909042104001c0780c564503101003210030b100b8004d83c1c1c03403198505940c0a80501d83c0006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 279958615 1250 279957365 279957367
    0x250806070206041e0201211d070519080604080a03090804031a060a0501050d150803030a05180601050d06052710060501080f070804020102070e25051201030639020f06160c06020d02 79
    0x109500b00244440968400311034410303820401e0040c3c140f4892f010b102d806850744c02880400c01055054008110006007480c001c00c0090591f00d036a40e4a80c003650003103c03d52281420f44110485074035003941c11100480310400b101e0325050000303040f40284c45500b010941e481c4c12201c1002951001d11009003101d009403900ca29054480300d000b40310889001140c01d2000e404103d82240201d001c078140e860040144011150980720300d001490700404a06100b401c090f800c501c0b000d0340c00c040c1040e09030301c80e00401490501c00c1e42c050035501c0540c8801e042c01621810300201c207543c0400290b000400c0d180140c5183c0c0c4500040f0300d03109155101f81c0e25614024140315000700c0d950103e45400c960082500716014901c1d0f001c444511034141a00305a002100c0103100284c0550001c81c0d01a101e48640d00031447c4800001e585903042941c13001c82c51480c1090712a40e2501404109a5051080007034507040c80e24042c21001011803000c28010410048401010130085505807030703422001c07003c11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 279959865 1250 279958615 279958661
    0x80a09020a120201030b01020a0f2d0c0519050901050d03020c060a030603050d080c070b07022a031b060703120f09030c05060a02040602250806070206041e020121 71
    0x2c68a8480000b8003030740001c1c24250803061650000400f049020b41c82020023a051419448003011044007610b010728018610036000c51504940c02d0364003046004088105082e46004100102d000b529800f00c60744a070b104904002039039680042d14110341050307500305010109072030100c0c102191000715680c81200413464001c240d51503800b41e029079119608481810403d45c009984902089640803010441042200000340480a4079070300080e4a004a451001030a85081084020808ae81c0c00c0c2000c4e00f8140c0410345010840080c4007644800b02080b100400000b10348548030700b020180522010007205269141c9991041b4200f207941207080050f0280c91070000c110341c1c40200d041d07446200313030300104030907103120300c200ca040f40c92940082049600003107003060f010800c4110000e4400c8014000107040301c0c1071060610402860780a800c0d540740c54170f00446180c1e082100c4418400c00640c100d40180d8104040342a003102840c00e0f2234601e40c1c2080241c024040403018144201803090038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 279961115 1250 279959865 279959879
    0x60c06130605090307080304060b181609051221040b0f03070305090c03210c01020301030605010f080109020f0d080913020c0f030313021005130e16030902030c01080a09020a 76
    0x1486200358400d001c188800d4031841d6200d5924015000c0c05440314608001050002d452a80290403415000d01000b103804409003100c0b20010702161004d9152071500d17000c0440da640200d00d0300152030221008401140c1d43c261080d80c03100c04181010300c0f26458000d42c604654100143d07001030108041e400d6844070300d0700c401180b5070001d41e071000c0403c0c240300215030401c10100d2928403007400070340248218402551200001b880c892007010402e1001c0050202003031080c0001c0d8040c500920001c2002e51400ba0925000103071941300721420792410b02801c005036120310000c046000c00300c0300c6290500a074109440503100c0c11100503800801c10b081d0100d03101c056006805130010850540d230906603000743d90740d20b078801114054940200940f0100040c681b441100c243d050b02da250140c201401c00c1d5501c1880ca51582250803a030840008100482c4900c03451001040d03150318060141c0d42c00c9601180d51616104c03049418407130312400150009510341e2000c680141c00900d2030040300c0d81d40d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 279962365 1250 279961115 279961141
    0x2a150d020310090b0d020f19031703060a0506040b0a180503030c0d09050d261201080f0706050705100c0e060703080f0c0306030601090c0c02270a061211060c06 70
    0x105800350142040c884a082d450071010301d0001c5c1d5006004502020303410410890844e40c50801d100d50403041290100105070400f58009d040c03000d4540c0103039a07062010402141200d07030b600007881004100400c0c085034001005803240d104e888d0506071049007414601c55240d180d940c00040d0980700c04614100b24441c0014030200c843c0071901e90002058a91081c422210042c0c200074002a90030b071000c18407007546a813450b2005003a094a0b07420101c403080d58502d001002c3c3d000c088550b11141222000c0142403001c0801010b1a0a0243c94008160b41d2280c840d80d0b0443c000014070751303500020032504e0192180c200e070420028025581c0398103a2401510303031001500c1c0c212561074203c0c00180c0e288910000c40e03016400050040c0100e030710340030304074000e003400240d107408228942081d440140c07a2800351500c5120300c1c4249000c482407126198500d1a8001c040c40404c508241d410041e0b0300e4100910001c1c503800001400c0d5801605000c1101480340e10605440d52240c1001c010fa400d001c58 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 279963615 1250 279962365 279962369
    0x191e030f050606041a2d0c1002070c0603050702100e031201051e190911070b13110d03020102040b0c030301080f010507022802040905010e2a150d020310 67
    0x34804110940359582404014060790094804c03880080c1050225080c03102d0141404010590f1910800e00c1d002d42003510b4a60720300440243c00101040c0001801424002d030303610701c800715804605258858581e2000c0e80380d40d120321014165200041a1210b20a1140407404441c02d041407084080d050980c0355640d0020818128221b074005c00410a441c002c880486802006415807007141440010003a4842400d02c2e05400b140048c40c2c00180034160340558000399030103400498642c001800c0003010340742c0080500d50404401034080000950f00b003021401d610080d1141d00e182c04ca039240590091050f50000710500720702146010000343e00100442c140e82800c0b003a50000e44020340b62600340d681c02d4603403001603008110f030020007010904030b203080c1d4941600103000300c640c030790080f8045685458080c0d49507510340b2000c100d0104208480c00403085054070340c1d0050440c2c0d100c40c4190300449540c4c0ea2045039221001d56022031540c4c240c515100c85246d085540307051454061240001034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 279964865 1250 279963615 279963641
    0xa09051009030e0a060503060901090c05040315090201091d01060f110109060501150f1d060909040f03031109010905041d060106080106123c060f0e010506040308191e03 74
    0x131408508688520284c85c0941c00c040c1c00c800040e424250748a0107422220b0500742040b03424000040492100e44448000504c401c0c6e0018a445081c0001440c10503503402258089500d0055401b1140100e191030341114501e25204000a048103400c8030071620030f800f8003101c1d6003883c0740360f802d0000642c443c904a96400501e2008480e940710241c540002403e540d00200f8008034240248901c84011107923400c000502c4140780c10304e40340000b01d42c1d040c203640a981c008032100c502e20816401d4407a1404802c100f800c810308010800340001c0c83c40c1504d000d2a070150b40c0301c0b00c004072a90780c500b83c1100c00d50600002d84410b90b84418009103155800d21a01e00040ca1040e00240300e60038911440402c804002400310944d46c800103d040403503140502510001100103451042c09801c1c41480b014002c4400890001c6103004418008288103030040e52044004000030800034490b8003c13140d02d0300314000d1a1f5929812080181e4240401e01d50680e5006401d425108030540d0662002c00c62400f4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 279966115 1250 279964865 279964879
    0x6030705040204240201050c040e070e12010c0905010306080d0302070c09020417010c0f080f100807080c0f0306010f031b08012a0f230c0f0307031103070206030a09051009030e 77
    0x5180100d091f9131702621a9249a00100000d01900d1040c0c11170660004082c01d14203880003800003c599210040300f902240d90f5501e810480d8103a41c0039680d88010402441d041c4420707070031310407020748030844140884107150740040c1e5441000b00c880c09402c020454044215100c540c0ea84d8030502e420940300001541d0f500e07101d4030002060245451013010f0714256940315682d56000540501c2e0743c2d024001c1040e03001050b00004441c4001c10030351002e4608140a4495140d401e801c1c0056400f10400043c420303080140103000f00c01c4036005220840c2d41042501c0c4410b5521041e80c0d1802c1000e40200300c1c29400c025402d9280409103003543c0c5074248000700402c104048020840f40c07801e07144000d000085404c00842ca00003001d08101c000c41c0c22078811039181011508030740341380117a20411420603400201d810414590442000611841008045d6290842c0341c0e0010300c0900c0000c1200c036038650380307610450500c01c04101b8425240482d607000c02c107071b10700c0d41030207010480449842403280340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 279967365 1250 279966115 279966179
    0x7030b010e01030b0a0504151b020c0a0311060915030c12090109050a020603070504090e2407210e0d09030210050721180f08010614010e0906030705040204 68
    0x807403a15494120f0340c01007004500380e2908900d010107050080c10503070789640c0e4600f1038a158004c51160500c10000100c0884500340d210902a042c03000c0040c01d244142d4101d0000c01c0410b81600100c0714485084034442d40d12940d25000660081c42042d0f2800490004807c000f8401c40c520010005881c1c40011115035a843d02d22507800c0c0c6900b00401400b0ba08040e030300b0001070502c0c40146421202508041d4105a10b612803c1308951800d52516250b030f0080380c1a038010132204d81106040c0c90320f01001d032603500d0620806017a00b55204003035554010300324482010344a203035001090200343d5806880d105014004000d160600c1350100303a20843e0054070041080d806074007101c540c9c0381c1c40529460b5503064a50b000d400c0d4030391890542d06004c0d200100c49050312843c10050090b1400c415030b40d40041c10705c0320315400c44455802003a042074a1442e45105aa0019100031100314116288171182c0e41e5800801c2c1481c1180d404690007500100c2c5c08144d44a01d100c1c0d0702c101c010000026840300c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 279968615 1250 279967365 279967379
    0x4051e04052a030307020405040201030f09210f090e04020d0b071809020313030509060d09030c03020c150f0c120f090301050f040f0f060b10030203341812030207030b01 74
    0x840600b5400381c0c19801001180d00500f881d821160b8800d005040010b68400b800501c0c030195415185d00300d2b15148401058291184802e01354034140c805454002c0d80f0824000c2e000e0a284000d01807130003c81c0d55080041c0455a420b28100e4245a01c0005c0300c100342000304003c1d1090301019188044040010780101c0ca03000c2e64802c0d01c0c13143c81041c016045a950760740b01603800c1d40c40b48861a82119080050500120880c020242e09600c603503181d11141480d418000d007030903090034030309100c0c1ea10f10f408403402880f99001d40d020480481c41c007a0383d40d60000c010606d003c103400081c441030400844c40303981001d0044058800c07400113800a100c80d44d16080c280c19a180121001041500e003105038001007802c10244540d8203200f0071002a000790ba000016007012042e0b602300c0d00080e000410441c03008660521400b06028038064241910101d41000d075141c0c410603100020070080c04d03040404603030122500801802c00d042c0070744020142d414000c0d1101110300068131600403240c0001440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 279969865 1250 279968615 279968683
    0x1090834081c0f0204062a050703060b06070c1710020c060705071a01030b04061103040203100c09120813050616060b15030f0103030206010914040204051e0405 70
    0x115031203100e291800000661600c10348a038990401070300b5540d094820030b1207100744010000361800b43c8541d00b6950140b845030b14059080100c20f800d0100c1901d119000800018001041c0ca038071030404601c10701c0c145d011602d10700481c20054a141c207190340c0081c086207a0140c041051082005454518048104110680c0300d9003407140c85580c04140082c05441c801c101800c2d01d284a0880c1d0032a40c940c014543c00084406c4c3c00a59031690300c3c10602c010010184500b01e5003014400040c0e007140380940000341c85030000b0760300f00300080c1c41d1300c0004440381c46100620041c01e10355204109402280c107048025401c800d00407600000c44c550b000c2114a803450590350240c044034604103290103282e170742c0006800c100b40c086401c1442c0f83c54511000c03400070003962013141c5618020480d0761550400a142001c1a40300c450414584101c0800e80620000c603140c0c0250140c4000c0799a460f4402c04036070340800400120405203440041c80104503012883c1c00e07040802843d0010301041c1c0024400b40e07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 279971115 1250 279969865 279969967
    0xa06030b040b130c06020d0e0108090a0b10080d020102070b060f030d1101151d0a0b0a0b091f02060103110a060801060f0207030203030d0605030106090608030a050705010908 76
    0x52010000040001e50024100b99110a150a200940301e44a135a0890940216008040907070001c0c02e41490703048e80035030100303c81c9800b464004050b041a05482da21403c0002c405800c1ca000480000c45036000c440401f002088403000311aa1120304e183d00038001e4100c0300d01162610a004007159291800400441113200e004010301480140b03400c05451114401240b20244d5403030744138440120454192800003441d000f11010504107800c026039071b1840e001030445459510703040301346080d03868180c0f00c038041e2602c100d00d0a5850708508000740d04505110204801703800602c462140a80d800702d01d6134100d034401c24104c03542201c1d5004000d0108020701600c00000c6d051001040b120b1710500b150281d044080c019101140c3d02c03500440d0035540300040c5000404e440d01810002e40c1024071484005002c095402c00c815410800c81d10f40b41d214002240c410050041000d000344074080d031003541a654000101651401c1c00814403002c8900d044c01c007140c940d103007204824100810b07450042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 279972365 1250 279971115 279971123
    0xb0901021801080703060947040c0c0609060b0a0602010b03030d051314010c0f0203090303071202030d02030f041122050c210a0606021906110702060307170a0603 71
    0x1407461003400044881403401840701e000c260b1142d00000ea080c0041c030821080c459481922000c8190b49101403c08201c51f4034117240d14000c100c1c160070071403040404050710b0b050440b0082108140c1440441d15202c8800000d440340b4030b0305205404006040d84404140d4200791800d41c40705555617030682c201c0714000c0394183c0640080040c09000360b0f003070b8000c1d6402451a0300d11441d000580d01e600d81c911200082c0030392586e643d00c004009641d040002d054040d4030b00d100031450400e030b40c00482d845e40901e80004091207003c40249040d24002d01c1a41c1c0381c100e180004540302c0c0b40210f18080041340540d010740351001c00750760304c0e40c860800c50128400341e40f038803500b0405c41402c1c0141030003d14004244105c2100305000794003d036201c3c1003200d041c10116080590460405185030411241c0c00d0b4440c20956004207911095806404000055a42c0110000500034010002d0360b610344280c1030025400036000040004003030300501000c0d80c0c600d80780c440032003654501c00402c007260030a000140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 279973615 1250 279972365 279972397
    0x14150a080606220911030610120b0414190303060902040303170612120403060b0901030228120f03020105010b09030307020904060e0105130b0a020a05040b0d060e0a0204030b090102 79
    0x40d40d2424200309201c103148a044044014443c92007506044030680c502c00c40d121401107150608a28040003da134200f0300700b003550640c5910f07194001c1c2c0c0390710041c00700a086100e0400010180258250000d400490796415070784a4200702da80301d0f50790280c51004078046440d00d030002c11492864800d89003501e034581c9178150a1000c0750911a107215008043c80e07130044580520100d4078400340684180136150080c007980711819840c00d0025120f103401d0700340c0101c4595004101690300c0d003040304481c128480c46420102c1030000d9117003080403190480181e80c020081d4910401100320001d4001c0f5010760300800460362034240003030b21446018007495140c1c0c01400710101600d480800136802a108040015a200030340184500f51a01114606903150078440ba40e41807000f07140e091540712802030070852406002800180460049004626139218045107041d00340b480750340300e400500030450941c016841c0140c000d002a40c030502044a03200d00d0324000c14514403050081ea411032000e54060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 279974865 1250 279973615 279973621
    0x16030917031201033504050f0d111c05030403150c141b0c13062c0f040203030d0f0203060f04140c09130507020c09181216050114150a0806 61
    0xa1703a44205d0710341d8030070640014004005014010400100d00e100120030050b1554904410012491030b4018200d0040015888100c00545403415011100780304072a2140100000b80101034140c00e03110b002415848002404024071451038585804005440381c01d0100e103c0c604c00449100c0804412200718103424070140c101610003002c1802040f4007401145d12003100c2500144510468040405002d81d0300e26062080b40d0000d88460007000d1203000c1c05001540b68000740c0f850101c010b008401030410304000c201150340c140211034041c002c00701d080c040d03104440303000c40c000d40c1305a4046102e800714240408030f505080c0030715034840342c980fa2020426610000d59003040d5008003040383c3d0085e58829041c3d8418a17903c1207500a101c00d600030038500d9180400c0c0030030076001405094008100d0301c0f40c0e0350903080005089081c40c04e0310f280180c542d0a00e00f507042c8210008080280036509081300b514882a464a0b002e1003211841207152400318444240460081e05008801c0c95800c08000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 279976115 1250 279974865 279974873
    0x4060b013b151312080304171209010e07050d08030103060b01020a14010b04050a0e0a140115030605040b18060a0e03040e010902070209091902040b061603091703120103 74
    0x103122044111140d030455a01890800240c9107440405401c520000100300d910b0400ba01c00310f81000b418400241c1209692640c50f2039089010003440104440d0004441005030002c610640d10850000300c0300d000142130195005018040c1c0407001d5000d8850382d02c0010311840c4c0007811001e4290045100ea180d40d00750f80b1524041d01c5480a4603042d40b0078154000c1c001849019030032640300070b450001480c0783da20820001643c8000e0003020103142000030701c006525011500844c02070344810212400080c0400702405004505186280c4010b003580004c284901500410301c13645c40341440624681c0c54100c13584200b01029201605ca0307221500265403003810390700840b4034251540c102c0b8107241d91404880c02105003600000c06640d00860010214104510b0300c43c0c100e0215005000411124013540d02e645038a03400281c411034a0300c03000c0d9001d888020403100e050044500c200c819110506028001c248a841841c0284010123901c54140710088191a510000010080b000e81d1039521 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 279977365 1250 279976115 279976187
    0x320d0308060411040b07110108011d040201020a0b01271424060a05090102060928060b03010c02010203011e0305071215051602010605120d051c050f04060b01 69
    0x14254210380d03100300480481c0d1211021300020305401070460303503420840c50800b5a0900c0c281045040c04042c0300184440c00ca1211103500c0045140c005e08450398a41c00100d2038010f4040340030304040c43e01400456880034400001500b2181e079416588030350985611502141d0407108007030720716071501010845401954020250039141a404a90241e0a178400285c107503000b0780c0240081200001c4d4080156014070001d41d228001ca07000d010700501103003840c86640c480b403240c4402240c80b42c80050401150354000d0170301400140080104031107110300a17000354000e0203105501d400c82000104e10844d41d49159090325440000b4140c00e509d003000c201101508c0007011501401c1c0c2c03031010301111308580304141c82010014641403400c01c6442001e401c68a17550031090007109030032a0800d450710001048811a215840c080e80e0b00c0d080c81032a000d016042c080d00960f11810801030103c0e00302d0540d1264001c9000d44020808504440010f4030050032a0204060f418091100c84040d850300b09 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 279978615 1250 279977365 279977371
    0x21908060d08310312020309010804060c03020f040306020c191110030b1914152212080405010e060909060d0c0f060809070f0807031103070f320d0308 66
    0xd824030700743c20180c2e41d032420008001103c0c0752040903114104103010240d011a41410001e0000c0c0d403070850100c0c0028100f8a0081c0050f083c251038840b01644a80300e5412a400b000740c0001c500d4666440c0c0c43c10802035032169070b04c8440c51041103070508010194044040049500c46d1a4120a04030602072081c3d48e82d00800c0d48051640c0c03804000c1044c0c5a03d08180034416243c80e40120060a0041811540400b4032480d400b80d0503410454413402c42e1040ac840c11400c0c846c80003040403814060039929150341d90003207104800300d02e440c0000c0024040c0500260741d02601c4052105007600103000c0e042c081c02045035480f03010a80400c40c2c500300341c06801c0c00107008810300320040c4d0f2540d0f00720034071881030351107000000c02010030003d1000003803054502a20340b034907400b21010b1500e00410ba55102d140406889600300084007003056804120079001048055400382965683d803207681a00c1000c9050708080d12191140181941c410080c0020703c0d8100816000c8800203a4a0894800c0c03401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 279979865 1250 279978615 279978637
    0x601020609100e070906120c0e06011b050a050d0504060f05071e1a09030c0105060402120106050d020403050d03020c0c03010e030a0e06090a1e06030509150a0b13021908060d08 77
    0x103513004204040c1ca80903030f40180005000c40151100e09261403454249981c0c0701203551210041403018582c4d0160031480d03841c0240180c0343c0341112604000e400c008002d10002d00c0c0d0300c918240d10303c0d819080005442180d2050f00d41500042c040801038645118505004100130000c43c408240c5018900c1b9a5081901904008200045040300303404546402ea84552040e0300106681aa00009000d502e5000e4000d440550512100c20b0700b203070355290180291814407202042501d20030b4426410b4500450300102101d01018048070068003e5014403c0d450060241c01310404032401c0c14090400b010030050f00641c5047c2c0700d0700b811104c07a00140056541b0071000c20010342c0341d42d00c00003101e01500303a28081080183c807080480d0780d00c40844e400802818100820003140640120740e2801c0c4200043c081459640e034020b40c2c4004048001040d98804418005150b2001581d07010b412028220404001c0d80762840c9020380d0325120846200d40d1005a4170003000c00540c461000c0c20700c206003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 279981115 1250 279979865 279979873
    0xc03080c0a05010c02071e0f0303051b07060c1a090c150d0f02090414010303020309061602030a1109011d010506090a0f091b030504020609042f0c060601020609100e 72
    0x490b50740909440e011090030b40140d110000074024003012541902a48840b403554001c524a0400d00d400110b07902c1c4006400d000010903c11400c000b45019000203194a10965070301d19211035024100980054040c1c440c3c4500a040b041540e44050078980940740080040982c0014041000140035890480405580c41401144540501c9010712148003181150150b103888584041c04110b8600c03101d1003c81307141d40401000400e4012040391840c01d0280c4406070754580c008101c641014403903000940610450b6590020701000d94105600e05a080b5580c0e40a640e8a191440c1c00f500080048000e84959100400c01460207030700404111001424404c8020303070325403080c41c2034041a8407414003241c075066141c07501300701155440b40038245401e08100504054002c55018040e0341c5d8264002c540d0761011844800c801200c500d202c000c403080304202c0c0c03015811100d0302c40c0c01c0a0340300d260034461500403800c3c0750300108642e8032a4540c0401811131110380c9003d00d02400798040203d2440c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 279982365 1250 279981115 279981133
    0x1d12030c070e0a05090304050d0f0201090f080a02040b030609190609060c090311060703200f0f100b0d030c08131a0c0c0d03080105040b13020a0801030b0c070c03080c 73
    0x1006101d8070008201a9442c080c0501d030119080c800d844000300300c80000d03001048103001c00d9680c0b000c001c1200d504450072508203410352005880303251194001c072220f07040509001800140c00248107000d01d1090b5028800c11424070700781a41d41c0d90960b541c00090b080f09840303a8a844280904000d0103001e034070003244982c000d45541080350244d036684c10004920310707400c0c0b0900c09810a4101c1000c81580c07101d03d00700c426240146601d40f102e80e040d2150307010076101c21624804000401d440805c200507208001c614015079560741030798600d081101c60400c8080c2213a0324042d14242c900c2038158613000d0644035240d40702c00c150341c0302e5800b480d0085c841481c0403c032000d00c4080b80c12040200340c00705da610100c0310305161400030822801846020142c001500203540f00c00150304448050f10007180c6102c000b00003030625102c0110700b08426102040600030036078040300b990304030303400348a0320001620744120501c3c85100d40000a014407558500030000100300b80700400b444421402503507280c0c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 279983615 1250 279982365 279982387
    0x140108100c14030f01031a04031403040501090b15010909060312050901021e06010906090507122d0f0506060f190917010f050a02040f0b0306030109080310151d1203 72
    0x141040d11310a070301d21851401441040a0788800845840c1180a041418906a580100400301145c090f250390300b00030000c9010882c00f5000032100c0c690080c0c0c03008542c6050220340e400718041ca080c140c0015200e80b0000340c6003015205510a80380c1141c07000505194404058582d40e00682c07401d4114407400000e4210140b003882e2100c149081355001c0c0009514191421050380d003180c001105140c0b81c0014426255000003501c450390418035030100f075018607084458400031000940442140d0015440061031503903034004130801031024810403043e00d0355001d01520740140c1c008c010003118100f040201d1415100e4014500590514081070a5502c40403101c1308400154400c6180b43e440d030105803041c40b054003903d03500c0b1071062011400c040c40c02c54050541c00c602c0c413236400d1000c000401300303c40b500c00b90403904010b5000080b05540c0c0c1071811034115014030301c2c85a126542c0c40542480d0b17945208119032001510644850600f030f44e0004204085182115140c501c41d210820980e41d070f507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 279984865 1250 279983615 279983617
    0xe1306060c0219050d08093d030e0106080c190803040303080c040b0f070b060f010504061805031c0206070305060a030b060406030b161701050102060c030a060b0d0f140108100c14 78
    0x5506c1903442c2921003032841c050090841240000000702c00240100071609204107444084c1060b00c41007204500e604440c05800409007100074135410750910102286160000403140342083d0246d80101d204841034404440581c038602440a00303030420402000400e01c51031001d5003180000108925081d82e90181d2501903018891030182154045892000c0c0903560005550018058480400c414100c800003001c51240c3d015110910884400a10001008640640180070003074112200300f03040c0e0007950203403087c040c8a03900610596001401092090040c00d00402d00500440c26407401c42d510051240d030010310140d086943d03148008082050350810700d0103500c0880e580c900011080030014101d039000c0e000028291040001003100340d80c0055003035407040d03059500d651241ca54211140140500d64810b110404001c148803030003180a5101c0813118120340401c01ca02d8040c0300842040e0305003445410364940206001941803421038103c0a003400003850411500c0b0780076003901100d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 279986115 1250 279984865 279984889
    0x2030c03030703051e1006050705010b03011404150e07060c0201022e060f0302030c0405130807050706030f0911040e0106030606030c050f0111060a09021f0e1306060c021905 76
    0x1030b03100c00600c0859810580699160400e0f13003000105d62400c10801c1144281c2c2e4400c1d4000c11500044080901a0a500685012000400038400c10f1291100c6451017482540c1c15a0005030700d02d0b002c00c10f0300b150700c10880c1c40c204180107400083d141030320903110040042401d9042d4050169862480001d2109041d034010110700c010320184940c60454080b03031813541200c0c981c0c2c03038161000d0002d81d4000a211310000740440d40803c0c144da07140000c2803550030b0325000a082ca013001c03c555040081c0031420f681501c0f0340c1c0d50b007003021200030700200c400d03558407000151140609011f40411402e064100c200d0350051480003040c842e90300c0c1d4a803000c4481c19070003510003480100041c4041e141401050011350b000f4640484050400403099458620241441c0c1140d640c50352404115280c1c1440500c403101006a070070844280503001800030703c10300c0b507214442d81041c2c0fa45154801e45200300c000740d850b01e586150840c12140d0a02456040c000703122001030341d50410000319a0f807081444a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 279987365 1250 279986115 279986117
    0x60b030d083d06020d051806130b0a020a1209060507120e060c0703020411270d0212060405010c0915110307020d030215060603040f08071a01090603050c030706080106050a02030c030307 81
    0x8241031a0141c024201903002001c03600301b200400070301c0e616010804d20032200080484000d561500c4042d42802404840c0d84440c0d0301510210b0751128907500400c243d0300450282646174403102418404803094400da010717440c040b52051060030040743d8040304201d41c4202a050100f0541d030800009242c68014064010940d404040c0520440c14a4003910440c903900800b41420f080307151420703030b00c07441c80e4002130a449915480c000078143d03680e03106400f0080c1c014008a081410381015292542c00445041d5502d60034502b00351704803482103110104130b0b6142c0c04840891800103404940114450b03680c2d203c80c1c4011700c050005680c2d0011410501c520030740003011a9496014048958480189154440c00f001d008000100d104800b80d4070748203178410449540d0382d149140c032400c40048510800f40f0911100d00100300504180e1011040d2401401140c1050340110304055950711a401070000081c40e4800411040c0d00403805480e0450040c0103580c240440906800e145403c00c0364414 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 279988615 1250 279987365 279987481
    0x110105090d140c030306130204090524010c080306010e030115090504050601080c0d030f0c0b010b1c050c1b19060c030e0102070c05091306020403050109060b030d08 72
    0x1403a494001c440c40300300010350b810303040c24400d124030003d480c2c1c000180311601132042c000b00460901059412076025000482d000c011604204484505855040800501c0c03c240301d00c00080d1903010b074002496003580980180e146980c1c0c0001150100c09001c20290150340310010203406003c400c082d000a0490320300005070a28160526500c0d000c0e040e4030030f04094000c0402404152a10820518010381600b0148280030044100700d900012012015084422440000c00c1c1d40040b840108030300d000015010b000c04402d880f881044400c00d551400101e070f810041c0d0031000300c026645a00a6450109489a1003c03a000304080d185841c0c1044031100d5a918031081c00640502c140040c44441e01b0086040c450541d940402460641c0583c074821035849001a1071229409403c102c0d2950002d41907442d942c0d0380c903009011700310401c001c80352070b030030031200048508002a110016201d030b0703641d808058a9041e20554000d039080d000f401100c45400341e9003200c21350f10907000c0405115080f12 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 279989865 1250 279988615 279988633
    0x3090307051e0303040b0421020a0203010b03010c0813061b0f080f040222021911010b09090714150c0a05070506030705040612020409060305061b0f07030f11010509 72
    0x81820840342c0305401891598081500e506840004141c07540568000b503119401e0300c46092070101095070802c402d030102c44072102c04400c00e5000c94860b850f24829002841441016802c03d030036034643c0e42158002031554030001c3d120880c1d01d80c481a080e401940c3c005408040302d0a4800c816045844000100c0c00c0c0b02d86000d84668031000c0554828002c41d01100c0c075050580c0042c0c40703d1a00008030070607040c601202c174000301203036044684100c80c21142d0350f804e080b460000380941152079a4500c455180900d21311f01403d2100c1d140d2720070b8000700050510386007884010301d101d1441000981d0000c0e894082540381c5d101d40350081100a52100040c484c14400b45002c514100301504400e00508080c404d100303505030042c2c01e940680e00c6034240b008c07001c1250300048009002c4d540c0129011b509180e1b00105006001c60594062144540c14400000d0040c608070081d108044003521582c50403c0001c001c030384a0150490b000c56686040c000e41c0381d01c1c490315800d440066a49040c0c94000a038a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 279991115 1250 279989865 279989873
    0x2d0306050708040b070f08040b150a0602010c0e0a0308090114040b040b0403020918030a20060f01061101090210030c26160e100819050a0504031d0306010b180603090307 74
    0x100d640c2c04517203403806805801d45404024100200907000425020102c1d02040c0301c1d000b049070641034108050400c1e07625981ea020003e020303001020340759001c5001401a90080c1c20900100d5054941205150745803045e414011030390b04170031003203031b400b0b00505000108003c442c800040004060030045070f61101c0c294010440410006001081d01880009440c409000040280d8080103201e05108840082d010070074155085210744404050190204208024410300e40190694407a642d81c082141000d0301c0c011b00300c8041a070b004c0e610212500c40d4000766403003500088030074141031804840708a8068503551010400c0100c00860408070010023451400080710049250841e01d0b1103248050b2400216400703100f141100d40c200042a00000c5080d001008103a0305520f11950800840c0b40282c5003030000c1109680440025070114104255114140e100341180f420040282c01c0700e91034220142d03855400342c09a07402c41e52002200c0d00c2940e8075540603510543e054809036644040d1403030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 279992365 1250 279991115 279991133
    0x503040804080106180f140604150801110706051b03150f04020a0804030e0105270333060a030b07030c18090609050604020406020604060e0c10021f062d030605070804 73
    0x1040241c0035203000904041f00148040481d0095401d03030707000030382c81d0f08e00000101420075078010040541c06d04941043c1c0419250040c50320074011401041192145618401d2000b45048814262801440401d14200c03900c0312109000788000c04040d000d40b0300d000401c00ba41c01c00721505020614070b01c1000103154000301031807042e0304246803091422812140c0218004103141240c1c103000175004500426803000c00844006107142803c0058a810b48030840e05000c0c20250650070240d074035000700703c060030f1107442c1400f541d500051481d1184c1c2c51401c01c6008041007441d4408100c10700324000080b1041218007006003008000c0420010300f0300e0312003030513240060600c0e40141d104000400200d507000c2480350f00554820b20102d04038203802101494020281d4003e41c1c0681311120030484a90000381c600e81c045680d2040d2041c1189640c1e041c822118188200980c00030030781e914103030310102d03c3c4080d083e02c000518681401616900ca80301110011208080420117040600042c001410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 279993615 1250 279992365 279992381
    0x100e0f0a06171506120307110a030f1410150e042a091a1f0c021008010e0f1513060b1803281e0b040602030601031a0d03050304080408010618 62
    0x150f100000d00405c108455a00d01c80c2040141c1800c2c01d190320100581e507511038540042d030700040c01904020321414030310210200e04070035204520917410343c1c9407115100c0c000c400d014641440c4008072036141680306203000d00c004008a41030b40030303103c0810390f8040b440d0007606019044001c01d6562410178240c40300310741c1b0303503041d10381d622918295480c19940d586c501803129010348410701108088582040e141811408402035115242c0d0800c9080282e02078032203412907200e10340c1070045458445010b915010b05a0f0342e0720428420400c0400c45060540c248420b0000c00300b0002005a61071407045415004140e03100c01c0038003400350301e000c54941001040d86200e402e24650b200b00d44180d110703840390300c0d0b9400d004250802001c3c90f06841850724407071014054011101d101d41d0714041c0381100c0290310880702c00d0b0100f80341c21821096650a80c1188800500127400f040000c3c00e01e4801744c583e5000248110707110a010800450190300030301561000344403507810414030103a03103280e41003a66001d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 279994865 1250 279993615 279993619
    0x1716031401030c15020709020a0c11011b08030c090a0e01080c100203030f04030302090d0320030412021302091c06141603150503030f0c0105100e0f0a06171506 70
    0x10700108910300140011906440452440c4d041c0c1c0703d40507401c0250f25403045241034030100304c43c00c541c1d420480a000c503e1007954010b2541d290540155060900c8016070f209880c281100b003c0000c400b0390040d5044909500310b02d0a1803203180c0001c1041007250840ca14401c0080d0040003000310810406565020403500318a0301c880000380207659010082c10140140118008103051501130780c101d030f10b843c001800035080c601c00c90a01401d02d490000761500025040c0b0411106c4600100603503054034882d4001d0040c0c0c45158081100c05c924900e040141d40390300b082030860075a00c102510300020b0802c030f81b200015036103040007003c40d50f26407594215054003804001c007038100c00c402034003991954140003502c0b100042652010600d0340c1c0129800d0320001030b468075486611801740c540d00009034000c2c810b503520b1554581c0b000302c0d83d1050704101544d4001064891080d014019400010b590000980c503644402442c1c0c0d0450343c24031401c0c070743c02c90035100c0d000b100c84c00e0000c0d50040d81 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 279996115 1250 279994865 279994901
    0x50919050c1807120b06092707020d021b0a0801060602070306050a060f03020d230109151517010207050a03050703170f062101050106020115090c05030c070201171603 73
    0x41c000a0040380700c0303010607031842d0340d94100c02041c0d54642c0c6c1600c81a800c05040140484650b0b00f0b0030003160b0a1650710301a800c40316000a5145200003074954505070194046c00c0441c84000842c00401030959190340c0c002d81d1818045150f090900c41d00009240c00d5005001043c03850038444215400503100c50707401401d00c02c0c02c2c0034400c01c0d07a02d0002220340c10f40300d0f0300f0b039001c41d41014908460011400c003160341000104d955005015009000300c1c1e4081d150384e480e01c200819400c402c6030b041c2182120302200840007044180e00f8141d400500748480d0002516040e0540e440b0360410381442821408600c0118100c014180d01541011941501c0303e0945514284401c00910800009140902c540c00b12440e103a61840064107801501803198024801c650316090007a000c1d11a035194803420404080000a0340d8030035008620207172215880d401d00d15201e207000000030307a1003020168140b00e1881220f41081c0031780341c4c40d2403260309103d041c0e008224a0960040c1514144025210540c0d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 279997365 1250 279996115 279996121
    0x1509050f0d02060d050708010f09050f070c0c09020301090c0e0913120203090315010306110f0d0b010314040b0405071a1204110d060c080c040303020c0103050919050c18 74
    0x9a100c500e004141007101c944091015600c0041d01c07600c00c02200c40070035402c01c0140300000c3c0d0810160780c181c030441d01d9920100f80e1101c0200044800c01c4408c3e64003174072a03e01190714a40190007200502d80100c402030290754845405200f41e9000381e001c0940d240d9654208000c0342e520490000c104841190001e8480c00c01a10b5015400d0303121901511644004e590218030b58001c00480740c42c4d15025055031945e0450008000c000d20703003440306861a500f001602c030200941c1d4400c071002a02c040300810f04000c0074120300740081c00406091070515a440d03c920f072446804151491046100d0b6071540781629180c40c015060035207a50000c070300041d14403400f6071440d2560307003540e100600c0c0c403407032403016550307820090b00d1644c907119007135004140c4240b01c406201b00341e00400d0758992661100030540d00c6036580003076144111322002d001600401c04a00183d803080d00183d8000000c042102c06500890b41420f0300c61507500340807141c69114140c0005641003000d1050022084454501010720b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 279998615 1250 279997365 279997369
    0x10c0302031e0c0a0605090d0201050f0c07020a090f0207050c030c01090b0706090204110703030e2d0c03010c050705070b040308030f0c040305010203130605060901081f060b0a030501150905 83
    0x7000300b81d40340400c41e50364010040290110025a10070007280c0048072501e6809040600046c01c09990b107020902404c072200d1220740c01409081e00407160781d2040c0f00c00341d407002c0c090ba005400620f001c0b86d03c4007025000007400203090042d140f844104910069075415946050307880e100c0b54900e424005d0700f020b030000280d07a8010944404403070b41c0380101a51044907242040c01821207540c005d40c0f040c50076410307040d400c1004018041c02c034440d80381003000103076100f072460381d401c030304000681c10b1400c038a220400c03050303180078100c140c50501046410303100340e01d40001d0030b40700c00304c3d0007100080c00403400e50140b250410090009080424030350f403400341551141101488010b01d564050070504003c61040c3d402c1c20200e41c01950018021501c90414000760b240c071500c40b0798280c60080c24070020500c186480111581243c0410004181c1000c101c3d101c200c464000500e111800d40d030300c801c00a090f484000c002c04032185255000503143d07042401d42401c0d58400d14100c010001020002d101039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 279999865 1250 279998615 279998617
    0x120103111f09060c0206160501230c16110a030b060a0e1504151208030402100203030603060402010e0307030b100305330c04091508071703030411030a020603010b03060a05010c030203 80
    0x20f50142c0c60030202c03441490011031658800c0940c07100b0444840c500701c070148001903200c281c4c2c10080074443c1c0344014130f01c00c100b51100000c2d1400c0c00200030403c0200110800c10f50b1903884584100b05083d450307209540018000302d500e501c199400700745201048030925000f030f2a00e0261586032207070b010301c0c00d00310004d400b0038000300c030564065a9525202489036801d000c0101c0102941503000210841e01e00d8110300c04d8005039801c074000d01c440004044158008000c0d0f0703105d42c502500400d40c654446e001120491141078000f505070003002c00c0800410f058a0100c1d101c1e0f09440d10b8000c0041c50351601d14500569801c424404c00101c0354030403462082da00c2002e000d500640030f01e08880d100e0b140d40c0c6240b0310413603001c14800743c42d0034540705180c01c1082c0020225507590341964a010354611001a82d51544024540c1507007040000600007050b010b0003015112015045454081c00d560200b6010b80c000e8002c901040008000c00542e4680844c400c00030b010203180c07540b4460415900650785e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 280001115 1250 279999865 279999869
    0x602130e0a09030c121808030a0e060702010203090d0c1206150501031b030f0212011508090105070c15180507030b07230d2904060f0b09010c030203120103111f09 71
    0x12210000482c221a204046c0c0701c480d851841d0300b900003143c0d2070303250640d00d5029003d468041111000b11a1440c80c0c808155081240c040c0c015500c0c0209401c1045408200c9803002c4031200354003080032071402d403042c00c3ca40b0050300c50f036000902014140304106083c002540040e040600300a851210700e1000e2180318a40119410b01040c00a02540750f4400307806a60f407101030407980f14000142c1c08a40a048240c0c65006861300d01c8562548849103082e00ca04440c00e0001c5100b05d203103000010300d40035100702c8020428038001440c1c44050320400076681c0c1580c0545140d40300340020b009000e800c502868021000d4109052069000544122300f0007040d03031042c59015000c152601c00e0700007600000881c05107031040320081a1002462160001c0b0180124016450941e0202c1e00707e0000082c1000c0d03c80c02c2501908141d5000c00440703004d038081108604502080c40815540b90044080c80d018501c21410b101e01c010105003480300700120349018200c801c82c501c0845206075006001041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 280002365 1250 280001115 280001123
    0x9070b09060c070905100306150b0f130e041113020313020d23011e02030417030403171005040f050601120507020c030a080d050c0406020c0105090103090602130e0a09030c 75
    0x61608040c4002c50b090482d140e200764003550500b01000503202e80036100000382c07841048100101c3d101180c0b40e48400c0402c1c000c0a42c4035004021059541403200081c001d5644032504010625496405481d40018203a90032298040d446a60110324540001041400700040320308508524204013400b000c0c00180001900500a241c0501c041c01000720108160404290940c043ca40907902064000d0140402001050004c3c0880390310201c41d034004c8034000c9130440a4842582c1003041c1040295101620440030310840c403542404081e00020305ea071050007202103100e9040d2416041c0b005a90038404040040c0380b4180802610341e0f044141180c21040048000420307948a903020780c90540c90f007018a81c188134500716172041085000007040b10481c0c040090145459151a1140d01c0c02140612702c0542c0007180308100c19441100a000103200500d40450b16000640300c02c81280d10010f002509241100006e2011000c98500150040d08c5420b007040320f8010360314004c1015022100040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 280003615 1250 280002365 280002367
    0x503040302090c3105120c100e090a02040608060901050904110301020903030d0b0f0904080d0209010903021e010212030108070b090f1c05070614040b090307150c030809070b0906 78
    0x420642d122820380da15644000e500e0446401d01c0e030740c0004d042010280003e40c803c0300d1a00821700f410b0503e00110103060880007808013120010400440485103030500c4100080850840306560796010312900801d08641e0042e695030030090004d16024004000d1806240491300421007502c0d115442076001d07820280840041800100003800fa200e0808140d5040c4000b0540404048490f8820140032101719024030210b401c0605000a4140444014006c4a024400b925400c14260018034980d44145001c0ccc080585960003e80c0074150140000010613070481d5820155030100004818814222803480c00d42d803404069996843c10341c00b45102c6440e003c1a102c4050312440249030200c44000c00f404e48802180c46000360628104806407043c1c03180540009107607000d003591868980111a01c580f030f1a0522900c0c00c41c0750f00408503950140b040d008009001d41280e0214840c02c4200e80d80d8800000c0907007030007032200802401050050300300240802c00e00841c0e10803204100d6007030b1441c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 280004865 1250 280003615 280003621
    0x1090605060304060f06050627090408090112060e0c0d0c020f07060c0203030d02180a0b0f1b1e0309100203040e0f100b0403030906260105150d02160618050304030209 73
    0x194019206c0c5901444d00f0640201c0e01d0002001c04405011348600610b081e911500c4650007004200d450594001e000d0310b42c100003030050755118401e5001c03000310408010819954600300300ca12a4030407a168034106070040741c0750311804410300036120310b4560380c4001c00d123202400e14542d445004902c0380e4000d1100b800314220464405100381c0b003001c440b00788115250540005906604880c4000352071280013503001c00302d481c109140940d0f075501c1902450342d0034440d04501c01d2007842001142d40c6814402d800b400780890490811000341003506601075601c0b820f000040c4516114030f450301c4410340d0000d0005020407510311010320f0f0310008190861403070b40c4a50014508101d10b6410500202800180c0130007030580105650f01120455503600502413119020040030030010480c208100c41c0460041181c1d15040b0b81c42010b8045100c8818a85213a10780114100c2e03002e0300c810020101c400480000340704e210721403082101803800d8205443c1a46680b4561a40324500009203d6141c070004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 280006115 1250 280004865 280004891
    0xa030e0f0315090f030f090a1a030c1b030c0f0111070305120606040305030a0906021b030a0b07020f071706011508010e150603010b03061f090605070f0606030305040603050109060506030406 83
    0x425216031303000d601960307a144091301e1074440a80c00840c9050061581e0343d030000c0c003a4482d0210380c605400d100d5080d410f41d00c1d1605e401340c2c1940400404100841180c03000002c0072800e000074203c01d060712004001c507190000f981c60a596106c8214000d4903004d01036980880d03000421180080e1740f900040769695603540000e101d0303026581000d030042c840031a4105805800c03e24250944030581c0071a15401c004100b01300190b0f42100c81136030581c0089216000107440140700f690480c0c02801511507555046003200d16040a1783e0261303031505d4000810000c0030f0000c1c030186000d810130324440e0040030f40d80b61016140040611031000010840c600103004000d000c4001e104000c1e000300259a25651102c41c03010980040e1140c5110340601c1000704c69003144403104c10340349443c42c1c0301c0c104290700e40141600c590f00007030019181c103041c400092001030701510038400030714800d4545540f140d040940c0201104d00c142c008200c8541740c41014029075483c18152540154001004030321601d5683c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 280007365 1250 280006115 280006123
    0x1101050a0507023d030b190b0702010e0909011401140102061b1204030f1107030c1202040e0a0501050f070503010321050d0e07051e09010e0c0f07050a030e0f031509 72
    0x460310001c0c504513800d07280c010310800030184680d03996070600182800c01c04004c51022441145120740d84242410042d201c000b0300607044c01401410700842e907200c0000802e41061040725007881c580d56440c04080c1100304011040d000d8041081143d12009004001035075942004e04140e0962090700c2002000c03a8490007140d20b00c100a042402c0325041c180f60103001e419110903c1c20204902050400c400800024001c040f01d0308041486a40d61900002e5803842081c1c150980e006500d803c642d11002004000118205102d20000100c51502640000703040300040c00803410408100010008607003560b422030400c41a4641c080b40c0b40314441800e03a040c4c841d040d9151005401e03c000d043c2005008139040080350803c0e40d0b0500a80b0b070b40400c0491842c500818075603c240031034014040c0054106400da44060558840741c60300c44035072208451034008007000c59140d401390386190201a4408264551030406965420016500b040000c0d140d44095003e582c07071003d000001140e400e0100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 280008615 1250 280007365 280007419
    0xc0309110616080a09050913021f02010608030705030a0807050c0d210f140915010e04080f180112060b0d0504061b181a03070309030315121101050a050702 68
    0x364038039036100d01d0080050212a0240301d039520815001000030901030b6803000c51180e16a00401c40f600450301cac1c805a4a264201d60f89000c210765035805d02261068042000f41002d0b40281c000311713290342402c9401040c200e0004c10003802c00ca01400300070101000000c001c2800c2107182841c0c0103200745200d1040e0200030519002e6132170342c20042c8a401c0085268088480b040040d45111170319554486101d642d90910f200002100c58030300c2c01044103200130034015410920600840386044007480340d034002c0d6000011130303180000c907540c2011819a0408054083d5400070714060100c50300d414109103845c05580c01c0307ca4007a4580001508004407544510071203204c042e584250340100d444020800d40b000505400680004240030464811080b00c42d210911261280340c40c699545c82c084015150440c4124280360b01e4180d00c0c02c00790030084106001c1c0c82030702c058216031103041c14180c90540c48981307114103010301080404401c3e5440011a054036070142c07150400b5013011000c4400e032405035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 280009865 1250 280008615 280008623
    0x312130803042027180105040308070e0307230a152304080601051002010f0f020a120b06040b070f020405091609181203150803040501030c0309110616 66
    0x8100810040f685880d800d1900e40700e8900070403a03a640b0103001c460300f21006003081e020051215040c2d045200c1c84856889a0220300700c0c03928007035420f04917007555402c0d81c0c224041003040d02003014644e07200d05c0740c01090390110010aa241c0c1342000e4009407101c00e040d1a1000104102e8101264441d422131a004000d001c8000f15038942002c80204140081a0901d00503003180c00c28049001110055900303481c0303030b80c1c00b0f016543d18000800074055a088002003d40d5214185101c010380070f81300e48141c80c4158100940c1d108950880181440f829644541c0403510344002c60304691a50403d9070107a034090a0300550f0384500b400d04644814000c00000c1d030143c03d11003009050314000c00c41c1000211718a9040c4101d980740d0808505131041b1005000c2540b2031b03403d00101180980d454088a4075060800141400941040403140160b54005260a42c030024040000c0e590510800e51601020320341004103122554079080060b0703000815a10615000c690141d4507003454055140050380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 280011115 1250 280009865 280009867
    0x305160203070609080d0e09060409030c0c031101080c070512090a05091003020405090604120815030d020607120c0c020415051c050115060e041a0d030815060c03121308 74
    0x3d501001010002e00d4004d05180703004000c0890311440c01002c041038a600c00030000c0700142d484900380402400c08400c180c3c02c000c1c048400401050111201c030000d0f42c004d54072609050341640000d808040081e156040d02801002048041007011800c00781000202440503039a000d000001241c3c51030f150041c0768401c210740b060ac8440700401d103c540c1280d1081d0307014051969403000320b544844007120050f140ca41c2e684007100710b051142851941c000c0d8602c15210b5482815004a4070f0001e00d11401c50150b03100724144071055820000341d0800d422a4142400002011000184a00b002540c001d01840c1c0790100c42407140701c009901c03005020090510551100e01e0402021a00302c12407040e0340c0c1e035207030001c074a90301113032106040c1c01e59045803503105c50084200c080c00010f10090181d005600e01c03503240d40a4640d10b010030045490b01a80d103162503420440b08901c003a880840301688180740800405458910100a03030381d0902d080020440c2960301d403c42131203904172981b801400000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 280012365 1250 280011115 280011119
    0x209151305010503010c0c02180705070f0503030601111b0f030a1e1b0e011e08070605120105090403080609040311010c0309030807031505060a05040e130b07020303010f03030516020307 81
    0x3119034045412980c0440c002e10074101e035000150360010311101701030b4000d00310304600b11001c0001d400c081d030030088070710f001c92400010343c5500e400d41c00203135421500c90700700105000003580c0c8482d03981c1d030746034011010303050500002e858103070b01e64001c4250070301400860501000640e0180411000142c00c441a01c048180d45280807024681ca80300c201d90061070304080c52185804401410709a5120100180059007400e010082141542c004d03650704c0400e85101049074007080c004040140015200c0d2621162100910a41140141c00c00d5008030303400c404000c007186d404003065400081c180c6030100c054507107090407103000c9660145900c075582003810b1242c5c170742e60507445040340501070b40e544031680e1961601142580c035104001c0e0145486030806001c1031611200600700306a45041040c0350542d030740034407000044102c0c1d034540f000c98003d155005001d9540740f007513032094003407024514541c180070207000c0180740c42c0009410000b012075005c413000b80b50403c88a5440d0002e00b10b4288a03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 280013615 1250 280012365 280012399
    0x1200d020f060705030c09280305010203010918051203100f03080a120513060b01050d050a0b04060b030103150f060506120a1d07051009030c0b030714090d020915 71
    0x403a00161500103072041e4400200c0d091303c5041940d01445141e260740c1c2c030b405880300404c07011a03e80030310241c092842801c03808101508400400c02544601c0026031a90b03d4040080d044030700008900705030b11402102400003520125050082017035006009032030b40c0764480108501700840c0c00c4100b05518035840401803000301d202a180c0c040c03183e80c64116206810301e184c0103076003056529604035903840c540800020507940144264035010314200b4202258000b0302d000f0307190151892030086513902a143c1d0036007414020039000c0c00100c0061481c5514540c0c0b418070240f40c680c0b110344c400345d40c0d114920840030580c220710002c280007803245440301072145154111543c203841111a9500d402d07200b00a800b8010f4440d110b91854030b002c1c2000b14a0318046c0543d1104815007201000b40c030810200000d0382c1c0c0109d00e0098214070501a407603182c2500c018003248014655103860110a006404aa03590403240644441d8140c0d50408252600724180e1803100c854121031354080180c0501074441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 280014865 1250 280013615 280013623
    0x30103030903170c15091204230103090215130509010e1f060c080309150408070606050109030f020616140a0501111303241505040c03061401200d02 65
    0x2e01e00034400c2c1c00c1c0e0210158164a414440d042030007190360020400b2204808040c0400c651215882054581e403103100f09984145038040e4001d00042c0138a240c90070b000500c40b06551207040020b0908015004094002544a80c500d01c0d1124805030002084040030342400401002448090462030081d40c442018043d19841122141202c440e0303242c0340004081c0010340f150403600203071264000c000e0f45031184100307a80001c02d076520910480d00c42030700c030480c0812850b02c0b55024841d0b29854668074a800000e40e00aa4403050402032082c009001140c0050651581c840d41150150740c4c3d12040c02075038604081ea444040d142c150000003480c140d91000c00d59544880c4030394006c0115107140c03a103403142c038041c034424514002c1c1c0104050001412014540808003002070007807807074014215600c1c0943e24840b512030150303042c0c10b40400c01341c1468014804802402d00b424407645042c840800744501c0ea030045681000f00d03640c1003142402241d50303851035440c034040c152903205c210140f02a5403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 280016115 1250 280014865 280014869
    0xa09050d0b1509060f0f042403290a0f09050d0513120519030c05030d0614040e0d031a060301080601030521090405100e0a0b1903080306130209060301030309 69
    0x4500c018030b0758015500d010030001e4800d020007443c9014946104003400b01e00d01004d1703c01c6420554813520300340300b1201102c203003140104184687d00703694110301e81809044006014407655421a640046641208400c4a80c0c04141c40000103400260080120301904114001415500480300d040710600c0d030040040003440304104102c01226030307800041021040ca00405400ea40004404840c00c8080c14408081c180c001d01d40340f8444000b540366141942c2c40210812032881d62207804118940c1d685400c088803103000c940c20003002450300a041e44911100030020201692070141c41c007844c10884454400c660080c00c40b0380c60b90303120204146d440b1009e01040e9118400d402040c2041101d10030b207880704540d032a0f091070411030f56405010240c54060f1654640400e1201c001c601c0ea1111030115205140001010502450090130300913500540c100d02e10021928010900c00320389800100c81c3c008000782c1e4048900c10b8891031190086c05040c6071164410000000042416800108241 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 280017365 1250 280016115 280016131
    0xd0204021c0e12040f03110316090b031606023a0e04060f0524040b0f0315030c03070e0a0207080703020303011a07121d131d030c120a09050d0b 63
    0x844003c031003156941c00d009621031102000c0794502c090000460b408110b48100c0c1019044511030345000c0d2148884140710340004482e01d41d150484485071804010031000c030758010000001081c1018402034490072410482001c1070782107000400c907106e520502d1000c40400b142507003020007446100500404140e4900c0d44100e041440104100140e03160000c11140003c080403007843c062a15020624090b01d132141280e407040c400000d0085080b001040700520805003980d5900d41a8445258020b1440e5883e00907401b00d0b0280010b6100000c064081c5d400c1440292481d5a0b100889400ba00c41c241c802001000b0106843c0201500000554103a5000550107401350a6802600d442e60290b00005000500c503080300d0120300c0e0041c403040251203080202100440036103000319042c04a0b204400007100d5032002181400480b80b001c220341d40b03c106001d10b01d018146080d265417000745820340c0e1919040010b18540382801198100d004100103000c1ca0201555401d10700406003040356184 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 280018615 1250 280017365 280017373
    0x4060311010813021e0a080106050a05100908011e05100b030c0d060b0a030c021207080415030f0504120201061e05221a010801060c0c090f09050105010b07050c0303030709050d0204021c0e 82
    0x12171f6103c8180110801c0c0ea070701070986808035151008010041c100c9100441c2800031155003c20030b25400e001c1c03070050030070702001e1326500381e01c00003544d04880006042882600480800340400c0c004001140c2d00074000c0000951640d111001901c01889643d01c210191300780080c250a609805400c841c2070704400b5025583c09003940d1244480c2c0d80300340303e0002d080000821041c4150074060090000e500d40c58540080c1d000340d803e1581d81218800e407800c1d5547c0800e54500c0c811690b09000b02000b422190342d6110442241041481d00c400260041611135140c4012081e01c40340d440c00400321030801d088080c1f041f4119074040161442c41c10071118005000781001184850084905d1480b0780d03444402421080d02e003026110040001d50b008112141c1c0b10255100420801d00406000c3e0003003503226a554a500d1400c0c0e4900204140054040d030814420001a9500800048102c1d42d00740d6140c0104a6a480020020700c15400420340c04030741d045134210340140c00d83c00f1200e0100140704403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 280019865 1250 280018615 280018619
    0x6050c12030915010f0812070c1517070201180b07110a0b0601030b06030108060711010b030d0503060f0f031009050102270109061d0d060f050f070e04060311010813021e0a 75
    0x105888020b14006c0074442e50001090700100500c600041600c940500084052161a0b06960622036512900c0d0000504d081c9210042e42c00300801150f08400f09000130880b0342c00602d0582407101030852f000e070040212130001240e550046003918039045c02d50042e911701c403840f4540421661429140e660002b403500d11040064146042220f05995502008000598810400300c4625a8070b070680310342035498050000041d10304010398400c074a503a8807141c0d124605a01440320701480410745034820701d4011400314090300c0124940219000702d01c0040756003ca40e00f0200d000e0710034034050080118212245081211200103c00c1d00c1c50401d90381c54142c607507100c00454041e5021f00e01c00170400d4050755030030382d6031030300558090105100344008a11400004003410031604100c60380451400300c00200440560310400c51401820115400c0102c0c074290348481d0300140d214500340c0c2c18840560003140380a00e00c00c0a42c20550703401042c84005242c1020480d040d51403584800c3d016160742c201c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 280021115 1250 280019865 280019879
    0x150909040c08012f0a0e0a08100509030406090317130f080105090c0a2102060403050303010807080706020604030e0402120406390503040807140318061306050c1203091501 75
    0x44e80703101240c540c07107207070004081091803074042c0d0103480034105001c401d616021594880600c0800200a10030250945501002c8040c0c152074000382020080d810400c0148142a044581c040c00d994115a507030a0700d10501c0e00320580b600c180d034900c480c0316441c45400904c07012020741480c11781e003410000788001d849450b03c02d42d5880759190041c0e03018102c100d0600c400a4900c900500304610445019013078200c0c1e8000c1100c030392040d002590035400c00801480341090400401000705800001014010700d0a2002502c4180240004080004540b411907031a651601a5033300c5004020b00144241402d02c0d1480003070800e441c14540c0791004c60034009950341c4400502c4400c41d160b8007145030740000d910044885600090080303a40c0d100520260300410030607828800d003d828640156500c207e26007116907208010401c90f8400c1500b0804e8400c1c600c0050b00b86801c848030303810003584440740c80c14664145004400c00e4017003039001204000b140385000a408255013654030500c0f9050741c88140c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 280022365 1250 280021115 280021151
    0x41205130e090a1208070815010309060207080309060709080706030b0406181a040b0603040809031e0d080a020a05090409020312072004060501051605030d0614090f060d02150909040c0801 82
    0x141c01b408160b24600059180d050074180020980d0149030010303e40e50715507a801c0880c2c000c5030302600c041c42c1c0401046144d18080040540101190030401d1003a858510200e543d281e4a0261008041d1540f28100e101d840342e40018000e0030b20002b8092403551403000203001881c4041003041e0707c00e0b100c06140990b082078800d001103004003514040c503580d0340e503c1e450400c0e40b01c1d000f2a605403182d07070341ca201119101c2d081040c028021201500817441c0240d03004021241c0508404089441003140c0d110701034000c1e080310b585410030f0702c0110f00c00e8990f00001c0e0901d402c5207840f0452040c0000d105080168127406000000b001c140144640c40410040c00110b03500e030300a050100304204900c1041c1c200c00c407001a01c1034030401c204c034900048136100ca015964154050070305804502d50380c00540c035010603410391000550400500d586410380014410b100010f1019011b58070b52441c0300a0030b00c1c110101c901803080540501d01c14180b910307001007002c20760b216421055203048a400800700e203181c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 280023615 1250 280022365 280022371
    0x20f060703050c0703030513080c150a020a09060f020f030f12130203030913060b190e040c080705071a0c07020a060906170603030c070b03060a0e041205130e090a1208 73
    0x1030f0581e42050803c0c1c1d0150010704000d8281c400942403e41b0382c8001442140040060402d0741c000340045038410140d0003c00a000b4281c48001401440400c80c0360350b01440c840201d03800d80c81e04101450400409030b04094a5180300e01107800001812040c050640c2d00900407180d11401c07032030860f551011124120807031a03500a5040d001044900f81900d04040c0c1e5078007106a0000c00100c5550782c020900240c5e101440020321341c40c000c0401c101242d00b0400c500214001514188022100c45c0320003080404010500030030b00102240d21811f104544a8054201c0204d181d440b469007401105002c0d03542143c00120b121785100e01002c14024890501c11040b240107860b40100c102d810703030406844001c000d01150701840b003417040100c5054104108002401da41041c1039481c188042802001d021903003000850350381d482d05100020b840030848140c01d020301d00d007054803140e04c2e0449050790303480c0f075211900410b0303000f052058098002c2240602c140c800e18507604544141001521001012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 280024865 1250 280023615 280023631
    0x106020f0c030a032d02070303031802220e24010b04030506160e030613020909030a050301090b0d0c03050f100605010c06270602030f0a0b06071104060312020f06070305 74
    0x42c40d48680080e00402c0001c03242403030518088400401022817402041c03400010000680c0405410030606403d84985910700450f210105285d2146401044071702e0021403842c6d01b06081c030b4204c10541385281d0300240b2075a05450036100341c0c803464109183c15210b001482c520b61600300000140c101c06213000c44044030341c810060b280554440308803101079981035401000b4000c41440e500c20300d65090042520608110f004500d805807140184407008030018002d40169100300300480c2010341107800d91303046a4061101140c2e0203004808100035880804000300302c10b82003480801000408951050306245038000c41344061510700f00130f419111540708290208016000d41e5002c10307401d801c10b99a10003680059134400000c00c600d00c9a0b1185110166a03481e1f000c401e2024070f511044007140c101c030550605000107514000003a010b80302c0d072000140840ea008450050580b206d42000b0011031300f01c51300740140818000d01a4569408440b902264064800000ca82c21300074070070940101c1d24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 280026115 1250 280024865 280024873
    0x604050714010c210e01050a09030213090212030414010c0c0524040602070501180b121b1b0c0405040c0605070501140a0209011205061509060912060106020f0c03 71
    0x303001c8000803951030200a080c104500c11141c02e000c646000c007800883c680401c1000c91600e013912006024544401e020703410000e08000c0e0f40d4103035911040c8441600d80403511034500e0010118004001c0c40c080384001d401044a0000344900b01021001d8001c54a050503900c180d0143e001c0116400e14821000400001c4500c0c01401a07042c5825062440541e00648450b00c0741200c100c0300158105503c60001a0700c030700810b005d95688a80c007103000079031007290050501d00f030484100a0740154403000080003050720018403d401b051600ea4011b0001160300b0ba55640c1161543d4002c80b2007036079405240c400d03140c0200d41e44c1090700c142031180e034010360b182c2809401d00000310b60030741c4203010541d281c0d900e0345440b004d0a40b4407412580a14486080165102c074070b0300c0054180c03030aa03401c2000207481e090030083c00b40c036840600700c42c040d81c1c192400d0303444441c040064514011016840e805c08003401042c0c0d00f0240000300789040e5180e60b02212050120107030210b645031400d901c110f4040d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 280027365 1250 280026115 280026119
    0x1e03120f0c0d020d14040506010f060c05100903140a2a0b06010e0a0504060b2d040b0915071b080d020c210313030b0a060308090f01030b0406080115060206040507 71
    0xb190f90103070522040201c008190b00c0340024600032082d005480c19241c42c0c0056004012590229845100070501410507911118080c3c80326a1112200c01d410200710352144800c408061260040d1060003002400042e00c41d03c00080060104000700c01d5071381e05440004240a41c2610061300507011075106e450186030755121801150040644001c294100e04a030a000c103441d070340c9014a00140c02d00001d800d45131110380c1800714941500390f0450011071f005411509400000ba400c5806840c04055800d80c0d500b0380f400402c0204181c00360181940002107803042c01c21582d13440d60003803000700c002c4640308aa1a41d503000d0f2511901102e00001da400f5111020103400c004000c490f011010f220034104201003912214210390080046d000400c1c4066014810803243c0401183c01c100c40d201c0401085086903a811000d00c00d81501612402e200904072001e81c0c400d42160350703000006402840360546d03c40901d23000c0e01010280c81120340c07001c0d00c0401d582c1d20004030325226079000401808200c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 280028615 1250 280027365 280027387
    0xf01052b020c031803010c0509010804030522080d0201150b0a030506040204030c06020a060f090c0e090f011503050c06090904080d09080a200a030206070e01021e03120f0c 75
    0x1046a0032580c00c05030207001021800b04207001a00180000969080414000508160071510f02d0180e61007440028030290150340d92180515510980c1410030300e42d42da030903030401348808940400e095800c918407100420103400100e181e8209400300d8000707000910268810600340e50040c011082c01c00c4083c0b0102d911148203400568100f85d000e8001031a294903a161080300b041540c10a10250b88410104000c100e12031068280c2107003403120400c26400702da52620000b1400d03200e600b99513069000031480e243c00c20300224220b00c1080c4000c00c0003156041000b0303807140300c511040d600c502481052000904240003194854000284040d0080e56540c3e59258140c21004003820103554a411202c00201108002c1880d020b05807035100c80c801c803c10203120001244820710f80260814600e60000980000e6400c1c0c02c80e00380d081c20341d44030303410400403440c200d101c81540f140c11007001000503a071803010000340b070f41203100196500c1c01c0e40c0d00300c1c0c2544c0140065840311703041541004070740e40c54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 280029865 1250 280028615 280028677
    0x307060615020d0206190b180a0606090e01080d050f0c0f061602011107060c260109060815150f0303030a140603070f03080708070b0f0108073003170103060b0f0105 72
    0x4804010800c181d0749140000d10480480221aa25186072b80e0314020700005400c03240b4040140b2442010f00140c0d81001603054a814082a081c01406404030b001d2070b4203101801a030300b17161510421a440c0e1010060301c10f9a901d000c0e90f201216000b0a01003407506441070080549241070b5407402841c2042d550348400c0140180e410301400c01291344c1000305401201c82c8250030300d90580544450039414041500101c1c1c41c1640840c0056100700760b403600740102041c000364416090700c20510f880c45c810001c10601020032007800e51600001080200c3e6180c07d9024501c120b8541704011465944d000905507104030380c1c0240302d030b603241803d810070001e0304680040007028465801c2034104003140c2d84030101d0202c2035640003d1907a55030014040e0070740401042c0010600c4001c210944290800d403807000b001626074004086e20080b40301d00030f150103442081d401000e0008025003039a524103088008002c10a0418860701c1040200101c41d031082c0260f51000c0004200124072940c0810380c060780d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 280031115 1250 280029865 280029881
    0x40905070509060a08060709031505010806060112020409021b0106050109080a080c0c041a040f020f0f1315021e0d171005060d020a090e0103170c0307060615020d020619 74
    0x10021381c2403400b0032812402c0c081580681e8640d03e41518040c01d608d07190015062000044050501e84001040140700004485030044420300380a9500b018103410180644241e03040300310040e00024002007001d800800850140d05002c00800055450340b0044885e039509124404032030b4031204d280408502420001c0c0200d140c213404889a10541002050580c0c4c80442c00d04c04000c60b8505041180c18a03000742e4040c5000403108502e05910402081c9441c010121070761030ba00d0010440300741580c20407481e0009024031410507540440401d00c02035071880207450082e100440c428404030924000100c0b40c103102015142c4403101c002d0316200e80f020301c000400e1074820300b004080000f01c58542900404041c2079813080560380d013070311101c040c200000503880300200010460040020400700d000c545070400d03c1003021540c48420b403102c80d10b103000d210000b4001c14504103000030b4420784074200700c2c1404031540a480348074021a10030380e02d54400702c2d04072070340c800c5c6000c3c40040d070080c0f6481514 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 280032365 1250 280031115 280031119
    0xb030607020a15020307141b1603050f120406110c031e0f061605160209010308130506090d060203040804170d0e041506031e050405010b012304060804060b12010504020f04090507050906 81
    0x480c010007200c0040c504902048003210014049d1700910070b1201c240000c00105542c071004184626814001c43c0ca40c0c410b80c03103507604028010320300d603903500e00c24084480010001011030f0840c8003200d0340b41d85071410a03001074487d48a07594000042010105010784212100800400c441c9031aa10503035a07036102c01c0c03036a045541007030202001030742c1303541c00b6901a5008141c1c0035158608503048180111007a00000e2203220b061195150710b41d40c0c03101d42810143e2045000d80c498845103000350b164000d60700b00c01c103c40021b44004041050001d426034881c0003555801d02d01802d00014042112010940b0801d0801c40301014840f49000e500891010303013440802c5a0010401c84460080301c90503a000c40307143c0d4440081c030342d6a603031000c016040702071441c601d03481d040c0c0c45403803002003441144101c80034001000b00040900c40164400f11054a01604003003080d151482854003d003000c950132031103460740540b181002d080c01e10942e0b0191754801e00a0204500b08020440d1204000380007035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 280033615 1250 280032365 280032397
    0x5031204080d02070b150307050d14030408030d020904270609030e040f060f0b1606110405100302120c1303140f0703030c1101020313090f0b030607020a1502030714 72
    0x41c5041c182c5100510300c40f40900014006800c0c0b0400700000d41c3c58211046200c3e0744150014410b0707564a85c500c2d00d8081e8020310180000920300c0c00e10341140a1035001c442c1034000030564a101000a40080a03818011601008a2488010a03001c10380762081c00c20381408810be030703400c00122070707502803010340f4020700380100404c240d50005000d0304c0054a1940415864403030820810301d01d05449409009007100103801d0160f43c165030414401c40140180c103840e2107100501c40d040d42441110060b200c082c100705061592000090701139801640c0100700301010000041e07001408030195510901503d80b100f03052440d58a0744800c190123145c0c100707801c0c090403004100050080204400541c0300313407074034000300c0320909040e42640507091380e05040d0740040002d40c10f242c8140801c1317400d95000c8040041c40340d46451106000b400b02a540581510a90007440b0b50381d6000200c0703580f201d1140069030101400000c00c0400d90005543d030b1030108007c14000321000c0c40348400b504014089240d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 280034865 1250 280033615 280033627
    0xd060f02040609030213020a02060415140a06080d03061410050909010e01150c050a020409030c02040609020c07080307050303010510110a030f11061b030709180501210503120408 78
    0x101040340c0c090703481100803c611000400460400e045420311051080030304608001c0030320006900d03044001c20080070b00f50101d0301740c04030041981c041c050301942e814418145241c88141100201780078081c42d1030350300c11203071a512520b02c80c2c001c00c000d035074114070840c101c00703609002c5c484000c490b0100340090100500c000262915089122402002c00d000f2400b03165151054510fa003503903201c04481003115405a210100742e0001d01c1308843c580c1034400240f0b007a118101100e11031460300000394032609105000448254580140081d8410002610341642c1c3d280c40c0d69503a4424003070001d050b50028401080715152004400d02c00075a5424a0401d00c100f00007424107020381020100d021034441306581e20010340c8020460b0901c0c51420003401f0a04000742030103010050161122241000000003800700c40c400d1050b240140000341980d8104981e040010014280901940b00600142c0301c1100d03400420700f009084032500580590b01c4d0410150b68070000f08802481a100c1c01d10800071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 280035971 1106 280034865 280034891
    0x251a030402061303050105040303050f010506160803061c03020102040e0f151002100f05060909060408030c03070c0f0305031008071401110a120f08091b0d06 69
    0x640d90701d41043e003011940c294a103070001480ba509000601c002c01d50540c01c0303076000e80c94200700e01e040c5d680c9941c2848482c0c02071a22440701410885103c8001c212420000d5070000030182202c2c05202d0808844015000c00704011001130798001030410404c8c0b114000c0b2904090b18002800003418032030421103605200d84106445412120409031100e03000300f003200c038000740010090108032864a880d03001423034112030b01c41c05014032a001501c55900842c51030b22499000b18901e0540d110004a1a11a0801441c3c00140324144440b6404905400032880c40c0a11960362941e5a103012008280c040015a0000310305e80d210350342c18410103034401d400242094007031808a410b19084141c142c40c040c0400400390500c2c07032550171070028641c0143d05d942604025282c08850352240e0603003a1391941e2007840700b0b40708005104081091b1030201e01d80781201d8010307000418401a0304807 = true := by decide +kernel

theorem cover : BRFrame.Cov 279856115 280035971 := by
  have h0 := BRFrame.cov_init 279856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 279856115 ≤ n) (h2 : n < 280035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
