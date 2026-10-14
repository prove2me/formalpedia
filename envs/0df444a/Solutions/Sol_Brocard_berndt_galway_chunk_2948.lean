-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2948
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:13:09.17689+00:00
-- url     : https://prove2.me/submissions/3491ec07-4a90-4c69-be53-101f13311368

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 530035971 ≤ n < 530215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 530037221 1250 530035971 530035997
    0xa030b0a0f0513020d0e030a1206090912030c020c270604020327030c15010e100f15050f030c04080d08060315040302010f050106200610171c080a0c 65
    0x10704200014001207603c1e03000a139009100390513030700c5070490050080a40e921490741c0c3c08000d104203000d100100740c0f1070500c00003040b5159544282050282c0c801c00341d460a24581c1e000380e014100e10b00b01981980540007540d0b40b140c6030b055056000c102c80f040010301c41c0c20304000c1400c0c003450240400740118030520412801c1c0203c4903450307038a2680c1c29001548100d0003146940380d44201841130000d40581843e4140308100d09820b1810b8407414901c400a59481e14110511a0410320680c8900441d000d01003020661229600c00005034920700589886180721402c0e855031700950b800c1c50101c40000e01001003240520524508a6191509420728201b00300080e81d110034280e42601e81e40000d90201c0d0415001754000d039011500e0101c244131541c5d5444020349130188050100380c2d80005000135103044000820800d00c0388424034800c0301500d08040102e40e905400f80410b003500d1044248208880302000c2c0d040290080c01c7c4d8907059981380c6290440c0913540080d01e40000e1107410070746a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 530038471 1250 530037221 530037229
    0x3070b0103111309050706140a0f14040b270d05030301030809010c020907080415230414031c110a1b0201020106170a020306100b070609170a030b0a0f05 67
    0x180c1129005841000e0341e208060014460f40c411009008074146490f4039003081010219a50003265000d0701d40303d0719200c00d800781035864810030500d18001010250034a00e02d42c007a2008100300c9030042a09400d182d11002080304c2070740140342c480c0003500d410580419210f15408c69030740c50030041c0c6a46011041d640e0326150f590006010040c031030040030403c040140d11564443c4442c030740041017900c450406c40d80103001103109a4043c0c4000880c05e4051078109401e01410800180d403a0304140003882d00c8404510303a04002d030045900310348500d403a620343d280801c068803941030552100e10003d2540000c1d1022601c40c03020300440c0100601c59600c4842c0c00403001c85080403800f5007107400a0705480100d0051445800c45c001901c1000e40c50082014005442400340f44203030304031041900e0b01100760300704803030b640f003040c0a8130170802840b00060482e0700001c2c2654030076a00700c6958503a06241c00c3c8243c125030048070000741d4411501c1458a03060029400078408292a4100603043c07070081 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 530039721 1250 530038471 530038493
    0x150f090f03230c0d030f03270c080d050d1a041415010f0e04020d060e0a06080c190314031908040317150607050a020301020d020901020f060f0703110c010911030f0307 73
    0x5801d0008000c1d1321b8800314003e4001554070194100500804800c40c0810400500c404405071403003228000c0110f070403c4005080b05c00e0b220076803103650420101040c014068005100d00c00b5512a11103d00c4580c1e460b0342c000d244081a043d409083ca0786014000032140c0c81d089040e1354101320b1008180c0640315000003a280541c80280d601503501d4800b00f280074054a425401580c0001c00842001503e01c1550300c288141e68214042e40c0f04408180f007001a5405000a844a1008541002c00010780110071a80c400b804080a0b01d042c044010b5010b1400074002d8000c0011443c10000c200415a011107420840000d845003a40d29061924102c581a89c0007400c040c080c45000a4010900800700440440258014002c2d035442c03149510320f0340030f07400031401c090151048280101c1040d1003c14854403451040000c2d691541e28a03108801500704582e0b894071000c4108000302d4030620038010b22108a0242d07034440320108004052500d0021003490162041c0c04c2030000e840001c0b41c1e030b000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 530040971 1250 530039721 530039723
    0x905060304171905040f06080903040e090f06042001050c0607050a020106091b030501051002030304020d0204090210021f020421080c03030f04020a06030501150f090f03230c0d 77
    0x8000a40c64031418544a02c034200c0100c0d00b1080c0034040900b255407000c0100140c1e49a2007141602c21fa54120a03030729040c007034411310300c0340e00240024002031440321641a400801c01c0c049481c411049203801c1e09180c001e03102075800701185120091580f1080c1c425003078451003860042d1800002c2c0810f1070311a030002e0042c0081010000711048442c0c401d42056000d0b00080d902002070102c10844006c0346200c205500c004242490000181450703c40c011400381e1100d5000f5510b1966503a0030400300ea503a1883c07c9a20030ba5a1603a40050b803105a084018602640c00400800d403101040a448400c0f40e0701081600b8010881071155040a01074103040d0440a00890091303c11440d00082c0c0340550031884000d44804030410807044252154940507500076031f4001102511264200c4c140c61090099140c080360100e00309215621400a42444415a2606a11450301c6e03081c0305541c1a4280c0c019120b607840304500d20319400d056196841403606000007011658401c1c00410088240c03050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 530042221 1250 530040971 530040983
    0x6010e060319090507180605041d0a0312060f030602031f050d080906040308030c071509020a0e0a0e010c03090b0a14010605070302160306020c100b010e0f0f0301090515070905060304 80
    0x100000400c442002505c020348490800c400000403100d0030040107055500c030b1240301e64103100d50404a10610310380e603088040400c0280c4010350964038166103209580e001c844070381d5518100007914080000450001e0340c400e460240c1c1c2d07410030740c0810b5540c40b18101140c0c02e040d22040204281d0341c07110351415401364031480031a191a55200001c400780190307480501140c0d00001000350b10108480113050b810701c18030304003100b0600c0400c18011a000050001d411616014007072100341c812452056000c42c0f80f50b8003103803001c1d958034201d0945400300d5071003011035243d009900420007080001c0754888400c032030400614801c0908542d607100103124000a01c0030014001d0103042c03007072184c0390a9000742d5040c020318950780d2030b20800039400342d0901ca409000f840b401c1240e060442c01a41100041691040c07140b005540030018040b4030326282a60110b503800d01145291400e0003040d1010b0b00841c05000246031800200000303200080103081000a081400c1c860f6980742d80c15281c0181e0000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 530043471 1250 530042221 530042231
    0x305071b05100f0c060501080a0221030d18140606210a030809070312050d050106031808090a0504091b06080708040f06141602121c09020f1806010e060319 68
    0x98051320303400c010702c0d000f410044c10840082001038000410500301442a03c1021540c030003604508042d03440342e1400400d507002000489100c5002d90055001942034221441600c8030b15a20101d000400c03c14400307058100b0004c0000b185054000c1c3d00d452500b600841e201031048000068503568104401002c1c0300d04000410701d146820000d00d0083e6900000c0d1501c02c602d602000343c01d41c0c0201c06812980c904210020a5051281c050030301e002d20044e0b000102d41080b680c0d5201075822502c0c0e115045103e00400082d240c0d41c90240b444054010349400300440c0408040711403080741d941050003072004400c180a60281c1c00410140d001c0c2d00f220584500c20003518100d4007500c40051070f080d641c0100e0b000d00203072500c1090100903108840d0200c1c0d805406120400c52640039081c00300342031031140c08420005510381c4d00240c41007480109041e104424480014007840e104407440d442d00b0220301d003001b1803560441ca00001c044d00880d0101e003076203421340d500494600c03c01950030b01e0a80710 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 530044721 1250 530043471 530043497
    0xa0c05091513050a050604090b190e12130e0403050a03020d0609020c100e0607170405010605060c07030c0e06130c12020307270312080c040902070305071b0510 70
    0x786181844201c40101585409000b04010001501042e1120300e4075501c1d000105e4000d2a05109030a951030340220744004665a80b41001c0c050280b210001c0c16940c5c4500d640d002d04881800545400059203150603120038402c0900070084850b90000d0171802c2c90003045c800460b81180c00c2c0c4446100c0c03881c016030b5600c225010800546481c2e400240c005002180d040c0c0f007200c1c041500e50020952140410942c8840514240e50711800d980c04000304c0c102401c807004506090549660140c022800426803598420204d0000d0344156101c02c41c5402c00c1c0c0c010b07c204a035040c1118024084031078402d15600f821070000d0740610224048426503656026081402b038007e40100c0040000101c0454507460807440240c96005003184075048101c1d0381141c0d40800342504401825207400100240c41c1c800b6540082d107070050b0282107041d00144c00e01000a90b2030382400100911071207903480310703103d400503e03200c1700f0000704480d0210204031051050002e81c07034416a955480c0e01e03030320740300440c0340701 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 530045971 1250 530044721 530044741
    0x2011218051c2c030a0f02040509071a0702060417030304021e060904020904090b070305160c080702040b1807090f06021c05090a03060509030c070e0f01050906061603090609080a0c0509 81
    0x18680f000c0f50035010b244450b005219200b02c403031007101e009640a000da0341e16040041e860340d0340341c024080c500468503280d00184004c8405028000d201500c5030345829100e03989901000f00c00744100880b03a000000704800c5003014150b040308011032042c1c10301c110030003c000032601c1c003401800c41d001d503a011601f02d0f000c3d0381b213400a01c0886d82040c0c0c10066800c2040000340501402c6802c410281c4c0318144000d000c0d8424008400a140c11481d21414129030b5400c12001c0c28403210102e40c4501c02400c0340c2c101e030142d0072030075004001d0781d02d5401d109454600c1400b241d0046034003000030f6401014a400300c0c00b066807c40c103001e841c02e00e4010398030340917900050113000880d0400350103d4604003c00401120000080ac0018400300440e05501e0340e0381c074280c1e9468011500b070740f4102d14102c010000b0342852005c00d40c00c008010405420101ca20204e10a9107105510660006552600801200b9000301d04000641160000340c6140c1004d901c40a031080da0600c50b80e40200110b40019401e041c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 530047221 1250 530045971 530046047
    0xb01150e0306101202130515010f0e0a050411130b0c070501030608030d0c20010b03060a020306010c0807061b05070209060604050604140303040902040608010e060910030f02011218051c 81
    0x10341b6403002c00050a00448d00e42c0030513482c91034940890102003020314050b00071340305810244802411103420f14105404d00015142c19956200c465800b0310030b03206213201d0540e2920150254542140c1c990202040744d80c0f0b007012560025040c145080c005101c2090084216a0100d500000102c0e5580034100d0445c0c900580c0081c8d0a02c60881e19020701040c0c90640101d0404501141116215281c0403d180128881510402d000c1a0f61154803070004e802400a801814024940003a81d0a800307040c8203081b5881e1401c130400501d000400710214942003010503045401501c40d00c0c24241440c000c00c9142c0300c1c2d0300801c60100d041031103821140d40c0800444c5d000e0500c405042d52141c0e95403002030030300c21007030113a080b8100c80400002c003a402d0409846124015050f0000b01191035034a030140031407017000003a03040000b03100404202011901030a440891040318001d511682c1c0c4c20503504210402c05020410f42881040889180d4410803681040300145491104121020344151400c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 530048471 1250 530047221 530047249
    0x60f070605090f06090f0f010e0c011218063219060803040b041a070206091c0f140c09090c0f01090e090102120c072d0b01150e0306101202 61
    0x1220307200170098905404150010005806400c031001494181c0589080e12845e10340b400c81d07544001c400030703107a6200358100b512100140b000040d20425060076040520b68140d4142c3e81d02d6150002918501e801840603981e05011101890a5102d100c1d20002090b0010303000c2010f81203400d48002094609602c41c1004141d00703412a80e0b10b50b91603001100c03940003846010f1000824010310700303041c41f5003c1213400040d80105107628000c52503042090291350610240c0d602c8240c0d886c0c29000442c0103c403064a2802001b8406034800004d01581c85c150b03244e40c184d0300540c0a11f09101c80b600c800110b41109010446260201181d0100100e44d12101648900c4202802205021445206600400c075001d00c1e400d00724000d994200c540b101a2041c11401031a9545840d460104680f09103e9007030405a413034940d44a00400d911124800d410a8101e00c1f003034000703a210a03441d60341005000d03008c0301c0e0940c007510880c6400d0011031820107140c41348a9045080301d895804554840420070502 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 530049721 1250 530048471 530048473
    0x90a02090a0b060d0f0e0a0b0703050a06090c030b041808030f13021c1b06021e07090c03060f090e03030a0b0d2906030115090e072c06060f070605090f 66
    0x303012420070480035080760b000b68005d140c50322070441d400302c1c400b10f0801007203608488105041d0f02c0341c00c400c6005020045c90044090390f03078100860f010005004203203502d0340c0c0b0f50b00071600035001e01c01c00c01261480c1001102e98074010041d5000510f01c40c1c1a661300000715503a00e41c40e945c42044882000d40c00307200007035007e8010581900c0b04645035048460060049005074030310681c444175860211a00d0185c0d5000d60f02844d11940880448407400d400540301030140d03440d05039152010402e030f9003441c40942c082500c0d204248080a405110b40c8018100880d00340813582d031900d081d989910010300404025504c1e0031800c1503940712000384c0181d2540c080c1d81d8441009025144055090103084140801500c039004500c0e0b80c6014000d418000540d020f0150b5103e2402d0101001081e0400c2c5100450146580000b600c5828080b1221003180c0400d90151442400c191202c0c075403001010360f4410002400b0802c80c8940d00030070b944200740d2088000510381c607440e87d89403403c03031200034001a07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 530050971 1250 530049721 530049727
    0x9100f0b0a050631030606050405010e040204050702011b0306170120030408040e010f0302040b0f0108150d05060f061203070807060902010528020f030c15190f061706090a02090a0b06 80
    0x200441540c05404036801b89108201c4180c0b41c100b044140c1ea428401c9151040880c000300f03003d894664000f64104045000000b522145196032000307240c1c1010343e041c0401e075074220030400c941700801e90307004108440d00200904203484a000204184950b00148400e401100140802c00194100c2d006001e0320000740d5001d41e076420703080c0740e000881d0004038016420103001c0f244034101040320605009050312821040d0303885400380c0070700c40c9400000795402560b8819441c04160300340090b80c0104296150080300d880c0030000c0c231580e402100d0aa243c2d40d842004000702040828068a50140e4409004150041c0e1b9000407210341c0101031488080f0600c650741903284108004030801181055002e603000b4680070304d1416224040c0d4581c81c0309641026291040380d07114605c1c0c032940140c101281024441241141500300c940002c1e0841401d0760340e890510545a142034810003200510f40101010f00c5c00d000c45a864460340440240602080030129040d40307a940c010b441c06200140206031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 530052221 1250 530050971 530051047
    0x60f0f15070312020711040f09030c1101032c0601080f070312120f050609060a050f0d030c08030f041b03050c04090305040506070b0a0b03030a0f0c1a09100f0b0a0506 73
    0x80e4120406030628030913803500c8c030300354102c0109009002500750561610000b03400c40741c807105a209568040f841c101542e40130210b19241002540c2d00000e0903801d6604105801303001264070780941038024070400d41c091320200140c21000070360381050729442a01e001c411011540203403003490b820450f42c06c4150615040841800c65503014900c540d0b0200d62041446c0c413090300380100914180140381c0c02000b541e80b500c44508100b43d420081c0d5100c2c3c03420700b02a0070152036014480c0c100703a49030074042034148140014032055a109000044400c00780012052441c0d40d400d81d07941c9510040b5010307d465403000c0080c14083d0098070000e15010f003440c1d561300c1c2e0354605000401011204400b000f46403403803070301440c02c00200351171200d280f42d01c9604010903615010703110880658000c841c807800407602d0004c030f4039815007028007600096004000702d00020385848182c0c2c0e403051900311810716110b0f5203074050391000a41011280b080e2482590b072a00040d40e00000200d074221a00741903d606d402c84 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 530053471 1250 530052221 530052233
    0xe0c060a030e013207091d090307020402030903030915070c0f020f0406080f060a061217130f1412060601050f07120c05070902120406110c0106060206060f0f150703120207 75
    0x1800070240b402c544105a4611720140c0d18000b441c01020340c41e6150086081e85510458a200e40100c0003c044a09281003035000a0030faa00031180114550004002e00446050400001c00c856034440d07646011403030829001011036049480c050003004e65507a0100c01d5450f05400704041280181040c4822134580e95107940d01c101c030403142c4a4038825240010000c8801c1c3c410001551045c01c2c400e00305e00c03071984900e003040358000340e5000203850030002c0c1c410041001d9194402800c003440ca0995480c035003c600109c0380c640c2a02c0c107010340c00184071011609008901c036a44485c003401c201d80c6a0070007810040684c010f40304020800d04038075000c1c01c5640d402441281100d44201c2c12121401c2e1907640307100a0703000b207114513000c07520302c0400f140000b501134003c0260303040c03000065420149003206d100e00b0744080c0d9001c0f0780940c01100910105003400c0240004001c4d054070a480c6225405001c200c4203c41500f146208082c0800c4107000c25120b01c20900a44144190035511000142040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 530054721 1250 530053471 530053541
    0x41805030a180f03080f0d02041d0c070507030311190b0108072403020702180709060e04020c0312060607021905100815010c080d06030609060e0c060a030e01 69
    0x103000304200c1440c2001c030a002c40103003010380307070607612004040e4030356a10314007103800013501d014002c4405e0024a111441740d00c0500010000203568502d168565481e503d01c803203000e0011440c64008019203000700c1d00010f220310440340d00d4030709401d130120404009820940114001a1a101100d508006020090b8003980c161094001030782d480503520041c0d080d024480700c0514a440c0d0f07071544212801c602950142c22a140083c103001101550702c102c50b824804100d07162800710700c0c0001c00b445120307800354114894420071b9404500e04540c0d1220f443d6240141000700c000d65220000003822604c98400b52500c40d03502410341200000000101e60701ca01c0c0e80d0249501031005030503000c0c0200e02ca0901e45000303550080000015002010044402a0b6004429218a02d040011b600040058441c810003140a240001403d41503840d190b025950800301c8880d90350301000d80c0040f1030390361030211001d001803418002452244102c3c00360140c1b662500310300441ca840b40b0744601c100682006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 530055971 1250 530054721 530054737
    0x1082205011506080601090e060d08030a051504110d150b0304121404051027090902040e030a0203120a0b1807030f0509120a020f011b02070905070507020d0204180503 73
    0x1d800b60303c401084908550840e407050008520301d01c208484d142c1c00840b290000b002a01032b1400b809907488968046d801a030b84091056134410070000c070400c1100000150140c100c4040c48651000e0314049001d020360803c2542035070792540c10740000715000c81a01d0041480203000d688902e080c2c2400b1042d01440c06000c8007141882e0909962051864216002e5610050040340038803e0f0706011903074107211003005030416a0192440400b51900f0000000805040c000400c00a10740e1051009492203800c41d14403942c004d011001e01c0e140c01005940036180d04c80c00005c0c060703440c1d00001c0c000d130011054403600800300e661007284920303044000a21810b200c1c1c4080c081414050720180459004480c2c0311201e401000b451100380c1c0c0080000c1c12031007194411501e5400c0b0b080486421101c010341030a0003245c0c07680c019451aa010302c000b0005080140307007000145013014003d0241e10404ad0000d1090103d0b107601011503550380d0166980c000541c1c0e540b890a04989030aa54a03409210 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 530057221 1250 530055971 530056001
    0x120f0a120c05250c06030209120f07050109080303150d020d12050d060b0310050603072601030201030509070b250b1905160210090519060207032a020108220501 70
    0xf04240301c160b10145400700281d100c246a40e00600e01041107000350030801410303500412003017840179110010880002c0090341e82e0b010b00446450300002405048840d800f00380182c20501c10040c01401e2080d130403440f80000c2e07410b041440c1710740c0300044007100103000007083c134001001d0011040340d10102a10b030f06610008100255600c4068031402400100c6505000c1100c200c4280090b00300f4a02540c1c10455a0070710704200c0c480c1c050001d403102142481c040034404039100400940d80d0501440c0d0b0001040c2020313081d164104400d02e0303428402d05602c003601039200d590032443d00ea190701000345110b80111890b004e40c01d00301c01580713000403c0036986455a080902103500c00c1d8034098a035410b04165001014036a10364024400034000004040d2000d0082d003e2195040c40014051407aa0b4030038400140d45c1d605520340030381009440250440c4d030800d0b00d425000c81c03a4440c034260085640900b0321707000640d594106190710030300c1d91188807a50100d0b0f400c1d040401105412000d02c00100f50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 530058471 1250 530057221 530057257
    0xc03011404090b070e0f0d151a030a030c08190807030b0906060711040f180b0a050f010308130f0803040302330310080604031d0102120f0a120c05 64
    0x3001c00042c0c031103040001d000008504081341019002e5000c162502d41c000d014a46600e06082c005610081101d5003030300c0246030704601b685071101c248560540303004104404260303401540e0200f5034480142c0002414881005011800c1c04048415a40003100045003451010320100e0014504201a2103000c08681000c4100d141e61034a2000c1504c0307032101809682c1412901d4683c921032041c20402c05801070790320112009852114054403200001c860780724810b010345403411881d401c900610f03110605140c401440680348001025504481c0c000460503150083c4429480038004142e20900c0070041c20940003944102c08400740c0100d0703000b101d030b64081280760751a000c800c2c5480e0040070501150300765030303010307801980000d941c0094581200e4000c2c3e40e2100c01303113440c1c11005c2c3c8080e030214240c420074100c004100e41c8401006402803010304034007401904104240d004d0103403400c051440201c0c99050851180b6400560403090070b00900c10b01061034809485540010140598001c0c03034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 530059721 1250 530058471 530058509
    0x60603140612030d15030c030305040609080a030c02011d03010c090519080c0d0302070e040b0a061403060c030a090b010b120106050301082505040e161502100908070b0c0301 76
    0xc0100c042d140024060751500c4450241039000300301603605051171920448020000c00c0284c5150302c0030f90b104c0d40300d5940d20b80c24454080c000c01d0140c4d200800c5d540c040d151800c000303035100f204003016a6084c00c068501c540600b5000001d000c0120302980c16610f4042c10043e1954052508030480c0c0c0e003603542210300040c44100340100d6002d402000c1441c0e008100300c00c40750902c0c024041280d4064415541d011b078030f451402c80d48002c15181039460380020383c2840550a5244510002043c01039019404102800c01080c0c50303120041260611980110004140c0308a81d003000c0e1081794002001c80d102d6840e6003000c2c0d100e0300190407030200c5171602c100115a40d8040c0003202c1c140c1c0d020b08001c080c0c030709030040e000342d1081c0850710009005450f07a0001656441d1405a4000200d031440603001000c4041c0c05020714504030f45c04229420181000100896004503060625a040040100c0c8032010350400501510598800901c0c140844080100c2e209000c0b020754103880c101c803031010700308141c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 530060971 1250 530059721 530059729
    0xc0f18010318020307030b0612150703110c190816030201021209060105240f0315010e03070506070204110702281d0106051602030106060e090f010b0901120f0606031406 74
    0x70442c00250180c1c4030b802d0510106030301d811b04030340c028002803a9980c1e8030f0b54030450900b052030010045440080440c24032a1403038040c002c0744543c21203c080340b070410405092172584c0303401443c65a80c0010900070b5407400d0160b4201100c00308070aa1034408103983c1680307030080c000c0d40103002c084055441c60300803401031540414901c1c12220010001070700b02040040620f055004058001400740b0204060502045050050352180e0504003243d540d0208100014002400a17000d0358402c0d040300b8424807166076800140d455081e010750300021010300c050780310101c47c4110300c0701079484011400e5405481240c552035041c4010740c04034100e400f540d5001055402039a01140698104120005100b101c1c8148064074040381200c100000007030f01a00800d08603480c0d07800020001c0c0c880c400d4007505061030511240c0040901850074415850088a0b074170070f0040e402c5190400141820481d49070b5510f4020301559895542c00304583c0e966850302500504000d0a03050070301e002d8000044581c90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 530062221 1250 530060971 530061011
    0xa09031a010605030c0a0519080a0e0105071b030309020d060b121209010c1a240604080d0f0c1403030609150d0611070b15010801050a080a0b0c0f180103 67
    0xd403d07180d16045440c0c280d0703500402d806c0310783c800702084010301c1000307400702d03c92106042000341034642d03289600349180d0010590700204400c07403103070381400203201ca21940305030280c500340e820b184d5030030201c801490101d010386081100694083c0741a0703041340500c10315902568442c0c0741151550110a00c049034140c03900c20f2402c040203615801d008200c020b5002e032030f1039502e41c0e01c00d608011203101c8854100302c0720a01135a044445000b128400030a0780c00318401758800b0041155141e00f0310b031030320380d42c2c0340c0c3d0b40c2003104414100204800c00382d45c114000d4408000e40781e44910204030010801c88019581d40045903034600c104882c501203295400200c51400768000b01601c000a002025241c902c0034000400350683c0d081802c0042c0000b098003005400d00401801489072000040c00000426114040e00701a01c914500d0320204854007001a0f881c0d0a07550141182c141a03803120800d0f103040c0036001c1d00d1205c6500c00190240c40c4500d00a4004a813002600d08100b83c400e07c0c00c58046100d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 530063471 1250 530062221 530062229
    0x1030503031504021224044a03120a05130f05030c0a080d05070527010e040e0d021b0a0303051b0106030308090d080403090b090a0306020a09031a01 65
    0x60410800314038480c50002c180124080080c0c4007500d880310010f140d107580030003165512007100e800c2981d20f401d641480c0801100113800c403400e014156039000c22851141000c010211181001d00e06100c809070950031401007050040010000c02041b0b079038142e26a0712065803116104000e80c0001c0012180348210b6009400900c1c3c5040d41a40503a108900c0d01c03940344050f00c10384001d00150041805c20002d0048803480341c4505602e400000c05048160ba50141440c418080d003072002c030302400f01c0491801c255a00440f25420010848c50050741d510303080071020b641241c10b0441010070355034005004401081c00d0350803240000d40c1000d11a800042420314154000c503090802c00100e88598064400d0203a04580000c840d403445202e80d00f1500150302c2103010a000b1000c0004e0203000b4000180f80780c8103400c003001686000e5078003c000d1805402a01040d14003c03950103039688411801c64040e40d032100003150b0358644020b01820f226654881261644000c0000d419800c03a0391084904071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 530064721 1250 530063471 530063473
    0x3030705031f05100c021e060703081e010924080316060b0402030901050412050a020715020c040906021c021624090f110303030f01060f0917010e010e06010305 70
    0x54440d001c0d15000007101e01c520010b08100103070003192507074800900c0300320004a0384032800400f0544c4140000071710714582441411813a044182d400303032900011255078561514200d40f1507178a9000141d007a2f4a00d90340d128024090744004181010300d83d002e404c180c090741d003039440120115288c0c4405c0304802d0240e1203040d0000c4c008142054142401108020320454020031301540c00d1001c20200d81040700c0c180c60680d1128144000d00021003841a481305d4249029072414204040295803000075109590100081e01842000280709004088100d41d00a0080c0300040c02c90505001940141d1110303400c050000d0450401540d039031007100c0d0044e000440c040038412554550f0031300200003451402c0760340210103034080c180300345201d145685841880f0812303803540d2600308007212451041d13002d40244d104100b0f102c402aa0800b65604568680c509020340b4600c0c03107801c80d411130040c2c0c002d4822080c41e0b0070725039010406411490407501524020800980b012841c00d968020030702c006015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 530065971 1250 530064721 530064727
    0xa03090504021b0111191403010510090306050f040c0b09130203091e15070509060d0902030325050c032d01111812010519050a14040f031103030705 65
    0x3031410035801038494420000d407105051040c00d075109094542c5000d181c96400800540c40a03601c1c903484ca41c00c02d401251401030700d01c00105581d24081e10040c01020b100e2140306584c0784145105a407400302859100c0030610007410314030b02079404584181e5049030380ca181502d02080c0d503400c9c7e03000c1e146810402030040b80d202181071115002544050540072150241060b0040001c003101c00e03104140489100030140e13070062030300e4026090405402d079001c0160800445126944410a44e00701403000000050f59544507c002851442900c2d941c4130642c4440c2c80450311000f1007064100b0050181c0c00f130b03408664a4108040d121000c10154501c0010841c040b1081610840c0f8041e00c0c03070050f1000040e900e0703450100007505030403508481c17150b041c03aa0036000c41e50504001d0010514010750082c05a03040c1032140584801740c148100d1303190340e903520010355881c1c07954000d000403a024010f0991281000d040011040d8419103003540032900d0143c10041074800001160311070b004541e10716003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 530067221 1250 530065971 530065979
    0x302090f01020127020d1704030302010b09010b18040609050c07021e062505070b03070e01020d091514070821060108010e0403051201080d090801020910200604030215090a0309 77
    0x89504c60507604003000e940310000081c1007116400411882c801d4075610340c1d00d10310300203013550b103040200c50040c00401c00420440b19142c00f501c900c441c004803550307030000710500801d0050030560301c0340c0c0c10b260502c01840b4100410303000600c6818025100803011038041d003c020040b208102080750442003c00409003007039410b082003040f0f2000546c0d2440c00c03010588600e407409066400105920000009101d4419001882c6140901d400c0c0085e042c1150341e107101402c4058648200078120411a4510403c54480c074901c0703500c1208040e590f500c800ca40e08200c15a07411a0000340505160140a909400103410b02a0712401c016584c1026985c01c002e009209004081d00841c00c0c0003045c012200005d00d8440803501070300038040100314000410600501911040d44003100c640d104101001007511506074004209180d420704480d0707114001801001e500f6294001e0025014400c01e0008160b0b02040c580d1400002d642021100e40340c60036055180c404018004021509200c000c00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 530068471 1250 530067221 530067281
    0x301060b031e0921092704060b0f0d05060604240303050f120f060306062205070e03100614100c120e03070305062d0403050903070b0a0302090f010201 66
    0x150b10085078020380310186900001d501000c1ca2000d02c0000c80e00c2d010034801410b0030040301405401d144607281e41c2500002c4440320178141da0180014205503100c0000159a2b1100c96244820f600c0c09401c401c0c1184481c280079131280d10540306e242c4a1030400c0d100700c4500c401100c00320030402d04460780344c8a00d40345a8080e80c05600090010200c0c0b03030103012245140c108810710174403407050110340e40c80d2850310900305402c00d4401045103110300000215101301c840d01c100c0e58041122241c9000400e174840c6941500c96170b182c490300c07607418851703208000c000203c550060300031a924140010032007000d4404100104446100600000380740403082d10201720740e104190740c044983d0800c0710b156020107000c2400d180c4640c1040c0e4039a80b01c401846000c00d2089140302c2d903240c080560754440d418803015082c44100c00780c0042c08112010401541e1590103010310401440d116030b440d0b903600e5103030101501035005841c8052140500c420b40541d95401030044d804d43c60000603071000c03507480785000c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 530069721 1250 530068471 530068531
    0x30405070b03060406090e1c02010213090b060903060106110d020705300105011d1e07050d0f15060f0914040f0b120618010902030307150b0d030e0301060b03 69
    0xb6550003511005c0005078402140326000e1816240c0001d807501d581d5010300140003014141c14001113a1041000382640007100400c00d05840e0500070200e82092100000b805a001d012811303a8140210000010101d13000210f025041c8812000c2c1c40c199040048240c0e25080307944075098001a60340100d52005958002215189c5402d04220070100320f08079009003118001d0300b03d10151540300c4503040c2004001017030160301c0f0004800c400c42a182002d05902c0c0640082c003542c041c003401260a4050362840d0700011002c24580200b001120000c20001c08190094030030b40020031103201c20070b01c031035100f0410700b02078400b01404c0500010804042c00000c1c0b912104045000d5511588500d003079807403007802c01d1070f4050100204100d08000c1901d010b10782c00038040907544d170726100e010b40050702c004c0255400c86c1d4100025400b40c0c454840c4180c090400050550f40c82200224004c0070180c01120b02010f08100390002c10a150322251001001d00c0180c3c0c052081004007080009040211101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 530070971 1250 530069721 530069731
    0x140304081b0f0a0b01050102160803120903070f050705010f05030f0718030b10050a120b0705030613091211010b0a05060703021f0b03010b0402030408070201080a0e030417060c030405070b03 83
    0x455500c240c1d240c1c03202d414070104500c00c03164201560010042903a04010070f015105242031031010f105d1403d002d09584e4810fa540c04180041003d000603600031041c400da41d241504203450000824161805588030055405010b02081c1c6603248004424031540550744100c3c8042c400040301d81361190709a9091600b00301d0256180a000b001000040c00014003e0240010009002c0e015083c2020040f10b1407140e0081c001c05100d80d550740d13010600915007a900100c0320309243e652a105e18001c64080700d0b03064082c51600703051115407000c00c010105044c444424580c1d4198413580ea0f8002982a90401500716a000c13120320410b114901d4124001d01e0342910a004450640508841c46000b0181f00046117003180d0743c440460160742400e00509a83c040200c404524510701070361403004a0051050280c10001d06000043d18828907901c0690341c00500e100b00c0c5c0c0c48a42d5102170380c618410000d40c5020b1170080601240002c90b0a02c00d881c0142da01101501d442824040015495000100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 530072221 1250 530070971 530070973
    0x908030420041d011d032508040303050d110307020d391e0308010603090614240904210e0d030504032901090b01020c03060703050601140304081b 64
    0x81080e803107035901d2240104207000f100d0b00f8600080c080050508440c03800540408110091000c40c0c0c040b880031044502c1c0380503490484101d0822039070140c2a0000c5000001c107402c0d0001804018160844040d02083c00b03d0802801802c6c00900300d006140003d940b418056808010090340040c000e01844080b20840a40c1c604c001c200108042d284d80b22091042c910074059581070320034411800c1c00018100c5820178100d0700783c805035130000c0045030144a02d008050b44c0d18940020041d50350005030748158030600c001010305200e000c141c094004000030800c4074182a10002541c284262014415600b05403850b10b804580100104010a80c18190040100007036001000f940c0394141400414025610903441d14254584200d4240810805214500b4242ca0a0040c40a42400035041d07074035181001c030f5201c03401c0b00180d2401c6031f41c1c1c04007036141c09410708006116915a000a100d03042c242c0e503040e110407410b4007061840c4030981d00500002d4041155120f4030303003010015054408610 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 530073471 1250 530072221 530072273
    0x6010302070201110601061725050304050a050703110a0e04080301141305160f02011a01121103010b03150a0b0a081003020303160c050433030206030a0606030f09080304 74
    0x280fa59040c10007d070050f00c007141010280780c120600c0e000e200c5520034842004d07074031000241103160035029441e18070748040010000000c0c2c1001001d00034612455800811a4209038030cd14080014114080e06d140c01207505610003d96425440c000601498000150034503590805090140540383c00e405140c104c450401b40026100d454800c03144070b0a8131950707c690f41c420444c00200443d0403003508104580c1800c030008841010403105444901c03003424108070000305504140b02901007035030751814010020000080790198500210700c10051440700c641c107800410100f0140c9a007601880c10420780c1400903000c07180c0981500c40c1c11009412501440c181d50b83c0c006882c43d030003078030f405101380303950b00800c420454071040b000080c0000310340034083da42403a17071903000e03e0b07801240085441541100744802842e004441001030760700500040e64a180203110300e0701900181c416003000a00c1e0200d411880303c51403003912441071740b18008610f19222900e0b00314101002c01307407007140da580c59 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 530074721 1250 530073471 530073497
    0xa03060911030d0f03110a210608010f0518030a02030301060c1b180b0f030a1b091508060112020f3007030b0907080303220203010908030f060d080306010302070201 72
    0x2000b00c0c0d81400c0c02513a0b50362502051000c000c0588031502c00b580d040399000e002203002e1350340054015803000f00d008031400182014580345009040760f540506090b5180031075203401c0ba0704a40040d44600c000304440d42305500c590341d84036900c3c41102e24180041e0801d00040c008070307201d12421a6818001c48030410560341000792007044148a500ca01e62904041707050211204480c0182c000c0c03201c04039040503054440d400800d4a4840301c10000300811460403450f40d5200320249408003030403050b1801c00c5190481501018004a140519038040c400d44000144c0c400d800600400c0310b541c0a0240f10403461002c00b4481c03030711a81488101c01ca0f1a44032103516400c44c4c071aa0303102c46100103004010461950511440c0c200c0060303c00b42094020070300a10800c00c0000c11250010325040f040004901d9880c120b00c00d6608a4000a616500380502d80003402a40d03005140a001c09043c1c0500d40d0301c03007c00f04640081c1800c0c005090542c00d200003146507010740c3c040e0207a540181410180c210701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 530075971 1250 530074721 530074723
    0x1106090c120f1002030114030a051b01050705010507111015090c12151509080307290a1a09060a0311131b1b0503041421060603010b03030403020a0306091103 69
    0x110f0344140c4140350340400100001e00002503a00c80c00041500900340018180d103410b030f118010b210311050240c160050303400301c0c1c0e4800c1c0e00300e602080e0042c00800083c105000300900d0360381c50f85480059031184440c6072402c0a007030300c5040340501081800040301e03072615003258050b259030301d2882c081c04030f86103021000c1d6080d809020302140c03000152001c07050800812800038a5160059010030100140030b00802c2c1d0b00000304c0305500c1c1c009420384420542210200c0321030b03e110b007022a4012441052245560701d0360031018040010031100d000b2001c840317080c0300c904442103641c564400320003c81000415a00500c0c07613122074000d00346410090000010806030703540c5207480c0160000c200e019141580d80003030214100c195000c07032525074203d2500c40b507070f41c0d02560103003410020341c0c6c1c1403450796559020726415483d1132900207141c0305070500c034000d5141c880807141f00780a9402c043c58811549408070441c1d060701e50040080101c3c2e03055071640c0000f0481c255044a0541c000880c078005660 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 530077221 1250 530075971 530075983
    0x3080a0f0e0601080d140f0d02130828050613060f0603110f03030313121b06150b03011a1b07171011090405040303240302011106090c120f 61
    0x40340e10002c0c1125498180080d26101c010410401040402009400718095500403520310070743c4a90500d07102c20130203406000031710520315802c81d007640403000000d07602804504860b1280c6520000002d0b5107a1000304601c50002030001001d540150700041c99004018000c0100f0324014840042c48010055000c421280d46030010786892080300350307410f1140b130304806140c5042415030146096040410181d1150b59451b41c0c0205031118244c1440b800034428030412600e124841800309070300c0a40d0074100018410300c1a41d074181c0c980c0744400b00b03070341104d1803c81e41201e2001102d80d00c0c103184520a00216007040e4101c144001408031071035400030042004e60050120280c291517200c1c00310041e503182c030100c101c101080d1410414104001c6660006070344c038101040d07501244031390795450100c00800d2091030f19542d403a100780c0d038058451a800b050a068034801e88644000250004400b5944c50048070710380e40961128041601d24244028040d4203c10020200c644440d070704014541041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 530078471 1250 530077221 530077241
    0x507020c1504030209010b04050306180a05120306030f010b0f010c0501060b0a050a080a15090216150b01140c100b0d1a19020c0705040c050c010e06090d1b03080a0f 72
    0x58000c40d080c0f0039840d1400d06940104448507c0a107000e240c800465142d000090030400c0859641c03c031541058000d000011a05900ca025148210805540c0708a60b4005540842c02840f86a07c4220788000500c50130380e000314000d040b040c0f800b400c02c0c01110055007588040b039240d5280e0200041c1da01015000d0801101e45032a269102d14a030f03000181020702c02000c400d002420000300b101c488850140c20320503914180c10150740e400107409010705148810400500c4a01ca69418082005d095440084050700903030b2000310035040030244a100380141894a00541c0001984000105031a440350200c1140948004080402e0b0344a80c0400c820f004900328400110004001004078900030207800702485c04001c50814002c01545170b5101218040e5500860796040031241d424050000c2d5280d00602e8002400b80c1182511a280c0310760054890800318464501c81030b000b03134000c0102107400724802044c4030314840c1640302155101409080090781950310750368482e08140f280518882d40c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 530079721 1250 530078471 530078509
    0x40b0307080109050607111903050708090621010b04030b1303020c130204030201140c100b04060b0a0903020a0905010e0417072f1002072306130914190507020c 70
    0x54640f10b01c000c1c04000d0b0b184185c0344c160300113099444100c2c2c01038592a503115003520b03142f0b8039141c4c5880e1026046c0b00380b000c0154070400101d0101111410a001c007080390ba04048000744a983c0c03440231011500690100a00084090300018203060038041d0007007034103000380704543d41c1d042d4a1020402c012400a188a42c03070360001420300540d40c00940d02c40e03a140306040c00f54601142c03028141d44a40d51240107161007030721444021403503035694108402810141402c4c50351043c0c1640080c204410a00c4124020740c8220400540030b8003a1240c2c034100c0303404018418481d6515a44c40025130300c2c198204428200c1801480080340310700c144c00c004060340d625083d55254040854800d480d0408545074802d054000c44240072a601242e102e007110344d64450045010416000c17400d0701c1c01e410740e40d241c000c0c4010441040c03a02070f50004808850001e00204240d01000b45086440002100d141c445031080010744483d2814a030700c2641d01c4185481640c1501c0059000100d0900b0b90340d1070a581 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 530080971 1250 530079721 530079733
    0x609130f180c080a0b0a051b040605130b040302030a02100201060b030f01090f090c120f150b090907061707050d0e060109110403050627060f16110c040b030708010905 73
    0x300b0000c0d08440000d0034001005052243d0b40740c0c0c40210b07042c0001c1201d04010b460300e02050b1203102030461801c038030701d41e50311854a607030f200c2000800581102d03c40c0321030f00000007000074281e403444048400b80d98004d809011140519020f000d4003610800f8202d01f1907580e030303030001502140040a11301031002c0303c503041c085514010708a401d4404100000400e640f03041d403440009401503c040b07048600084201201d800d06051045c400985100040c4c0301e20b0100a00002070a890f6000c031120b018101c46005907a19041856561013a0b6805001d020503022468002e06170304202030b040e44202289006440d00800411184c1528104811414a40c0c000f200511040b2801c0c000e1400c103a00b94844541083d255032a016070f0760304050141052050400011205100c00000e00e024415402040340d00c40d003405100411081030895000d012102c0c008206084180f02e04110704400b01c1020040c08030391002010000140300c484456507161241345400100c5050038011900d18038080d03805048 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 530082221 1250 530080971 530080973
    0x80c07060f030e010b0109030227100f060c0c0b03130f0501060f12080f0307030905070e010302031606020d0f02030903010c121103130b04082106030d05090609130f18 73
    0x20940f07010385101d2095904221a0004e0799900400d0601265011103001825000c1c04005075180c00c0401120035907402e103c0d0400c4442c22621040c0000c4403800350040c03a26585c0c3d000100d4410604c06002807540c0844042009508080c2c1c018682000d48400000f0625450790344102311a201864116003a9444e0001000300e0550941494007c1000103015110140f4a6480302c1c030b80d200c0c600c046001c0303102c08000300c0d03072031880f0768000e40707406601c80c3c02c0f9041161079000c10b03038182e2000d2001b00d02c680304682c0c10000011000010728200ca1040d00180004141c0070402d503540c0d191a02c10300708601c800d00c0010500d0303500340200004964070f40c407446001c01400b00301a0030746540361501451000108103104120540b20b030510b00319500900e0380c100640f2103160074840f40c4241c281c040d07100490342c2003104501e0a41c0f00d42d02d018540480485890031006030f003d640d6405125081c0d07a014900340303da02d03002d0500000301d00e0b0f0000c2c050b0b0700140410780b244041c000c40e500c1c606030082c20644e00038050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 530083471 1250 530082221 530082227
    0x25020c0d03020a060e0304060509090a0f0203010810060b180418050102030703020a0e040603030f080406020d090c080609011a0d020d0501020f09011d0307060c0816110f0108040f0b04080c07060f 85
    0x41201440f00050747c40e080c2842000b030010700c600f1441074061030301c040c0060b00d03190007a4008000c10040002c00e541d60b503540d04000b6501c0260680c40c009040c904040082c109441004980725105c2c00301c2c05c0700c004890b200400008280783e01c011826000c03105810000940280300841c41802c998034010303122000c0460050200d002e8030a66401280303001c0c01880401c3c3c108085956058541c0713040100d03555035142200280c018404031385003250604170103078104403600c01c1c81008c1d104d03d03c04445450799a040d001c1e091302c0c0d841c40020a03400d035a9940d04841d040002000c03007071364000b4210340f4540e03586995007400c903404484031800c000001301301c080c419030313000380c0440c100030351000798440e00c2c0e0107140003a445804034410300080c08460752282d070422a446007515030b5004444000d500e18002800d0034850680205a60703445042160351810a641c01503030107a0086401080c400403194103a40c0c2d40802c0e5030017400c180c600d22420b000b04d0031201c40803c40300005d001c003036844100c500c24036175001d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 530084721 1250 530083471 530083481
    0xd0503071a270715050f0403030804030f031b0302090d0209090105041101090b16020d020d03080121240b0a0b090406060807020c0411041e031a25020c0d03020a06 71
    0x8404800341c41041c81c0c42c00c1000980d2803d81d5101c82c411100d80052040c242c40c40d2150b1345414194540200f000000e240d0400581c5208034002d803511b900064090904804440010186854400040803901c1c0524440e42c050580e030b89015280707a14662a40d000100766203822100000307544e445204010802101c00c0c54007810100c02c0c2130205d841400c2008005540c007901a000b44c4280e200d19038542959a5103200c8803103aa00075210f8644400c55040c010b19401c424000c1c60405034200080941d14225140b0f250310b40342d00880c0811895169020203d0000020200c0254154840f000380219607520b8070100e005103030418007280c0c1c4002d441c00b80819550180d2210051052801c01c00c901c05030085020b02c48183c0c1210009203140441e010b02c0c201e0f000e260400114180780d828400b02c1e4028940303d20007940c1c003940c6130a010540111050007600310888040c0007540d1609581c0c5036204407071006d02c00029540c01a104189610400319034803007400381d402e6005a122180503000d000c040d22031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 530085971 1250 530084721 530084761
    0x1e0f01060b09061204080702090a0209010801080706020a0f060f140708130b0609041b09020d0f150302090405010603080d1b030e03161401050a290f0d0503071a 70
    0x14a0342082d602000107195801420440d010180f503001c0000e04101c0c2e00c9086a90702036005180582070b08100914000a40007001c0381408552044c0021503407031350010b034107000c848050f03004122410030703a5104803041904c001d080311515210503200c44c0000590284100d410007007a03500c079851400742d000425040380a00000030b1054182c0b0310802182800c42136039800300007030312200c07043d485900e0045a5064180300c0d044071500d18840c0401c840c101030f00206198410301005006c22946c1c0140c100032681b20503800d031f002c1d200f0000e0400046c01c1c80d1981340e0340540120300014030749940340c80303a50f120340c000750010072080d6540c0021000342400e02c281ca840c503036a901c1c0c100154000002c000c1da03079118804080d02c1c080305640e001000c100b030054026090303c00f1382000b80000d081039810300000e8161960102c009603d00040400004603004000c20351020060206128554010511920a1804000740c41d54082000780e0400306a14200e440740c8050301006500032392520f00c1002104240d041c2d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 530087221 1250 530085971 530085989
    0x50403050a290609063c012615030a05032208030306090a020c03070204142e0303231204060b010212310f0e10080a0f051e0f0106 57
    0xc3c0201c58550f20011684400f0941d150f4032100003089000403a401000f900e01019003038100700079150f807414480340c0a206400c0e207902081051b0105941c8880d480c00700210a003020381000283d9024200094081e40e64000d41600e03080c1c2c029858407800c1d644400710588040000c0c0e10108562050520444018140580510b08504042d000a20301c040040e1840d8225a00410603414060f024422204000da00400c01c20401c2d640052141c41418202d65442c503460501040e0458407505455100403079812a07a11110350b030442e9015100e81002c00c1403980295507078031003400c280903124018040c0c581d00b00c1d0311501c185818503002d020303200300301c61039811500220f2500c82c050300698203440c0140c5a50f000c10007000c200b040f000c803450f010711840e2542c0c0c150522000074103007000d034000416211001034140b03c6a4070010312800030551449600c1441d07109000c0302010981205180528610074021341ea041c4814000d000c481401d140c0000c06950804c003a0382801140c00d2150800600c1061 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 530088471 1250 530087221 530087303
    0x7080709081b130c08040219030b1609030b18250b0309010e0304031a06100c290a06061218080315030307121b0507090c050403050a 58
    0x220141c480e504508000040c0240b048002c4481e038038a8511055031101d070004000358801c2d13400003007814006450580c05205880d02041c050b000300851042036036040310582a0b641c40700c2480c504078403c2e41c2c0d000c10401c154100003100058001c0406405004016120448015111415801c0c45254900c0c0307058901101c444401588400500804840011b010503840e40d2f22800b83c0340c09080010840d5096010000b00402001001a41c00c00c10110040341a2010381c0d6041c14010840c0752151540041030b402015600022100d01100f422400e140d18545c50500c090f501008501c1c1c0c3c165400c00381c05498031001e1000a40c01100d00032031180c03051040c0841c40c02d030821007a0900c41130702c0c060806400000080d0110024890001c194640030742142d548800c1c905005454842d180f480c84001103064000c1c00f1786a1601116011058000029245031032504148500034030b2200c02c00c5003400b00c14800080450000c1c49496600e5006040d40c0010b54120005083c0014090601c01c0c0030f14802 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 530089721 1250 530088471 530088479
    0xd030c02060c0702060708070b270c0906010c231612060921052107080601030e0a080f0c0606030610050d0206090616020913080706150807080607080709 67
    0x5030780b81c00031040c00306595100014004030348588600d0304003a00560001849004000001d2070081c030500040d0200d021400340070400c81504030701007117990703811340c440c198a243c18500700c4000c54000205040040c40c1000c0f5a41d85d440728503000c010207520703661580800c110b00d00305000340b0020070040e402600e0303002d040140040c5600e080c050f02a1009544440380c800700a10441c824070180001214140c44203442c01e00282300d58000004141c16805c82d0398410301100d2440c12490040c44140c03030b58402c0e541c4803c01140104100304600c402881140504c030302241401005001380d408018101d6903030340070610101d01e4880e000d450140642d0002c8100030243d00e0308030700f00055034030494400790101c210740001000c82c000c405000340d01c4040002c82c0c51804007640c0d06406624820f0f0b03001000344d510046205400c07945002d000e40362020030080500003c0081e07009464400e203070386100341d181c0d803559002c51604a80340c0116286174420001d1206d00740d0412044ca50195aa00e40010480c0c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 530090971 1250 530089721 530089723
    0xe1e210c04020c150a06030b0f010303030b010f3903050d0612050a15060506030c0a0e03160b0c0a080c0708010b15040312030e10090605010905101a22080d030c02 71
    0x16200d98619132082c6200811629061600990015504401080e40c0c1d41400803080c41064403c0c40101c0200e03161011090782540641060407030b0b021592140b090b01c00c01c8d08130b507134100105440216807002568003840146603056022640240c06a50b9064840606e030b4140400c0b0394840d000b01c4081c202c40340100000600c0018900030f2a03034048003c10780d2340d0400d02104090300c001e810213544101e020007080710b550740040160100f40501c0e070381c02600c00c68403010705480d038402c0356820010203c601c9092181d000d50304010072180004400f1074a18074216110880150003a404903da246c004d8001005046c00902401e600c9040441e21800030f40003c0a02d0f0002d4880e611005080900410b0f022818901a6001d1141030101c0b42c00e8880e00c4a904681c5c0d4018804003101320360440c03501001041e000040e1150503c84e261125405020301c2c00e101049040c90003080742103001c03450821484214004800b06140e900c513080b080660042c0c2020949408e186942da520f800300751a018801c1003035a4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 530092221 1250 530090971 530090983
    0x504110712020a020a0b0705010c0f0516020303070807080903060a0c0f082e170c0d060e03250b0105010e0906040b01110609060603120a0e1e210c04020c 67
    0x5440502803810401d120030980c00c1003d1600081d5000201c1080010107011010003004020301c514004c2012000701c800c1074a6190800341c00e0740014000740003014100250404102d01680020700b01c0c0d08043e02c0f555460b000d58400041100d64040124001000e42010010300d504038030040b10500207400c0345030740100b1441c40c00300c4c800304100310031011070300e44128400c100341c80510540c55009070265691403180880010300c03030361276070f8100c001c441d070890100400e60900070320b40100a40300c05600c0b501d800c4044d0011014124450000f0131611420b00e0080d2000c04240303044610701401085203090107100144d05a002605001005001c4100c50741c0d0000a00e0b40620708490010386081038000407201d02a035600702400c0c5124510601c00c11582c0084c1c040d1103207030103c045039503040203501c4000090042180e40c0021500c000b52240140c608100c4c004552402031001c82054624030001901c03c41040181900310021010705200307400d024030084643d0801a01c0a40c540901e07444001d543d54 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 530093471 1250 530092221 530092223
    0x30c0717070e06220e010902030606010e06120a0b060a090806010b25080904090317070e130b061c0f0b120d0503040609050601060f090503011406010e0f04020c0a060605041107 77
    0x8840d60f62181c000c04d440040903601c860440030400050f024105500030720850000340c0c070911400c0000740c810340c402c500c0b441004102900d85410035001826540c43e11031702030a5260b440b603c511201c4001e40f10100544440101070380c4044041e450100090304012040e000101d043ca82000f244c44101c0742c11300034280b084030521003080081050300305129240916403516a0003420070400d042455031010b0909609072171042c4500d11616070b8441640c100340300000030b5800000341a8100030b401541c5d4840b0741401d2000e0005440c10503411000071071700303110145401c02603680d600c000e2848070a038072a2400c0d0200c269040da4030396130318003c42030760341014014440400400000080400c01980c2140000390b0344a0110780c00ca58503000045e281005450350400000c2030040e0001d800d05d41405034080b20950820b140d012602c07400d004490b40d100b545856500001038460b03450007600c07984000c20100c2c0d4104007070441410079203003400544480303520941c8114105290703d4182c180c800700311900c2c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 530094721 1250 530093471 530093479
    0x609090218060c010b0a1701050a060302150d06030f030f02010e0a0201050d0905071706180c0f0d030215091b060f04141216090c0201020a0f0806060c030c0717070e06 73
    0x183c440b03100e9650151510080554101c0700781390000600340d0020039100081d005140080c4003a035248a442e0048030b18512020794042c0c0009405001e01c180c80c0f000f04001180004045861a00c940340c1c0c07101c07200312200890000b80e0344000030820719070a00c519800125640e0140c0304611007500028020700661400503102646d600203a81000000c00c002c0005240908607002244610150162201000c464500705200140304040441002061040801c00010052910000c180c411301801802c40c1100714250700c5811400e8903161000400188180306403c000d06007050314200c400c00c0b03126201000ea0282c1014031640840d201c01c01c054405998007951410026125140003500e42103c10101008a00030803141003420400b01d00da00060b107004420500400f011302100301d00700c0c0701d031403000400141d0140e812008288200c0105821050040802c0e0910020480c1a802c541c40030000301066408810308114039075100c140381680f0350f403010280c0702652078990b80d0850220010041485 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 530095971 1250 530094721 530094727
    0x7030f150b03090106230406050a060c120c0605040c080c010c0818210a0c0b0702060a03200a090311010206010f151704110a0b031513140c04060909021806 68
    0xf002009500079002441850f510b4869032400340500903900103107004540c000d070705004002c02c1c03e00305551254203ea440e551070203882d68040e107500c0c03a00800c1c2c00051040115003843e40d030126200d0701a01e800b40b4000c1c0b0342440800c0c6450303211840c01000c50401c5050001015400000c211705c501a100d444401c125000207080300280091410f60068002281300701000f08090740c00040010703440c4c1c1007407107018078044a903182d03514103505000b2003000035407010b820003003c0350082c401c3d0010464a08403410403800032040301c400b074103140c005041c1d000001d40c1e80e84007003003805882881d0010025081c005002d040d41001c00b1000120907601440c1c0ca2000c101c081e000d070091040c41e03c000d00302c0f540b0140340498145407403c041903995555080784a403400c100b001c40c8500c9403504817402064141c0c00b01c501a0804414081072100c1d200c01101c0442c0e5910310441103a074402c40b4981f04643d82208665200e00f004d01c05403c540e03039904400c00861040c00b81c9a242d0302e03900c03020094064210741940d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 530097221 1250 530095971 530095981
    0x10509060106390305120901021c0207110901080c01091d010e1503030403060605040c0f0206061e090406061703031501121b020f0d02061504021e0a020607030f150b03 73
    0x1c4080f04540c8120f1030b9840c986810306160b0301c00040c000c0c43c0b0510b003190b841e50312008a60303400d034003c0d41089614121044104143c191166000f4021507104014100e440e030454000540c002000b41d01c100c0044c1c10901c88000c2c1036a001c0e0307428000e030414840078088001c840d400130003651014001c5030701541d041000304844441c85480003440c060000d0031242e40f5a203e01e4400c0240120388201c0380a1130401c624191014018400c07100f40c04a241d00030949540c65008002e4a000455034945810152030030414460302c0f82c140300d034810340c020744010410780c1c83c2800440202000c1030011890b40c0052086c480c11504400701020000400d107012241903159280c99001000d02c3d0701d03080c0814030200844200140c0124076050012801ca040d500c80da400007005988810045959114012507854000e80901e0b1580c00340c0202440c02413025903486507460000c00f140e02c80300c03505002d07034403990400800f070b81d050207444400720304500c003031000410303800140040c01100c0c041ca81c201e0784080300140c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 530098471 1250 530097221 530097287
    0x60b030c0910031410050c0a030e0c18100807080604020a05060708030a020915030412090801140f040f020907080417040b07061e1812020106050901170715030e010509060106 76
    0x21850205c40c50403c0301d81884c02481e04140c0c4044030752030100b400e1411940c1c05040203d2403040251024200320180b481c11800d541807404000e0400d81072858034a8085400c80b410001c800c060400c0800800740c904007801000f1481d200c961000d48145003c00c006400910750300103580d0420403c42c0c015845202e61030000300c150010142c2c0c484951004001c00051224140000c919840c0a407204080c40c0d46a09400f4244c59500320502000000d9001203082e0310900503103150321a0140d580c602d071401080e0700040841405466520000c1c1c118400d01c014028040107100e0f40b11414101585002d160100c52106401000300c00740150b5038074102400d440c209a02c207036046642042040145d0b0442d001c2048202c0d00429081c1c0d850b41040b0392180382640144901429524020702c0d03c5450703032a042d21040c1d854145d414008450160741e60000b503069141c202c640c441c400c41d45000c1001d03008c0307000044c00c68400a117105880d40c000801000b10580020004d000350745483e1070911500c03982c4d0842c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 530099721 1250 530098471 530098483
    0x1713090b04090645030806030307020a0f06030e0d09050103020a0c0c06020f011406031e070902030a0b01021603080409110f0307210c050d0e010f0603060b030c09100314 74
    0x18000a0510003040c54410002c45400d04062840e035144141c071256100c80c501c0000d5046454442c2020030074a500442e01a0350f0b151f920400040860340352503010350101c1d156501d030b0760003042840d03013000040c4001a05402681c4090010000030103511001c0c2c080180078107850710400b4141a8006606040944a12901e0702000e4210102d03080c4241c0d50381c002541c556000300b110030389520303045200562040f0561000c3c090100240104041c00000100716840b80d00d80b04400040c0c071808100041102990003e5446003181c040006030448018002905049966040d00761000700c0d050706000041088080e1070903200380f84000150001c0e0407034100d000f4481c006e19500c1d08000030041110140d440004c0015103074071405076072030310680700d0110415200f00185000c0811030038001e1401101c9940e006100000044d000407030b514062420031402c44e02e46030804e0b40c1081d00c8806021590404201c040078118041c0c5c1c040c000751803c0040d141b10015103000042114420115000e0459410409 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 530100971 1250 530099721 530099723
    0x8040807080d2c010f0509031e160b06010e010c12180335250c030b070207080d0215220210080103020a050d0305070b0702010e070e01031713090b0409 66
    0x41c2c50400783e403105620a20f2241e0018035a00b0340c2020190001c6044902030980510b42d04402181450a00e500049101e071858680c841615824894010b940003410101d002141c045c1050502e6410040300041188500c40211814130035031003041400607824084445600400b840d015200c0641c01101c0c4030700703888070760000d050045008441e0a10452401100345421a1f09a02d00c05200b941c100791351890062007482d006000e081310707040c10ba220346007840307800d4030380719104c4140700c507850341e039502040308050700d9141c0141d12410301804800c00411078034544401c503000034807605848004020384060018a43c10b61080e81e180d41859070b054043d1400e14042e4020304040382c420f09018020401c1030240f100340d04c5081814000966420140603041c0840c0e0140d90315460300032941c660342d4007000b01605c04001c640d61140080b0010030180040310250513014441109075145040110380000204d1402240d44420070403034440c2020303804c43d02c2c1102c981e80d81c042105450f400004005001d0000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 530102221 1250 530100971 530101001
    0x70c031101021b100905061b040504060b0901120e0a0206070f06050705071205090603150f06040b0a021c0206061912030e090907060806041a1201050403080708040807080d 75
    0x2a03183d4050800421062582d001c15003121548482d9484210035a0205400900550803c0c40400c0031541c05002d01d044251035101003910305607030355000c5405c9420f160301c8122407038808a48000310750fa000c0c0c1680300b0600120804d00c521803080d00003075204d14880700000d20641000403000100b000b40e00301c403000709801c03c104003d28a01a0b00140c8640c4c000300040714078000c5103c1c8000e59601880a44040e908007a1400e03040d0741d151140f0038181002504c110f9401401d00c469403030103949100060015144841e41c45403250b80200c8080c0c0341558040556845500d048440b42d1655400502c3c0c0358020700484580c40d040d00301c00502904810540c01035008900412020400e040c2c1000c00b4590710007050f50141c84695078050f00740d0702d60141d4005c4400242c1c0d075501048a03884c0039008610301d505004c2d4000e00407820701c000618600b26101d5040a00d9454004110a16400008c021347c401001c1c20185081d10702662002030920803000c0080103c2c0d80407403591110b030542e90000351803918038a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 530103471 1250 530102221 530102227
    0xd05011506020d0f2307060209033004121b090c020705010906080f0105011103041e0509072a060b06070b100b0c10020a030207080d090b0f040803070c03110102 70
    0x4000c3d2a00c8429241d040410074039074411840700e02c0740485020125225104a0300c229188600d9041e0f90301031101643c8480d001c1c000a10719a40511050b0b070f1801c0c40c0c1c041401001503007619241503080f201c1072506881c805120030030000310b58403000814141d1048909180252400ea1a6598151038000c1c0e06101d1805582e02e40c02c580009000382551401d88480e030b200341d0385080442c0e1540c000c50b0440360b105280b0004103c40c3d40500844103010052405a034146600e402820400700c042c142040104000e400c030400c40b60a2140841d41c204001d441d201d00c80846101e0120060403c40260542d00f0111188180601c41503901c9524422001000e140e03a524050600039043d0205071081c1c00e02c038502c1c001c0001c0f40700c0a08100c0d40429001400f030642d407405009507500039000602007006154007004148002425a001000803c140650000360107843e81441582c2410003001e60320061070701d07030030700000ca20360f0310590b9030100b810329088821102916003155841c0e54244183c01c198004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 530104721 1250 530103471 530103479
    0x60c020303090f0d0f0506060f0603162d050301090e010e031b07030204110903010b04051302010305040c090504081201060f1b020103090b07091706070906050f0705030a12051003050c0d050115 84
    0xc6480d5008400803180d0040d0f61058004001543c44161146008840e4a41c0105440b50003014a08507440b4000307445d403403914101c0022170411403c01410dc001940010041c484403d0620410001100e150700070403030303c07a84c44240784da030f440307003003101800c1c070180301840c3c0d4a00a00300400b402940d4003900c1031120034150343c001a000c0d000144a10310950924180030b07205e040c9407158238802c9020885003014003031190019030003810b000c2e2055a861500840200e03910030640900c9004c0c6208200865035915000c140001c591030681161042103602c0d155080940d030321582031003400c40741501b45044000c2510068004180d0520001c012030072103410410302c80c1c1c000c21408102c0f080682940700d001368501580f91514011110f25010840c0b041c9c040c8a50740c4035a000d0400184401401e500c1d140c0140c481d00c0c91030b00034111b40302c0003500700c500c40780c0721a9850241e55000301482d100310700d6180c1540e54040d12000454a094050401441000103002c02500107074040140c040c03025600c80c5e25 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 530105971 1250 530104721 530104723
    0x7030c05240406090303081e0604020702010c0c0f0302100504080a021507050601090219090b030f040c0e01080318190b0a0c0609051c02120a030504080d05090d0306060c020303090f0d0f05 82
    0x100d40305c180c012503e00c00016640240100f403505190360300c4403c07101e80303a07240800c100c0290418002a4104000e081412001600700c0c8d08032006449075602c8280264611b02c100000480d03c444030130b003004803e2100b042105c40008102c05940d504842c0fa0007688107203150498a4001d028000c0c1041c03060000004606500340e008040a40000c0d960000d1000e0690003a92410510311991040c0a010070000d800000c485104940040c841d64000c0c0f14196140402440c100c02030f000f40813160800280368001c0110300c004081c400310b064a1081a4450040c4203140c0107a1a11402498a50000b045081c80340301d00405214150b20142c04c2018a003581030150f1303510b041003403892507544106400c4840b80d00000b400ca00000782482480d182c800d03003c50440142001a00c2200c0c44201800704c00846442c40c0203035441554800010820906184d0b4002c0c150749003940100d06101544020401685001c0111680c0250a4901080398018038010030403040c082c940c00b6001c0c40009641310304000c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 530107221 1250 530105971 530105987
    0x50105330f2215060306270e0a0b060405010f0302030a170f0408030408240c1e0d020d1506020d0e03070801110712050301050604090506031c031d07030c05240406 71
    0x400b0007843c400e882e8803240c00b41c04881c1c10303004841005540c01440f0601d11441a1617010b07012060202190419000090740d15104000200b00c0c0d0340c00c0400c0402809007064410240180003d0180800032031441e00481d80702c1c40c4c241c0c4084c007454000050b0341c2c001410303070088880d680d0820380e00720341ea0380d40c07546165203d801c103000d0100b2074082d000c21a08031a07020b28408181c042110789c03055071a00e6410350200f241c1c0c40000c0499480c0201c03072503000703a20401009004031011501c409a66a550700c10010100c0c0c800c4220002e2048500500380200c80d800200d4600c031340d206003081001010310360002890180c1030b50000f00d0303960803e8580b40d80c482109010340000d0780f02d0660481903080c810020b803a11702003401810b80024080c44200030b14155074000c01d42041c00501907641c160020140c0c0c0c1c4100b11011080d4001caa11640c01580b03e012040e45c20071081e5420014200c018115a955050440180318843c41500040240b002100d4240f0b42e0084043c82035010703640d602c1c2e8800c40070304808 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 530108471 1250 530107221 530107241
    0x10605150d05090615010c1b121202010e06150a030813060801060302040303021f0b1315060804020609010e01020f0a0c15020309090415110403050105330f22 69
    0x70b42400701254541e10001251400343d205203a01d420803486880045903803480622096506c2e94840b4540300300c413100710366110040c1604020761040c0d9860303800d11599046a100ca06421a89811b0b420703800c83d000071034125089003404003811b900300780020000d400a461508007501c5c6120000d83c60080d5820300082030211040d94a4120700341c0e80c2c65070150300300d0203607100140240c1c000565000d4040304040c2075a004c0c8041c080002a591866404103034048403180031030103045d50f1a00e0601961400980d144014502494803220500d4240d000c10010f004a02c141f0f41800308411441c8981c1e80280110f181c100d140c0c0040b41c400b031955040c4800c01c00054481e6003c5003654100b00590503201004841d08000080d0507000b880d11180d55111001c1004030816800c19611043c42440c24848002040250f0040c000451103050000c43e4550160f10400041f2140c02d00444a103460030100d691240307003080450b04807134104070141c00701c2c3d007860340043c10408411a04a01100c1030149a115464503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 530109721 1250 530108471 530108497
    0x150506100c05060c0d02040b071406060f06091207080d0e0915100e04060f0f150c1e02030a080a1d01030c121e0606121b0e04090501060515 61
    0x248045480980d2092805403010b040b035000140000d514440c000b000f40b10b5041c3c210001881c280d03070b550b03240c0c13910340000c5400c507805649500c4514612108010450b00b10760f0484e503400b403000d40c20001038040c1c810060306c640030b03003c4c21220fa0307004001444510000e0244509841c801304083d40010055104601924401c602890109824102d80b0420400d001e0014220b880000e801d10010b03242d05034003d069580c050780f03034030000c500010120707104c800a0000000010505081c03039001c240c4078040b00311601c20082c50b1680c2c040440c4034a02513081c101c4690b60000780290a03030001c03e0411006070800307040208002504885160311041840c3c1c86d00303451000108140f4030304011010303030762400d06100005510084c400b105610a030300c4600e1660070041f00d000001c0b5034030640b209a44080d4008008255440d069807504604c40c01586440c3c038031810700001c007110a103800381901d055212a107010704d5031203030300724100710003584880041e103001040d401800c1c10021000c90160b10440301a9a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 530110971 1250 530109721 530109739
    0x6040b0928020607020316060c030212031b030702012a0e010815040e0c03060703020c060a0b01090317091305180102040f1505041707141206041e150506 67
    0x24180403507040a400754841d0034981815070181c0070030000750440c540036645030107403004c541c1401900510050080016844440a0103050b003006420418416030b0108c1d00d40c3c082003005601d420000440f003d00e0120b10000c0e48030b840c2c842040b401040c100303c0483c9241920f5410584102c103004d10840d1050043c0d65030413000c21210011101c1c0b940075942e4010882400841c854a132406800007110701c25107104941c5a1400c03000004d1902030141c81840109500154404180401b1f0000b00e40c0013441403c1406000307035041c0000c0008640d40301c043e013a800c2c1800c0b6400701c1181c480840d2960310004089007001001e581c4103000802c8259459040c400c2c0c0c0710409151280c0c10f00a403000c5504402150306810f01d0040d0300c6200300c1c4054104820440c1c20000411801f10508054074a0f0303400400400b011070500c0a405051140c0e00900ca200310b4003102303201100500000c0c2d07564050b07805080c840304041e200072900f01c0220030000062030801128060103414441c4c0d405030344a407808581071a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 530112221 1250 530110971 530110993
    0xc0d0206030424060f09140606340b010506040806070509122506030b0a090c020c0307060816140d0903050d09050105041b050915010e150a030c090501021b0307050306040b09 76
    0x1044400048188548404000c0015010728149c0d0151800d210320007080700c4600081c1420b1000e90400b02c01155941c0c0348442c100b003d00540c00f0500d805040256032151800341042d500c1070342c1c1d10b4020001c40c03c000d000640e0950b95126281548003403c00742d0215500310380c2c00c1403c0e40c042d0000c40721100703028030a520001030b4940300b401100102c4001034000f4060b0303800c0030429809040e00600b0602503100745071aa514684040141d00010112661044071504040603032400790139542c4808020004030348d800ba040310040c1e404903000e515105038001214200741c030b000e8405001d0500f000c2c0109240c5840d200a0200642203203108a1082e81404400c2010700094030300100d9038052641c00c0506a400100006800d010001041005041407890040d00ba40011842281458600700d180b1010544504241c3c150040b00b07007056070f074103180303100358203083c0009d645240003890600444e000e04003c852640b0300380010405080090f003030b505285400c2c2008101d8020681c0c0c5201c5a111b101d81c802c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 530113471 1250 530112221 530112239
    0x3040f090606080f3c0f072109020409020a170c040207020f01030c12060801020405030f010e030a14040f030309081506030c010c0f12020303011e0311010804050f0607030f0b01020c0d0206030424060f 87
    0xe4401c08c94680128151003010180b402820107140c22a0040c1d030301c0f061140585d845400c2000141540081e801e40b03001c0c4080c06c40d0030250b0082140d8002c5005020311401640c44d5100071060700001e00c2e000440020507203048400c0341079004000c490384d14096010842c940c041d001002900c1d02601100c00751122000ba0f00d08a516008800700142c10038042482c0a522940780c4102c11501c500c0c4140c20551540b00c410300c403d080d42c0c130480110b91076040c10801220180a030300c0307064060f0543e0319071070324004011039201e048220506042003866508135041201c58442005040c1c0c1220107903116038102c2002940e00d5000380203401000070590391a2400807400101c100a6a500080301c00f440d800b4540107440c0c604016004942e0340c020071100c43d529001c20803e96200d41c1e180d40e030200c0e01858506038602123034620080e032411508281c0c9250440c2d1034010065610a80c152800d03607407079450707080004190a4138401c03688142401040d0000d070003030742d8210100f9562401000889140e84080b98 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 530114721 1250 530113471 530113487
    0x141602070605090307092d050a0f140415020c151b03160315050301090c0302090c04030203060112051c05070b161d01050c03040f090606080f3c0f07 65
    0x10981c10b521440051054420f207410030320203460326940700000d50144d802d00702e9101408000301c00150323642e081040303030f45509406011014400312208001c0e0f40143c485030654500010406003540c40c101800341100c640faa8100e800424114007602c45407110503a18640000080e90195282c44110320380b9800c0b0708034002101d01a40040c24500c18552440170268003404c0c462410060350b0380310300f10019540c0c80a0041d80e20307441c400d813040b24031365041d8810404900400f8245101c1e441c03090205000680380007400380d040d1416031410400030707002890030782e14042c544111504000d001250340b6075a26040809041418801c428220709a92204041c01c2c08414079070b19280001d2178100c64800030301c800454408580c00600d040f0b0301d400fa5070031071646035500c507a0110318500e0900c803040094680500c82c40d409807906240440707481c20b02903201180450041d1140fa1000610801c00070007400100140409042c4550038207058010212407030b80d03508048480055001c03900c00001e04080c403d01032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 530115971 1250 530114721 530114737
    0x10b10030c050403120e0406180f020c030d020d02040306060609060e010201022a1006261b061b01110d0c0206010503070909050c060d0b01090906030206040506030901141602070605 79
    0x1800303040030700d151a4414440c40d072190700400c1c003400c81403c01c459141c90048202501c01c642514000a25079003274641100d80aa44070103c20707105000b001d8002d4404000c07190181d111001c09a140c003c13442180f4004e10071540002d200c50b2405000003005c2da00074007040101c42084d111f0700c80c2d401e07121006a01740d100b1a185c01241c0c0090b5000420a540029848031a155400c02183c0c07500b44041d0803041210180d401586450760f04101c1c118980d1317010b6902c075140529041c042d2a4040080c0c001c000c001d80c00c00c00051007144081409402c05800320710302400d45080000900c072048441c0340051042c0d000b00d0901c0780c007a0500390104540c500015129048a0010f40100070443c80c0440b407100401042c0c00454440c040c2c02000e00c031a07034452000d002035081c4d000b00000c0001900c0d0014140110740c1e13101c20b002ea4100b080030400350f964541030b101100e00541e604c555036a20040074900401d400c0002c100c0104d4904144a4095100048448580307c01d400b1510050744078502139070980280c0c5a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 530117221 1250 530115971 530115977
    0xd0212070f02091509180f0102040f05090615040f0608130c0314030d0e030406260a02070602160605040c0906230307030c1d13031704170c010b10030c 66
    0x70110006050054603960300501c15107441c0c415196850000340140f1007601c003c03540302d900710100400400701b0311000c036031840320348000c40c549407404401e620341c400c80744101440341041c85c000601d10b449403096450420700c00540c140c1c0d503d07144c0800e496010110b00450000603001d000064805491b4605114010b42002140e155a440c60342c9020100c014000544440c4c001030000b8819410280200510102d4450245855a0500070000d0a0f031000d0080d400c0e1203100140e00d5030740301032081c600d9a000304040ba801f580d5080c0c01e080441c064860001c1c0c1404400020240340144030b510307800140624401e0000110003503170780309070b101612000d01801c8404000b00641080c08152964941c1d00c0e2000a000e0b41c5500d82e99449460440c191580303e918400d05100a510200c0c1c090031426510281d0464200f034859010380340141000130305451500074043d100089402c1c01a004410f42340092400282035a4040b0640154040c1082618150144011511040d5128040c0c05403100701b1020303036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 530118471 1250 530117221 530117243
    0x170705070f0209100807060504030b091c0e01022e140c0a051b0d050c150408070818120a02042f0d0e10050906090d0909020c010605040606020d021207 66
    0x80c00f08060120054002c00480d08680c000141d4540c1c244154401000240c0380c141e1200d01d181000d000300c12004100790341e07a0b00803260009021a80c61011100c0b40c00c0d610340ba8000c4018140181d15001241e0030780e02c042d107105541c80e4140311158041c001c054030003500500114000502249814805548141c15110705000820340c00348104080c06040c051200c0c0283c0c101c9403210614107124414052038006030b800034900e1a400c1c802c01402c0c0034490f1019036201d07545080d03190320407540544a8003c4c100030b000548054900030714480c10f0b50750240100218a0641f0400d54503031760309410079040f0700a600b820322560340c031101c52001d602803946026980340e00c5413650740030300301903840030b40507003805503503140f00b01600c0c8020008030092650300d000003c0c1505040104a20b0310344002e01c094855406080f00104042e4445005000c580d6604005600c0e2084501041d0240117190445904144ac5c070200280c0c56600240c1c603849404203400b6243c0101600d400310038a480342c0e0001604410101c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 530119721 1250 530118471 530118473
    0x50a14012910092402010b09041a0907060503011401031b0f020d021501090c1101051906080309030a0b0601170a0203010e010e010f03120302072405060102030a0801030f140d170705070f 81
    0x10110f079130b0007880d10001558a5000d030000e00302d03a60946059856116000441d01d0800100b401690480c0c00200103121492404100620610050090340c0302e802c03100410101a90003504405200c0300400600d403004121540c1c01880c0d0a45451414014450014024103050002c100c0080c8849034011103081750f82031425410140201807600020084c4c45049646000b2080c0b24240c000c134070590b114070000221400c2c240a684c0340b50048921500108080a8550b03000182162401da00c424154029500e860050b030340c400f440b00c85160004890703420481c507c0110b03402035041e0f40e00007807018904e0762110700d45044510309004491703942c10300355030520102c0c0403518910007020480c64054a030440d80d80d0b805203104c1031300e0202003071042c104105e820040c43c180a00c552006081c401507092450a40000744440c0040c0b202501e20b42c07510200c1e40600080715003a00740c00c41c0d014101d560141020000800307034200003c10580c500403c0e80442e00c8144a00c00b192040d0f03422815603852a006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 530120971 1250 530119721 530119769
    0x27030f030902060a17160e2107060302070210110d03050402031c0e040f0b030316060b1003020903060c090f040209030a1416061b0605090a0c0b0c010b040504050a1401291009 76
    0x186540441c5e00c0c110792303d075040d0320b04da0400001c40540364030b0740c003d81c9801540c4144038442e81c00700380220910040644500d05030f8400200b01511181078030b4041016221800030038180010101c89800500b01c01c001516041e402c031500b15400081a01c0401c0341c5500054520101c49249140a0b410f80003000b42e26001030f01d91488134402400350400250041c01c01e00000c419160303030980d40700800d4020071800300c0e9142c1403100c164024050411540340007004400200352403180408035101d6940417412080a4500b0801c4200e80d5601114402d0604d00c1400d03210f40d90540c1c185458080f01d414100800d00380d00c1103401102400e034549036040c140351107a49000141c500140750f050248076020702c1c03001256a80c5036403801401128004d40e0384243c5040c10500f91000185483c0c0268185010700c030004000090b00f4442c075800000d2a0652007068600d14094074054030b42c0030403028440382d0310126010140c0d2000480408071502d200740c1101d1001900c212120740303d141e503012580c0d4540491080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 530122221 1250 530120971 530120989
    0x30102090904030c0302240403031d0706050703140d060509070509130221070f0201060e19090510050f0106030e0d020714011115090127030f030902060a17160e 70
    0x3c17090041e01d01681d002010003551000b44018458025280e0052000740340d0103108040c0743d5070307001f88895402015107078855500c90b402d11461007004000541c2e4810b0500c288140b4100040e21107210f0742e0764501c000d00f0005080701d401100d104807514000714650702c9c0030350106e801c0f260001d080c03c0250303480c003602072000b900200c0c076550f203c0203295010a800541d0030449407043d01e894940c16050915032a00900315411900308205601c0f080041c0542502151040c000030740721014082040070092602d142402d01251a40b4001800e107000d0060b854900d007540c0d410f81da0166010020380d5980420300b070f07848400043c2c82001d41c004d590103000b440049840310304c10000604050700088c0700c1d01100da25040030802d5107018182044180f20100d4000c0c001c1e02c1c01c00714180402d80c4070140340d681c14030f4207065000c801014443d10403a402c1400e40650086102150020b20980d01d03042c0418015101c00d5504c48920907845189000913400410844020765030405980c03840e41d006100b03000c0c003015403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 530123471 1250 530122221 530122223
    0x8010303030515122b021c020c030307030c0203010b010318060903090503030721090b031f0f080a02030706090b12090a080c15310201090302060a0f080105030102090904030c 76
    0xc040803c0c2202141c591818a12585100d0310007882d00c068650282415000007800c0010000c0685e03c1c4c80880301d40c0084c0c1102c26000c040070341403d41c19804030503842e080d0501b0f4815010b0101061038003e1580150700d0084482c025402889461040c40044088960300c190a0754082507414142e070100e05140c5c02103481a104e424680c401c25102e03400a0300e0358000410440c1d1807007901e240721042460390740f00c0e00654501401c1a0701c0c2542003001064003408010403211511003001d01002c90080011a500d00403c0c00b00000450591140805c5494581c940c1c400d07130080c881c0302c0000904ca0311450101c07041310441007946040c80521000301106520150140c803081c411282c0c40c002180320240200014400380d8010b03c15244c68a0381c54020388002054180725460700090b09440c1c0d0500340302c00d80144202c0341f04021002c0d00e4401602d100c201500003a400a40200720b140c0503a41007143c421a1410588401c600340c0e81c0c400030035080c0c0c41065402604544000089030001c0d0090050030211 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 530124721 1250 530123471 530123491
    0x6090103150906181a060906092d01080c01090f05010309020d150524060d11070c0603020a090f080703030f0903050d020105011805160f030207080c21030106080103030305 75
    0x1d40d149440341401d42d000b00349203803104009919138074104440c1030442e10114800035400d0f0828903101d400600b008170000c0c1034600a05500c000184405502030303036514880d04800300b040d4112152400e01ca410700e800d0040014510070340810644a600400d1250708032001c91940c0b9200c2414207004401404040404a0300006803c50010004030a402031584404000600043c68034204406200b40c0030340104042c0703400c2c02c40e03940b224580c0300c200c2191021044e14101161440e100b1100e0496031040c90405804e0455180c808140c099060f00280410350a03540e804801c3d43c0c543c0f480d148108501d12030743e2081d44c4003e4007000000e008400552804146050862029540c1c5d12080c0c24011304204900050355108014886807003800541036509109244c10400351a00540e602c0041190302d00c05401d114006001e070382003901c640c0403552620344c05003140b5241d449805c0c284c0e964030100000300c0d050b40b07811078a00d103c003485403003600d0480d00260703034000d6507074a503440a800818026164180f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 530125971 1250 530124721 530124731
    0x60c01020c0303090a030206061e0f0d150507201c031806060303091a03070e03030903150610020a03080c0a03110f0318010510060806030c0a06051b03030609010315 72
    0x2801010b0025601c1601c8150160071101810301c2e0003424564002c00d90341c420382070101804d540002d565900100c0d08070030740312401c260340c2240000d411180d542100a0406000700d4103a80c14078459004580180b855444040380d142c134254106149010f801d00e00f5400d50b10a10300a5040003028907031085031545070400040300340c840019241d00410905098402a454400030030402d03034011103500013400b480d0503807418072a81e01820f060074440038001d030b41000f400480107001584c092040b1080500c00404450441c2c0310b118054500d5601200e54520400184006207800e0307001207195141c1d694542d5030035902e1303540c40c11601d0b032a03004002200105980c2d0403800c000120b1490082c00d03080c081c2d0002c580c40745061081074901d131080b801d03000702d147d06201c240482c584981c960742058404038104110280d44460200b80751031800a15a94410a80b02000442641010042ca00c9520400304a0043e40ca030505103641ca210039905250440e50340d000410100340b003461460222240c01c00c000c16 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 530127221 1250 530125971 530125987
    0x501050a180302061615020a171009151a030c090108100f170d0e0109050d110301140106020f0c0a050d050a05150106021504120e06070609080307030b1e060c0102 71
    0x9240d420070802d91416034811170130101488005032418040b84144d03d002d515110500400505018880420f6803000c1c030b00d84003140c06480c0074038424020780300f600000c02c03403400300078100340802032a1302c6088126a0007902c1380c07070241964022644100b010a2280c3d00c1c10903a040111203030500100b00b000ba035005028003041865000c2c1002000f0b0404001703911880407150308550401000900314000e00501c6c0c41320100c82e90b045100308045440c12240442d5500c40d5003005100591a001c000764903501e030211840d50f4428044130310b8103072286039003103c100c501030300002940e44c129003400076480b0118040c06c02c99840c0103031541200714401c00aa17440a0030035682da41c0b4188030000c28402b1000c40c50010320031280d042113005220410001030003090705242d103618411a14100000041000c545d481c0d46841e11003000700e500e00c5a1018003002a0410ba003048480742e04140c4000c40000e083c041d10700c00030714105241001c120307451018001c0020104040000a5104e019010595502400000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 530128471 1250 530127221 530127229
    0x50906181b0309010b0418050604081803070e070806090c0702040c12020d060302010f090609120311070306050105090c03061003051546090b011b2a0501050a180302 72
    0x16014100310f000100d4041005030400c42030b900f001c080c400341110910800300c042000012a00c1e0401d811000503656102c02e01003c001101ca1002c41940602c00c01034006a242562104070703110307140540d0340032940d403218000c02000c41025224a00b84406c1480a00003610b0154492000354201e800c14215100303880c062141685c002d1320258468540d0b4103010425541c00030360324202100c4629266450f10b00708003010b0115465401100c21007000c1c2c050030020180151140c5091000d01d41c00c80348119135916189020300424090940a1030b50740c1c0102d01074080b040d00741e03400f54400403d03604503480c141034200c0c01480000c1801a43c803074030405403141c03070305d88040c141142803014656480313050411103075002c40c204401280360700e0800c2071800d500886d4a0500003080e6164214042000d580e01d0004888211440c528684007014001081c001c104042011600b450600710042c03100d11032184038900404444d128007800b00340c0070005c20051a201d10301d0054004d030b56100b9218070035201c1e0045 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 530129721 1250 530128471 530128477
    0x12071203020d052a030c07140309040510090b060a05092205070221070b190204080d1d0a05010f2709090b01170709050c0d05070513050906181b 63
    0xb4182c24604d4000002c410301d01d803242e021030242131040b0b85981892140c00c505489000c102905030208446014542c8505100704c80900000400134856030030b00383c0003410040b8280c132603c05150b15080c0b11552508000084c1d8141d40440d448150821143c0014000e00c004000c0c0c1c0103141d40b40000c40140c0341c902c1e6101e501d0107102658002e20885038003159880d217100c100c80321030070000c40920030400002c06070700c540c0c0d070320407a030001602d02c51240680e0340010380900d400c048464081c035401e03a018668801f418400b030070341d2030039054800b281c044244809103126002e05170000c0c80b80e080e80b549090055002251107070701091805c10213000c981e1081207440881d0025040c55444103603035010701030f0030341589015084000000e041180580015581c6950511550142079190300001740e101c00070380240e40c0c1c4055030003402d12480c94011001445680640440000e11724100400301d040e09168078458031504001d8021440040010b8a40350700c0036000300100b002400d01500d541e00c40690f0405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 530130971 1250 530129721 530129731
    0x221514092103130e090a02060a11030c1c080702060a0515060705010b040608060127090b181e030421020d031809021804090303330812071203020d05 65
    0x91522120710f07030481c0301903101a0744000e1182c42a5424804080340104400120940c12500c40d5035658150505807000c04060b0b038004420701002c640c030209038101040c0407030504030914050552482104098501c410140d40d5800140d10030400681e5070b480646c41990011036041e05810a103039248002007031580001c508403820b9440d495103086500307050103088003a00c030210141800b581420304002c0d001600e404100c00680e0a412040040c6801d039010f0094190000080381e024a0074120b004201a600d2140c540c040c454200382c1c0d2100f030b81488400c5035803030500014500d02440c2a42440300b00400d5a00b211000c00704006240c01a61141c00c0103011074426212010311000c04030603418110006c2d0711140071240100a07614000b601c8455000140b0811900000c01d0320407412700302c00904866145404c029071080405140c9106801d0a014504102820012030368641c800c1503162494150720104d111401c3c0440c00010b62170441906103901c0e030307240c0103082003a1020180103030ba000b41d41c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 530132221 1250 530130971 530130973
    0x1140d05060f130e01050a0e03182b030e03033a1409120a0905041806231b040510052505010c02060106080c09060409022215140921 58
    0xc0300000d1101b0300965a00800510080010440020303116480e0700c5440e84080031040c1c0440c0404444e030361a40090200103222200002205020140c10741f00b40f0145400d42c040f41e00802100701600c0c00108846000d00f4004c1d501703685004116000301c88071902c81d002d000e119200f4141c8112040144122401d01e441c1c810808540d0408582641c00c080e204e4058880d0908200b25050310071f500044a00304403030b01503600040003104c4031070300d01e4132a41c114401440641001c902400483e81030440510f4050720880c0e40c01030ba00c5010045c1c202c150102d100c80034506090004014600e4a100200d007070014a052080c50405100c08241d1400c204100f406100c0700742e1102c4006001c024401d1803000c0e04680000d080a505101e00503258040083c1164081c6400081d001020340303860b829038004043d044425500c40203402d020724800c0d58000760350403001c0400c080c001440707c240c02c481304c8001c0403503c50103803024444102144c0b582c0303e01c10064014110302100d01120780d01803012260715880700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 530133471 1250 530132221 530132231
    0x40c1103070f021f0e010807030905060c03180604020d02011809061203080f0709170a02030a080717031302040c0e12101b02120a090506210601140d05060f13 69
    0x303c104108481000c880e04003007075180e10a443c486030003000300c022030142405c1c036160560b9040360407005410000e00090481c041c030800d001d08048450080e5004900d50325806c41c1d564481c41042e552041c08981c041d52022107009150003550140200121203810000c040c0c3d0307490f031110f004c50155072155104154034102824030b403007855489218079400c09940000020541400503004000b10301900442090000314400c1c090010801c00ca52070b245a03025081d030f98034a14904101031a500400d0040d0740302401c3d24030542c50040180110f03840780005c182006441d0000e6000d000042940c082c040092000403000b0075019510380010503034041b000740c02400c503607c00d10003040a80d80380003c424104804003030010b80140d008180700c3d110400321202a43ca541201204843c0c1040ca9446160084c2000030340d000040c032a5266800d2600380f0340880c2c1420f0315480c0c0115046040421015902c003018020039200c100710350005134100c0700040c119221004404005907440580301920300d00a940d807 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 530134721 1250 530133471 530133473
    0x6150f0519080615130c0206060310150311031002070b06040b040c051b10020403080c0105010f0b07080c0708030d0b090919121e030504050118020609040c1103070f 72
    0x103041540c81c80c409010074641d22480c1c036070541d50b41c83d000382c840070340550100103854481c0c40e000780030b00200c0c070242e1040c86000b0f03541101079182c41d01034409900a0143d11203001480003180260059414400c4265014030718688030340c40040c00e001d600070b03414050340c5079a40c0317a110540040c0203103c0c01222114004e00f868400c00044914880c0c11500079402c0050405550b500710703042e0b4100326042c42c9120100d171030600803542480403d15590031100c0c80480d000c8103000c14032000d841586d100304003c104d147d807109101b100c1c80740c1901c5107030b07070009003008004002503010000c1d2054035009400c84940350b4440400300c2c150741001408508403279440a21140c903281c8400e200d60001e0705c00e400380640980c1c2d0015101900440c21004e0720400040c2c40e0044903d10948511400003078a2880b0f00b00c0007003001006014180c1903805498640c24a60201d05101c02107130013002c1035a000344030700d2400125070140009400d03483e60860030302c21a54003044152500b1b200421409209185400c02d10fa01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 530135971 1250 530134721 530134729
    0x5150106121407020d0c1511030108060c030c0f0a030e0d08330603061203030a02040f0e1509060a120f03020d05030f060f0a27050a0e1906150f05 64
    0x45442e9688030b1421240038040b010f034001c0f441200ca08100c3c940400d040c0030500b4048120054810340403449031a09001110314403118000c1c50507110300c0419900180c0300c544031143c0c14001652240c222b29002c0000c002000c2c0424000e0540d48140c0c00c010ac3d01c0d0050390007185c100721840c2e0311000420b1202c2c2c20024428500300c00b078140005221300e07074007040c182040742d0303e019914402a280100070000101e429940c44108203c00081c004c07040340e0380c914040307034524040e40051003203d036100620342d008941000811a8148141c3c0fa00100100c81c0d10840100f04041802402c0c940d000011880085846408840c0203071a80b4011034501000048519009283c030f41004107034401c1190500500c2031400388041100c0e0842000c40301d1550140481e07000800c0d440659118054030700040070083c0b42c412561354014098a9101001c02551340d5006a8030140c44c0141038600c8240c01c1203500301c00003121350002294003130140400040d040000c54642c6501d50454002d100928402d410810080c58 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 530137221 1250 530135971 530135981
    0x21030e06311113060f0803122203080a0f091a150108012310021c0f02070303110705031609110f0901030b041113080c040e030a0c0515010612 62
    0x40307500c044a2041000e81c07240d480310310103070107901d01c2440c80c0c0004400c44011900030700058890f1121040510380d5401c0c0180d501c0e070200100d091210581d01c0000d5600300d442c0f4120034091380654001800d107419603030448070b601000300500c003d11781c1c03112100c1c5a1081846030039803981c8106c02d0091f010f003694030110145100103212032201052101e101c0382c0c1c1d0b64080900350460301e000324400344940b02c841140c081c1500c1c0c001601c2c2c000305a21039044001c0d600007414034801c106c2c82d02c404100d0400f078204a51280c038204104016030f114500400009200304046002803202d90b042e504c1e4180ca41000030b0030701e00c0c901c0d881840003004901c10b00c41800c96100b098161441c1d007100e540303440d110590f00e03800f5000e084a2141419680d0382e0072583c0d5256a04a204200d034410380180e500e443c105010a881000c9000c0d80040b031281e000078100e542002d10440c886501850021810511815030494800f15a900211114010030800e4103c5000c4a0a180e018103100c0d12940803011048180c8800ca030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 530138471 1250 530137221 530137291
    0x120a02060c09010e130204031b0e100e070e03150c0c0613170a26010f06051624090302031b0a02100e011103030c0316020a21030e06 58
    0x34008114120b12aa04018115068541681c58401081d02c04210000901941d4405480e50300704813070001e104454041c0200503900c6410401d152600e6907280034080b01c00c039000308465401207402142000b030061980b01c0800a009044a404000c0840d51050412060f10101c004035004110000039171010301080e0341c412200c01c0d01d04620310b07030390316246500b06640a140c0c1e40c01d000000d0305a0411b01c507003120340c02901001a007484003181c1082c07a0f02c40c20340c24070508180400900d00810000d01c98021100742c8000110310580104103a2075541032406c4003407441a003100c920225480c0c19009004006c00540a13402550310381010402c00b50b2180105003c01003960400380c100320042c1e4900040040c0000301e85080c51b1944211401a1a02036000a660600c0c1c4408802c03c0440200381300214031910528070104c21b00c0b07145c5c1605076950404d101e0b00500001c00c00d600168500411000c26a1000991070003280703110a4540c2c02d81082c1d01a98003138400c40d0001c0000089241c0401800c03001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 530139721 1250 530138471 530138491
    0x60c15160f050f12090703030f03090803060f04090b0a050403030c08070c060b03010608030f03060a3f060504050606011403150607020a0306060e010303141c0b030708120a0206 77
    0x5025010340052030384140861180500401180310107501590a00f5900408004108840c150502088241e40e6181601c82140014840490420540d10074019011010f60118801d42103444040c20407140c1c1c1040e1201e1900b00c7ea03900322080209a0301e11080340901d060030000501c5081c40e04009042c2c072911400e14051149800c180510158407a0b003002e03d03550000300016841d042d050019025100783d41c400c2c00c0c988000b05500d89055000c1000311301881c0200c0d40b40781915541c4011000009000b811345555580b0b04450001045600380d403000c40310714010903440f010910756511001c81d001942c058a4660004007000f11958020654007402e40c00f407a0128110710f843d2540f000200c154540d01c6000f04c1010401100b15290708410300041e41d8000c41c2440465110b82c022074141500b44001e6000844200c2300c44900408041180d00c11000100200242039020200402804401004c03e4051003484800985580c5c188812000b8105940649035140340380750009180c0030300a0015407203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 530140971 1250 530139721 530139751
    0x21141006030513061a030303010906090b0904050d0f050f03040b07110a0b1f030506041b060c050c0d1a0f2d160903080c0a030311120403051602060c15 66
    0x4110b640502035580d01c4e40c40400441d410104511500700a50521000354040c840030001255500c5181c02030419201d6021003000b140d5024010017400900035100902aa0444855028400c1c4600300c489842c1c0101d082403440c042c0c600043d02c0326a48102da069602c00e030040c0910038030541c00442d0800340c400c0c5400030703c840c00d01c5884028845001803d0421061030346152164420076440f008402143c0180549880e0324041c1003020700b00010341980c42541c0c4014001103072990080041440d0315030040010400301000f8820720a040a036510305548010131080b560044901d0745d0030b207600c54030304c00c2da580749035040c42650440e04801040c0120aa400208031901201100c204015808070208110304088140060261000d8449403c05001c1c00c000080005203001c0014100484a00c42d80c2d00300140418000b0800141c058030400c241441b40300f40100d404030b03200e8400307020100420281c407103441c0720304d6000941581c41880000c1c80723600060b03a00c240b10450070350410781c0003000d1a00610 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 530142221 1250 530140971 530140981
    0x90f122514121f063b15040e03090f030a1709060d020a030f18050604110103020f0c010b010210050f070807030608030c0705041a03120a05210609090304060f211410060305 75
    0x4005c0d0041481c0300c2804504c8006074074410900c5654000d100003510410200f81c1e034280450312640400c140f18061100308000c0700450400050200701c1a410502d60308222800f6503420469521055515500c581c060059442c1520507200400400032147c80008245402c641c810081e14004038403c80c0450b2500e0303030b8030041180410002d902070ba20546c40303500c5050080050b03009009100c105800d180f00400c41c503009450550145c05080380980031201c1380a04074603140b0640f00201c0b0071000219680012900541c06450555000401404c01161150303ea81d840342c035642004090640540c003c2004100300c0c00c0903c0b0700032032000241541800c8012460210795201d0b00070b81004401c00d0300058074001c07140328501381c0d016101e03e03a180d11081c001486002c04d41e454240d551a10414549000c500d4460001044408613111a2a401e0300090101c000fa2102d661440414820796500321840356220014030035418107804041c0410402d040c03c9810020458090308804103051800080c04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 530143471 1250 530142221 530142299
    0x60906010f0603050405010f0203100905090d0518030a32010e03040e100504150806060f150a03020c120c0d02061506090f122514121f06 60
    0x207401c0e034003181004122500c0d98a42140105200c6a00c1030b803846c030200c05e022001c0c0300c80b80180119a403583c818003294507208000b03601c401100e95840c004c603904209000e1892490b03009061080d1009007595501003d6458000080e03084080d86c010080c40d071003540c42c480714080030701814843c0301402005082d0501d03500070754900c02c1e4050240d85042c4103000070703004400e9124403005072802510611440380808800144014503008203000c80c0200d000041c8141005d84200314030341402014000c03400303480105003c05500103010360080503000c129070a2801c078104144003141c107540c0c01a5aa85501c0b01115007000b5544080d070342150440810310a00802c02070f101e01c50312004841c8036580d9800e100019070303020086201d1641083e0b00044024030aa07001c030b40c420002c0e01201101d00c4c2501e20020040c01004030f03008100320a00121000d074042c2c200b25081803038180d030741c0d0225900d4003500e92480b14480c00c001078003500652920700034440024030103207000401e06003402e560140074a1242203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 530144721 1250 530143471 530143499
    0x90b0d0204110919030b0127021602010906030504020906040507050f1b0d02030708030c0d020403060c02060121031202090303040e0412180e18030904111e03010b07060e01091e030206090601 83
    0x2e801d0502d074480a00a1518100d490808d90010000841d80e409403070301802a49101c2840c00c0c0d0104a42c0d01002a400d406405480d109580c0244014a19522401000020003019103601c0c1080000e0003020000e00109000744407500f45e982c0400c0ca548074128810707141c5280b19007128110b4005100780030004254805403074200032540605501c0c1d403180103940c1e000340101e901c0a4007550429607a440c005401150a0b4140d4130360107140c00340420304442a4629050000004000483c0d804038081d4040340c0364098000c04800605a03454a691040d085a4108096400b80c40a045080040104030b8001084c920481e0182180014182c501905007142100c0100500b41d180c440c122416602c28041c401c40c1c030700c030100030400c11094034148003201150300003440306141c1d490030001c812940d181c00c030246d904031a8969451072078003800d56a413030080d02d20b000256105640b51496400068803081044480c14001401100c0800306418003e1038054090b00740040f42d0021001440105102c05403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 530145971 1250 530144721 530144729
    0x3010326030117120403030519020d09030201030207080409050108060a0e010912050915030109090201110304080d051c05010b030712051611030c03040f050a0b13090b0d0204110919030b01 82
    0x4000c02003c1c503100000d09104a4428440b66550006808000c06070080040e00c9180035034030a4006a00b424a0b0a9a90b06201200c0d000481e41290b0104010361107900105a0381d44108406030800e03a4916120081c2c84003070b001390140750002c03000c02841012034403501e9142d20f084002480201e1789030711520300d00600440009c04100001a0000780e0341c5603501c5c0c83d801102004c42d5580d8079079641a032000100300ca95001ca001401000c200c42c98940004140d80c282c58800b07018200c004000304041d1204c1d8440c000e0190a00038640c84001d11603501e1240500a18020a00c41d5891030030341d02c0140b03034004502a000a9130310348814002d01018162000740c5030075407410325105c600100e00115145000e4600103250902c000100403410002e81c0d03d90034100c440030b4400c0e0720310544450f4400c10b50b02a500d01440b200c41c520008120280c8184c01000d0000c9010309504400c024a4000c1429600d45003c0402c40480002c0c124405041c86a244a000141044544100b50440d51150b0031108103101e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 530147221 1250 530145971 530145989
    0x106022104140301142e0b030112051009030302120c0c060103060b010c050a0510110a0e0409030903020301140108101802040b0316030b0a060b03040218042402030103260301 76
    0x4640859107003540945e400071210f4880a10b035150a40c06110719018200540c21b00403070b16100b0040c8140000c0303c4000b40c4000f86195800c42c0e0030148000f181c1310380c20340103803207a10800700c04545102042c03059841c1180246d80260781d9044007001c40c45007007009000310710590000c1102030450700c40070071100c0c1500d80c000d0002c2101481e81d40101c03060840360101070a50300900500b00204980014091890200d4100c10f2144000301c11102d200c0d0301420388084c000c5050201a8101d07840c0c942d0142d1915840f90818240c3e098580d000300782100c0381100380d5000007850400502c5205000c1000d01b8030030900f140140300c0d046030001505140e20040074000d00540d1601e400c0314140e03800740514081c00044a440c2e01e5019542e0078410004101540e6035041149098400300d64488000c3c110380c42190080e0001d45030741c8010240410700b43d0b00400c2512035a00c5102104860521000041080ca004000c090386030b5065043ca02010200b075465038106d403528a010994002c18182030380d046809040b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 530148471 1250 530147221 530147249
    0x603010803031b09010f1d031002041701050f130f060e01020a121808030c1608131a03010b0a140310084602030a0c060314060604090b04021309050106022104 69
    0x800c1000c0706007c040403d5040c05001e142c18115827569000c0c3c001c544000b07814020303442030740c86404e00320342c82039a0741c510250507500058010554441d90440a86c85000712244401c110f4031001c0450b103185c40c00014594001882502c0c0690040315490244440d140400c8903448400000303280c0610510b004203000001300000760340042c03440945990390328250944000ca4401c1c070b4160503d0f80400a0084d40d401180e43c04564013210320342c0720703503450041c580c2c0910356428145040f034260040301c804010010f030400260100c00c0300e08040d60080c241c02c603c0300d4000341800e20103420b107000d840350100400c07003480ca40d209000d03403040200ac00282142c11a10313402c0a5800080c0d103038450040c003035090b02c500700c542002c00006000c200c040b10100c0d58204903140c2c001c0900030044c801600e05907032010080c4000d22800f0302aa100340003100000300011316018110031080a00d0b0348950101c050141d4440041003a00c1d01030141405402e4501141141012200c182c050540030303034021010100402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 530149721 1250 530148471 530148497
    0x10c020f04050c041706010b0703031a0d0503090406090e0c0d080412030c060b030c0112051005120102040e010803070c0303030b0a0e0a090c170604110f0603010803031b09010f 77
    0x4054104000e0103401408607151003012411954000d121340f000481d02c005200d00030b0b5101084e42e038180c480840e0789502d0076026031400c4010b401c1c4508004000818091080c882d41d0b00d40c611085140e1280d4091903d810b81001080111451580508441428101c0c1d90078241008038100100c00e40c21100d40251001908000800c0c0c0a00c0e003022034000c2354050410245078010000b501c150f440303484144000742c50481416200c40d84111800c6c0420840c1d094407581010b19000b85a00c030f014040014038480d92880010f034480e149109080c5140d5000030140030702e40c01300d140b59015003402c5008600c1c0a44c140d5406019091a2102904142d91500c8652290340c071448100010020000e041c5040e09202203284010b042082049800c0041c40400040320454100c490720741075001c1024040507525a20340d15112210089000d034002d08840c00c1c464580d4500020354040d205080085481e89411600d040d6440860728407c141da0009002e2460143e0b8440c001c00b040900e140340c000591540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 530150971 1250 530149721 530149729
    0xc090b07050f060705070c09022505012003040506010509042613030303020c0d181406040b120405010606020c09161404090b040515030a02150c1c0e1905010c02 70
    0x20600b00014140100400c0c880c0440d4020050101d05000d0803140c1e0101360303180088400c038804c00007414144a25040c8042a01041c00c03619803003540520004111800c186608600040111a80b640c0d8200080140014131104002140c00350230151000015030612b5140c0c40076130791f000481c4070000140c0c4045141e0032890101990000030b03c050360000039a40300e18008c1c000c0d400c440b4040410b03104201860308041c2c8680410000c0742d510350030f01141d076400c083c4203c1a40d40c065501541120f400c020000390386101b02c3c000c00030440c440a101a80f400e0a142c51420744641c0c4c3d0010045600c0460603e00c0d035941d01d11925013205080c0d000e03125070804604241c03580240001800c03595200441c00040310781795038122580c5100215410043c80d507c1d00f02c0e40d040040752500d410f4056102c1c00c00c3d000103041141c2c1c40b05009612401d41c5c1d0509401144103031400e9110b652502001d40e4212091440320380010380c030460050110780081e03000104460381c40c071580c01c038815a41001024400d078425515 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 530152221 1250 530150971 530150983
    0x210f1e0406020d0c050316090b0901110a0c0e1f0b1206041407030e0f0a080702040b01090f2309151504050a0b0a020c0102030712030207150216150c090b0705 69
    0x900030406002c01070400340c01174600c1d001225001031110000c9070030009548141d09650680340d8000d019802c00c0002c6004560254032841400720903c10145110040b030700044441c00100340c101c0c80305413140b500c1e0112071043e80c03c0354141c0405443d405001e010913814002034030781c0c2c02c56070f0702a11405d986500c00140500303100401c50800c10034000900c4a055419000300341d4560515084900c81c181038400c240c1e42e030101e070070041c02d4000c00303000c503070018606600b100060000524003043c081e0f85584001039003099540c4038642485a1a400c00c6200001c1d124000406804031200b41d020f1801000316511400f00c50441c4d407055407244a0078a9500f228810b45e006440080c000c3c241051310703404081c03000d9218080304005845038200f803420f5913200000721600c4681c480003c207030941e07450300160040e40202900700d40d2401d0760044445d892207248054002c02d17a8460440c8a03841d074130b0170120b0a00043e50440e815046c2000130b400c540d150064119030031260112046a5202d415041c11400c140b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 530153471 1250 530152221 530152237
    0x11030403270e0a05060907091d07210c12021602151c020702030c060f3412080c0c0309220e160504061a031b210f1e040602 54
    0x2e10710000d22410303c1c03880d4021381c072400095a480180303841e021800d54000d000341c400d214400b201340c480e405c200400420443d400c403200e828000e69481c582e0031030840001e251601001020390340c28034011040d60215814284006c441011460001d08a41100c4c0c1d0240502020780a000c1034a640b1170607810031400c0f911403807c160200c1e1803a07018004e910001c0d62015400380d02c2031065070001c11840c80c05204842a2012000d0040c5c80d20000205988041070741d494408283c480503a04903000c1c00c510500c1d140d0f01031040f580422103482d400707800380c040400a40001d090340d000740041840c698000044071151541104c000541c0c8000c80091540d0303404002894044a091115241c00c0c2e50000841c1c0c0500902d06401c454600c1e06c0d10148800c03600c0d40d12800c0380312101056501c0d80d10002c04015a0003241c1c400800ca0714000c0300c201201c45500001c10314040d001c210642040242c03182c46900d03000745914191000509100e0030690842484055403001021a03001042c200319040d070440d1000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 530154721 1250 530153471 530153489
    0x30f110102160605010e0112140a12050d0c03050610140717040503121623010e07060908120711011814040b01020a0506010b130305010203130201031103040327 70
    0x840c212070b00c1c128070b41c02040040b10103c0c01c00c000400e070130032598840b6050702c118402d803030016001e41c5c8882445100d05503204505000700d1103460003180810720040b4903044152282661100340749c091074111a952015801014a00418071080c1d40e00e131003400c003001d142450300403421661680c0700a664400c1000040c2028403040c90b0a54540e003010141c801c03500c0c201d0568040503601040c0c0ca9091103142244500390407180021000192030441d0112402c50800820050301810300010b801c4980d4060b5210300c0360311042d401c00a16501c00a048041d000c1d940103402c1182008825034239034040c4000092511207407060b10205c99104121401c4889a401c1c1c001e03035070a6036100360040121800c0740281c010360600b481c480312540001845140590700500800650380380030900f02039a00286600c402104241c0e1001020031f0b0240080c40c09540700758a0704d004030916200147c21101442034071a07a01000b8800c01001c2900001001d03000e010800c50700e80a118006015452080290848001c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 530155971 1250 530154721 530154727
    0xf06090504060605090105010206010308030103080d0e010f05040c0b0703120c0201020910031407031b080a11040617100f0e041a01080a1704080d0302070f12020f010c050307050304030f110102 84
    0x78000b803508103100310707482680c5101681e600d5a00490311000d007404082d002884c10401000006d0854008204138119060000703952002000c459003507404403820341c040c05032244241300c140515107610200030410503a0103850800180d9010303050780310202d0300c110115075900c20310305500e000303404641d180e800c000c00d81c0b4030a8280f09000303001041c42c000705a0102d4031001c00200f410b4043d201d08002050300003030155000c44c13080b17030880d408403004100c00c0304280c41d0040c0141115201c0054005000d140d1550307180100d03039606560080300010310101d41120342100401030403940d00c445000751421003484c007000780d45a0420800f4207075030072004005103140100000320b0030000700d13184008603c40c070002038081010030740c0c03407896010b075006020058100345901c5420f01e0007980241920b030700c909003100306d4003c19141d002100818404c0362001d03030040b204004c0044001c0c41904800710305801c0c903034118103145600500350b000050008090012001c030b0140240d000d0b0000c241c01004450003555 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 530157221 1250 530155971 530155973
    0x50a0803040c06020303060a03020607170c0705090603160302010815030a0809040b0d02010e0f010e1305070f020105010e16051210091404020d0816080c0a141507030f06090504 77
    0x111944100c0e0300b512415180240411201d201000702c070b002d4240200302a100270b0441e001c101c1540d02100040b01c04600e01c1c0b040b14814150798029101940041d4007406140780b0300001d110011100501c274612942004040c41d0101d000d0f070100c50144c980a2030008015540d00304110301c0540e41305a02981881481045800c0015940c001d10b1103000665041c41180a05018001350481c04103000340440e20841c282030f92800c000501500c86c03401490320061040d0200c0216865041c452a600c40060310707402004041500100b10700580e0714148000c004942c980b61555240080140550a4102107807000d425941c1c400c90aaa01030740c0c1e040304260302c2c1e0800094100f207480b03a81c40b0394141d040c10000c05104d0b142e40800030a11843e00034003c0c50008105903200f10195006078030405288518200c10800304075140041e00302c80410a0090a181c1c0c001d0400c90a244002409403056600440c0f5a00038400f025000342c1d002440703800d0102c9c500c280c00010901508440c1c00c005e5800703282000b008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 530158471 1250 530157221 530157233
    0x40801020f040609050306042a0308072a0807060302071a0a2a020c120304080d02010906050112050a0201080402040e12120106030b1c050102040e180727020d0603050a 73
    0x483d601c54580d0300443d40c0c0d41040c15201c0c8400c49014011010300c80200c03051512a048102150491504a9084903100da80d0310f900c1d84c0200d1010b4074000c03c0e0700e284111001e001750f02c01380180212140407006601e002902540c44215000d95410190041070800401c20034070452618018140300074509850f041102c00020700262401800d0000340b491100f0086001d50034441500c04554003800405508106001400d03d500d200c400301848100000180c2000500444100b2100d5a002040340c452138140001551030681041e10b5100c1d40000403800507000050000800d41d0a08000800d0b6903180000f400a1000d4049540c45004800b4000585800c1d2001040002003a441e402d40c10790325110100d04803402000581c2d041851180710880e82c3c0700800180389524440c100162401d03849410502c2d401030709603404081100715003405507100f00188814400b405ca1400c82d0b0141c00300c0b886008580702c00803145414840d600144984280c4d40607004070703000d103070010304540481c2041c0c941a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 530159721 1250 530158471 530158477
    0x22020301290a060e010e15070c06023313240f050f04020a17010e03042c0c0313020f10050702090121060c031515021605090f0c040801020f 61
    0x461080840c1c2d0008140c050148074803101d44030f0180e543c80106003a50040c01103102481d10000d100c442c1c10700181700016441d48a150250240c2d50207400100030103030592816040c600421052031514031400400a8045c0b640071307502c94080c800864002d551401d146881764040410109802c007400c90224198880b5001032064a8112070204a1a551440d01d559039600c1580c0082d40302c01c100d1000c1042400c40c0000142444581d400080d0620460010300d186520030ba000c40000300302d81e407032100688107400d02518427201420801c0c0540c900b07071100400c540301c000d0001c100f00744000e4030300044d5180d103032a410707015602511020700d4001001000c0d2aa4000c540224405e903048000442d207034400c10400c191000390103060b403901c54075980d1610050061001c00108040c0d803060a180c44042c000720600052a070007094035045a83c1100c002c0c1803503100c3c4406146240c4218040010343c544d030002551120446070820074680f2608980c4020f0711882d0302048807036001007031488104039882c000f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 530160971 1250 530159721 530159801
    0x1c03030b150f0414061201061e050304050d08070e0316031b03261908010e0a02090607110a05060a050306040501120816110d150c030522020301 63
    0x80d12500610403800d00789544146542e40c0c00d019400d01007044880751181d800c90032140010000d03070400303941c2d482e590704200c0240e0000e00040e4100850b550302c40d14901520503548a04d15183d850b6140507102c6951700c00826120404115104001422541c071409250082d4070b070040035148810010f17000041c1f103195a01007910594000321859401c0101c035900c41d01160b0380000001c407185146003161b048000002e5404118000c1080f12810343e0050015000d2110740586070f4241650404400403086803004001d11400e074810401101566182c6081c0e6030700540c480171200d26805400007117a120b41c82d80c8d20803504030901240e071001540c5c204010350b1040100b030758100203036a41d410b05018010284200984032100c100b02841e022076012441983c175500600f02d5101e10303c1100041503000c5c800e5281a59841c01810b40c8075459560341c002c44506120a140900083c20524100d15080400100c19030b984105900c018085450a41000880d0381d10304112a50745200a4010410b5041c003a02e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 530162221 1250 530160971 530160979
    0x13050a08010e060f0403050d02032707061b05070e0c030123060307052107020a03020106080c01080f0a061a09090604110d02160b07020a140606060a0302091c03030b 72
    0x10010a00040502c580000c0b0300e0180020034041d00d0300b6207401503800000e88150704019040000c0340b0754654500044d4003522074941b0a1211290140500d40002202c1c031007081d50f60848102044800e80c008110340048070440549078581c62180791103864060181c2c499080c5500c14000c201d2004107900255040361104007500c510046004080c41c0131188800b40c036503121605001255045100310082c0503509002e0305103520362240d07c40e11031402c2d00d080381d12000681c00321840b41c08250342805584028030031503004000c007100120004c0c00b0440001d055608101c07100c40000e207078494a400c517400600d2007201d116040c0c0200002d404c607660241d00b8036400f908824021034554185440707000c4a00300e003070300f00b1810b0008041d100070280d80304411205140c5001d445400c049480c600303546014120f641c0050101d1505440c025402e60352040b0b00e82d50307a4010108104840d00c0e1b01301251a91051460700681e07402d403a100041d0311405100003507041d503000e40750040800d80c25a0000340c032504112 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 530163471 1250 530162221 530162239
    0x504020907020d02060c090301020702040501030501050a0b031f180f03080103021e0901031212050f09150c03040b0406091202150901021e0a09050d0b0a140403020a1b05061305 77
    0x4074003a80c3d6035901c602d42c00e00607801070000580308150b0b070016020040b001030025203007a40d43e800003015540300b03800503039450b5590000e01030307804803521074091941019005840902842c0080e003e000910b10f2a611a0a0303d44213a0501c802201410306551a0b00050b400388111540c2001819000c0900040b4001d03910750145490244c1511b240c0c11346400004c0c201d0030242c1c01e641d120517090080c2d5030842d0500c10700e007060780c20301309440c0a0a485000100084442460403003000c2d49008460844401800080424000082c100000310b0b40e00607007107402480203440b0b5150210050034145400b404440d0200700c800c481582c0882e018890300c1c4c3e074041041c4542c03100c0c0b4100b801c03881076040e0038074080c0d80d07201c4001c0d410750607402074006041141080041282e40e40b000c03d00200c44500d0031586070300700004000d03000b0041d1040e5100070300326054010003441e1039940038ad541c09038003001820303050b6841c00c040c8940c1c180d0314549024020241c10991130f10082902800f000700d150085904c911031032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 530164721 1250 530163471 530163481
    0x1090e01231501021612230703060504051906020d05010f0f0302040f111b011b1209060902040c0e010e1f050d0b100e0405070311040605090613060305040209 69
    0xa041498440314001d16044016219000e202080c5140d01c45101e0550240c04080580044d86075505401802d90003441d890004051500032000345452031460301d1f25550320410800c1007070018112007030760350140c40010182c5450619900d021900440b0740a03480e000c000c0e0030104002303034028018090b2148030900150741c075520f00380d024003200d0003064001c00118808202510f0309401c02030340c040c4c25100006207040e01c403003038a5090f0700203220308202820114034040650303c240b14010b0305a03a00001041c1e00c409504005121a607081ca17201400da8076600ba08044c04100d0348207200c0f140d4001d00c200700c1d110f01c05001804000380303861054086038004510b03217410304080f4100c03144902ca40c0b4100e03101e180440380541e2213810801c0445000d07a55180d50132140e4907440c04a45401025031a0f05e10780d403003408100070035280010181070800d814140440848030b50f580a94090303615604045840b00810302c0444c803140130782c02d16110751400740f420004200b50541d01c0780f03002e64001c0d176441000d0795078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 530165971 1250 530164721 530164751
    0x9020a020d0c0f0c06170f0c18010302120c0307021b0a120809030628060b0a05032e0e010501020f0d11101407020c01020d0503010302010305070c0b16080702160b180901090e01 77
    0x225911500e08d14100724440c0c0f1030002c0121158844014140181440301f07c0d202c0c650650300403141d480b0340c0c1e000081400030007034040168107c003000c0580e00012403131910000c100f10203c1807180c61828540001060204205807050710810302d4041c04540c604e240c40380400144960010902800c044003a0040f08920b0507800341c0c109490003406914504004a03c003107a159000410b025015a02080c0c1141d4588903140c2d0328a0282800c183c120390603007422300c0541c6603041a0301c00c03415940140401103041001080180800e40981080820305840c80c1c0780c00e0908801094804490b8070b000c13101406028420a0f1070b01074030959084503420500a80103981d511508c6a40c8008101d09100406c01503200380c000582c842024540f07a419a03a0b9035803090500f03003013512910520221582c07282d00d81c560081419911240c11301c010503020f04031100c40b544034212401104103050002510b4090620001e00740d05071403d000c0c00c0c1284540e522070180c4000e10388002c0e81c170303815401c00c6906030380628 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 530167221 1250 530165971 530166001
    0x60703110703080112020609220b0a0620100f14010f0b0706051306180224120604061703130506030f0105060304140319080109020a020d0c0f0c0617 65
    0x20b45901d8143c500d03400c04869002c0e0f01054401203920980800c291b4000c0d841d064007604152040520f0002c0c103588110f00c24050702c03e5008064001ca10514041245070f03406100c0c8683c2042c0c1c44080c08001e00147d00a60605003907149014000e81403000f0520a01e14030752041ea01e1010310780d1445072590700c41c14000641c940783c0c828009046030034070141c008902c080e4040380d04103032614030060700e0200559501081e600c48240c1c90aa0f06d42c0005058154106283d10407010102c01c01042c0b1004600060711669001c1c00650303a0320741c900c1d500010511b460315071020340a00078505400c0a070524115446503030f9031001888890001a03044000faaa08082007624003a204180c00c24005030f0038841480700540000b0801d50311a001c1405680044109000030b0032010100c403498940d0281e030480107094401d040c0c0c00251683d01c1009003450791980440ca0308400c00c0c0a181040c4040143e04220f083c404101d4030103802080103850005541c0d40115040840701d6424900700000d541d083c4144040755 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 530168471 1250 530167221 530167223
    0x220608030c0a17090a030303060305010b0108010509070c020a030b0907060f02060712050601030f060f08070e0c1204031106190e16150c05010e0c040b060301120206030a1d0607031107 80
    0x98001000c2d035001910480e0f50554040d8804052824035080500145444103c6c1d8400d90210b56142000c0c01480030078082c400100d0401e09114101d03516101c0400c040c8800280088208002c006e2140c0440d42da6203507400045130004240c6d40c04c2c0c100007070301d552140301c144220800304002034030402c092800858410311032042a01c501201003009060140a01001030282c0d04040d03640c00c030fa444a03c12407007010050400c000e200442903040c036681919044180c1c000c800108086c1040081071030204084818100c0e034801d848110f51581d1600756031200403c840c003d440d014100c200f0450301503511451035051000e041c2842604a0021807507110080101c3c1c0c0301a90791280428042c00c040d60742c81c50790f03500302032506014850003601d445086a015088501a0ba0008000720580d0300d0a40180140e43c00111403c628651402c00b039002103a903825070090040d10044001112000136501c078161800c2400c00d401d10700d1000c654140e444070b0741100c69401103440c2c01c1840f04000b1604054030402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 530169721 1250 530168471 530168473
    0xb0303030a0b010f0c170304140f010e060717130c0323210a030c1e1d012d020c040e0604020907210b03010b03032109012a02010b220608030c 62
    0x201c0b6054140040d1f610042c01030b80c0e003072004c0c41c0213004800c0820180c4110070765100001100c00850240a04020024040400700b00e1405000940ca2002010268004800c9103280803011034614240d0070006960340050b101c491580710384d0038000000d009020001c041c4100362040b103980c50a0f03192f071264158421b0064001d0500c40400e425010340d0110f00d1181450821039600c0000e040c170504181c0340145508002402204440325201c1c1e801051029981c003401c03c03c1c1407007065440314040c050b40c1e45282c0101800c804500040600034450814980310103042401690a00c489040d03507000150703402ca0065170034038005001e0510865503801c0b0190031010351880c080000100001400e1010a0203626558401411403d44e40c100000c10301c1d03000703147c10719001d0001e0300040e40d1100c900404100c1c0603410003c00106a00c840e03542c80740c052480e00d00c2c00d01f00300b0312448124018203018609940042c0007440c0d600701000d2418800d030101000c000103100150f01c400c4010349034002c280e003512031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 530170971 1250 530169721 530169743
    0xe07060f0309020d02031c02100c050f1309110909060904051009171809100602100c030f0507111b150313061404061803120b040b0303030a0b010f0c 65
    0x803a01c82d8000500c0e280c0002e0200c4c00c03082c0d03d82c0001c2d06003060110481c03100c0190220040c500c0e81c041c41010040142c54078200540b552520b0050890310540d4190300383c041001540107111004003240740043e00d0724038010400700e0540490000207a000c034408a120390102000150940b0302000c0b800e215070f600401030545214031060010180401e02003c131080c448542d041c00800d1004406015007006498040481002000a00052a0700a00380c06d80340202c000090021540004858000920481d070001c0c0c81d2405000450041a40700685c8485500301803c4c81062a807091602c0d502c80c1c030030340c1510184445920a003030340c0078054406541002e4000d14001590400c0806554005054500d2050104a66460343d04079102403541e000300d040540300340400e11442d8450703002241c2c460346071036005290a49001c0c0080c0400e04448840580b1489043c800e504c0d950092541c0b00c3c0040e044030303140c0c00c200d103003000075103001521240010020f0598204042c40369152223031803900400480c113 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 530172221 1250 530170971 530170997
    0xc030a1d22020405030f07090606141e0f0d091b210f0b0a0504050607050a05091e060406270b040b030403170403080717010f060302070203010f0603030507060e0706 72
    0x3203840501d50801e4016828400016152400e01c0310904418040c000740150500349107075601141c440c0d400c40c2003040280e10140c0d9042c07140710100d4484150078034401c100c80040da1a0b0701440d128421914140707100100f0502d0808465801c00b080f6540300300825210080c512651044000f514451040000400071003c0710b09500e240241d01e0300d82c084d1400449504098440540f4020255034400d0380701e554000300300900006101854002500c1e15140d49005801c24000b040c2e809408600b62080c072120300c0d0160803882000301101240c0d80588200e48031a51140041c0c00c480044c1080d07056194000c0300d50307416030100c007503c070256641810854101801e054052034145c1005000320144400b010000c0e15001120482620640c440d17590007240c2d240261009044003219100c1100d0300c000307036005000c900e482c2c1100c0006c0d43c0107031500603100d00745400064090f1510800c0404501d03d0054040141980000205203040c0120b8082c0901800084240e66407405449075000082003509071074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 530173471 1250 530172221 530172259
    0x10504060c02041103010315180206250209010801020c10060b03010e0a020706150302011b0302070b0d0f18120203070209040209040204020d06090209010f020703050601061808030c030a1d 82
    0x1141c0e6002900004001d20440842200303517200780c100307654068a846150a548425004aa0b600c0910000c00102460f9607800308000d0300814200403441c4000400d4400b811001c1200855690f40081c1801819695002c0c41070003544604c04961a40c050001300e080807001c680604c1c400c60300e1624510f403440e031030038a255146201c06800b040a2030b40800404c00443e01d24000c00300c003a49990480c2c1d20492440c400900081d043c06114587c42d0703074854800004c40e4020407007808940c0401c0d16150b6582e00106110018403544100d200410314104040310106480107918800c0d0781702e0003210218104400059a43e402140c0000b13501440100014005042c901d2460b90080c0c4058005820002004c505005981440d004451000d0780401c00c202c0319039018808450030130060014040e4581192141c50312240c050103110140031140000544150000c036080008040301e60503640c139800c0b9803c1e419160340c440c0402c100000c1c040842e015807252040c0c06020320b001c0c000e00480c40d5107a540090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 530174721 1250 530173471 530173487
    0x4050a03120c05030f0301051c020f0f010203090406090b180f1302010504080d031a06070f0b040c0f03050322060210110c03371b0f02060a03020c010f020901050406 72
    0x1000b0401c54020700b00008804101a0611144e07002800e503ca40c10074003403094051258076941e800400d010115000340e103840712800e9803d80b0580e056016a81e0010050f0f14500c10826035a4000b480e0000014200a142d84440c0381c200f400c5403d0000f6402c050404d012201c4250340b5035581c03001c50f801040034018442841b0100c18070604040d810f15a407818072506204012254a02003500c9070f0484080414000d19240c0c280c00848109041c940f00fa201c41c1c10340515050024802504d08000c101130000d80340c07860009100400c4042200340d240d1074503948a0700104100d92440b840d50850091406400b500d10099554550040c10200110b00440340a051241c0b90300035520000c005846c001a0240700030f04070201d5810806101001501c14160300c00b5020401020720008034032000052540200c030200b00280086030041d00380a24180004d25a10900c4000d60010001904050300b5030960050003a20b15a2402000f134411001801c0b4140d1103400081030001e42c00b08400d005840c022050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 530175971 1250 530174721 530174753
    0x60e1f0c170f0f012111040603080307090e09030301051509131803120209151e03071d0909070504020c030408012406030c09090f0e010504080d0c0504050a03 69
    0xc00741d06960654004405510705641811507002e4a07810810440009100c20b80109a40611011032428010500ba200710861078024060500700200310459902d0303402c1324002e0340d08400d809580c0c0c20202c0010781140b4483c070400c1f5800303003000000f802c0c1c0350300801660304903280600220600443e04444151651100f070318a0340c0451946d80100b180001d92103815500e28100c00d14000c0742c803907814003600a1011004a00c0c05034010014404280c07640c0e40c0c4d41d601c0012400702c858a5401c0e4041c0b038004240c00700c180c010756190100c200080e403079001000743c05522181188001c00d4507510184158908100d46003001a80120000c00150829500400040c00c9520a40313003055268000d91382910b4420003021032000c4000e44d20781c85110308003824002040b59041c200b00380301c01c4540103040c400180c0328a500880e510611000301c040290009002c03850110000c11086c40c252400f0401600098036400c5e015141000403404503001e8002c44003643c1d8021b11030003220b40f456590f03600d14004114 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 530177221 1250 530175971 530175977
    0x70302030414010c0e0f0a0b0912030c012d09020d0305090d0512070501060b040e0a42080d120e07080d0804030e0607020d121416060e1f0c 61
    0x202c1d0b0500c4002031003440f0540c10140e40d5910001c0b42e15042224492000c00c00c940705200c800300800100714003000b00e0301d6911003621413401041c00a5080c50550082040740c002c0d030350070141c0e11420f107601c10040c3c0c1d001440c5800d00302c0e41c4d1100b541c4044116049044001d4200001002c2c11000c00d01038801f8000035440246a114481d0b810750302c0d6410240301c200e07030341c1040c0000700319501013040c2800303980068020003161030304091501e6030360101100301a080a811550311184945000740c072000b4600120020b00c175800c443c901c0d00f208032560720000642005101ca21100c0411001c03030116880102034415035889550307a500421a100070502841c0101c402c0c49803601c00035050304140503081181c000754850410a00d080c0c10068142d800b461609031051200b00600d0006942e114000d0304040c1d04544441060701da40e200c180d51341e100680b070720041b590001ca031096003941c0d0802a60402d510461040c003134001c4002d1b0b1181d5940c504801c0180074002c0004e17400d60911a980700ca01801d900b45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 530178471 1250 530177221 530177243
    0x127110f0d0809150306090403080421081008011104060e0d05120c0114160c050c1903031112071704150e1017010b0a200f240703020304 60
    0x1000607954000c100044031055800b180380b01c400c0c0350003228462028442000310386140342141c0010340140c0000c00c0101071080744008035051200500030756180c01c0e0841e41b52121074903c400301070100b9500f02d500001c0200070032000b065120f010300030324000780f4911550904250400c42c1c15140010f250b451641c202c01050341510101e5020041500d0300c1c000c05a0303c982d00d030352481466081d03070503112070391040410910511103000350f00201c022000e9400d1501e150454040d152060810b03014901c21940070407070701c20b130400301d0015100041c1220f100c4e4558041c1402410082e0380c0f03e0700d855040f2246154144141400308410450000700c0070032140a0700e25140d200c00c148882c80c0b4440a8980015a1202029556003441004c036480c042007424003803080c010303008051128680500a1202080020401c00c1e00d1500070315841c010b603000b5a14240180320603101b141d541e03080c0941d042400380702e884841d507950301c4600b440101c407034a204c19860301e542d1292810f130040d500c05002120305a1000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 530179721 1250 530178471 530178499
    0xd0e120111070c1a07030e040f0e060f0130060c0c060903081005240a0c020a080318150a0c030c2102010b1002030706050403050403050a0803060102012711 68
    0x600061090b18824850111884d0030981d41220211380000014540342c0c0070030598010030b800240b045118441190003181c0c2071071a4000b01c1c0a0104034400001c81e2244800744010445010250750594000300c41950302284100010041d1140848080b80120740101d02c00010415540020b8400e02d00c07403c010b00110b01c1da689100449083d004150300094510f03041c0106540e174a001b080082504a91019480c00964a0b0340ea00c0c0e04a080e101e0f070304100004085003c94040c40e00b41d090103400810000b1110307902d0b0806070b1640c1c81964410202c44509412808510b00840040050890642c1c054240009030340151052103100c82d06034140050100d40b00c0001d25500b0f580307c0c0b0282c2c500c503c0705140341c04070030107800d55080c000d41038070404400040c5414242e000003562880394201101090070744890405450b54402d40d007010300a4000c1010b500b0501c80e0031001107014400a074000c0001c440309452a9041040103200c8885009850300300f4000b040c40045407a000841c0104030128003d08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 530180971 1250 530179721 530179751
    0x40608010302093d0515031915060302090f1f0f0210020a0512070207270e0f030711150d1a060d06091a0312070303020d02070f050c030d0e1201 63
    0x42c0c41540d00da44c00c01c5280b44030341184a1103020020300381030350104c840209410004d201e900000f0011041c00d180306010403031100c6190001e00380070100e0b0900c0111983c86881c010086d50208481d6402904000190791040c10314400076030512001a0031819501031905045130002c1c5208910011413048441d0141c1c000c40358801030040c0f10290311a29612440541c44400b00d000040110007550401d200c104044e00560f1070118160903180f03158030390384035100c10000040c05500e40413020f41c40f40000495039088000010700119000e03405412556a00c0c0782046220601200b00a42c50013080c86000041d01003500215200180c1d9075042c440b1101050214140390401c8910000c80c0d5101c0400b04070b07900c494401d269910623410600b080a00c0030501181e80c2d00c00035524a1205140000d403101858801e034156047d03500500707010356640c0100d04050001020400050702c1500480807100d84c1840c0000d51007504565036100c120384590a00c040100380024009001455500c0e9581c135120803071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 530182221 1250 530180971 530181031
    0x50c01061a04060f020606010516031803032003030103020319050c030d02062a2d0d020703030e0a12110c0a0902040806060a060e061602091905070504060801030209 72
    0xd460718065111882c2100003040001d40c01c0500041d50044410710985903446022141d180768400251a490754051608440800e05580301210b40d50514402108260340b12003044002541c0c02078000250030f418451544178842844005d60592120a01d10081044d4184100b0064050010345520b000110003107401c101d0800e48800068000704200044c400e00d2400d41c1c20100481c0300710090350708141410140d1403090b9808003240c007051b1020721441d188450340e0f4800d07260010321055182e80c0c0b50f46040020f50000101240468100702d909441140b0006c2d07040403064101040711819001607000750703000508001c1168190007200c400e8203003a2070304810744000700406000141c3c0c4529289545050910140200e4071422000c0404c00c005c60340021142c031400012200d40741d407401c104001c00c0101840080c0250400642020018101144524855840c461440611060f55918030403079052185020700004141054014005820b06645040c7d10010350100c02d0f042000d40e00001a40344 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 530183471 1250 530182221 530182259
    0x63c0b030f06090a090302030706020d021e1312020f0d020a091401080c0109050901062a0b04050114011d0613150f09062403060b0d0c031d0a03050c0106 67
    0x81c48950600409090202c12240c0c08007061104000080c1d1583c1c00030f481f403003202009800307184c01049080445a4981c110303041310a0391a90411a100e490110600d0b94002041c0000200200c0c54000752802c41100514031181e0f00070140341c503030105401000941190a401070380c01500000011034000040d21540031070040c5032244803020f624000340245070001e080042030401c144c4402c100035944841d0140360540300740e07043c104400c03035000c00c0c141000742c405051442c0d524407a00750082400382e40408640100c1c0100001d00840c000395200590440c02846511099a0b01c410740d82e4404644a02c443c3c0c0000b801040c0032500811000c0580c103072050006100e503c41d8030810204110b1030105140070080c64500c4080c80101d1420802c00c80820b0b030030190b00403000041c41c200300e92038403960141000e002c41c640101e445480c08035002d00108400114003001c41d01c7c1c01003000580e00c0500d0350b010b40d0046a00205000d44059500312140d8020500c8030701c496407a400c000ca0289110b4450020380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 530184721 1250 530183471 530183491
    0x90118140a09170c060723131404111902240906010608060a03030309020d12030203070207080705030a1b18050403260610050d02030c0904063c0b03 65
    0x70801c641440d007034102a03042503040304581002107408070513000c0351a9a1140d440e04100301c17011020040840b58139607082400126020002c0d515801e114480c82080036151101d000340140603654080c0021515805811b80100034248100c507859060452140040c103080d00c1600e05083c05048100e45160b002040416024a1075080081498040004600603d510b1410a0140c20324501103518882107000c040d0816844a21002c01d645550014542c221362244030721803003850f103110090094109403550001030145140002d013101c0c0020744041034800c0100540102c1e021070392071b0402004503140420719128000c8000691104891001141e038444080100b503d14080c940140300c22400402014941040360b581c9400d040d05d1040700f90f21036410f03a013481040c244200b082d145405040a0f841c0814000020040ca01a5420242c140c81e041500d050240c0c6840d580d0300c15001d581811700204800c80340d02c81c114800300e054040b0300d803030000306410301140c3d46500410101e41d000311825155 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 530185971 1250 530184721 530184731
    0x18080705040b090f130623010f051005041e0b190305070c110103090203031b0c12010207080d05070302040504110703110105100b030c0c060907030b070806090118140a 73
    0x10340d003040d00464490305000c0f2401d580a21340880280001100a0125800048020f240d4410030415601c820041c8a00c1a0440600180141910040d540074000c00600b10303101c140001d2241420002c1e980d07801050388480c2d003801d08080307500c07942010458580c4205044082c00017641d11050004152204031844001c2056003090009015100054905800c2091003014080464011a02207051300740074a000329144a503800040d2071400380e000203200c6030b5500d01103c4061703500081e5054400000307407102c9481d84403607402d0328201e0280c070f200680440020007111264525542c00340303520090b40d007070050800740c8440c0810210b4914000e980400c080005500c0203158208140c80d4044552400901240c5003180c03105500041c81e108a0300b0242002c00403c050903110000e458001c281c41003101d251b8a440e0351060340d142c083d4031043d510709500c080030070451840387d4170140c451203001e40180c0c0141d103030482d89070402620380300c1e1105165440c2d03801400340b4011110320380202c07a42d090100d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 530187221 1250 530185971 530185979
    0x9020904050601030c06050310050103020c07030803010f1406030702060708131746090905100e0c180f0d050f010b0a0e01030b01051507050102031e0f0609010306020307180807 77
    0x1c290031700f81d008071090081c14410044020004010081aa4001c0c0b031b015032500e00b525201451b05149070401840d41c0c0e030120000c01c0c3c0030300d8020003a00703c0d041190301119000c240f00501000d44401c0d00c1420040c0c02c940d000407111801690900c0d0000a0342e94003d0b1010142c1d100c0301b8440708060340c0d1000c210303c0050010500004000c0060340300060134070321102641071036030140303006041440c04080a40200c0100d04041d000d281c021008040e03d040034403191411080c4600702d0503880c06003803c600c54140c04601101e0b1000e003a03842c050b001d00300078083e00b0200c504000d21a182c071801c00d0b9208204104800c0020424083c21000340030b007000208220000314104406030600303030802c02e501d1562000400c04940050b1210341100c409803101181c10541040300750705846290b0002d4480e40c000014001511100190b1103402c0742c11f849044601d80301c0b0102700c00b0205040d0f5505a00c5882140148041022540150707000703902c3e070030030b680c2a4007070210303440802c1c15a034080101c1c0c3d040424200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 530188471 1250 530187221 530187233
    0x60d1b050f09090a151d01050919050c04052d070f02210306150f090f0d050303070e030f010c1110020c03041404090204021c0b030c03120d0902090405060103 69
    0x5504101c04441007082d524107003002641e21418a440500640d070100f41800d180e8402d648080e0307000c1d041c1c07280031446440748005a0301034601619000201d10400d106403100b10364040d4920203031a4400d0203086800000c00410011f8100500040012040380b00c8698103001490640c03d922109403003201c0e020b18041030054480c0d8990300088040d90013100c00b005060001d038155140001d10074815070346940b00c139800314801d40c280842007034240308009040b41800b02008041e1010800441301405c42102400910401644c98400108aa44103201080c2841e00448001030350000140444880d48d01a00c0c05a095420a6290b80041062940c1c00b81c1c40104c113011403891034581c00001e628059105000541c1d81c855441841c4c80d14001d00080c12403a0780381c0c0c000005850300141f055458050900984800c060048600b0460714503101001c0302c98200801d54030180400200035080031282e50070b0141d0903601404158201035036071115040141d49191019004d103009400800c440d40c110700d801c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 530189721 1250 530188471 530188489
    0x40e0d02010c031104030f0c1d180a020a0e04030c051002280e0d05160e070e030615120a0203011d061014060c01020d0614012c0405060d1b05 62
    0x36504041c200042041315034142c1044608503648144601c00c5a509424a07140304040c036040030108d80084810325114a005003803c034000c0066a061035105e080309401030f1350310417401758020b4002c1001002046114010208282c0c401d001c7e090034901c0445c203503a25420a550303074440b0f590030b0368045003041602071038075124a0030300041c006c0600b11034000301001e40000061160700d0b00c503c514030160003c121050000d19040141d080f600010291510400184141c0882e440710001d015036841d140c3c14a80092881d003d400108030710680401400309200d501001c1c0c007030b48010b030300c40d90840c1c10040c0c900348034124500c5d014541020b000502d00740034508188001d00003104a400d0030106008040d01050580090f03c01140d0540d03944180003d120301a0040c0c11150b004240790460000b164035000c0051a6251000d90342c28091a003141466880c600841440c0842c56200c3c10108bc07813814558005a00904003d101021600c5140e079000108a480f02c0c28070700d81109014200560300f017101030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 530190971 1250 530189721 530189741
    0xb19110a030c1d0405070c141f0218010f111603170309030d05180f16150c06020f071211011812030c0e03030a080417070804060e01030b040e0d0201 65
    0xd00c50440e8039030384120200142500e0f503118698070004140042d0007000c4981c107a0743d10403210901c00c0301031420203484034004038002c02c00b11007492030405000c0c040e200301c0d180c2c16040440058025110070045601041b0110040d00f48000032900c1035900808000d5a061070302a0200d8684c042d05503d8201c603c43d00d10104d0201c100000c0c0b0500030607100101c256804c0b00b00702080011243e42d88195108100d5a50700009518040e5003041026603c0102d0b030049580340f203203481402c0e1aa903641c0a9081841c030007074440040c0c614419200000c95940090001c18401c0089502b400d4007a19505184465030424101144230148a42e40c41c84082c06100442c5d8550312510420b03001c1c0d07485400307440740810101002c050b650034219500134050000380ca1100000f41c100d90715161055009000004c040d03d042d200c8a0054607041d000800ea5400c0324122640030f4040c9045c5454002c050311024180e21403c0e060603107038401404580c44078410601c00c1c6d040c1400030300c0850326450b4041c0c01c407500d1000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 530192221 1250 530190971 530190977
    0x80907120605060301240306050c090a062c031905032a01200f0d060e0a150503070510080901060b03070e040b0103061a09030705030105100614070201020a0b19110a030c 74
    0x5000c1b51036652900d0000c1c1141d401c5240403a40c0d5442108520151280408032079004507071101c00705010390302c03001c1c0c140c4d525010310244640711014a43c410203004181e0100e50716501c41100e03070304072462100100d05802d22520450381020240203180d1428100040c0a505042015a1005142c0000d0180101c108130b0b03000070080000c0703a080c01c42072900c80c08208000d41900059081500d4405038000c10061214509a0403075007802d20400018281504441e040040340e0310002c151481d01040038400c54100814200c1c00098070741c4180c807444002802c480d080d56848000041140d90000154442d041c075580c0c0d44030148044013000101c0320b0200d0b10504051804405000203511000d00150600102005a4603440c4c806c000924200d610780250f50554244814004031540b0401e0702001d8070a01d840b25001c021032101c02c01010300038040041d0041c1e1000720604040344411034116003211a5061010708545108100400c1e54a451610a81e501c80042d140040030b9041c845d059030080245 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 530193471 1250 530192221 530192261
    0x42105030907050d0f0b0c13050609091819150609020a0e061b0109060203090708030307171b0a0c030f09030c1401020307020d1a0f0705030403080907120605060301 72
    0x6801c0540c0c8501c40e00595004c1c2c040d5600220500c04413280c80a0300315400f140e4913070f0625000c9102c4809400502100800f01d00d2102d0220b81460198180c40400c0e0b806071a8031440c0d650708502c40c00e4150f8510050100d17000c0c04500410000190100c03007006401035101410508400041030101c03400b50707215009040c03061083c5400e01d81c0c81002d10801040440e18075445c3ca84120f074038046400c544510030201d610381a15481040595005107115504400a0b950000c2d6140e602548900c000c03940c020000740f261407036980a0050b5050284c10424440114001500c0b4009241403644924054400b20f4029443c0400f0954040304541303002c0c045141c0082c10601d50b03591061820054001c2c4491060204030140c0d00e03920820603600c100750020070141401a081c103069042d08804100d01c80781480c44400215102c500080d03c5018038260ba031410f1442d641c2c3c0d2801c0304e0300c2c0c40281516500380181c9030b0000d1b240802d410207440d8a8010300000441c1c1c1491400c0508490035280c0300124048a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 530194721 1250 530193471 530193481
    0x150a020306030a02011808011d0f01020c070b0708130303030506031023090f0d2c01080c090d051c030501120b013b010905060f09060d030c050604210503 67
    0x100394840034584c2820f050003070798410003009210f4007460300301d0510340d8a800000300c158208032906c1c3e401c0c045180c060b1a1007100008800d4281d1140390203e10459114207800c100007861070006108040c0284c2c0303000d0900601c4400c008000701c0c16407042d400641c4410601c005841d0512180100120f0321008104d4413801d18030381a00c124000d140c49050090321400107440c6003040c4030508245002d074060702c1224805610207048010058000c034084000c0c3d01c0d10610b03940095031442480d4a05840d001c243e40e659008001695001c0720f04540c202d8210819800050070401520b40c0421441130380161000d002c01d802002c941e81648001e140c510044440c0300450185a40281910148a00400a4003800c8100a070103100d03010300d0a40760860070401440c00c5821580c4906170743d81e401c002c0c4000e0f16810704010f1482213039004541c1c001c03044030210741d583c600b000c81c031811301384a42801820f51407152106414144120740503a1000d03200c0d510301041001880850307071b440603641000c901b1401e103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 530195971 1250 530194721 530194723
    0xa020f0d050106150903050f01050f16051201090209040c080c070204051b07051506061912060b030f0403090501021f0c1e090519060e0d170309150a02030603 69
    0x4018116402500104020001d01400b074115001401192210520b1620003250060442d41c0c4c612003507480b03004090075919a2041806800e01850401050070081d466020041601000022804003800307420840c03a0350891b007010b00680282407054005071581241e2090002b034801181401c1c0c100301140c8100040c004800b0261000d054054074001032640d00c0c010490064000c0c5080d0144001c40422914108070300041c44580c6150f03400c2c118803098440009000840c081d400056070401c80106041d41d00921a980108401601003008182c2960760125040ca6500680d0a903012820f0712080000345038101f038a40004160a00c01003482c0440c0d40346080c900441c8903641030020b5140c845000c1400d2080705012010b8906850b0010607903c5484060b04d40b102c984100c41c0a40d40003210391810020010000003259070070b40307a00c05d00c0000f58080000581c0c9039203044441e042c10b00ad454044616040146220701a07800003022514112000e4100c400c02c01040310828034010001c1146c942c030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 530197221 1250 530195971 530195989
    0x2003010905130b04060b100903081204030e1203070c060503010506120a060e19060b030601050418150b031b2a01243b070512070914030a02 61
    0x2011400001c40d40c035140003084840480600180002205400348410f0041541c4039500c50070b022102400707000041c05058036014460311003d041100c05110f00401e00307070500d400561007407103403415111400d04800020a0000814501c4030303950b0002c522a410043c0300320b03500010341458248141150300d0724000034620320a8200910210407520b010030022101d0743c014401614040c40a02210324200361810420314040d00b8041040f818070200140d881c03120000c6900800042c0e44d568030b040e040c400d031003c010604013280b41c03045a135141460300d0b5103074100c40200a054507400f801d6903400c00c010002c030002c4003820384000d51517041003002d058514840b041018000c01040c2c804400e1100400d9600520ba80c17807003002e00c0c0038544103036843e1700780078071060050301d454070122104001400c0401e100c1c0c124160110080c00d180310261801e083c0110b490030b40c010a645000707490100c503101e10318183c0a01b07588680100f600e0300710903c14400000f60300803072040d00f54018540f101c0d4035000140b03031403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 530198471 1250 530197221 530197229
    0x1091b1b0c14090a05280908180301050703050f0718050a1e140d1101051b0f070e06030712051006140411070b0406020d020405030105010b07170c0c0105340501200301 73
    0x40580d0042005846d0754219081e07103070300300205030b4a6020500651440c5803c2800d00ca21035480c143c0000e0290307000740314181c0201c0d0240d1558101d9950b449040c0c400048c603034610440529a42c00000d2035945030071440000d000c14400000c229581d4828011400c005600b2604011560220304034198480e000e02c610007a400c21000084c070200480142c40503c2000d0700713250301503070301c000d411001000000c80002041900c422034007420303541c40b40340510000c181d46007a4503802040301003001c48500c4070701000b07540c020340a43d0810440c074000c0d1000c8801540c00305013403562851541e10302c0c0c0f40074891415001c0020562a140102a41e1390480c1b501d001040108055408120f00e00031b100d195064801a28001d8020042c55031105400c4c502c54100c000119140c040c3c06c024480700001810030307108802c0c0110020442002c0040054900340c100710242c4244441082110220301e003405003549110150507981c11420042d4200300d400c6d141d00c0080e01c510340041c1510a007200b0f0f00b50f01124111 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 530199721 1250 530198471 530198521
    0x61409071119080c10090213060501140c01180b01080d050304031e020c0a08060f0c0403020d060519091b090e0d0513080307031701091b1b0c14090a05 66
    0xb51102d031a1285090144802c02515489903001c001d07a0010154810030400d4000c84a10000108906882d0240c800d20300416001070402c0c0704082203000741001401c0c080311031000200b0f54681004158180b00e600420548081500030010054030f40b0a200b040c83c440b5851070403500d145001d8802800c1d0192040c811300017181a00359680085101380802c2c05840c5000b0003a28806980d120300543d00c01c01038980d55048254100454495006002102d0459074050030241a0341c1c4a501c51000506c0c0051441c0b8068088000d20b107000701d6a0f109002c29944a16814411040000e5003106031902d560040c103030083c41c0c010b00da100450f000809000500c41807510903655101503110303103603190240d40880410310010550070105504804840c51441c1014469100c40ea82c0303803483c81c19a1211100e28500604448628840741d1085001d10340629805c0c081700c02004065480024500c007a0344004c5000c540c005001160340f9001c9c50700c1da00000c001c0010711440c14100c0092400854445c18038141c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 530200971 1250 530199721 530199763
    0x60e060915030109020a020c09010f0e090111070609050631050316050d120b10050d090c09050711014b02090f010807120b04020d0614090711 62
    0xe662914120240107a5408040d610b95940b00d9619019400c01254403025014080703c030801420314141c1e15040740c2401c04a030701c800303107070410b03a100c1d125014000d03c100c1e549480082425075150002803012621234400001c0c0e030840781c101141000c0b8003a02030000f60075000c2104050041041c0409111b6040d11041c801c0348106144c041d140d841409442907582e801028010140074020445008400c0d5503294000d045180c0b0303010b04200c8070f4000215500600d50885208103d100e000a4880401c91030f07000182e01c0b10b1512aa1141d60b882e600200342c4684440030041102d034840030910004501c10300a100001c09410041000e0900102c40000d54140083c004040210b8020a40c2d0b8074007102d22792034030b0202c07481c80e100c040d43c4521043c1780036100285441d16154880c2c00c0c80e40c8951490354840030400d4003221400081c00132400c100364810f809001c020590b175003030b202d01c00c020400304d40b50030020804c000038010b41d06001000003003441840b840954480b02d0110b080001a0101c00782000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 530202221 1250 530200971 530200987
    0x306060409140108010c140304110616051617070302100e060c010b0a1a03060d0c0f0806060a0f080613030207030f1208010f060f11030c060c03041a01060e06 69
    0x5006640c815100c10b0304081000b040b9424034600c1606a910b040001d0102c402d8048003551429801d1424001d80c480c01c000140208100000d069200480105654940070204414500c42451054150380c1500302e01020f1200303140c00503c0c0001011030059070a030740640b249102d6202c0c0918031019008040150011145522031429589814401406280c5407404407110034001c084240d00140218075074240440c001d0310403215051240d0344031f1041c5c0e146a9444052112250982e04121119200303088045003041c9d16003040301c041c0441e200100101d01d0402d003041a040103580c0311002c7c0d100d1120342402201d002250303070380d80300c401c50300d10902d221303840c1c602203180034519030002d400385085007106000c10144020306461121613540b01c3c1d1181c1d03210440480c00d140316103e902c01146000c152028030340e014041e000941030200742a2410308080309001420200100c4400300c440300d00100704000c005540304034101c1303099800c16007c081e6041402c05805522211002c034802c82c004a0011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 530203471 1250 530202221 530202229
    0xf130611030708151f05090303210702011103060f040e0c12010e01060f0b16150f050105190f06260705070312020702010f081320100e030709150b070305040f05030a0f080306 76
    0x50f40001c0075651030361010110200320ac48510080c0c41090043d400c0c0924030b061001108266400317039100605c1d01c04000c0c044c070104402041000342006c8e01e4010030413070707010315915130790244001c0e14180004a4600600d518036821140240c000c50b49803405140c043c888a00c441064a07a243d8051490100c2c0000300c1c00c1650076103401d1050901d2160811181914044854000c0c40c1240c00544042c0600304151050440d406030394000c6003110f62404600300b280b544590b0b86110551007948462282c6603e6204102c0132a108a84038408541c0c00101c440c10580e00a10660200f010f0b91001c500b003010941c002000c8505410420f4100103a400205000b0386010054044041d4044c002018220901c5400e540c00b452000080e882140314202c00c007845070041950b8807103600300a0140040504103180d950040030959000b043e07100441c000030034100b40c14070003000014041e07122207440c1c61518031040f4500e9015041580aa0090404030700003c0d404d4405110190780206d18030703101c0c0d41d140085 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 530204721 1250 530203471 530203477
    0x801080d2003040308041505091e010c0c15090b04030506011e081903080c0c030313050c0a12151103150f1c05060705030f130611030708151f05090303 66
    0x1d0303407007400001800030800410360000c0080700ca44030b1102001d0750405400b070343c090140c80211034004a40321101200c5401d0050450b04100c0c0c14107000d0100422501c4880590b1501e40150060460185541c0f034541c0d04000c80c00000cac40d1032001b071403803d8290f0750303555190351042c850302104004812004204041d01f080000150083d9400c840c030604910302814031841c00c00c4801e40229144001081d0b15000c000210303407255403918021480d58413050300700c0b0400400d8607019606400f03104003522803a076030045050700400d40c2e0410803101c9012410010701c0c0078002101c5088943ca8008011040707850b5006481d48005040e082c0e0740025003000100c0d000c40a941200380d0300c13201075003d540c2e5000e0031001c0305a6450203601251955980c800d0144c1d190b101c03e550303603c14a140700000901212031018004038103442074201042c01c5004940380100c9400c2960150040f842c01d100700513003ca407801d044043c40c041100d40001001c2d0740103c214107010702610220070402e0005030700c9401c1e1420012 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 530205971 1250 530204721 530204777
    0x3010305010b0303090a170a061b0e030f0c060d060807060809250b0714060712060b07020f060c0c031905010e010603080d1a13020714010507080f07110607050a0e010801080d 76
    0x2b0711450454100d407010128a580070b0700080781203440b240e00b02e802c00007104070109641e4401072005a03055020403210f03800090410800c9a1601c5020030f12603070503c80e0800601c0540c5505c00142008050182800204686440c2401200800840c60f42e40c60551104450010440e29030b030300d07a0f03030401812200855900b1a071034420710041c424030a5100140a00031080540208441d40c0c491220807158860010302035440f4140341e9068017203280041c01851003091850403959a0000711010a060001c51401501c1808810445905210082c0280d880b0440a84000c104031411542c928901d80541481c01c2d030708503510100080b85650a48202c0c000090042c0f0301440a10300d01202c8002e0350211004a90026111500c001d0660050103401d0240480b9200c01940d0b5981070300011822500502e144200001e60010a0004100f844800c0c000d450b560f99581d902c500149003d0450005219410b040122501c0100400703000401c40100c4141c0c2403500840381d20419102482030118592 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 530207221 1250 530205971 530205983
    0x40302031201031b06020a080910021c0309140d020604060203090c120c150406050a030b0a0308120907080a0803060f0d0203070b041e05010c1410020f03010305010b0303090a170a 78
    0x10000c410310000c01c072140c00782c91005448501d2191904c5c4100e86640050f94010031040090000c40414a00034100c04413402c00c0e8811602188000c18129500960290b0008046941c941a00d800d0011026031f19000481040c010860740e010034200a41d100c00080001d031002d40d01001259080c0003c3c000591021b10081004400000e014501522a211200e0203803298916079480c1c04004000c1041e5411141603446040c200014600b00303501529401e0304490744106000b2001c400201c12501910141c0015600b02c01d0514050108034584425074214509a503c10107159000403514070449a10090a41d036110342c0a01c5640410710030301c18a00001d41c10b0189500101e00307880c4602c0507008640d4625107240130300140b03024051610300d150148a00080c0c0c520114008105e40c843c0c00d02808000c4008c840c80410020080012a04181d001921206e80040100701b8003c09014a10400b10110059440c00c881000055891071442c80342d0804103d84201c1030a00003400e0190300d01d60b80c1c00003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 530208471 1250 530207221 530207257
    0x503011d1c140c0c040e0604020d0f0503040b0d0b0a0509010f0302011d0a0e150a030f030f090504020307030209040f050f010e04142407090602030f0f2503020613050601060804030203 80
    0x9041d125040e104d0314a00441c0b07801066419542c002072132074019500a42221000ca0303103601e42240c141c2c0c2844041c0c6544c401040b000a000107008024843c100d40100c2c0003840c022400c0401c45507132103d40c0501e10428144c0018000100182140b500b10b0380c1c2400c2084000401c002c2c0343c1280000c41d00415803024180000040002c0401c135a00d2041c00c80800e400c1c418618241008058049030201614a90400c1d0204002900828030070b01820842c0c18401980d640e600009001c1c0e2340100c2c0c030007000030340200740c03d8503909081c092001c400900680034007070741c545090740a083d2501481b4405070a4101c401007014030071240e8000c0d83c01c40c251001c1e0340f81480112006c40100e2492003c0594404a03240040c0a4510414090007980c0007540a5460300709648502d8a0503004000b00004a40c803c000b181c1301514159688011f003403100751100d10003180c504002e820490002c00d0400e08400c95161071000a00c0451581d054403400c0c10101c41503242d5042c201c0c698021000d92031311031f10840d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 530209721 1250 530208471 530208487
    0x60901151206050d0b04021309030f050d15060e010f022b1701031a0604020a0f0e0307050a090c08340309080d1d030702010203030430090503011d1c14 66
    0x1000345c00d4840d900030340302041c214280d00c40800855404520280004114282c443d401510030801070110f290040c9020555014000e00260849902c0d03011320040b0320b241400c40500d5030001000f03000351040340064110a10362071040692505d14881800604d4624040d0b407a126000b240702030700e216200202c0ea621582c49180c40c0c43c40c0d80b040300c1c69066400904002075200c0c43c1600848207d08444d03519500600301004054424011101c60f2680c0750091b128049069150b0015000013042c03010004903400300c401d00082c000c042c000d81118130820707800d44036000c500342150441d01050710f40c00d4110a0301001c04004c40c02862003a000910f10346001515542c56030464001c032803600020550040d014055070049030340d034070503400000d015820a00010f4045144603419074106080102e030a4040612161011002070560540001160b5060380900040c1800d1040c0207a00100c0403505040c440390313502950365405000b41100c0040c02d261410701080d8802c00c0703040c000e106001d90950301d1b0950 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 530210971 1250 530209721 530209733
    0x3020c030c070f0b03070e040e07050d2a0f060809121c0e030405010e040207151d0609060103020a0e07020f0d0903020f06030103080a0503130b1e060901151206050d 72
    0x1661084060f00f00443c3ca012401c3d40131242104e0103403035151900000841a07c0a02c0040c005500080d07442c0d014000000440d51121004540b80520802ca150700180c6590b12016048811460b0403d110070108410b0040d404c5000d103060586229080c03000103a41c800d8002841c0c48a40760b84800b05c000b000c290080b000840750300710228012605424000d22440f01c02944d0f0ba0b004a2017454001488508005400d0030258024040e00e801107061581c0135200e40740c4e6800340c4009441840300c404486680608120007440340c5500078411a0141900354503540001d05503201a001e0421044261404902c40500030001e0900301ca4026094481420191001800c140d8103444164003402501d845002c01d8070305541224142e0790301c04045420420b030b41c0781c1180c080d000148100410315101403a00085120f081e4401e114003661a08405508451002890212000b42c1818000c0d10008018005042443c0d00780d850344100d483c1c0075142007800c07090400509100e9000540003124070503d4800c1c0f00c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 530212221 1250 530210971 530210983
    0xc03020414090309060c0309030d2c03280f0605180f12070203071d0415020702010e040e071707080f0a080301030303050a020403141005310303020c030c 67
    0x1000321401c1100c01c615045038030034240100c81ca0390080d00104840310316403038407401820032401428122810072018030086490800385440341808140d025019543c1202c452100301c5102c2080b007502c66a504c1d41d02d0101c1e80d10344214032880b05a5420610720320110245510003402603400c440340340340c1402030707013007180050105032541103030451812280300d002302c00080d030401e5400500d002440a0a100600b40d071781c80d04180022039250041c4580016400000415070344090031040c600300302418985031211595000882013246280144600030160303801201c03030050b9120684001c2030960f0005a41e03418000d441e001045525400485062690310004000050701d50b102c04a4410406c101442c80d510003010200811000f420001400000d103c2d13040140c2000101d48050705003030700c03540c4040c0d41e40800c2500107a5503021f0662007020121a0040036040342d420703403203100c0840302018030030035580d88520b84040500a00c40d03800c040501c40c3c2d04460f81d0320300c104262034807200803c4810f52220 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 530213471 1250 530212221 530212223
    0x709111c0b030d0e01050f0f040e1005040b010314340e030c090f01180902060f120705040f1403030d09050f06010905010f1401110d0c02040f02070503270307030c03 72
    0x80b00c1c007003030060f0480c003540c440f0f941a00141c603400e00f80a00301014207000d50211412105150040c000010740c3c2c01d10007402070050003034800407012a8100020b000481d41e945040700c0c10181840e607250041520812140d0f0041c441c41d0721241820901000300b041d0314426440400050381424180e0b201c41d0780401c0d0b86010070421070a035000c0e40c01c10f10402c1003010050310207400741c4200b0801000b01c2145076025884802c101c1d000401c1d042d2058001400c00d4002c52500288018000365083c103c48100c0c0015900c030b880c42c1407460629050032100c217005c0c42d0900458545800c145d00c1e60340700796010025200a009029403d000c2e900300d82c940a0744440c4207803000d4055100d004008650409680100c5040c1c8502d5013203452031510300024150404510404103040c8500f24140108010090150302036058a94a84104004907441880102c508041c1401c000038814070145000031000700445810391550203507c0701104004040482c1800240f80300740d49031050b00e00020070044040141c82c00c0b6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 530214721 1250 530213471 530213473
    0x608070509010501141e0310171612020402070609140f0f0c1005090406030318060903120309140604050d080604020a0f050a050c1b0f010c050709111c0b03 68
    0x450354800900c0641007082c0a12400304000020501c030010300c98010f08450103003041c600300c20603069009034000e680207841010402d035217220148804000310040100e0f400f020b000406511100882200e0341c03c415018a020400110f0418030030b640d21a01a01c0c03180740c00c0203003040900250324080c180050001e40400403030196650700d91020034003145219803040080d02030f28070304110004000c2452030014880c01484001d0120706410385852058101943c03190b210710340f0081050950407210781c0716611400030072032000d0b003d00000c2c54904a00c06214841e00780803d85800b146803510f00b05207556403013402c0e4480c0074104414040009030311b017088599906c407060203841c0e40080c4010380c4202c66400011a1501702d110061510460040800c400c142c901039040100044c40c03582428042410020803601c2040c4002e9140703031400c0f800c40214002d08220101c2100341c1d4600341ca401807807241c070001d155111101b03d80341104a0072201d421080d50f890700b201d0580c80d4101001082c00c41c0f049802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 530215827 1106 530214721 530214733
    0x708041106191d0303071a07110f030909070e0f090a020903100b120a050d030209060706060e042604030605040f021008071d0a03030f0e130608 63
    0x41c0e01e00e0f07900c0e5240d02000c0395440440f10769111030180303e90400c010740f400103455545c0300285a00c50385809255503481300301c20345001c09034111145403070050042c03840092601000a10007203100701d07204402500e5054085a9031841c034010b9680102008446c01d0b105d00d85102c816034070449040340035107031040020100781424a4030a00500c19500d42c035075003280c0d01e4040e0798604440c0310400144581e0b00f1175281e40b566040c80341031000c10302d580010183c2064954900301c60503e5003090062001943c0d84214211381c00080310f003583c60044195113100c100f2400001c00c0b000f038600b485014101420750311010000e040c0a0821140081e4000107840143c44200701e121600710640c890250600d846d01019203031102c2044c00d070443d13640d1107110981f980e6891882c40e003034a405140c00761100d4001641641c2020302d440c4610b50051201941c130703442c100c280e00710f807003940e54060a440c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 530035971 530215827 := by
  have h0 := BRFrame.cov_init 530035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 530035971 ≤ n) (h2 : n < 530215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
