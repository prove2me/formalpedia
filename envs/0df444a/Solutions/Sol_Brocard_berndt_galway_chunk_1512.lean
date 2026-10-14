-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1512
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:20:17.552856+00:00
-- url     : https://prove2.me/submissions/2939f8ca-6bb3-4374-b6c5-33b30ec6cafa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 271762589 ≤ n < 271942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 271763839 1250 271762589 271762609
    0x141b010518060420040f0606121103061e060703080106080105010305070e1002071806031b151b020904150e07050f04024006020601050d08070507031721060d02 70
    0x1a904d02c54040c0c58126036600d9105500300341c9800c0d6400304400780341160103441140a4600c4050301420480348031488807c400c00c5a6100c03801300d5140030b20580d040700d01081d110840f14015000480050200245604510410304a48041d40d90701c0050f0f0f01c5c1c0004406a030011380b90030000c512540f260710a40e107009081c007803400c41d9610488515030b6481401c40d0b080c0e0340302940c0c82161661100148180294003c0a076192014816504a19031a00d01c032001c0c0010340300a00d40401001c0c00f414849005c0c00203d403401315400030107800241c10141000c11880c0148040031682500e800c150290a07100844c040d01141e200804903402c2d4030300c0e68103000c00b8bd80b00c3c0041c0c5105071101c0d080d1041c1b00e00c1030403280310400032182004650784142e003058446680c10380c1240781035622130401044140d8903c1c00104400c0e900c01501511095180340003132502140381c00c01080b00b07000f541e001520081e00f90140640d50018600c800c1d29140d808110b00c036143d02610702c180c01a421400f020302500300041c1138 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 271765089 1250 271763839 271763873
    0x20717251e02030a0c0f06090b090f0108040c030f0b06040c1805060d090503040b1902031207050d0b0307082802030c01030905121305010e01210c141b0105180604 71
    0x1644084e40b082d5034000c000007044c1c202c2d400030b040010051140300d921000702d00180c501845400c0c601404038000584480c810004c0138104045000000d007000b10b4514030702c0040d540010f020200403100c1ca0300501311403040741d52034003561034420850449803041045002d0102056034030b100807814071050080e0303a40640c0e45085036544031002c0e200050003c100074802444800d90907521002d84196004403c0b40e480907140c1190302c103116407141b0352400c00c08070b600501e860804540d06c59580c4030300409001c0f992000c6500d409544d20001d002d08012403010300c3c00309110074001081c0940102c1a0403404550390281d0194042d0520001c00e50023035100b41000741c01041185ca40789585608000079038042c0c3c1a010041c2e110f101c081006580201c0082442c1100b407c0107654042c00c84d480892440040096080090b2a5944080e40074028001e24800d5500221060341d20b480000d01c2080104805801000562911000900d8020000c14005803200e0a0000d00565115034891120340304900d815 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 271766339 1250 271765089 271765093
    0xa1406010f110a0f050c100e1903050102070312230402060702012c010212040e04060b0105040909060b150307050f0d1104060f170903120a020717251e0203 68
    0x30b0800e00a08001450120348a01001011308002c4d1411500f0f0405082c012809094421503038001240c00c401e507480c12210a0342c0402a40d950b03001320030030b024800e0744050500c1d44001140c0c400d0681c403101401190070462001e00030b40c00c03a4031600400060f0302709a140381e20142c2000c80d0040c0350903001404624014940314000c0d60840c80c0c12078458202c1c081c42c1d41c2401d03000300d00d21780e41d5805000c03440040100c1c082031820686001d040c81035607030000340000e01269031043c52110302d81c01403065030003401e06002d0401c4401e0301840c2203c010150b50101c6445140504044150803103004105e0b8030407101544c3e043e051400545200c211500a80c079107009050711401135006194ac01c4014100500d0b0701d5070303821004c451101d40505a000071403001c1040da00c0b0354081100441000003110f126070005418504079031780d03d0060100901031360390010410f024184448884140100c0540104094120700c1080c103155089040346d006d032606001010650309410400000c40c47c00c488014450020b41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 271767589 1250 271766339 271766357
    0xf06090f0a1203020f15010303300605030c090412180801090b1504150b070804120c031b1a090d020d05010203090d1b230a0302010902090a1406010f 65
    0x2000030450229908507450105081451100380741d4104440301400301e50304003805d070200c1c01c43c6c03402c8184401400301806122004154910714482c000b15074520340781031200c40380d8207541d810040d80074240c14442c1701d10a2081e80c6091411345005e900d0180203603441030b02070b07150921070328041d681a90320903410412419040c00001c1c02d660300780500781c0c0d00c80c880d6054180a140079100446c00d0148002c10901031840d00b58100072020700e641c000c1040c0e403040b00d603694460310280346c49a8a8031450700031304039020402d01e210040000c1c6061820603a0300c80c034005503500411520344039515145205401d140034484540006030300300341009020801e400390032010b09402035004643d0b014212002190180c1d40081005114602071180106801080c0360108903071041002151002c0c0441da40904211034080400642003100d00b42c503a840c2051105031500102c0700d0801a000f00045201a4041d619040c009504070032a0f2242e415407000d0b50013581d4070303621184011110f485240d114202400f140030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 271768839 1250 271767589 271767619
    0x804021908031b0604172d131502190c0905040c050a09020f1207021507020a11040501150f03021b0a0c05040b0607060902030304090f020307090609050f0609 69
    0x600c602514400380155a50b81c48014401454060070700d0742940d5404c03400c1070000144001000085c849004000c8a07158450142200c460401c030400205003940000c0c1c00900b4403044201500485420030000140159a0302036810509580c0c62004010f800001c4900007440c062020004580e015030261041c1503200d900d00b90840b801514150348090700c100040006207404c4400101909032042c1c00c0d8109a03e02e000004039000d9002e00c0510b64041c2c0340011501c510800580e018800940106000c60a007208060340b04c218558082c2e6001401d12040004c2d030410b80900360495404c01071300c0806d17140d110b5080f0b4001c010030314800100358003004501080380d4540155143c50107400701170328046002e17141405960600740d104a024a0920424010582d296000d8454003500b100780441c1c0480d5030310000e41588030300e8101032502450720360845a449002d0340a1840f0306203640700d004c0f046407a500296040000c910030540d005002510003030217428100040d041580c00a869035000d50100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 271770089 1250 271768839 271768879
    0x3080406020115080115050105030c0f040308030405070905010302060d05190c0509181005130b0409030c050d020604170912010f0c020d080402030303070309110a24030204080d080402 80
    0x564032400050391104252102c00802454141c02850364800030006500103c4076860581700074464541401400300000b19480d451004485d6401c240b00d1110769116168a000c400540050f203040e10907208801c2d002c11044401e1260074140d81d00101031500f00480c882154028100042010601c50760840116000e03407898019450445100d4542981300c1c8040f9017804030800c08009035418540c110000d000d840c484c1000d00c0021342c5c400352244c0100141380c030401c4000d0304601c4201904140b4040c42e0340305155101e841c2035401c1e8810010740d8900b800010041b6540d01c0c0556015189a4962040c0d0484100000080207103017405090700310800d84e814061421941d113a903406c60b0031904da10b2244d00284d4144a40080b550260a0101007401d1640129a8901005000d14107050f81e540c0c2403000d000041d20203c00c5010b004042c46401e5071108d00403544500015649001d1008100c103100b0300314000d000391030607a960580140404110078030100c41484c070103401070760008010b0b107a403080d060031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 271771339 1250 271770089 271770097
    0x90307111509180a0e061501111c08010509070518060c010e060405010c031104031a0403030b060705100b010201140a090317040c0e100e040f0c0f060207141221040308 73
    0x8020003c19482c82c00110000a49240903020580380d00100c0400000440051000362030402c28605000461030b501d065500d041944400c1040c042070050b0000b509651118105041c0c0d40142d0b05240907440c0e50300c058555000340d0619103040055000d1081c42402c00e5000303024110b007090000314142411040c607905041d400e0303d0a5a603a511224000ca4164243c0141d8450f00291000c0c00e1601d0318540741c0310010100c00c80d01c0210401400b000c182810b109800900c20360800400c91591290719140403680c501400a04230381503070400e030205c61158010707c952151911400c8120b070960b0f82c0c10760b182008140c200c10403028050303c8410140440080c168091086220714820b042da80e0400c021205c5e0300c44000c0c162011003082e86070a0201c0345200b0216604a58000b041c4092600784e450241e02d01203841d00040041071a01200003040e65002800c101103d0b45c1c0c2d00d4a012000740c0000744140051040103140c229400103903841e4442184c449180c07002d0540e803403e203007825181e64408900b030340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 271772589 1250 271771339 271771369
    0x1202131d0603060c031f05280501020d090311060d0203070207030b13020a0314120d020403060b04060509010b0f0706061202033a0512010801060e090307111509 70
    0xd041009011404400000c039900140c0480090010303180c101c0c080c88503444000d0841001c00c1c900ca0060018043c60040c0300d004d050028105890b00a0305602c04c00c0d056401504454482c00348040014203500110340d00301250916502e10b0f1100307003543c4900b41c02e084080310f000d4002c3c9007003115607241c81103403010318011010744e070290000070f20314140100d0240f009852081585600c440c1500185d40d0000c1d00c070304581d07000ca8034a4845030401074aa080400c0c85a00b0000c0e010001482401e010700c507030050080da4480c080411040100304c09000c100e8245004480d00001048018461003402c180a0a1101c1c02078010b240b500850340d848209503901644020340900106840d02d0452a0030b02003000801da15031516556415400a543c28032040e0020109e44d000408521f100054850021240312000c0d03682c0920055035a4813045001340618400c0e0307003100004a0200301c80702004022a034429410003000321b1100720b010104000da140f506400b0704004c0080140420944407280702e00c440c18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 271773839 1250 271772589 271772609
    0x10806011103250209011a070308220524040507090e031605060a0606050903150c071b091104060e0907030e010515010f0c030816181205070603021801120213 69
    0x482030710622141c2d00c4182c00c03450507d0607039403032846403401c801c2c26501d5650701850f00001a480b020f0002c0708807202c03600340504d00103a0b0201d44080c0000000c1101c08802601048005001c00701444900b542c0141d80041c140d8024680401200c0e0b000e41192005105201c180c070314202c0c0d07004400320850300c03510040301c244d006001003040c0c018551203074000820f001d0070101e1400d081c0e10001b0307844000c2c0b41c4080d1900c20026004c5001031035000181c1b4085a031122900f1226022055143c0303001101744161100c150901c0e0018503407580172010f0320116512a01c5003120a000f01c01000b141c0a001030609e402c1540c4c40f0000b4810f00317000d00906009442085075440800c80c0440014050700c0720344001c20600c0340b0010500c0c0026845410f50b41d1099a11007030240c0610490001c40d21110701d11100f2151880400020811001006042d61301d18403a400321182c00ea03507003a040c0c090b40140d40300c106030030000b030f440070f00194010000c000304c0e00c0c8940030041c500303896400c40418054081c0c100c40c0004c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 271775089 1250 271773839 271773907
    0x203130801060608060d0f02040c11030a03060906050a0501051206040b06180a05121002090f10080f060a03030f050d15060203070209060607051c020a12050a021605010806011103 78
    0xf6a084510b880e00201c0c20b445062020302103841d070610b0020001c8009004641d1058816081031045128000384600d09069035541e0a002200030060b02c03090003001707200d514206000445180c83c40d00802100c2041c0c4a00303081000110004020100003400e1f250060740ba0081d6920b66501c240007861071000c00c4e01028038440d801c6051148510150302b005008541c4210540f02d501c0300003900254541100c0f202594400d0080b01007600512460030280d0001110f11006880c53380210b04280320340380015200b481d6503030b80703810031001115501c000307030129044440c030801c428820801421040880c4401044281c10500111041161359001000580000c20424114030305a0b42c0b460f008041211801e0070300f0303455103803141c4808021068000b10101051040c240794024400c0d04840d982200c10120040f100600c044c105601a6a4800060259004032071402c031000450740143c0d40103a44520299840b5401074520300741c0a4070b902c24510041c45004441d001c500307412441002414240400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 271776339 1250 271775089 271775099
    0x2062406030c0c010b0411090d05030d050f220b06090915040c050a08120a0c0c270c0f0e0f04061a040f290711090421031104090c020313080106 63
    0x5c5480c03520130144601c1c1003400e04a1801801c5043e00c100e607400b1544062000c40c1440d2a030f246110300c42e00d03001414100340421038040e0718114868421282e8058684c41d14021142c0c07070750a044180382c0140340051403008260319061980e1080d0384074192104444081500b980300701840c0d80c08a60464413901503880900c9107080c9040e040c4001c11111004040082d92958460014003440800c0400c100f21451038000b48286001c014006204403071084d030760645540d8010307401159020065524504124103002030307910400e01e81442c1c25055442d40ca04ea102c100811900a40030100789070b00580712100420017104050f0800d5000c5040402c0b5541c41d403905511401c1d44055600190198103c0444c06100e40c2c0030a43c00c1041211458480360f858100d840c20307076141b0f2103180c032542d00040090104402c05c030740710250748006445d018141842c0c0001040407815550503d01706040700b0014041044081d85681094100005d58010349007000315070302081003055016030010001d0f07910360b902001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 271777589 1250 271776339 271776341
    0xf020109081501090b0f06071716030504090b010c0807020114130e100806040512030a150b090a09020913050402040617030307030e0c0f0609120d0c1403040602062406030c0c01 77
    0x40c00340c0503a06e140003810800c0c002081c40c040e114018000d68403c03521000c601e40c041040b034004540c0c61246800307040c00ba0600070201d030010700446039200e2034100403004c0c3d03601580d9240340d00d42d400311199183c0383c100e6004443c0740c0c500c4400d080340c80c1e1091110f4003890864460f088040c0410703070005000740c5404024002624070a0f4011040740d0001810700c4041480031402542c040d100260700c9541c1d0b12002d440e80010504c0070500d42ca41104544041070900101e0300821120000312010350146466400f07010407449100700c4a17904c440d401d22020911445078100d250b2040c0014800a491035994406120054410003542c00e5a0400000c01164680600c00c0d83d65a0102d1402401030406c030b200803411410060b10003d00c515808140d00c0c00341c0e9a95254501014180c0041c0d407546070b0418401b501009100e18100c1d840064181c40c0152210000150b40c2146c030290300808450301c07419200c4041801c20b44083c3c0f041c1d07144c4d45546049480300030003140540e901d038881039511589075108038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 271778839 1250 271777589 271777601
    0x60904061710242306070c05040e010c020309010c031407060902030d0306050a0506031f0605090109060804020a0302040207080c03040605090a08010917030702030c07030f11090c03040f02010908150109 88
    0x1090090f090103000d035080100900720402d507407042841c441109452203c003000154068019503100f0030025500d020001080380d10421144295014413480d000865858266110b10b8041c40051348184201c0300990b110344002c0002c0c5000307051044002c5100850415139511001059031502e03142c103883d104508080000e10821081450100030781814000000e19100385442124424007020001c101142040c0c1c80c0e00700c48942030600c103a04240c3d544406800c0780c210050143c00725006c0c0c00009400342c05000d54912480d03000340081001350441d42000300030b402031503040d520b00000b8042007a0001041000b000078010545036a07403988840d2041000d100c0558100601da039040050101c005020202c0100003c81460f0043e0703165902ea032001c92650040b0295170400d032080300c0002082c01540380182c0f10283c0503100002c81032088200b03101180206980c240014041080000c4c01315100502e11901c25205140c804482c42e40d8120281c0b600ca030650b96a10602c07001d00040040c80c5051140b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 271780089 1250 271778839 271778861
    0x170a0e0109060212060612240306070201060812070503041e0b030903030a180302030304030c060b0a0f17031207050a020106090c1e08061e03070806040506041203050c09060904061710 80
    0x8500e4200740c9100c4104440c00502800e40f454114804092503c00c1c0401c0d10000e000c009d81102e00740c0c82d04800c000e002e40128410090a8011340c090345800448148c100e406c116088001185814503007180f94910400301d01100d1407111030307004045800300c61f4a00071401180e02800464072402c260940d502150071071000b1080c1d1f50b120391001c0c1e00094020060ba5030181d05401e0000d040d49aa0521002500e005844180e00031a24440410340103a0384071040c003610802403501d031201080b41d544030344e03900c140030840d00080350362000151468450002007030540031034800491090356442c110000d0b07441c04810f040c00f14064124101d600204050040d9101940e80380c04441d90a1003408600030840c0c00c1c1c10010042e540c00000100d54604101c140d006280c0c0c43c2c01c444403032806080040e11180240c07000c41d40b00010711401c1c0d4240b0b21074000c050107180240002c41c40c0802400c2000319907488840410340042e00c6600010700e00458a03c0c2254420114002e0218181c410070900300b111104240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 271781339 1250 271780089 271780099
    0x40213080708010c0c2009070302040305160e06060d150b030a1503081b19030c0b012301050a03151e050603010e0a0207050304090e01020d060b0703170a0e010906021206 74
    0x81d2440c0b2a03408402c4505450f000403042121450a041b00105c1c02c92545086070450300030400d020800d07606034024000c680c000c0080e0b541541d080000040c030480180b282220700c0082d0b201050440c600309004180c80001800b00048608040d48004a14135256108107500f141c040100902405103000b441000c440220340124040c0c151703614031b07072035014581041d0707000e0003544c0e402c240c00310041008241100800100703442c85005841d00520388031044504072018403845000040740800302c4054240358181000344040c29414000450b019044000040201034546120b0f003074810480540c000a0b00c0e183c60b141c81813070366006480e504903406904c00b500400b000c00c01040302e4404040d01c60341140e100390000d1703075913292410468036501680d080201e0041c90516240d50b9a6030541c020040141012028003445558507500c0da414001c02a01070003052107401c0403507407202030750000707644034000700800070703007105c86c24511030841d1101c0504968480c3c1c002010600756140c40c280c3e030351041084030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 271782589 1250 271781339 271781351
    0x718080609100c020a02031606090b0f030c09060712020d02010501080d05040b0c0c031b0a0605030402031005040201031104090504050f0c012c0603090307020f030d0f140904021308070801 82
    0x1540c180d82d10b10070041c0400c0c00b079994103425003061080c003205103150780040883e030001d0349103a4610b040c00301c80d01c20180400c00380580041c5d0b99041ca819141b1b030001c050003060566541c02c1c4060119071201012035072054003000313002e00040c269103410900850a5004108a0144d07040c0a0300312030041c1c01c022201d034800b140c0700d50100d82c0b00040380d040d80e03c42c40741142c89010385081c091508400306401a858062011a0b140c0c0c00c0504070101d802e108202c1d180c06010741e940c3ea080e1403910003968065016002049035410210305604440e40052041c540020122030030030780c0141c80c0e005070300a103d8031500d80013803200340310f4100b1100d80bc2039803060103402032428020028107582c00020f03021680745c400740c108944100c0c074030241101c010700c042c0495030340e4540415134070740729801180102d1199201042c8007809050006604800e90074075110840203450b90032096030b503001074070401035072441d081001e00035a880da40080c00c20300540d0050300031a00d0419000d40d0800e0041e4015038034682c5041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 271783839 1250 271782589 271782601
    0xc0d05090d02060c0a05030f190e15091906020a11310209060313060510060509040b03010603051501030210020307030f030e0a06063f030f1707180806 66
    0x1c1e0041160b50490314113585641280c10a4104444e40c40f0281c0140004650100165044002001911503840c07036a1890007849800b034607c01d000c0c00b14641c2020140411040076081c0800601d54244000d01b0480c1c10380d400c09011030b0306904da81080d8010f0f00940644020441c03207003546001c1e50030488844c880417005860021941e030a10254541026440c084040140904e80c120344c03079020044c0a0650320305e041481d40744980c42803802110390700e160400007050754003c0d51045c0701340c81c1e156803103516040e070420400028061854115515550310302c0b0000014100300000803040e407440c000d0000941c034500402c03007c850800e5241003590802c000c03103000260f02c9650b01e9480c08850500003049003c0b103e0280c80c0c030604c890010000717850204041149050b43d5111903000b0a40840c0a814095503440714040040d40c0010f4801a04294060700000b805100c1c5060310b04090700e007182e080b01410664000b51003007a50480080f030102002181802c80b00b560307803800381581c8401001207003002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 271785089 1250 271783839 271783849
    0xc0f08070b070b07050d1103160215070f0207050324070804030503061e06030a090c05010504030c0b1e04030f031205040203030702101b0305030a0b010c03080f0a090c03080c0d0509 79
    0x2154010002c150103c00583c504c0c1c0102c0c1540e0f84c030506003c0402a5005a17540109103510507510f10500c0368400400c0001d00b0b02c001080c1071480b4280c855003410303443c0c8200544905000841100660069901c0401e05440c1080a0088080303000344c003406107030810103410b22030300c809810507003002402c000700008a0303000000c0b01d40184043d0b031034840c402c021030750f84040c0d0b0401c0da00c031035032084000081c015641d58940022007014001c00c55203c599a4a0005580a11540c0320090043c0341e107803000c011030031117070b8090450f074507031030f29140d40c003203504620402280c1c03140c0c00481d0807014a1140f4002d141d404000c00b030200b140400104010300b46900040d54038020050001d200c0c0401b182881800c912030741d038a0700c2d004085000c1241215180c0750180258108035803407a0040d1415031820519803040100c01d80d0f49801d80c51382021a116000040f10001c3c004095005403074550040100007035000c510640118001c0590340d495000d112901418562009a08403c00c030060020180c1c0743d80d2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 271786339 1250 271785089 271785097
    0x9120e0d15020d0e100e0106120206130521010609020a080a05060a03051e0f0c0108010303050a05040b0711180402030709091703070207060f0c0b06040c03020c0106030c0f08070b 78
    0x205903180e009007842080350019100f40f0f14650b000900308079083d800c4403000a132050300e00721341039018465255011400350803544603200710041403070091140e901604000008000c6083e40ba240040c0301034854000c100e441240400711405002821003110140c602845008040c0000101c1503140c15000c8200414844000c0c0000549640d03900200752650b980d0100b0000960b405000e50b0140c0040049400142d0b406070705d00c41684c007600140618240012840b8007541405841d883d0440e421901c04070342642111480c0030502c034003044003080c8007482001400096115100e201600000007041c000d42c0080304d00004030128041c0309001c01a0b074081103100c141e9981e040c0c005841210340c14a0300c2c44403840d9075040e071004000014000060342c0818007005843c80c40d00c46c2102801c0301d0108454120a000c400341ca41c00030200400c405250070707040440005a940345c0541007840d80c500150849039150701c1104c1a0303101c80030401c000301402601c0300050030400060919145004071148051203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 271787589 1250 271786339 271786343
    0x1050906040f090204060f090f090f030509150705060417090a030b1005040e06060f06030405030a0f2d0201050c04080604060903050c0601030f060b100e0120010e0109120e0d 76
    0x80c4070000551004003e90040981c590010414050700340d40b441034460000050044146203814400c00511598071401508c0c0000c0e0710400110102080751001c68440d041110304590224031044424081e60759000544080c038051000b4005500340f500e08250504243c0000d14440c3c2020300a080060380c44140910440e60445680d1404c6d41e6070350518401100203801c040d6100d0f24190f170f491118130001035224452913081e00d08410f503510000400166000c11100108654402c10401d032400f44595041d415200007400c0c103010340c0032140c601c4c844034a8801e100314500c08846044014aa609000740d90300400c012200510f061309000c901ca407202c000030006040e058884121030100351141c803c0f1031480c0001c00a444083d6103a191501156040c1e141c141c5582c0e0800d024016a803034001b020a44141d0651101d00c60381001c40015100d846980b41c681e60110300841203500d4451013800784e03007c6491042c00004514015250292028094883c0901008a94010304200b44c4900f00c01d0403500b0307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 271788839 1250 271787589 271787591
    0x3060925120e12070b090303060d0602070c17060601081b0421020406030c0305060a0b0d03110a08040602070501080907060e12070b1323060d0903020a02090c0c070e0105090604 77
    0x42003910707105000c2d182c1c04482800900c5200b24075001c50200402030328809101310800c82282d1170744011150303a80019516154003200400f03400340014034650082014501c240381e00e8600c2c0d41d07285055880c1c810323003011100140e04031600304000313981e200040175805010383c01d42d90324800d00840460500c1c0074602410740710710849441000707546e100040d12003156500070410b00c0b450f0703141c0c0b607d11030740c00c1d45110032102c1e8800c103408900c0212150207881041c00307010301030842c4607840b48c40407107a080c660482c03c0301c13a005010b101d401154041000f08080d107103640042c0300440c500030004180c2880204544a90b402001c000c0c031815500c110601a0900102e50400481080c080e1310782c101007035a80724604034130002a00e83c4070001075180c414121600c1d0141074164540d10707450300b00c0c508055042154092030400c110101c2003101d42c440825280a0702c11114102d20660205011501c140c1d41d02d036140c000429582503050081107a1405047c1d0f074500400c04d5450321000c41c050308400b0300b10034421 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 271790089 1250 271788839 271788857
    0x913050f15190b040608010602010c020a1e02130b010e0103110d0c0504090509070e090c10051e041805090a05060112061407030504022119020a050904050303060925 72
    0x1d6a5000356007118941000d10700055242d40f100022907503800380c8070310000b1404001c0001010780c0181320309402c445450b00504445601a92940003809030035400610007403003002780c8409a100e004211400301d081220000c0c41d40d43c210005091000290340031410181010030001409903a8425603d070b11540c04404101c61403400c9054810f030285070081480645001d0400810710b000141881c1210344810103021f454842c0301003691203900c907400442d0400003004c02556001d2041000f441e401e103da80c000140d0f6500c207020943c4590003640540440071501100c00780d40c00051069a410040a00040c0082801030313943c0c1d40c07a00e805209025061800500010601140741c01801d9103407015040002240381030786014001700803d0300d09034040c40b00303590700b43e1608034603100f051041a50500104401c40c2d4410105400c10815034080340c101100350000155511590b5146d4001ca1284001e9a01e0b480d002e418016410001454a444a10f5403d141140d202d110914441c544900780303405214 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 271791339 1250 271790089 271790131
    0x120109020d050a0611070201270b0a2613030507050a06060e040506010b0a02030405190305030f071b0513020d0603021906090f05060316090305060c0913050f 69
    0x40410810294122181101c440100705002c180b01c0220781c030401041109045100c02003225000d41403000b40880c1c031705c4041000a81c12201210080094207004208050b1101c5031034205800c903805040101e5152940c283c5224a810580704200c001100141543d1030714140311240d45030ba00740c0c06018850002488070901909100d1a030007a500000e06004996a440303002c0d10043d02142c041e00e6501540e0300100315800d00b40200c130052100799000b14109400c1c18100b02c02d109400a5101a21500280010000f24103001400050074403412098448206042020016038004a00d240c484440c22041c41a0360f101e803686d00c0c0700c011003074005072a0682c106d1108002d00b000d810103584909160001c94011012909000c196200c40e03640041c55641c40400a2103210b00e4001c881e400141400040c20200004804416520461501c0c9072103582c1c030703225103050910540c0c5050030309500094401c06803c0c242d11040c2828103000041015160802e105412048050100c55811012a00103c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 271792589 1250 271791339 271791341
    0x12090309042a0206040521091509010207080a0309061b061a0f030105040b04020904081b06040303271b0302060c161a0a030522031d040c05091201 64
    0xa014400544200b10300d01519448140001200005480d500100d031507156070b40f840400d40600480c5d111006207609031082181700c051604090445500041c28820b080f0710b651000031780e8440042d43c40844c0d65880c00c0200085c101219a00500c1c1164410b04030342c03000a520120f4401151010f14051050749030001c6128200050320300003810050a110194880d5060403180001400782203907200003001c072103018503090300c1080764064880340a44000901500746642d600e03912600c00d903101454161600445c440c0480442c4418966600800802c01015054403c0c21021000703012141040e2500205940300e00301c2c0640010000e21111f4801800050b00c03011190285a00822a039121001400000d90b02c0c4440d00303030032901c0e0b151b0702400140d0342001c540505941100c03030701482c1350105418040d4064680034200428030b002c040c412604104104400c0b440f118866601c10043d5105e402c2c44c041c0c0c400d44100783c130384a80e1414010800990704a811207108040645008500c1450058264 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 271793839 1250 271792589 271792597
    0x3051b0a0504091218050d06021b100606090e04050c010f0201021b06060f0d02060a05071506150206010807061209061104031a070f050a0815030709150812120903 71
    0x241c01c6403e207014072040069122556800040305d03900c03150840865105035140361640d21074550030580340503511010030540c1d0020708440415482a0a000c0440d2004c01d203005080030340400303180d646a00c107000081d03104080000600d48100d9000a42c2080e031100c644036441d940e6154107200c2800d092800301d80c001e4041d201c00c1103000740d0003032181d4800088240c403214102c41c0b80b40300e403404a500450514240071079080160700500804e0406034044416a81c546c050303c02a1644c0ca2102d032022241007850107403030007030901d4091b40c1a48900110010b0314010040c1c024900740d4100c0ba00501c07416a12011a003c00c5844000114852103507040801c0240060702e818071519000040210612030081d030040388550600b8111181d564445000b00d502c048810020780028104000c007042151260070425048807441d49880c0555030030f280013902e0500140d0028064039100c1c6100180c10207208210002400d4031000b4001c07809030400c403c03807140b00d010340640500320500049040c1d94820001d807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 271795089 1250 271793839 271793849
    0x8090f12011a030616020307120306080706050c0610030308221b050a06030b0319020f090901050a06050a030f08130b030106050915121603180c0504060b0403051b0a 72
    0x7000180c41000882810b4414a191075000c0e1040790081583d822103030350706a000c0907041c0e0145007400a182c0e070b90522911400084c80800d070700c0d1680820b4408041c09904010b00700c07900ca1683d500176021803c1c0c02c1c0031004000c4410120b04c40f50410220790042817180c1c0c070a002940c40c589509094002c10920510a0f2024120780601c40c4092942071200802805075441242c003101c005550f1a01182030b200b00006040d0190401040710300c068401e15041e840c80c40c801407110b440b0086910106009042c11504102540c1d102c4003805944c0a03503205440182c2410b0302d80c40b4105080d51200303c0000500030b8010320303076800044d10340074504801d6250400b4149a48203da5a961344440c010b2042d08444240781c840e01038030385c801940301c00d02003c80300039502032000081e042d81d0711002801030f281030f08102018103440f56022082198402030300030103103100b008981526410311003800300700c6007607401c84090b0000400c8140085000002e010031082c0f090f801107d208a0f00c1808180558255404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 271796339 1250 271795089 271795091
    0xb0c06040b0c0723060603120405040c050d0905070f050604061b0302010e06070203030108060a06140d02031006091b09030506040f02031c03090b0901150b03090325050f0a08090f1201 80
    0x80c16084140702c00e28200d034444201710b410076141c4404043c0c49054062038200e45d140104410009030034223070401032140603241411801d000a0410301c5099400c00031044409801003501440101610800d0002410b0b0559500d820039041400182c982200d0350f402c500007480c50040242014401d420001c4d18078441800d562490a0000020f580d0390028020042c0c03601922001546549a80c45504220b60445040342c030210303000c03014440d10304040502645c05000d14404881c07160301c680980c80c0141011b5030300041602c101034413202e03a210055891802c10104020410200d01c2c0010312541050700094002c06511052000038500299011603000b5800e0703034010100a1a015030000c10414003610348800b10713980d0191000d08031400071070b001d07080009008003400881010b10146620152400c200c078030702449610f0100c800c000b0700d4442905441c1c1050380320308004003800308000c4c07000940010f120360300c101d9580301c83c18050215042c3c01008084903210f042c1c0c0d600c414480c854000c40700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 271797589 1250 271796339 271796363
    0x101a040e0c07082b0504030c110118080a020f040e0a021509040c0c031101060b030a150504020705010c02070b091503070e04051501090602070e0103060b060408030c070f0b0c06040b0c07 81
    0x44a0002d0280b000c48800c00313030441e00f240c100c14800a02607207101303a906a03500301320380610f5520007629910400c030301410055603100d01c15510316000a2034020b861440001c12000031944104100303103400034001e601640c1810520014a0800107600300b41d941d04855103140001c0210140d00e050003204031040d0f0240c186600b101c0b800340c0011011850030700a035580010b40c0c881c0c6412500307950840c03050320b01c803200c10000503403014070700d81c011000b00c8126010003400a9a55002500342d810014081c2e982e6550f0b160601d0f807072601044820000e1441841c800d0928914100181100524117000c01416070004000ba0600748a8280c06180c0a0000c0c01000311b8100b544418202d0180c142c8041e011500402d408a4003600008298040358520f0402c1e048980c07c42d40c9000c05490055029504000305000200e0400c40510103050710707031144001401d01500e07000c800548003c0c1d030f50281d070001004104c6c0801e0900003191540d4425009803070741545480d4142c035a403851154000190002032000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 271798839 1250 271797589 271797607
    0x60c08120406020d05130b07080a0f05011e1d0118091b0905060406032d0c18110f1801120e01050901050603030901021005070e06030a0203101a040e0c0708 68
    0x43d000d060138010340c0c002000640d4450701c0906156100400152001703001100081520b403040000a50000b80c061003c506440d0305481201a0780703007038100c51100c120b1389550b002500f58003a018402414600c009007409075019070305501d010018003c10656180722000f1004a00c2180c000c00326040d80540c2280702d01c3c4811001440c2074949000b01d410740c83c1000041081c40c6098090344050707070741064503003856945203030507101800c2d410380c640c91091140440c0b41c40410aa0740b8484028940b0840b100616014824150110f40c04d00030103a500318414010b8030b02c07040c80310302a5508940c0756520f0084002c501c2005070758041d2003140c1d070b1a0860501041c500702410641169025101103402485603403207000c10140c903406260006801a4400c0004856110880d00311a030480f40c03a0402c89406c0b241080070500651045520841d42c0c1d4000040c0010000e411000400504884e00102e0b166a0641c040d401d080c031a03403103100d10451102000c40c000c0c0c21158229021943e0014405641301d081d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 271800089 1250 271798839 271798841
    0x10504030e01020c13091a07050307020c010305010b0f03070e06040b0c0105090d14030c090405070504080c092502010e07031416030c150210060305011b0203070804060c08120406 78
    0x111421800901c2030511026154000110108aa580142940301940104061a006112107082a283d000498540d1400d0400c801d100f03601500580d540d9030b95a191620002c0d00d04074a82400310304044c613100041251414030380907260040348401d505070b904d07100c0680c21036208031406400e0354030680000d80000c800c0f4170b400040c00480c0c120b6009100540d03c07032040545404181080d403000c540350a04030000b002c3c10100940c2e0004050280714108581c640c0441c00302c1c0c10481e28000442c0c0009030038010000104000801035204458490003441d00303004040c101440d0140344120341468030701c052081c60003900b101d0f6565800c0070484034050303903134207220083c001c04014003540350003600d000481c0c0b00f403041200800d981e0400501c0c0803091400c8100340c00900c0c02d40c81d510450091548484032a00c45004100045010b1000810040b10000b0320250b0703060b10a00c07010075903100f040ba001c0007640c08015203045034910b041401e0035403802d040c84045d51003062424400c034a200310820041184c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 271801339 1250 271800089 271800091
    0x91a06061e090907020c0a0e0c03071b05121333090b0c010c14040614091305131205090f040e070305120a26040b06060f0d0605150a17270105 62
    0x42181c41f020b1840d40c83c80c14038994503041d50380e40020181080040c00340c50041d52081c804140d01d000300701034680340d61100340c24400c502903c10112140040c06c83c0c24402503010b01c10180c43c1413081e03980d1602c8800811500c61b4600d00000c15054064410800b400b402400e1032401407840c1d43e040c1da5502032401d911802001c0c843e2190003c40d01006040c0044030103c3c040d10142e50094440000c407914003425213003280c104000069000d140c8095a50340150240185030103409840d00c00ca0454180c0c0c03074100d40c01203400d03042d0300402405000c071519690b00c42510710801e0358203aa00180d64425070304000c1c2084400d40020349548100c8545034400c508400043c160082541e0701c6440300608403038100d03070012544035440c035405200070104003c40c140500150300409c0050240307190085400d41c9500301d4003c2640461a00e58855080140b41003150017450b506000704051031400403411009411070404044480c0c0c1c22811070f0000d000d80b4004030703040124180b80d51820030703206080701700d15000c0e01c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 271802589 1250 271801339 271801363
    0xe01050a0e0f1009210f030c32040806040b10060e09010e070905121f0608120a050918060123220f0603091a06061e09090702 55
    0x8036103500da039140000402c2600e030086000d80504107070744103012400f0182002d5007051341c4501003590401c00030150601c0f110019103140e2a104c0c0043d13400d5402404603100c400c01d079002d000000c1007484e07104003c940c1c8200203c1c441500c40b40c0c3c4964400e4681c50324019500f0060790ba124202c240404d00120081240c412280b0310715400d42107884250840d080054481d8454100c02d90000500000c40b1240d0001d51245c0c43e4541849410761303031030000b40304101154180712943c0100c0c81c2103141168860004119103191042801824908152165500c4202c0c100400300e80780440c003001c44034407507001c99440400040040b00319822029619080d250143d6500d80131420b4184440500580c00192010700182e0000341e500740038102c001e01c0340c415956418564415002480410318000c0d906581c0003410155900140c03141d0f0302d282284c8280140d0303245803020141d04003000003a81d00c05080b250030021003085a4103208075011040194001c4241c0c6070380c82580345080291065000441d250040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 271803839 1250 271802589 271802591
    0x20703050303100f08010605030607030504051c08180109080d020a171006030509160510020c061803121305100302070b040303050f0c0909010506070c0b0a030c0905100215060604090e01050a 83
    0x117a980e030400f422100c07a0720800780c01d90806400659060300941c0b01c0c0d41c4c018001c1e019103000c403203007070040c5540c1d00d4141e5501000c20005014031180c1e002c3e00071f1682540d085080208401c55803910744035100e00070003110484c00b60300068552941c07885801000900c45200007198a1418842225070700500c0900900700000e280038001159480f000480e0040340a45400c0a145181450188502d1996698803032082d0711070007107205016110100185030031030420818507a104d442004142c02d003c60707100e036440360513018032a003100220480f50300b5040365800c48070001c00368400b2100381d010303005d000e2015140881c103408201c180340c1c15401007407041c500d09500c00c43d2a0780c0c041e0300080c030340205e90642c0d40000c0c4117001813003203042c00802800503070b007d5181c0e01c2c2095500c60807403003581e0200c03465000207038603645581415034205130040007404040b615034540c0c000c0030030025518541c2c580c891900404800206816440b444220380103081c808100f4400c4800311000d4a001e40720507507920a8607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 271805089 1250 271803839 271803869
    0x308030a0e030f120c07030522080a0506010305192301151401020d030219050706020d05130c080303070e010e040b100c15060b03060d03030e0613061a061902070305030310 75
    0x46054517089500c4107034103885543c01e081c01d80034203c8160301d28004030000200001c20120340c10400300001e41c01c40d48200d00905040d03045280050815a60302c81a45005405110020000d40506400c001400c0007190008890354089152405020310b40e03c1d203d1410210840811814400041c5500c210301c00c2e000c0344d0707102082c000c08604a114246510b02d12152a903c00c0001c14410f000130700300c5d68040d4030050b0401101c6c4026000301d800503101d811007120070200d404100701c07003111000c005001c040042d50851406181c040c0004820a04060400800051182c40343e0303965031000359402c40282001000150002d000381c080c09103004292118240c260f0303040407011180c018031050310070020b08241135480d02e90130b00010001c010400c030181a01c038941c1d4101e002080011030302c11a14940307030700088859405e2200403541501072010360f28014a440030855115401102d44a403803203c003900640c035032988100c0c2401c1060700020014000002486000c000d640001010785003040126028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 271806339 1250 271805089 271805101
    0xb010804030f0c02011808030702090702030304051e0307060c0203031f030c031221050f09010b0a06050f2209060b070308012709060e0601060e09010308030a0e030f12 73
    0x25021044400900082c0c0454180744014440c07075540c455184103040c045207424030200e1400e20359619070400a12030713102003402d200390320305504680c0e046007003030014616604140d00c2d0150bc90000b4600c05015000741e84e40c3c07001d6804100112998540c10503c00c2007400040707540203460fa801030702c20420441c030584080c0d400700d04102d02c02c0308903540540d0030494036195a13503203c454030412410b0f90030705c851084688800003240700041840c8810b1070001410389000403000004000181809609030700d4204120400d441c0c014140041c0c809a06003c1d4840214080d515064030034520341280e00c41d204844600d440032045402d100380e409902007031084540ba5020484140140380000e000598040300401500340d0380e1a046125141d0000d400716400c0328400740e101a60f10007901101e125a440340390842c41181031200074090060f51802e650340184000c005a02504180130180008000001040215800364000e183c181128404c0d607445028a403504001e9420056030251080820340010f030b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 271807589 1250 271806339 271806347
    0xe03060f24090f0a0209120109031403011514130f050f01110706030e0a0606030b0f0f07091406090405010308031e010f030f030c0213020c0c060f0703111207060c030b01 74
    0x700c0801a00148440d80c540c01603603103031040502282e02c2540c0c2006682016240c24a610b243c18060100120300310076245401009013914845c4524907842c14070040c08950800701448081400034a806120842c4c5001ea44106210341012000f02406000001600c3d420284410045070021141c0700c07400d0b10b4800c01902e010420000310800c541080300700b0b10110b8081c4c0d1084440719244003c0380c4540301d035982c80408460702900186c403406c02e0079007000854040c500500390302c400384150109035810704040c064001c0e90070b8020003500034101480d2a1098990006035050440006c106000650b5641440c010a51055411401c0a0408030108003a400550412030403112200c003214130080c516250f006400c8962030040f002c00c42a5000c4401680e542e08069040600450f00103a407000201041843c0c01c640c4040180140e1007030000d0400400041e05540c40160141807441480c100550003504214100d16889881000490710009012040e8010380b0103400c1a1020803880540e200103603 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 271808839 1250 271807589 271807651
    0x608010e1b0307061b170309061b0405041805060a060510030204031a090f0f0d1211070605040f05030f070201030b0405060307090e12160303060e0103080702040b010e03060f 76
    0x142c05a00c07054040040350b01c200d0080114100341451074102c080503a4845543d0380d04408501c441300008414401d00f0001442860381200c030b0002e100d1080d208180091000380140d00c980c82c807460341d80788401c0c00c50508040110283d0380c0001075481c1c900d80602111300a02d0309014181c0502e03c500e03182c0141900a01c00c68003a01d80101c481e2111070600000c0c0d41070750b44006c0c07900c030690140c01d211403c801003c01020b0303d6008907001070f0001e80104074008180742001c00c0001c251a00f4801d00604400c4030508039001c06030080404030f03d642d628280458a2400058010a6840f0005400480221450192100c24800d980c107002a500d1002040180d5030190b80703040c0c1c942c100134010841030790b255001010302d0410000b91a468a009480040ca0390084c10011408000c0c0c0c8001900309a811300ca0240a4044400704c0900c650454558411718090100024040d41e900c080e6070000e68043c00c410301000718010b04a030994a010098008008000c0d1820741d074074840e1144219490381504090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 271810089 1250 271808839 271808893
    0x191d0124030b0403030e030c0714180606070809030a0807020103150308030a0e0c0a062d08010314030412062f1c0b060708070c060815040510090608010e 67
    0xc0203099040d500ca00302c00030b0000d0011828565035a21241c960a000e20140683d20301503400b4114491070295441c26070f0322200140c83c0b1070160105192a2424030f0010340b03800403801c6c0e503142e455003c10702d840b00d414840d22030060741c584500d00c1c05508011900c002000c2c420710030b0780c05204c0541031007245000c103401c41c00300070b00008043c00086c4590a2a9001170100c802507070440c0c0b00b450800b4003064800324180c000c040050b00f0311040022078100180200d01440c0d05c00a28003801c11102ca00a14070f84042c0002844c2400d40c030013100200000b0416200a003034114007044895041c0c0c90903000800400c903403c99600b680020b003480240c0102144203582030342c010803528004003503542440c000070010042625030750310103e070107564a801002d0442c441c89422441d0b529811800d01a0360410903038482c90820510004002c800c2c8504a0090f610950644001c035030368441226200b100c4640760441c2c0c08030340c508980021b00c40015004441004505001d0328514140aa10101c0c105280250 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 271811339 1250 271810089 271810151
    0x170708030f0a080a0b10020304050306090a0203120d0207060609091101030510060e0303040b0d0c110604170c030c010f150e011a1b0a0606030309050907020703030305191d01 76
    0x42c0c8141c0c14040c5038030551000b54070000042c1032403480700081800012681d0440103900204040c03000e41000c10500b1303048a0010001c00c409841d42e40040c3c0d48915840107102d00d400041541d01104035150180c6010503400201841110b40711900c0100620ba00002a0b07034200901c00e11101d00d500a2050078000c1c0202d030310300032415050001c141c0c4c08482d12400319416100820002616480c24405410000c1c070700c2d14089156082c0c1180103000307091002d521111a04181c05120010b010080c8105074621900c0303503540c65442041003641075000d425460b1069508105140d00d451324940d1001d0400d0780c0380c01d12000e10342c0d21020030f0780c1b41100c02d01540c400c520550324840320103807102c00a81040341c0c1540d0390861030104070f14114185910040d04644c000e0300c40205000f01a08011000c014043c1514112010320348076200035a1a4800d100c003074141603039100426802c4410110f118001182008284104240e00d841c85d580f0302130030b0101e02d03029441d00c08000d848560300b80c240100d006030707008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 271812589 1250 271811339 271811347
    0x5040c09151a040b0409060f15020a020f210a020307060201020a0903170708041215020f0313060b030a0b0108060705040305030d020a02031c0227010f03110f04170708030f 75
    0x41d81d40c1841001d100b0300c6007a0303802e000015110021000031300c041d006105020031614070300310b03222204d1496600010342400d0400a10010a9400104802d20a80403200380325040c5021001c42e0354130b0040050700002c155218a01c5480340342c0000e052080d40e2003a01259a07056603550b04a080340611444400040c042030010004903800424080d0f045000102c0c0c1494142a55203410140d40564070900d407644412910300e05100d034021aa441280003440d066140a501142000807813000601e104025038151641509000c015801200030000107000c0fa1608947d0303042c03401110500344a102d08034030500000505451042d000d42d8200c0e98080021802d00100804131406500b241d8860811880240a8050000b060240c0d11501c002c040d0001a81d4a404a40d4181c458044000700c2c04440c01140c0301c1010399a0000e60b81510070b04070301e00000c0030b803154009230302c407442580d014195012002c140495508120b5101d0a24030f0a6401112001d44d0351b4400691203000b044405046c01500384 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 271813839 1250 271812589 271812599
    0xd051c02071202010c1703011514030c03130c030204020a020c040f1406010f0e0910142413030b07030b1903020d08161b080d0c020a09021c090605040c0915 68
    0xe001c540024882d80c0c1e030101200c2c4c85ca40c82001030304240d0201c03804100d06018000c0e27071a04030745d660b03d13141c909414491443c03a04580b070103101d1001030450403d0302e2041040c0c0302400340c101d04260143d68010000e65035030100312002962603012440080c03241e850300c80003103d030070721078814000c0c006c1013140303c81410b41c1c5103070064620840e21180c00e01800444071030b03521650f80d0005c2143c81100e514402c011102c0c03c0c00d42344095068800c12041c0104580d28810300e0414141889e0039065071000042d40d0b5940e009958600f4120041e840102a00040f00c00c0c801e040750503800079001c8501c2514041d400511000d0301c218150000d100203074010f89511800d10104410340003c103024828400031140050107640c407803810075000304540116012a107400e118601c000d00c103003c000e6030704c1c0c940454202d02d1600055048800c42c410a65140c1d1300003001c050980710341e552903403429115074042024507810704204004c0c03c42142e0032100c2041440001c2040c003403030711a0b6101001441c0c40300390070500f01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 271815089 1250 271813839 271813847
    0xc151b03042001050d1404060f0b0d14030f030408070b090304030b06041a031603110a05061b01180506040c061419050f0406120b0103110f03040602090d051c0207120201 74
    0x1010715040200c10000d541300d800b860f000c6c0310b0103c18150403c158034940b40c01d064040710503022040b161b42c3d0801900320780a5450140403a0415007101141c964138095065041c13840c440d2200b83c0b01e0b40e00001c4200800c1c07100c55409451120b02134a0444072607690401c510b82c4900c1240401090240d801010030400d05142d1b10240c02c5078ac7d0100040307032503044000064a090886c641090356401d0707120f400c1c0104111794105010114003035400c0d8250074141030004200d0302806081403a603070400c120510a058094000c0c01500b0105150071840c010241070054030f80750f040300c0c280d450034102040040d41c5842a0740c40c5c07200140b2103107454140480d0100e60710719401e1030203c180400c1828001d0b032840c140711400400080415848109280582d15401d000341c840140126040c145440c04003441c4008160403111620700c0c038a40b10396a0340e078514000e0024040d9040050f00260616800001c200c0e00048a41d420844942070510b842102d40c4126619511400741000310030003910408015406 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 271816339 1250 271815089 271815143
    0x1912030f0b040207150b1c17090a0602070e070203091804050109050316022107030b07090305070f090f2007080906120403140301030503030c0a050c151b0304 69
    0x2000c00302144440500c0001801c1c1d0300101381c25504210000c0302411a4078a5200d032102e00b400643c0c0d254600c0c0c401b40c080182048000c18041d03c4c0340c550322030340d80844011380b00303c40322480010718052895454180080d940d000354047d04000e5543c1002082c00c0314000819070309081d100401051001001c2c01c2c103440320b8540a130080340c3c0d0f90348502601e000240b041c03020f002d0721221030015506580160042007031041d290004414140c6a07000c0c5010130324400b003440740641c0e802010811180c0c444200880e0b6081640d40042e00c40c0c05086004182041c60005010441c0ca4111061010054118640003140c0480b04201444041c0f507a2411410348030780c014000c80740c02924810f0604c032040c0c0100380c1513484000000210404081000101604440640c850f075842c654918259070640c0d03110742c3e4910014024044413440811412052441903080310b1804600c08140e0345a407a0641800402c4041520380030350407562510018000c10040c410381744500d03000107140034034492500e00c901c01046 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 271817589 1250 271816339 271816361
    0x5040e01060306121226100b030f04060b1203040b0310080c0a03150b120705150c0303060103050411120d020105070c150b0d020a14010f09050d03080702030c0f030408191203 76
    0x190a00390001b400420245801645d080a20122180c9031024181c4640d51898000905030f5000348180249070144820b103550195111400003521084c2c0d42c0011100d5408542602040c0300014010a250160b0809540220040000492956200c4c242140c54001c0e66094980040701c8100404c00f1131030032030000481c1d0161040016604060740045648400413001c1c0d008540c0c800c4d8006c000c00e0500005025218035024092030901600016445d01c91101805050425881d2000300b01400741c002d10280c0e1801008101d110b01802155180c1d4907088920f40110241d440d00e030008000a00400280d986c080d4804094200c4030240c80701c460080400f82ea81e02d070443c8910070010010b8550045c3c0c2c03070107007040c6150661401c1490000500411600306030004002c031066080040e503c4030030100e55080d505041801c156580c00030101c2c0365004001500001e841501d540d8036882401000a0040d40d4002040c0d270500404940036031424566a50004d0020a21519400304644250300070759000b5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 271818839 1250 271817589 271817597
    0x2030a1205090d050102040f050d02010903060c09050402190e010503070f0305101208030f01121113090b1e0a111c060503150f090f0c040b04180305040e010603061212 73
    0x102d00c0b40480c090030307185102100c19a50000d0240f048683e5200c0c0803005040484400500c5011a07000815446d0640700c01482c1039102c10660303070414003601c8454003418000c0d20444d2120307045454002ca03280d442c00980302240501415145c41c0d4480e0040328800e15540e12038500e41400070004a004020040151090030310f40700e8040760899101e10141c000074040c843d001d8403400e180075030f110b85003070680c80300424562100d20b0b403000802d42e204184080104032048500390100d201c1d8800a094003236001811440080100401c2d030684c910302022030514010030f030541d0b5440d141c040c000c9407141c0f180d0010404061010f4441c20700c0014085c0324844410b5030208040d035803500860300d001360b4819000e9000200c8810044050050303107105a1002c0342d03000809400c10510710054480c800c0708400760181e0703121100b0100c0da8030380350080304030f603d80c185680e5403041d00c1e0304004041c2d4025018582100780800300000301d1030310a0203594240c990f00c80300034680026540c2c0e8460701e0b000328503402c0c00340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 271820089 1250 271818839 271818847
    0xe0112110d02030414010b0d15090f08031006050906090d02030a050d0905040c02010c1d040b090a02070201140705071503110c0f010e03130e1f06021506010c02030a1205 74
    0x240021000d40103030707400100702680300d0030b0616200c0b0490b4010016500141c1c546581460150780d0b0300101c920690300f040c0c55407c04c039003000100000c0c048040d0060000081402e8413800c001182d8001d510078810120071500c4941c861344100c03554801c0d1076442c2d61040307081c02510024502002e8920219100400b220501282d0f66922410166032043d0780340070510142041141d03003001d009202c414006880200061810818040c000c481c4480c227420f00c071040c000f40c0111988036648240e10655009180380d60b04c1c9010000e0030040d5028a070203c0c0010b032600f08103e8100c6582d41507941c00c13940603000d00385045c00c044140d0702c03022188906404158644020101341440c2d98011300f4503619160180c0f00348003e00c0d14150a590f40d00884554550040114400d50565205210b098503292880641961514100d10030065445c2c0105841105c0d070000009400d500043e0f860304840c0f6030610005039644400041d1510461042c003c3d4054028511324030004040303000c14070403008181411410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 271821339 1250 271820089 271820111
    0xf0a17010e0a0b0403091530021803070f05090103080a0201020904020d0c140a0e0103091103070e040b010f140415080601081e0d02190501061806150f0e0112 69
    0x2910820b0b8400f5100c0c207144074240401e25503c1000803001c1d140a45003254050b094460050015150071001e00c4041c2d400d2804ca1490742c0703000c50707203404260400307402d54492031207980103a488607850704030030300c203216818002070f080000b0340b40f290454030010301a44140e8031756110413501d580007180d01c00465600700b001c1c400f6903503123102410f542902d0020006044815400c0a05042202c140310b056604091181c414142e500c0958810001c0d001e10340070030404840c4c60a2104820503002c0e89916001c1d01d64082030440c643c1c4426446140201c42000940c0d90f42e8610341d800313842e28021605501c0e02e0f035014039050f08080d0072191901084941704140c09648015445c1014801c0c0c01c00940380c1c004201d48030083d802c400e0a1140d0b03803614009803181800024020b1340e20f01c0701001d07500008181044c88424050300f98495001040310b8200420030490760b00781d8000401260045402d140350704205040210300c0340d101d452400c50180c4030700c00494281001954250b400507803041034940c8540703190031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 271822589 1250 271821339 271821343
    0xb0d020f191a03010801140906070c0c05041b08150102030d0b0d060509030408010b01020c0319050a080a05130806060f010503060d0206041203030501171536010b0f0a17010e 76
    0x401600480550f600ca5040071415800c0d900d410101c2117800005100b03001000c074000c110b8982103000380c20719840311315441c5008200451aa0710140c0c3c000e01d07280382a91401d00300c01101c286d0b034140303030754600036580c8100a2a11486c601ca21840c01640240b0140b805c0003610380c030060b03a0110040c81c1607101013040e912003042d1903080360030380400d800c0400c00b049401c2e424098000b5044003400606608003005010a607601c101c90741001511402c01c3c180d00c02d00005000d5aa8203580103001f8581d902462a4082c00c1907000041240409000980004811300d000c50400e000300c2c03000f403a070b40406c00c8070001100c441d04082c5c48103034800882d07890100181d0b0b034900140300400c1c2c2c401c1c03940100c020070304000d401c503801603110241a8030058520340c80480e01160b000c442c4c21300c1c041c0482c4580c903000d241e0340e1502caa52810013900e10725140021100321100070940c11044411000303204c031307290b40cc00788003640040501641e009808180184014085071032084000c0b030700c1100011f5000240f00b1554 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 271823839 1250 271822589 271822619
    0x1e050f04180606080106090806151207060e09072f07050414040215070f12030b220f0c02031c0902090106081504020f030610111e010b0d020f19 63
    0xc00980d6441d0100291604a0f0044c1c1c0181600d00300428410301d808a085e889590003046490080340d0203400c07520320350301d4000d140a0700052800301e4190baa10381602810b2700c1401900f0b648a21408400100c0b13191049007210b810700d400340c5540030b02c0901c5c01061310003100018000c00c81030013000800328aa48a030320521254142d5403400864505090040c400340d00718004c028140c0003010894100420701400c6031100041d88039000441c81501d50f042100101603640c2d1090740511038030300c040b44400040050075420042c0c0c3c1300420070030001030b80b003c0444051803004005a00280f14600e151541d0f0360008004c40500320011642c90301d69400220841001d0300f1000205038170105016000135020a42c04004c0d209440440c034090440c2c034000c0003800000c10052281c2902120742d40001d1154841003d215000011290803420740511006c090105101c0d40340551b10b4540d00000900d4051040480d10340c024080e40b604500240521005003400d2280d20a074031489900045c2c0d10000401036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 271825089 1250 271823839 271823879
    0x40b03190f18030e0a0816240504030b04030306080102030109020307020607020a021e03030c070801050916030201080609060409060c020d0e0913020405100803160b090a20030c0904050303161e050f04 87
    0x800c2c002c6040c004200c228108d110f031460040314180f5542c06c85585c2150449060326003182d41d031940c2d507a40c0d2504901510090300540a554008400007502e90384a0300950b0003440350741c0903201960340da64022139444c40603c0d070107035006854150460441e4032640044a0b000da0181c2500d2808050700542ca14085580e07000340c072245c0d500c0c020800c1e03140040c4942c42020031200442e840591a5800091003100007030482440f42c616000460030f00d540e1030b03100e4440c0d00e501060901a662944001035203518654210001083c00700307000304090320305034044c80c0c80350f80c0782d00240c0720b60031031602408020040180960070300c0c4140300012440210401c05071551b0041880b001041c90994074000403c828040d0081d81254001603021002514003209281843e4002c40e030071070320358640300000340b03411003114440d5006089201030109001000c0003c2d48034006c8104845052490030004880002c40b200062031a8650458042c110511402c01130824001140c1c0d2541882c0d00c072218084014030913010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 271826339 1250 271825089 271825123
    0x910051020060106020c0619051b0a03020610080109020d120c17090a091a12101d010608060f0f060d080a0c0b06040219050f040b03190f18030e0a08 65
    0x1000ba96a041100da02c1c1b140d000d6800038182000e508916610848400251b01070003000b00b1700104580e03c14658804c07028422080350382e041d0036810043e4455600350b444505000400d00d0204080d001409850115540030b0840711a0100c5138840e00008182000d81e0700411000b4200c01d408940e0600f1424030203510343c41803a5441454000b00306800c02140e1100758120304184840708d840705040d03400c44d00c500055a207940c04150714520541485003a00303582c55000d2a01d002441c080c10707031020f02c29041c0c0241000b080125140c1c20143c0d0303146012580200c0110684001800950410124680090004e4910300a000040c0c1e100038041d0050090400010103400900741448080e400154000f03009541c03c52070a010000c0c02e01340d203140048580c05005000403480f95600750303103084800510114500d103480e414244008103100090340e44480342c113418151100505901c0d0300c2000d144250084044081c15070300e82c1d09844800d029006141e218001000c0003440103010b100010101c0c1207004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 271827589 1250 271826339 271826341
    0x50d0219060206090d03050f1305210702010e0301150605130b0d05040209180c1011061003051b0d06051e0c0d06080708060c030919030e0f091005102006 67
    0x14040f0300e000e82641ca800201030901c402d102c242307614080b10a8002000041030401d0711594180b0a02c0d025800503510b0000c0d02071128004800000e802414005100b683c82848000ca20004c00d4261024244480641c01c071242c420090075006400904003408442c0c0207207206a82d03500207090350f070031020000c4082501c400c10041103103064080c0b19070200f00d10005941c0d5004045031150340c1d0711580c0300c80b4000c013100c64a0707071030716802540c1c506503440d42c80e01103c55030b140542d0101d10368102481700311410301c1a2900c1c10b8150303140c8001b030303010008050116080c0740d0030741d2191400340c040034003c00c00d50a0059000001b03c04e1645009200e0055820002d9507010150b1901d411a603903584520790a800508060055040215400e030b00406551781060b12600d411907405d0611403500c191040e09002c8400c0c9104245d0441c2407070a5448085506411300b17010141880b81c0e480085408114030024020280500c0c54452142c10108480b4901449200310074000d4091808110880c0415684060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 271828839 1250 271827589 271827601
    0x907111207030818070b030901090b090d02011b0e0d11060724060506180a080706180e0106170c1c021c0b0a030f05161403060718050d0219060206 64
    0x30083ca03400504503240e04105068030765405841e6901c500529034000d40000c0880e458040035004460520380150907030740c07541003803a0107079900c103510410b003400341d401e0102d602c010045500c4088071a2031765844042001d0289402c002c1403140c0c4032003c41d00340709100451420798035010042c251941c1b00e00b0407507164009a00c1c5168a4040e0810100e070050b0030408140841d884000c16039040d005440041070b402c005100c0082c140c1d210384c0d00b01820074420003000041d00c590101031485626040450244043c3c1c4400c00780e20348610900404000c55040c07a0710020350b95040703117010761042c4441145400c106540c0715034840b0301140403003144800c1e004205110312032a07828107214200320b0410f0411944400a011a4000c840c40c40050800f0760486440014000c05100006004600341180740d01c060303c0d00f00401184441d0064179002c3e01c15580095100b03402520705401500613491544880c5142004200e0161031600c03040360004030005000b03103080340040441d0007501054000d481320345045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 271830089 1250 271828839 271828847
    0x303060905090a0807060e250501080103030e01050a030e1f0b0f180403020f1c030b121c05040f090e10090c1a070212010e0d02011406090711120703 65
    0x68000c9980c052804040c0070005000003440704070030b5070040c041c1c0e40b00c0140b402e201004081d40c1039105468016040707505c180b403c408a160710013010b4910803212290b00c0d00300442e1110303002d00005000c81d40e000d8241400d580100e014050201da9813401061003422481150f05100e010411b840410301c0710b03455210a0740983c0074400d5140c01c150f503a965420038200c00034000190400c0076a50b862000750100303043c03504c01d004c068403050248045030030069510125a000d07038032506030b0000203441c0c820303000f919141038070042400c80000d030000c021151040081140d139007122504d80060240401000a10700032000c1164000c00382c0c0240043c8103020210401c1c1000100a500029a1b1814545500140302c00e80c0100907500710440030354000791b45980140052141e01c0011350702000c001400764806030150000b5406145040650f840642c402c40c0076403e84000e00e100d0540501c0f40e10000f101420324070b04450f8042a10300e40321010300e144090ba103041c51406810300003141d40004020b001e050304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 271831339 1250 271830089 271830101
    0x302030408010e0f060412120501120b15030c13090b040b010303080601020f070e0606040b03041407060e011d030a02060c07090b10020a0b251112070308040b04020103270303 76
    0x41c1d4090113400040c889115141c1000503c0185081c441c008150603041c81581183c0212105100800c0b031942c6036040071210355594401201c40007607020000c0c100024140204580b4280603005200c0b440c1c0080401c0920407400c4191101290742e007420401085100c1941800b85025602c0f01e8065415070800070682e2100030a220705560082c10004c0c014140001e42104a0781d05821013050350301d41c40001a03913880749034015401140c01009000601080c004c14480c0501e0100031103c081e40d0321003083c0c80c11810700c01603034042803c100184c08050081c00c0f00301440b00f001802d61305045480e6002401c582c100d815400d1007927228940074000c1c3d071854460703080e20301c0d4203c1754601d140f94180f000a560b641003080050511940b600464801e9070030503e90342c00710480100424040860100050501e180e07000c1c00c003814400e003458020000980811117010701d03095030f01c42c00031b9500d0b80c807844164900588228101070b520310000c0900c036600c00e102c4251840320419400980ca80342401801c0d112 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 271832589 1250 271831339 271831361
    0x10c03060506030117071208120901050709090506180709060e1c03110a0203030a050901090b16030c110607030f0e0108010f1203030209040606020705180606160816030203040801 78
    0x3180020600140da1040240c030304450062514000e41031000b46410f017042071645c0952990019400d200301040101005003001c0300780d0984501c41c40d9185400366090b00c4050365460003080202038103021030041a0001c0340e0180c0d010784039070031000c40c150741c507003c54004842c0e810015003404d0003480840d038804d0758581c0f1709104560301500d0542ca8540d5802850f030507035005050029564020818150910410704015001000c1c0da446000640001d401e40c3c1c00620064000f44000e640490101d45140941d09420302000ca2044144041d940a9500032a11030301514100883e0460180c144d0300d0000404250f0320035a20922070180f200009000e520035580c4007070510069500602010f11815036940c215125540403003129082c03030030168000e100c1c40782001d801a04010020400390b0f000165241159030a5030551f0389000c15010581052400380d44040d80110200940320340d00035100040c81c1c1c000d0051003800d150412401d015442c1c158120001c4000d038001080c00c106210b002e1041e03050340c103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 271833839 1250 271832589 271832591
    0xe0709020301051507020f0a09051608040c0b07030507142a240d110909240103052706040b180a0f0302070e010e090c01111525080405010c03 62
    0x941030400144d0b044540d02c1c2c40204403980800e40781d095640c1c0204c150f804400261401d82d02e82e440e040803101600d01124003442144030740184101a91051078194403840e00000200c1d45a03040c042070440700d0340300000650030404244407040c04105115046002001164000c0003420f4096005401c56038000d258110441030100d9032241d652076076051000c0c44000c501e1860040d400e800c2030200385008000d00c04903224507082400080760080401443c00e01d0084956010030f82d6030710040d0500d14030100e8020715400c00d00301031442139400307504800c1c1c21000c41d000b5070f20a0311600079a00c4102d442c080031a0400e90200e0180301c180604400ca054128401401030181140040c886e02e59601c01b041d000dc1c80300582caa00d10003403520900070100501501d0181c0e10309940d441c003042600c41401d4812411b02e028801c0340040660088c80e241d1081d0021001401304000c0d0710241948030040100800040e0340141700300c3c04d20314480884004026001d0325503070510305083c1030090844410801c080245 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 271835089 1250 271833839 271833841
    0x70e09060901140f030102160f0b060d050706030507091221050c03040b030a0906051014100906030506030a14161502060c0a0c061d010c21020d0209030703060e07090203 74
    0x7800f245000080550340e442d00311401302c01083c024851091200c0480780755528079010020b480009190703a500805407406240c544034104000d21009440041081e0b115580401271180a43c100c1c0e548403015061400d4402c0e5213030422011030340300041c202c07102020b441c3c003043c0c000d01c010b039a0b191107512407030400c0c00e0140c082e02a1b50341748501e02505440c2c80c80440020b61080c4071360088080e1503444903060181d414100300c00c1c6220f061901410b02810a10391030303250300f41420f01220010042640da40c4107a03c0c40c0c500150010f0402400042e014011300b04620042051386c420744054100b80c000030114661060800074001030b072030708a0303031452008100304030b50264001219a04202e20307480d456501c264402c410345814448800c010412414a81041358003034090303184030a4403600c0d100901007407500042c04c0b100041c41400da0045a05840c800b0030b4044801c1d405840312a5040c000140340041080c0060b140c03119550007150b6040e154000b1a001503400d01500c0000c0602420950071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 271836339 1250 271835089 271835099
    0x16030317101202030c040905010c020607030b060301030f02030f010606090f081204210c03050705041d0a110102010e120d1401120303020306181302030c010f0c02101106070e09060901 80
    0x200140c810728048030600b0159100350755050000c2e202d41d4600400c10084000b042c98114085d00c5401154000b60103880c0019100e54043d0203905600b076030003000613103140e0030f666035680085922041641c04d40f0501000c480410400d2290001501c2d0030786800400c070749003030346000c0d00551a80005071650044c500300c0424082da90281d07001e445200e000c802c0300711142107034a00c10400b81c82c000342c0110300e0a00000140f20000c16070b102a03503016242405015201c41154144250804c12914070350300080701600071030000c08020544c10014400494500b2050f20340d546006207008172962901d100040c070001c0d0305154070419260b014111080c030302d50b62500f082c4c2e2869080903030001e07051580010000754640e54006007546803002401200c0d070103050041c401018410f021804901a10800416514543c0a0091403400c04407a60f20302c00584082da09102c4011108a20000bc0c01050340c0c118801e41014028280302c0d86c02640c0e1509404140c104103e400300c405031030b684c05003002c5001445 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 271837589 1250 271836339 271836361
    0x60c0906030c161a0702011d1c020c0409052808040909031202030f04030908010501080c060c071212030f06180c170a02071a06061c09020316030317 65
    0x5403048501da103107502c803c9103a451465400183c000184550980c84441d40c40704003044640c0e000f07515683c020450308902a0300c4da0176080542c001c8041903030085d03100102c00d6094030760100e4101514810340c0c5031000000c02041c00d40382c130b10400721419003024030350145484003200040720051103249c40c40c03a854a142c451542c1e5201d28066420360315110400c21b014103001701481075608080620455991620740c01c200d04084081d5402c400141000c4000203122205000b0f090689042c0c4d0041d00c1800504020406554040c401c003010a01400b2000996100540da40030b640b1401279440140000d1801c00040c1141e03e40d5590005091815805001070000000306551182c40c141c80010300080e072441c1907412208030401d80c03906040d42c0c0100036015040781c0180c54298030400c00c8124007050780303044d407a420740203c070001e400140a2110100e0100b04100142c0190304d58000015a0752041d0042810500780d54000e0b40c62102001082040540c40103410000f814104914015800c2103c0a40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 271838839 1250 271837589 271837591
    0x516110604020d0f080f0f030a150f0b07020a030c09051b0c0a0305071401050705091801030b04020420070807020a12020a0e1807080c0901050d0321090b0a0608060c090603 75
    0x303405001c00c013003454100400d603011035041d130f407101d01d4181e2a41c180041b4240329601c21030b400314503d0700b407084051046021440c0c0c082507600181c019144c1600f0304d1004883e42c1c0181c18181c1e07000d61400c1001010801d6410b0110141102d0000452240741800c5141003400800d00b201c10400300030001100b510401280e001c0b0455414503041da560400c40c00c181138000b12100030400c0c5540391100b0300c00d03820341200092000d507605898146c1c04810601c540300c01c15009101c040c1450b5890760000f401890140d0100710040c0c58107014001e2281420031a540ca03800c090001c48200c03c00180301c00540c41c0c4142100010100c5411810000d44603501280c4d042c0b000b840f4440030b03c0410000300c0c4845030300890085074100c1a02c1150b100a41d0350620741d9680104800325409600600c0c00810b480c02d0181503030300681c0c3c050712a001807880d00f500810600002c00c03804400b0310783c0d81c140440010207040c440380c0151103505000c60b005081c26900c500b030410180916a46901c100291509500c890f4203072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 271840089 1250 271838839 271838843
    0x10804080a0e01030e0d02011a0a0305031b0304150305040b060a0b070605040501020d1109040608010513110411070b0402090603010e0a030c0507050a0b030f0a151e090516110604020d 80
    0x40d28101d0b48040040c3e01a210140242d01113001e40b0080d800c1302c80e415442a4984240840d0881d815001c10050041001d0b450001504641040150400b0801d01103892601000001c0132245081e0795854400c403080080f444400000761a2024030042c055030042c02604050200d498030076541c40d04030324100a104500d8010304081c0c454000070284007083d415242040020302d414050406000382d80351680d4030221805100710714040c00840e50150500c50581f2810008803803108040d2141c440002c211254061640e2207500c0302c9080c0c44030240704c40030b01507482c411502e006050525104103c1206001800240281e150a411140b41400080c4850f0f07035030340606045000084034101203051010a030003182e040081c0c0d4000080070780a920082d0710a898980c40b02d01e1903291442024165551500300002c608100300c1d05100000028000050000d4800384a040c1c10b5940e1600c0b00550742c0031903080704140014000d058074035401c01c803c0d03030712802d110020784920720745036000420b070710085900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 271841339 1250 271840089 271840097
    0x2a030914032a0a0506130305011d07030201140c070b0417010c050319060905010b09190b030a020d1509020c010e012a02030d0e03040501090e070c060218060c030d0b010804080a 77
    0x805001e9103c2d42c580340701900016100e00e68444c064003403203000344050720048815600c6c1072420080070f50b135030744998044050100036180ca81d20b540c0045036128104210703042515000c102a1302200c0d402c01c49400107041743d404807500c82d03141058a50358040c00d541c2e40a03899051070340c040c1641c1e07407010483e40c0c0b000c2044d00082812100126240c0140516041280c00078941000801c588101d40090b1896110444a03d50700300a204440760007245544100700000134140041681600c41340c000c1e0001c041c4031000010745000c0c0c0c6625100c075104030781c00503004e0381d4001103204260000b8042c901040715580c009005060040c1044031503141d54850000c203c0740f4801e14402c045200784202d8200051100c018860a584a202d0b203440b50700c24415540407804254000a01d10309144401c0d1058038180c440030b1681c03185449400203940805000368403460040c071300c803c160f503860025154000c0240c006544400401c95460211803001031154180040f10040000041c4082e0417a00d41c5281450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 271842589 1250 271841339 271841413
    0x70501080a02040806040b101d16030b190503011b080a020f0408070605040f050d030e0f01200102030108010e07050a060315051c0605060f01050a2a03091403 69
    0x501c540207004a4000b548140a801d0600c01400307a151495806000d0413034155605c15610400359240d004080c03210200400e00d100007400d9902c650700c0800d4580ba2504022a6078106640041c08510ba0180031048149102505000750708003440b0f44018483c08000441e03010900130b10141450308000c1c4040000350300002c0805c00c40d92542c0640f0003c5c6054030864200d01c0e00d030140034020790082d014268034101d0700e180006803841c0c06121018401e805841d041500c2c8041c1061101800445140c0e0f810b00141c001130b26240c0180300f800000a9450070b000503140e50600036840e080d02c54280c1e211095034000030051116584a880c103400310b66150800244801c1654042c1c00344074510340c8890303800b4402c0c44001f03030f04000e001e81803104144180403c2005031341364000c0110700d01c4101c003d40d0028805001000f0100e010781010b40d01144003102180b9003910b001c10700d510f20101000c0c03c40c006411030808000e02e11418940c0da81002c01100900341d41001030581c03800008041001c0700202814070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 271843839 1250 271842589 271842601
    0x304051804050f0f0a121407020607060e030a0c050609060124141c0f06030b0105120c0904050a12020c030d050d09050a210c08030a020702010216030c170f07050108 72
    0x300c42c182c0d015100080d0307413006400c042c1050700e4840c880c0090780c0701d080d0041960b017114811440140e08608002a00d82000f01a4003071200c41d8100038002c0f00d0f020f65032240c03c071140c0c000300301429039080103580c0c160baa1161858683e00b4564081c01400304c41e88000d00502420042c0d0b9940e001c03806031290000c1b20043d40090480d400020034008003104000003c0c10f2080054043c809101050f082d02c0c20b014910300041e0142c11a07031580f10103803491407100d005010a180104032b148020030388604440070f0f034564500180c000003003910101c0c0e00c1d911104001007000080c2d40300c0142c101b05070010b09550b070ba0070000b103038494200020352070401c140040d0b15100d59119034403118545070400c08403122003585180c030109860000035000e40d041d00701121201c20707034031600004044690003220641544c0b10180c146000e5089402c0c04c90550003140d400c036056641102581c8000c41c000e00490400030300d0604945030200c081001d070707103407900145a100c0c8103590004100e41110021303c1c2c4407038265112 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 271845089 1250 271843839 271843843
    0x18040218281d0f060d0809060c0712050d09081005040c17010c12091a04020103060512010c0801090504030e2806031e0902012102090a080d03050603030405180405 71
    0x7412914444040c8000c0410042c00c107584084440c46a030110303400c01d40740d50003520b05480c011190302d0740c0201d484280070006075200001d0248814040e01540c140362034001882c1c1420a01e4112810b11a4800031140501a0130400190034501340d0800c0c0300054100146181c440314280f0200c040d6030b071600080f404001000d000315009040b201031001d98010110101c5028280c0b2909401c00030f00111025031056140b8442c243c1100e80c000031021410004042d0f500b00d0040040c4141d041c150f48a80006003a111010b0a880130740b003942c0001441d00c0c101802404246042e045071501c20f01c2c00c4d08200000750080e801a41c1c0d14000c8a59003410f0189411180400161f40c00244030148400340c000340310750300750300318404a902d03140000318006e070580d500d20708031104110041c3c002164004015a40440798124510302101c1301d10252420710090b004c501c80101d03983c46031040b90b100034000206c81c0e60510605400440803000341d1715041c980800581c5c5204c41c1041e010a142440c0003240070442c2c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 271846339 1250 271845089 271845139
    0x303070c020d121206140303040608040519050709051f03240c0f0207081507122316080c0d020f0903061e09070e0c0702040b04090818040218 62
    0x100800741c08405801400c002c004c94010100d25540b2810408045a269212580c400c05040058001c500f490302d041421078560030041c109440900480016a06446100c41c403020080d010780d0003031103080e10b81503819086450040401e01741c01760018084200242039444103084a8014041c2101c400c0c01049226000501c0d1000e6614545404c05000e4060b40241601f201e2580356003c0d1000c8950f00d0321100d8480001c440780c1803a10800340002500a030007581c1000480c9001000003a00d024000b96129254503e03080071140b4000c0102080442e001010001c491003036940383c114410b040001c10000240140384030100d203e6000b08014500c0001078080d110701e040000c04640342401d04035000c01c0c01814155070300d4051040100050704402c030000b050022510000c00e80030705540c9444130520b1580040404076489a00c50208000590700c50181d0650780c3c2c0101d070015914201c0c0d024408002210b0500c6600079401072240d030716100e0588010b0b640c0d0380c1040c0c510360301c00201000e1294140320 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 271847589 1250 271846339 271846343
    0xd0f0215071101060e0c160516080102120703020a0c021513170609060408070605071b0303050f061c0609080c0303070201060602010b0a12030c020105130806060406090b01020303070c020d 82
    0xc09003040200d80340d8008403070038071148600e0082141d107407210b030300b01c103005800c88990741010320401444180c200000c00c0b0222290094042d591210595401007200207040e50280f50b0a81d0049110000100050358480d041021802c00f14a42507009101800340c011180019108081e84c4e03a2910c2a44001811503c11110300101c01c0d00186e181c08491601c1c0382d420020403040e2040c00700207501240006a01c40c000d540246407107007061140d60302c3c50085e00c1d00621764010800e001c0c0d0304c08400c51260340d80b110b415201f40c0700490350340341ca1660f81c004c07204001c2100d841280c04100100384081c04100301d805a82d044440891051443d00f0103101300d104e140c642d203203944400030030400059810760201c0c0c00c2d141258001d00071b51a014081002d0f189260045c00c06011000084c1c000090040410078400c0c2c0c810f040540c249128041c012580089a80c0900020f0700030104001461903c0d1240308042c24800300d0421801e10320a0000b5a80e02008001400f400090307500304080d590b540e4000c0390410313 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 271848839 1250 271847589 271847623
    0x1207090608030c01050709180b010903140a120912080d0b030f1c05090a0e041106030717010806010e01050d0501090206070f14060c03220506010b1308030c0d0f02 71
    0x41e65829107156a54072101c002111540b0f02030201e601c80340705015110448000004484e00c1c2449080c50070300400c0355034800d5050040aa071700100141c101c402c94842c059200e006000301d040d290510300b4031501181c0c010705c10413091580a0140c152900c0611841c00d401184580c1c40c1d0450580c0c01c4001c2101c1d00c440350380748c86004c40e42041ca041c00105118141c190071848603103001800825120b82c01004cd00c10392160450405006407840da002e184c0c9e00c140101c60418401c2a404049030884d881911144001002a010a500040e550510301d0040c03482d040141030541c54041d0400e0b0750181030003090310840d5041104070074020250002800c0540040001d90342d400a480d0541c4010b0380904121038800c4641c040a284020200340030b84100c61200030070740785582c1c804242a14240455a11043c54003414210010135010401c80c1d0180c582042101d03540c0041d03183d87c00b46c00034103900c0703a1259841008040c88800000c2520104005281881518510b04082c01e9081400e4102038500038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 271850089 1250 271848839 271848851
    0x5010908030f011a030403120c030f1506020f03090a03062d0f1a13051306020705060601171b0d0f020a0309060b04020a080402150c0615030d1d120709 66
    0x1d851002c0e003540c12144007034102d0140c440360fa180744100340400c5030042c000c1144044944000c2c0ca0907003100c002050949000030704286200342103c00c90701c05100803000d00041074028020340d1b404110b4101403008003802142001038200000c0c2050025010003455181c6030510f548400080300c411072001040e141e0809074501a0828000c0107119094500523110300301410b1100c0021050004d20300400c1c0580040b2030294041a1100034000c080c00d56400704641d1042880440c5240c400b810f4154840d6000d0001807c001e00014807074050140b14001000c240018401080400000c41251620340764096071251034000041c00146000090308403054000030305e0704016603040e446150440d10800041168408101c240000c90044c002c8240104152101182c090718048005452b41c55181802c02c1c604600d446800b400c1c1030f001c0d5200303608015040003604c040e24040c0051005c2c2c503140d03e400460700486807009165414509900c0c1e00821140b00d240125160511000c0e0203400e10710014400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 271851339 1250 271850089 271850101
    0x1a0f07030c020d120f050309061b090d0305090301060501081905092817030705090402160821060d03050d0b0d02041b020f01050606071b05031009060b0a060f05070501090803 76
    0x28130504c0d1040020410078070001402c0c091803d80b0302961105006100a40c0e5170343c0c072441c1c0d110040b00f4000910809100401071607564011400c140c5100750348450310b40c1e40207000d0500f501c001d80c1018ac1840301d0340b81040406800c0755054140b548031514045015160f4050550502c004c3e20100b43c10344a0102c181c035268005014200201031060503003804840c45000382140501050325494000341e400c00c10038029103403607000350880075220101c001000b4003a688064042c1d002c072002c40340054450000c0c00980340842e03841e039408501500c2c2c0100c4000aa81c1c010440c1c4140a41c20004541d500311014041d1200328840d2000b42d400740040140740da54141d07800104801c41c065000610525082c0b080082060003814000c0c0700140c034a034101441a5600806540071030200e00c03c0380e0300440c0018807554100304495440d56402c400103180d01d86400c0c118195000004040d0003040100070400280b40c1c0030004942010041c50b105480c3c080618045015090660018040364404401c0c482d07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 271852589 1250 271851339 271851353
    0x312250c09020a020c0d120e180906090d02010b03070527070e030c012a0201021002030c090f061603120221070201051b030601120f05070c05071a0f07030c020d 70
    0x100b000100d4084030111881d8504220325105141c00041c10b40407031400821f400380c0589500000d046c1e00a0115104d9003009540000c1c5800031200500980e01840500904c004107208080c039104491000740110710721080440d9961002d0b00c92a0f02032200000e842c0c0c0503170746070120128508003080d8450903074205010700074100032a20100ca40f00b406645074109440d1b010350365100d10000003100c0030340054030240f0307211030b00784124405a05500415030150442561480154070030140d4025450b29240c890082c03085448015407042c1c055581000002c40751440c0d06112405075526107441c1d840c4642541840d000b0b0b0007041c0034801041040003c405100351703021510f5104100350341c000c1105680d0421002801001403404a925034801c03c0468295481802e41c00858007282001041c010007090408040b207108484000001c1c141c00026003c1181c203102c130600401840a01c105540c200f5244030820b132060030038405100c00700189040c10140121080c44009030024450250241d0703e00b4444 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 271853839 1250 271852589 271852597
    0x2e09050c0a0b09090a020f0705070e1603050702030313050f0106060306030b06030a03121116050a050601150207060c14011409010609020a05090103050406091509060b0312250c0902 79
    0x25118000c1500c002c644581d00009541c0c9200005001a0294546080d000001c6d031100c111161001020440180403c108005440090142c102d6502c1c0780e2030403d0008003a1240c05034103004040c140010303c006a58004161703a00245482000c0821004501e011450880801002c1d0001c0d42040e00002d0f15680551042049078082c10720001150348100030036440701d00424000380840c02c41518800b00014a0388580708801801c825180342400e40b4030038070711558282030204d0b265408003024504000050260364010706017501d01c001d18020205001c0c1d262111401a00104050840e00030107002000c03c0101e40301000c503008200c0c0d18401188100e401070300b120080b50361340c200080001c1c1c80c030844c821640c01c0b402d42d0b036030035080c01203000044010b00800341c810303204940c40d0754822020845000250b0b4000311000700018010004d807030114261651003038214840d8101190202c1182c0f805422904410300c06054013031008802a4000c0b0340e1410f099010f401d0720705940b40440e0440e0b25134010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 271855089 1250 271853839 271853863
    0xe060d1205090319051c03060803030406060302120a1e03030603080c0303010807060903080d0509030d060b0a03150803030601030c1710060e09101503090f0b04020901050108092e0905 80
    0x90b500c20312810b46046140c00100000408640c841c0c80020206d48000d1500e8100f403045281c0862401c0d03035000c80c0c600c1e40d04140c40646119940e04c070b0070001c501d40b0030600901440000c01410b80c120094031240710352041080408091310134032102d0010544a68000e0b00659440304170240c03507044860030141e07039070003d000e400d45600c208000400c074103020341004001c0380d0344003254603c0c00c042e01719003001506010380130a440384028001c121640d110340c0281005408030007042da0b192018140020f007941c00c403481c01a01030136460024450040040116079008600307080c01f10f003450084604640715032542d5900c800d00b00d03013407081c88444c0c21070462120448901e0782d500340d1110004e2080001c604800c0d25a4000c03524920303400c000c0c1c0d42c0d140c00d0420403202c2600b07001448100c581ca4a44119854160403a14059807908000462602c01085070240900f8a0160b000c3d14060810a80d90728009450540340c038010303480300f96a00341a0f070061f1000040030b00144000300b041d2526039500c036200000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 271856339 1250 271855089 271855093
    0x60705010b0114070510110702120c011808071221020c01030f020a020307120302040b04030f02180115030b191d0105040e0309090408090901030b01170a0b010e060d12050903 76
    0x2d400c002410f21090315a80380e0003001424603120030080000c02001002494107038a101801030001598607100011840e0307034054003030409940e03001d00041c4103a55409095400c55102081030000190024101c816030b40a84954040300c1c686040c90b9030480c2c102a0600314035880c4000c4050313810f501180d4020b0503007013038038140f24400c405907280040c1d001e04400d810042c2d000b48840b40c003082d0386481c0001d00d500300382801480c042d202c040f024907903031003038009031240000c000d41402182030804000102c510800c0401c2d00c03d5061440b414215031100007541c0816407198403010311507031419002205030303030600300050505542c0d0008541414154a1504c4c1d18454000006207e00385402250b0b00c500b0042c02a5180544103010421a94005441540c000c3da080c88001e5140d150700c1c0e0720702c4c0610702803000c0199562420351220381003501d0348200940380c0c110304401d500080610003132906584039106841c250303648420105550076a07801002e090b5240e102585885190010b0007084420403e800b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 271857589 1250 271856339 271856357
    0xa0605030d051c1803210606021b030c0907140412060b090a0509071e0806070915091d0403020c0d060c140418020c1c030b01080a050609070f0e060705010b01 69
    0x8020380032154024440a04c0710304075850b15001911401c0e00604410100110031103c1003c484d60340200d418a400c00005a840701d083c0075100e03400840d044a405070300318018064031003001e0114400c0d1401402c03180038007200b161038406603522201518060004005030f01ca01e1101070404c44003070a10100c3c0c803400b60407040085841e545042c01003620a00e4020002e1007001c1c50078185650300000c02c03080900700d920290f80800d141c0b1050203000e001e54070503510000882c0c1441509100c40404021180034054140010007290840d1005d403060501d011140c07100300c0d562400e042c0c0c18007150341c1c4d41d60380c008840b0401da420040c4540c841d0501c1d0106030348545684a0320400e000462240e409030300d201d0040040c550590100d19001009105103139001c1e00c400d000e120103c0c0e9882190103114801098a5000c03032015568014800360307100840200c18452410301102141c8003c0010f00000100a06810f503410b89a020f100c3c41703001d00c400900410355a1503181001402404252021400155400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 271858839 1250 271857589 271857637
    0x1a100902210f070206041104090506010308031006020316080a0504030605040c140f03120a090506031009050a020a0e090901180f061d0622020a060203030703050117150a0605030d05 79
    0x10b0142c903c02e140c603030014003e5850380c0d00d5400c034428481c400160320035113a6018800244050041a000310b2140f41015240d08100c0035056074500c01d908550110351051050202058501746043d01540d000881c21740e440044002c02c13905881075410103403080b82800c050204002d810406001201c1e00504607503202080e034010040c90307407070300c0e01c405a050303110840d030495410b800001400b513115503051007030140741d4030400300710a034004030b0314841c005441900030090143c0324041c0300d034404070b00302086103055040c0c20040c04032004c41c03803020f00a50311840040e00009007540807000c004a981b54001340030740d2501d008140c580f2440c1040f40c0c1c45080c452080000600c6201e078034841e99030317407020740740c0c907900d03507204001000411302c440706901d0816901070050707200d800d0060003501c1e507580695500e00c0c010720003606036070041e0f0141407910314510401405900100312500c40c6c038481d406107401d40e00d42100841c09801280c000a61502aa000340c2c0407142c0c011000b4600c2c101c11203891a2402046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 271860089 1250 271858839 271858861
    0x906021b070b03010b0a0806040b0d0b0403090f030b070503150909010603111804080d0209061206030d0e03060711120c010618052203050c0105101a04031a10090221 72
    0x81c85844ca05c1c403000d100c0841018001d10900e070f070040e0003400024802081e040014851071301310f038055403204903100600c403c0c141d010000901a1440340303143e00031245150303540c060b01c0c10b0040c12035003006808800318241402c88282941c0d1100001e1040700f403400c00c2071b10700340208101d100880350280c0c0c24105040c1405c0c08603210030140508407568006a54075200c02d01c0580c82010142c0c0b603141c0c20020448103940b5000a040f00030744e4040060090305c0e100c0285840c140f1410040703801e1000048803601c03180d400007a0664000708070300d06103c240c03410500711498160801621081c886010842c80b00401056002000322400a4160f204102002d444c200888000b03544c0340100c80c40c3c0041c0c4d10254410343d607014100d9880f924102d0b1a02680d810403908681c4183c0d0200e10003017080300b0400040081806c14492510380d4088985007901d0b6546108544101140c0c004c2c0c5580740100281c020924000e403040241f401948c10341d502d000c0d51085a6448442d0060381442d4610703c00818104000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 271861339 1250 271860089 271860091
    0xd1e0f060f031103030d0c0309020a05010804021e0406050d06090302010624030c090519050906060f190e0904060b1309080d05040c38070c031103010906021b070b03 72
    0x4405070030300d005410b50300e800c2d03907440ea2500541d40500c0200300894458000c2d21504006503940d0b90300065640080c41005111102030380801d04212241040c00050391b645184100c0080745040820741c42c0c1d15880108005c0c09065110aa0001d298145481030100a81180f00c81c94820b5008009860311144d510070300c07003036814179800d00560840803001c0040c02980800001c281311304098800c44d54480c00241c05950701810758a1208018004214a00b01060002c1d040349045484a08014500b405022540100f842d042c180041c400314011843d8006d14104d44000da0140024600c3c0c501400c08001514007406484c0c0134100c0201c684a00c254240b2880d100c040e4020a118545100e0000e4080a442d000d003007941c0b900c059580000781300d84041581c1c1e03030800031408660164000715004208070004c41080b074521075000c000380c0f00068020004001565405040000d81c1282000440d00425038000300400941c070002e01002106100c0c0352004001040340111200e1640354039801d0650b001c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 271862589 1250 271861339 271861349
    0x604081606230a02010b090a0b010f08011d19020f1207050702130f06080d1d0411190302090a0320010c030e01030914030301120c090903020d03020f0d1e0f06 69
    0x251101040a642080c0020050fa6109100108203141c0f18400500c14000a644425015035288018074855802000c540e40450860034902000d602d010041c0c166401e040c0403202ca841d4049000582d051040075940700c00100c3c00e241151107800b070b085500019030140041e1109082564000742c0394510403800c40c2c0e01242c1c003420042c0400b044884241c054000340350041079040c0c031080082800c841c20820808850319903500c48031007601c608a0346004800300c0600c280520f041012078248001000102c80b840d5170300140e58000ea02c54810110b00074055508240c1d0701805900000080c030014130380244040c3c681c070300386280c0041480c005650103c140000207011581d24007206020f503000e90705c055403c501070081e203070220510b41c11140c10f41d4000d030003046181082002c0c0800784400b0701c0800010340403030481000421616180a03681c0c0754100c1090b410180c000440c00d03040500d0009a440401016005000c0c08042101000c00d8610804003110401d26201d20256015001d000741c004a0f8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 271863839 1250 271862589 271862627
    0x60b121b090403020a0b07020634080415020c06010302040b0d03020a020103050601021f02030a0b010903050a020d150c0c050f03041a09030a0b070305011806051305060f0604081606 79
    0x9120209000720941d0051054043d80111440c00c0c000c11880b00d941482401daa0b03002e010b052408005100655030103410380b802c00e02b40181c00c00c0e10b2400222a20030300d420716041154156550327240c400503081d80550800005d600101d400501c1d1203000450b541030700c3c0308031001e0024035001c3e014450315200050015006a01410745040954083d44c009030700400188141c420401c0407441c8408103900e02460182000d07400420407640d040c091064560490007442c20f4003180c1d03d9911307900c0d902d409281c0f010307114000c0030b084801040f0740d811140da005904000240f00c43d401910000c0c110380c8880b4415a82c901900c907110140c041c01104030340a40d100382540007200031983d803141d1001d400c403104050309845100f1090000c103140030301941c4a51402c0d070f8042a65810500f18101c40000281c0039a0803609181d8107201e95641d503c1c10b8440e40c1c546002c0001c00f0340d01c40000584039001650342c5ea40003000002c000ca030001e00440c02d0040d29800d410841d0100d55212000c843e001d10180c4844189 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 271865089 1250 271863839 271863883
    0x2040504051605160201030e0d021e03070206040314010b0d080903060a1b0507062c0709060e01121703070207030b010b070803060105070501090b1303080711030901030906020c010207060b12 83
    0x91101e08211801c03145c0185000160101c003808590702e8018002c02c2180540e100c582c921078a4203001030320058542c050b00185040c004241d001c5041c6c0d001d0350000401c1c12b0120702e60540401c03825403115000010080c8582d2070055281060078481d0300c00c0803918024061070001505007561360150140609004a40382046000b40c2c1707007100e09030406034007100c01c907441d4a810320904200703a21050310010546c0302644a4200103030410725082190f40004030440c141001040045440c007c1141125000719403810b0501c0140740c42440e100914103190050321010003031018841c1e0025895003502c1c80f603000012641d8030f6903203103013903402003020090140500b00001b0f1640e5220740c000e8003042d4407550020030b444105944000c6d000c0e2040764800e8029800040d0101410ba0000c3c00c03580050312402e1107030308038003601e20254403807080700c504a0601d038840e8040c40c10800d4980c122040340701e42030000c5440e65040d1038003001403d030100c555441840034a00035031054001007101c1c1c0f0030400240f10b00c40300e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 271866339 1250 271865089 271865107
    0x90c010201050105281d0105090703050408030105010e120703080901020f03070b041b0305070306020910080906040b100815060103060b1c05041e120801080d05030604020c1f02040504051605 83
    0x1414504001c5d0000312848080024840740d8614038005a1544c0c2c46410000d58100310a000e0520002440b0b4410141400188004140010304980c1594400e1800007409410710000c2100440212900c1d50980700d8150f0000c01d1215280c0505801c9600b60300752040d034130a907511a07a4900030828060a618041030105000810140d02c01d8841e00101444890859580d20f074241002c03c0769005845180d000100400c261604840d2410250740908041846042840d800ba80d0f54a0060008199208800c007040c1c51141b9404c14000801c1903001722040040181c00c0860002c006644040c040f0341001c201083c0200c5a0341a500c07007a003203071240205400a0410100504005002501d03003016040030080889500da00224a80d4011008042c02d00c0e0040801070004505034000b02c9660000d41854206545c42001c030794101100b00d90140c0c0300c42e11101da003414070011041440796100e0341c5000420200310b0703401400441d02c042b41d080120f83e440c21201c84107400d44018030800108108043d440c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 271867589 1250 271866339 271866379
    0x60403020a2d060203072f1210180203060108030a1403040204020d0606020102090a08010c0e04050916080a05060705040e0c0706061a0d060b09150325030203090c010201050105 77
    0xc0310111008040b501400480b05020341c0c411103400180058100091480a002c1e803000010b410a205070405044e07008841d040d0b14000f400b050185125406289407039058400400c1300c8142030507000410000001c6400340320b90140306a00d0100c1c020f0140c0070002030b80101c08810340c0d440d2407030354444c0001c402d8001c08410b01030344002d204a9001d9401d1180e043c0303030110f500c610703000b40080c1e800050343d0301102e80410441d00d20683c003c1d04182e04002c60383c0205c03a4091003001d540c45041d24080b07081d48070151094200007200d140b80d5190700a0000014900c2030004080c180c0074091025910030703480b0101c2c112000c0c451805010050821440821450b452090040001728052140007806036100c030345003030720340c500c40d1705102103000041003446080090f4481e050080c1071024019243c01d2045020a41a40c52a0040c282041c000f00001c1c0750010244012401001d0f0507100310003181554201800a40007a030341c907600c82c0300350404c80c40c030b5500505c10507041c0c8400420030a0b012043c0403982c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 271868839 1250 271867589 271867619
    0x209161205061020030f12060307080c0f06041d0712020306090103030c060e060907060f05090901050d02030a080a0c030f08070206240303040f03060506030312011a040e070804030e060403020a 84
    0x84c400a010344000c11035035500740081c00304051600030041c3d0700d07140c0e0a0000f01400001c0c0489111b80c0203113000b0803000000107003010f071a40058a83e200c2c48810303400021505c1c0a00e902007500f114030f030410040c0c02810b0383c940720b114000e0303034807404000d108608100049000071104e858100300301c0300040c070100e07026007112140c451041d400454172515042d4450306003a0151010072265106c844c00f030190a40207242010200c8480c0b03810741c00e2031144000030b46ca01c0030600c10a8003d030900c600080c10b5441c148a941d1866030810201680c858507003174010302d011b40c2d102e4140e00244c0d444101108040c4952005800f602c0941d0040c00e00f900c4d51341206458542e03002110542d1281042600307113584007400584000c04981c5000c6129910f541403240c19100d000f480706110b0b4004010703000401210000c0c450540700d13403800d050707040480c002580d0b007648200d421000402c0c2400d400c2110b40c82d407041c0c24500c118800e80da815550302c2c240c418403020340218000258080d40c80c2d281400680d81c0d000c555 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 271870089 1250 271868839 271868867
    0x6040201080c0c19050c10090905090319021b0a1202220c080610020c0307033e04060806090c132d0c08070905010305040f02091612050610 61
    0x1a14114000c02d120b0710708800b00d4130a028504800c01c5840a0040a01040340b07501001d4803501040d4050b1400200400803502608080e540e40e9070124240d42002c00a80d03c060b81c48014540d81c2e292210b01c040d594220b1101c910020100940c418210780c102100d4890441e40341c810b03280c3d14000103608014464a14400760f07640781c0542c0f03040a4030710748e0070b01421180ca141a2109103140c1001401e1100810903101c0240655005503e1064241c40000703202003200d400c500804107441c3c45118840009518040c0d4124001c0e010703040350f0702c06d05018049aa1050b0440c0d04029141e5100096621000100c480f14416040f45007800c0b198149030300d078481a91112200025154200007000c2500352609019211610700d1906588111102e4403410310340ca4044d0900d0035291a1648005040c00c070b26002d140c0c101511040483c04000a169000d1444c82c0c0c0200f4031911440c0c034015140d00c0540b94000c1c18000780052100c15010328907417040ca40200d20203804031441c1102c00b5029621040a10b0301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 271871339 1250 271870089 271870111
    0x10c03030504030e040c0c02010e0a06091e090f05150a0f0605090609120114130b0105060d0b1023070c0b0306120f010c030c020d09030b06040f0207050a05010c110604020108 76
    0x4604125500c5104044030941251aa07c0da0380780180001070071800070321450740c01140e0681090085680065411301102c1705200c1e061840045080e268a481a2076130011040718144100382004600c3e81d00120700c03c050340840e4420103030140041241d801420302c01c041c41601960310500c012442400100841030000d4000ca02c3e0420440100d41704143e4100038000603591031645409000c0100401031b0403101c2d00c00c0c00c8400b410b403a01d440c8007480040c496623201c1d00f0009100143c100309034000c112807500050205186004220000c1c01d004181d50307108011004000c652013001034102c06881c242034000c4224042d66040049000030b80d4000752160341e00c400c0d05172b003040441c4020040d103903200804000108101d114014040c0a84008401c45000d6400240645403007550150000045076080104e5488a03210a00070070001c2c020412621300240c0000307280310a014002859106051044008202c0b26540700d0003200d01012840000f0703817640100020601540c030a00a450300321f50030450b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 271872589 1250 271871339 271871357
    0x3140d0b0a1404060f060e0108060a0306140f07230903010603020306010f0e06060708030f07032004030b01051507060509120c0c040605010203161709060a120f0b010c0303050403 78
    0x18681d04003a070058000401d410100102c0d4101409640000d004050410054a003000710147c0150b5000440604000c50840054030507074508454500640d0004010001c0007540043c0d498812012640044c118440b8404140707294403947c3c2044041103007004100950b4007052818995604c0100303e543d05640703407040031015075828460140240700c404a85000c542c9019010106160002c080500c980018801c140200c0c0050003206c1d0302441d0184544056565810141d0003044000056000c11841019544942d581d040042058a018000da841d8984c1c0c1c90f010007010380500201e1a0310004c043c0041c000280c0d05400183e0403000540688140075441c2824076150f800a240059082e072043d0117010040c2011321829014090030300c040e526180780d1b921007100407440308500605080e070a4101c0400d22400e601510a401002401c41c0e0751420302c2c010080c007140d50060802181407403c0c004c03512000f1244100503000c0d006031203106185145860a40081c00000e10540a1000c608 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 271873839 1250 271872589 271872611
    0xf0f0a0902282102160501050106180e091e07050301020a05091306051c0804090509010203010815040b070e040906060b0a020d090308030a05041e060504031b03140d 72
    0x100181c40c0c0a09400b41900b8600b42c0d602d65894031800e00b00040003400048454040b404070004202c162000c241003002d6541c11070040341090340c0c08110b07405051546440b001140f1154850000240b4445040f101d83e80c040c0c81e03880242d0301c5101540c7d5506650702044030313500382c1e5000c29401c03c40c0f040b004058841255440300441d09a900280c0f000000030300020b40280d161908800e10009105144030802181e42003801094036140c2404052a1062809078800b081010500c00c0702c000d04000c903010300840c1050800076010390001c1c010950f09002d6908040e041d618611002803003690001052505521466030655140e00b0f015051034220f5212540e0f00c0128242c0e0003064010150410202d590b0740700c40d40003d00300280800110100061940b040011400c141d0940f80c00404104000402c0c0c2c4841c6410b900c0a01c00c81c02a078010040c0c1c0300c2076824490550721040c85140651503017441e9000091070400700780c2c0da034107004010650440c01050040820340181c4030302c00d10803034000f400700241 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 271875089 1250 271873839 271873841
    0xf04030c0c0602060a0c05130303110f07031a06010f0c020103020d180302070608090a02030c040e0c0d35030f041e0b060a06050f0a0c0c0909031d0a050f0f0a09 70
    0x20b0b00301d800940d1008082c4400300d1458490030b00564801c0c0f5015040c0400d00c1c0300d0300d0f0550458030003c0c01b000010a10503501d80d1040c0604110480007100700c3c0c400300d0344c9140240d0740c0e0028035220802459040300107205540615a9024403414540d29101014400c0e0b005400035041b0000d40305006a40d034400351070069485005a424a0198005220b42c80c90b04030010060000281410384c2600607060800058800180307000301e00720101c5010504160b4215000e00d010030300f025843d070103610400d02e1814850024480326040c044c000701e480c44443e80543d10031416102110603001c0003420400515080c20380030060743c005204a2402180301c00c0b400c840071015014080230307546100b0f90300c14480a4036101800c0d400030505402c003582403844c0305030502101d000f02a101e0040c4028038405900300150840e840c2c01a040040b41040005001c0c00c004003800e02000c8500340304181611100b1940c600034555804849000340540c2041e91610144a2034010001045800901f8401c1c082500d1540d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 271876339 1250 271875089 271875113
    0xf02040c0c200f01080901020f03070c0615050916020c030f010f150e0115300507030603200d0503030a090c060c080306121009060f0b0411030f04030c 66
    0x1503071000e00014080c01c20100351100c00854065424018140d4000381d2510b46540d4140c500034200f02c910785d55800380190191194840020ba0f07200300004002a40790013102e051070305809000202302c2d26001b100d419103c00040c6c0200342d840034a40000607070034200d0780c04d0088101c8040c41994403a14500020038035040700990030341000c0e51103036600304458000d40320f02050001d2180c050b2000c17070301c1d200c0407054494040c0a41c918402444c680040010b000f549494080f02500d01e4042d0030303540d070144401c05004540c00505406050001240718280b1034001e00c0e05494021031b21180c5101c028541e030a640046202903a081070340714030400007043c0103001540c441e81801c440410b00401d03510704884444031b40e800000c1404500c81c031040100300c4140980354003502c159020300c0c440c0001c1d03c1140c03a001c4121850000d29007029107a01c2013010907004680400448401800100c2003c0c0c1000181c6001c2c2e11100d8200c80203000003641000483c1001b60040d0107404c2c605c0c4840c940c2e480703101c41c0d500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 271877589 1250 271876339 271876361
    0x2040501030c05150f072a030501020d0b04090203071401140f0918132303030403031401120201051806040e10051e030c0f0109210c050a030206160f0204 67
    0x10716080403c42810807082250b00c0b9521080102d180000019a0000c01e02500c8005001c0003200208100051105100d510100d6003805075280059030703e01d8443c2c041e41c0319000d02c580c41401c06212620600f011701800031010b9004000c1d10300c041c02d004101c070f201c6040c0d5200c03030b042000320314108012200d018020001c5a102c00c0f10250b035003140c841844203100088204818480666080201e81c50b10710b0380b0380313651541c40181038544100001c40600c03411306440d202c04135030100005000c10150564000b000847c1c0b6101d002041d03aa81d0b00700c0c10303499905844040d0202d1420403141185d0802d10011000d01c81004101d5800d01e81c8629a250b40140d0850b14070b070f954a4400400c2c802c92030701d22018140754003108005100e84080e10007103511040e401118074001c0c1c40250055480e40c1c0542c2e070203005414245580c0b01d00c0001c41c5050700300f02038100b5007076030560034a041c04111820b00c00c01d40c6040c2d94028118618111209061641c0301480690541d0152066207114006036614002c182c44c8107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 271878839 1250 271877589 271877603
    0x6050607151121090607050708090102071805040605060f01090308160c031b230609030c0316061404060f05070f05011e050901050f0613020408010e030319020412080906070204050103 80
    0x1003603c0001e84214400074040c621180c1c004401c01c031040c0e40c000304840030607a1121050b03844030344950041c0e1800509401c400c410301084c104e52440908554403091149000d01c0c410702c030070b4482c4020700c048042403110380c50006000450500c0424120740042c98090b0403190b03044075848040e29140d40c00551364108460325503c41c00306a16420100c0104d0010301100001d84140c500560b034800c20f040c2c010303100c49010301c0c4042481d00032a903044c0150404440c0c046d0a640303520b005050400080c0034035004100200d80e115001948c1c0e0030000d01a0703410350b803180e01da07159810b10415055845411094003120012802c1800800180e800e000f41d0620390500d0003c2c00078248008000d20a94100606511613685080c0801403080c40d48120f05800c0744060741c41d0703e8201660121f800180c452138110b2481076003072040b849078042c0d000005611516186034030110201c055180f50782644564401c0104000100446401107070303143c8010070f2050001002e4500e40f01c0640d0100d4141c440980c0107890030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 271880089 1250 271878839 271878877
    0xa0b0103260a020a0210030f1e110f0301060c0c0807081b01020a17031f0b03060f010f14090109030b0a0603120c0503040311060f0c031309060506071511 67
    0x1d0800c152140400286120340e060500c00c40c204003c1d51130b1140c003006485288100e840a800a001c0da03c41c50458045440a0012840b110910b007a01907084541d10100d514149451000c21040020b60b100382c0000c910191071a440c00104541d418404441920f901d0b0807118005540c1c80100604401005d5200151503495895100b1450ba0038004104506641181c0b84403000180444601078560b080034407980c2d12a182e20410b002c04c0c20141420184d250b080c0c01c07010800841540c051882a48210f40c00c000000d004001107907a8090155144042142d13400e22840840001c009810003142c11316103812560350760b44600005000c181c030403091540c0d846006205100c040d25144030700d01210b041c04005094203a840c03c0c0c1c0d034421884080e10f690180102c240300340d5580011103c92020081c0300c1500c582c0c6102c40540c803980b0180d5009000d5a116200040c91442401903400b26000100054101103450310344004031f44075000310491240d900e040210b40da800b807c1c00b80451034600d51071080b074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 271881339 1250 271880089 271880123
    0x40f3f03030b12060a0c211e15030f0602070c120b09011a130908120117010903080601050304150e160e010e01150302070203030301060e03210315030a0b0103 69
    0x300c40000d201c0d24080d4035440f05200582e20009051034004000c250001200000d80c4001c65507c0c5003c002e84400214144051007000450b0300010f01e0381c04c00c070801d41c40c1200c80300060021244401d00c4040b02035000c600410201d4059814051424003801c00585495260741d16202005a41c0d00552076007403c810041080c860b0507849160700c10b01c880300800c413031010b0515aa100c407141a0040b0710815007804403840f15040364110650b01d5030f10084094485ea0b410a074803001034024050300403004003034450402d5401c414010a810345400d03442e607a44039110400110b52641c4000c1099441e844881619840a5070902c43c044202d54035101070403030003468030082d400240303965000040403518034005014100d504444181111718004803d100c844400500760042d01803450080d600d0702020000045042d0804031586950900310260b8150154003a4070701c110121203031003171f09e0318803040c8000b4030b0058180c103a000032030100908440c4250301c16aa507180d0000240c0085030b20600852600702 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 271882589 1250 271881339 271881341
    0x804050c130501261e0304050d05030417010b0901030605180604061a0607050d050a0c05030423030a0c1806091d010507080103050a03032315090606040f3f0303 70
    0x5010460700042581340d42442c01a0741c5a0042550120420900c030600080f03c50070011a401000050202d00840405092198594119200d413070000601d00030788030b00444041c881c0b00307040c0c0d1006181055030b90031034445000510b802007803009030314403d0800c0362150204114042c8210303c10cd00206203110031030303600031001d0081400e0f40d014050622010000540c00701d103d00f8400e8451070016110001d1050859030b26405c0400030304940400280401d510085078540f40d43d8511102c48884d00c0d200b420242b40e5611840c80002e00704e41c028032414418a6486c9040d00d0b0f008090000102d100c9448081160444070070000b22000154a0042c16455103000c0c006c069020182d800c0442c12580766484a54941121040050805a5651811500080c440d288005004892600814520b404900c101c414064600524860500c0400041162400404407025244a10000b01100c4e05e0a04041000200c1e00c404203003d640703403003402d410340c10282019940e8400c1c2d004070104103022420302078 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 271883839 1250 271882589 271882619
    0x50702060d1e020909160212040618050d1509150608010f15050306070507060f0c020307051e0d0c0804080111130e131101090b030901060305010b030109030f0804050c130501 76
    0xb800da0052184402c5540c840d004190b000e440124072102e00c0800400c00c9017480c64000312640c10800100740800e0296000c00c0018050f0041c10b05102215101e4081050b110f4050700002d10a591000b02d400c400007294200040442c812600108a51045003041084d600181c000c0e4181d69956841003490300f5007805a41d51010350402d01d108054100004070380c944400070b045c0c4007401000201c61040150342e9010120001d0f0303c450030051501080c0009480f070388400f0303082ea02c0384220f407003001c0100f050280c0343c40c030040540d0051000855812040d00d45405031581a21030030000d100010341c003a001e00413100788410407610300d135842c00c0020b00d11403151400d030092a50504d501042001d4079200e90f0030440c6080c0c1100041c455040c003503004851442560700402c240c142e020007400b107180d005406c049c0550340f10b40f00a0060104010a0500300c1d600c080700980042c140c09241025540200c41c05038106000b0419540c100c205400850041201e59404001040d41c3d40010000740395070b04450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 271885089 1250 271883839 271883891
    0x30e03030609060409241a0409030804030516020a0e0f07030e06150a0906080601080f0715120b0d030f020c01020109080304060c02071e030b01120c0e06060c060a06030506010b030403081501050702060d 88
    0x10051209c2e2510000d02031000104002e091210010700481546c401505080030264020590788102c0d880d207003040403611043d80d44841d10064070001c6800a4040c0c05141c8510000c04001c20a940d640c20180150300c000c80b8030250070501c0450042002501da00524029200640080c1490351504101c24584405004e125506410500e003d00208100d0039406050b14010302d44039180d40c0d41203142100070001c600100d1303801036101180070101130300800020101c14080d02969a4402400016400d80c1d407000710013049440100005000102c1550080c54004498812540072a031140c0074405442040f000c520340403400c0c0d4100f00f080014030b2111307902401e0201c5003010070500e19501c80880782c005000d280350a01c00200080c100d1340b1180151181c0000310000c450003420482d642c0c00041c41a400240c0720b0b03000d08400481e05421240403680100d42c1aa80c4000a030342e40d6040c0740400e280e001140303040150030041200966200c402518009507180380006402d0950030720030030002c240284e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 271886339 1250 271885089 271885091
    0x1401090c05011403070f0e040c020a020a09090f080304031e0203040302030d0536130e07090905060a0e15070f020f07051305040203030f030108060403030e03030609060409241a04 78
    0x800b03e480034280c41929000809070400c04908200c601007940c61b000002e500c02e420074580a4080300c51540010205030b03940c000c1d203020900d9515246800140c3e201c041c0c0c09810030718820840000500709000460f0300600a1400a04903004480003020451268a01c04016800032500307009515007848001c400c0686801c2082c0391028507804601229812094102c001c1001910003075172001181c40704405180c001c281d0301d0085940307145d5900a05034400c83c100c4038070484a0100322409107129410a05030800b0041c14207558600805029142e826400c081901929081d640315400d0f20003a20301035415030302d8000030240d1000000345800c4a90300840c903580d015000c00c100a0300c3e0308070444035096072070030b01013003a40c0d07540042441c610585c0e100480c1c03201c2c00000002c00d10408500c490291f8403036501404042d490300c0364030399603000540e034a0750310000d02c1d40840c0091500e60f022132002071142c04d03044808441ca03510900c180900c2c401074004030b600c5510200311030070000c50720030b00c01800700d40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 271887589 1250 271886339 271886357
    0x103021204081b100c1e0206040803090a1e03030b03060c04180608030a0203130f0b0d0203180a030915020726030c01110a08010501050304050c060f071401090c0501 72
    0x10641440d40009407018007801400900c0c00c0380490039401404a4200000841c0c3d40210b03200741c2d10f002041c91143c00400561418a90015910261008510004154020f1500391127a031140030b038650020744071070054814100c02e0350000e5022810716241c14480001212000050304026041c5c0f42001c0842c0c0c0700703401c04001c0081820090040d1030503592080c19546040442c4100320740104600e800542307031484049142c15207a40d0000041845600b00d07010f900070360f40d84000d29580e1842a008104544009001d40c0030304000da44d018503840000d403181100742c01d034050007080c20603d202c0020360014000030350a205000d80d08081c0543c89413940300404810745001aa60114082c18184e0103da450481030070601ca50f0400c15218a21410701c020800d1080d01090950303031354051100031001c60790175400000c03258054000e0f00d10854105001e8010002000e0030000a98010600741c078041006000c20404545500608214140000000143c8400605084100340c0f100e9010300d0400c40500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 271888839 1250 271887589 271887607
    0x507080d151805061507030c060c0203070605040b100b120c070309120605041101020304030f080c0c030706020106061403090c190b040803120c0a020d0807140d140a0e0a0b0c040e040c090b010302 85
    0x8c10350b995420840000d051241c1e660101c1c210311070b4444c06400d89041030280800c0c0010810704a01a51402c42c07011034480d41c1d072a980c0e0b55801170542c801d40b0100b40f40c00150030032a0181c01080280c1c03080ca0b0203805103484405001803802c4412080d80d1469560b030400080004502041c003040000340015814189140c0c0c440030000851240108484030100b400030304804100844400014010140c40c0325545441d8000d008000a21506002408202c4154040243c040850f40904188400741420fa5070103c00d03c000030981040000041ca51082c00145602007440540050711600000e10f0b6101d41e00a06d845000d98064018030507450704104001103903400160102c48101c0a0900c690360f5600c101d0b098560012403003049030803c0c00081c445008447c1a40155416414200b40380029281c0c3d2426008a50284541e14030640c003001c40d0b580400d401081d902d50201442c003600740740035102d0f0013040820b04182d4048400183c403110a0188003400d004545601c0b000303203021400d1003011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 271890089 1250 271888839 271888847
    0x71101081006030b03010e0102041e0f12141e161e1211040c050406030e070528120c030c0905060607080711030a030e01020d0507080d15180506150703 66
    0x40d00c01c40c0141540e4801c09844c40d10203420440b11050440c00864440769260140c40c02841c40a81c5c0007089085208040360102a0f0380d00c0406a940d58200201600309039954001604e0001100c0403480c130941380211901749900741d5615480071003101810202025a00180942116401030036052070585811215540c104400c88203c034013640e001c0140d80e00900344071149169469070160040d00348000d444245400a006000301d403d02c1c1d03001c01420003000c580c240c55076a41c1c0201c560004c41c8118803d810700311b6a040c4900c145501c0d1f0541c24059a900020381c0e0b500000d10304030f0300d140258408000744290006800c00415006100340460700e0310b240011510f01c118600144855008580b141c11310010b070414507417600c000307012140000500e00b030141c00011029001d50042c4a12140381010500c61801ea8610780c0e44448903a00305448580d0a0003d812a6281010352810860340000c900400c00284003035050039140014181c1003400074040c000c002c20b4020a10180c0801c81e90000070340c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 271891339 1250 271890089 271890121
    0x2010f052a07240c02010c06090803011805070e0118050d05011401080d05070305131214010507030e0a1106090631060e01230703020309030f06160e01140309010207110108 75
    0xf444c1151403e40d0341e10060f148100028805011685081c1ca44010030010600841c16101c00c0012688080000d0a404058400459610f40011091070b181d01c5c46501407004400e4038170581841150147d1a0400b207440d00d115924180c49503034603840020f580c1e071004034040d8050709040000e444130043c5d82c07030050301511880038010b040000010742522000820103a100260001041011480e803507410b1807482206099082e40c0d040d440c040100b60414000d12480941d040803030007070325400240b5100e10145210300c404032901310808120315015036540000604140b2886900d88210060250000d1204609245980b40301c10744a901031001076000580b40c200030100341780c0040c21a103850518142401d240007020303030001000c95034200b00342d00030000d04000c41082c2c00301d0310a00ea0308400155198800e0320725103040c1e500641d003611000e2148440c010082010b061204030390300703241d04c040034541c002c2301c071900a030f540810700c04100800401c2444140c00c3c2441e040e40e060421003100150604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 271892589 1250 271891339 271891409
    0xb01030b01090e0703060e0403020102130b03131112150702060907060815032505041107230307120f080604140613090b073902010f052a07 61
    0x102000120130398841e4101d1000740070702d655480081c0c03c2c01d2401030302035001100c01c41c8108400701400700b010030307200f03041d684903905000c0c03580303440d02003600c4c2ca96000001160340c42c2c10100e19840034401d16000c01210b45400c2550300200014580000000e06005020704401065001110100b02c62544611102d82242084140050740074040000901d001a407110003601031407030710015100451481d5003a41141e0b000d807002e10a07824554100406881a14801094010748280c200010540000c3c0c0008072607641d000c581c038003070b40c82d12580900c4c1803030060700d0300195004c2c0501c1802540000c12640110301a00d0520458403004007191042c3c070001c0c01d90780030b030170500f07900e40340c11501d82c101407007440e0411000809800c024000620450743c410308143c1115a6504030701a0464076403600c40380043d611410b03281c1e44001da004559030749814104004100c0240808052400c540500b5102c0300c00301d0900c1c0c182c0c0d00c190000c142c00d055047c1d00c614a030200f54003c5420902203018200d810751 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 271893839 1250 271892589 271892609
    0xf02090106030e03120702160e071103040f17030d060e01171504140703020402030c040e06060408030406030902041b0c0b060f010819060308030106021614030a06090c081009060b01030b0109 83
    0x6178070340c1007c82c03600c1d10307031030641e541d07440080c0f000100e0b00480c0300702e503001c0c00c180d41d0350b4040809400201540c91040c2d11643e0f4201d01a00000c020300c103519840c400b0407517002d405407071170320b01d03010701290548000c0c0d0454008110381301c00403c10507103040c02c1d0203c10603081e009007002000025250440310381c02003014085074140c0488500b452403d002c20760145038020030440d101c0c2017190b54921a6040f0303009040307650340301c0c402041840c42c0840a0342e080380c0c0f24200640c50301d403c0c150214060662a03404980081d11400204800c030510412501401504c2d603e48544101d00e00740b001507620040e00d514090b042c5102d0852090340c1c4520302550002140402c00100441041d140c0300400141e440905a90308c00b00012611a5001c20380c4000c4002c0944018002615081c40920114000c401707503038140c0c000790260000032050381089441600980745060b070107a42d00b00c62030800381d0881da490075050781c1e0054242000703050b2096841407a404e10301003112100000c00070f0300c0100d49008014402d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 271895089 1250 271893839 271893841
    0x513081905191e0e0a14010e12060402041a0f0121022a070f0501110a051902120601060215130f080c010c0e0109090917070f02090106030e0312 63
    0x14015001c81d480905903815a402c0d580c00c6180c0182403207180f01c50034000c0e02c0740c20302420b00c1c00d1149204c040c0030080100000d01851418003500c140c00560303c240303818800190404041ca6503102941c014800c1864003500851034948100f20403501c09480c10300e40c61101f850200b69949aa40d00001d08410030700f40107403407182a640300045070b0300d8440b6102201c3c0c0001207251441c03103000c01113007841440c4010010481650300c41d054a030042030040307207020040b240003040a076224080410109a001081d28040360a545915041c128000804030244201d41070000450401d0200d00c13461021500c060036130b07541041002512020401004c00c00d110b0304501084002c4414242090095449888240c0411aa1401003841c1d00011034001455188c0801400210f008140b10b07902005d050303480c003028504160341e0320010501d518043d1003c4040c840d850345004041d00051030101c0c01513141c10610101032042000e1040160811010103091042c90413014800005487c448080c02c10301c1561 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 271896339 1250 271895089 271895137
    0x42604060e010912060e060c070f0609080903011b0207120f0f230109020909030315090720100c0512010b030c09090a0506010210140c030901060b0310050103051308 72
    0x2000f20990416400808100a00002c12420358066280459040191211540c825030001d56601560034050001e04d45d91103444005041680808000f42c403580d030090070b0880030070210782180c10b4500348405210761074001e42c00040d01080a10300514009028494050103641c0300548184d0450005201c204103450b0352040000250300390aa03400f005c1d40f80c034640b50448000c2d9000e405a00c0e81a80035085244c0401c103000d001004803842181c4c0c409142454525010600c4032058000f84850100b1180d010030b00c82c450102101a8100d2011000610007119017090300d80032112a01445002d01c9420082d001c1a5200046803604640540c812a9129902e0f8828880303144508103407194016445003c101c0240050f900c02c500500080e800c07500c0c8802192170340c4d000c5803440700d01d5451240c0c07100002080040000011a03000b4840400840c10342d5036034140c040d25400070765a2810141032241c0c10301a6503854410564404c60005210107440c460351115103991145e400c0c41400145c040c0742880d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 271897589 1250 271896339 271896347
    0x140c01050a181511070512030403030506010c05030307140d020d05060f042c070b0301120605010b090d0b04151407030f05100302010e01030e031318020c0607050a0c0b0f042604060e01 80
    0x100a0701b010a07581e10300a07010b03000f2107070f910440342100460f25017030118240354443c2058000081e4044011851511340d80800d132601e540207246c04168100800121010410b9400a090044411680450305041c601c040259032840c01400078050340c6800481d495601040c17104030003500c225820104e04610308941541050040c0d00400b1080400100014a0707241911990300d038180034910410072640c8500b000300c1c45200d04590340c3c3d44034011060348000320b00380e010002d801c18860040e0f404220b440f040180300355030503560070035222410401040f1140d609809402c40f402c1c079141c4104802c0c5482c254403000c88c83c3e0741c0070103030400c4000d40c030165030790740298040728280852074100c9031550141030342914440c800e030083c5071042c010035215407a44503441c007e0340e40251049000d442c0035540c60034103c8203500010103000c2000050f200e03100201c0c0780060018091840004040018030381801e00140c2c0001c0c1105e81174104848044031301e031618400050760162441e0b40f80040d403510114004075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 271898839 1250 271897589 271897597
    0x302220f110a1b0b04200103060b04060e01210504030215040210050a0c14030306030706090518060d06020a0215130b010510021005090f060609010e06040c140c01050a181511 76
    0x2c0000c0c41c13402c244020720038010340040c8130000b80d41da801c16075038010004400b680c005d4410344550040502017403044501600d0482c00c20b140615200c4510484003070003a007061211000d002c01c2642d200144000d00d0707414010300003402c860925810b000d0400e9400305d1075034030600c154402042070210310780704501e04c1501c4100760144c110161121703070481940c103d61640d000350382c1e40c0d2003031146450000701107000b1400d80b012210020844250355030303083c140884c1414000e01c4117501031141d440713080c0002c2c100d2015002c00c8132103034024099114151001e032140e04024103140a88090f048407040000e086130900c60550b04103841109103031448601c04e901c0c0011420911000f00d042104105850700300040da030741030385407680440b40c103500d0317080a2024008003070186d0000e224500c80010080d01b4943c0003240700d5101d514000541d01d80300a984011900468045041039440c1c00c280911605280500807440050381900b402c0040703e030f0340304c108003800c9400800c0e850780c0340ca004001c01e1300120155 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 271900089 1250 271898839 271898843
    0xc04150815090a0e07060c1505180604030c1a090c040905010204080d11152401021002211b070f02030a02060a0809070821090a0302220f110a1b 63
    0x11280b2410204210406440b00ca40e60a420388285070000841600c919042081207401050189800e2514140000540f070020030800c02418450340c40130300000c041240621480c0031b950340540300340b080d1514428042445510510340e04032882402464800840c1c4072280d14000c03900081c1e4291549840c3d4003a0090f0b0b0b00500460181800c2d00200d5504000d1050f01104010f09442e100919400e5000c410181a00e907081d4089175200c01410742280055071101508050044801a40e91600a00700340d9000034121301080c8403082103620213a40124040d40c00c41460980c408404070510300f170044500401501070f02e03903c1488159425510140840b160280e000740541d65500000c840c0a812000c0075104200c003485402e00014034858046090800c0c4132401c0041c1c480e80b115110098403a0708490100f6038400c007886000001aa06d5500d44040e8410414541030b080090004060448000c1c4003811642402c142c0751a147c00c001904590400105061161003110382c188003072211442c5e03100c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 271901339 1250 271900089 271900099
    0x4030803150f060f0d15060f140f13090b09041115040902120f010608040308011203031d0f0115180e03041d0604060602031c0506030109051b0102060c04150815 70
    0x1402200704c09038802446016803001c0d040c48210820090724132485000c2c4210400900d4200c282801ca40c4112500c103c0d00b441d2800ca03900f04090300d40c500a865206481180300d01422031010011860f4600031603111040468601c5520300c0d164558122012401880d64130941508a0300e40b8250180340036a0050055070004540b01d90403407540b10ba00f98016200403d04a040c0c00c000201c2a1040c004184180d5040c4d031005a81d07407900b5494041208000406c03814181c072410a800306044030700402c00a404d642004006d20384017008a1421500f251810050b006c1c82c4034003c0c415015400030b1071744a20010580042d005000c01c02c40741c1075001d03503042017007014040704d2804c030f07200310141545000300300480741001110755440e0140d99034814800070802801004419102c1c07007619a0100764040006400824101d1995840d9030800e528400d96440c500c017034049624081d6810080d107940a030908e081145014200050190034400418070396040004080000e5110030501d5458086444003403c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 271902589 1250 271901339 271901347
    0x1b3012150120070603050c0c070501080a020904050403090f09060f03020f0312160218072f07060908060a0b130c1b06020a030507020d1b1106071202060c04030803150f06 74
    0x2000c2c03a201c0d4028490a00024207040118801c0e441b51000c4480311610640100030040c03410005440f8400c004291840340c0d0750a2140003500e032914001c03948594440c0d030faa07403110340c148024010700d0401c0703820881c0340d00d1505605000300750b03c088143d0196034044880f0008142d091001074039201c1601c030146c060000200b10301103054400f400c240d00b06ea208543c103884a11141c1d5600719460070444800c000100711081c0411801c59841800829107000042c40144800d8490a03500c0c11040d64080c00014805007020010000240640d64102c18a003000313122191072030001608030500c90101102c0300d5950b541d880089070180030381d81c0c80d81d21410b00d030041400c014288480250800520040070a0078a0001075495101007445480240c040d20356a032a003520f0b805030204004405000c540700a038004a030403555403004040c00b101c81c407900500c01c2c540b0307604500034181301c07001d000e02d50a41814801800013641d0042601d61007659a001c4800c600784610000d0349900070140c00d5600100002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 271903839 1250 271902589 271902647
    0xf110301080d200f0a1401050f0a090c05100f17100e0916060e12010c140702030c04021614162304060305010605040614060f1b30121501 60
    0x850110038844c0940380c549189030701e00c1b001d10700360340c01100c1c000004e580c02000200b42025607441a074400d401703407102010a076201c00106040784c0c1c4900d10640401c0c0c3c8102e4804061360b2003001c101030454001041c6009050003103090740040c59a0140309604401140020500e02c4200002c1011407115008051155a41e0101402150149860a020300423000754250100014015805c0c0030040f5943e6018030141140355940c10b070440141280c0c0350080d001c800403107a58500251202504031060305481801074500075410030100c800e092269001083d010401550040c800400c64a80034841915000c0034081500c42016407841d15a20604c1d0010100500c001588950306442090b101003102944541d0302031180710f0845012036125000b000328040d0031810700064082603251105220303c82c050014054144005842040c84181c01c100d07141c010b03144514032201d0264040c0020520b020040901c00081000041140c142035800103103412042c2d2050580c508410700385002100c02c0075401d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 271905089 1250 271903839 271903843
    0xa11031c0807170603061504020c01050c031608010b0a1209080c0d030608031c0c0903140102090a0902191805061b070501090e0106030f020904020d0f110301080d200f 73
    0xd80d145000200c54500e0f005403100901846405150010010141d40c4d40d00800d4842215194500a40041c0c09000c1500d03054424003d507401031040c1d000c0e080d200c5c039050068108034404075215104105a0400402c2005100c800711071060010386001640241d010440ca80a004070300350007000001d0004101c0d8880f41c012031070305490101c40ea01031040170703035607600c42e60b4034007a001c45110244031002c000f01d0210416441409440c00798107000d9000c40e92911205416003050000901c4c5075000201890303180703042071742400a0840c9120450900000c00e0b49040403141c0819a0400d12880001145403c142e224107007000b040c1c0240001d91b00e0701000e021141d460214455101d4038401d03600c01061560150280f20240d520010a4890aa20b06601100903240301050300c4450387e1f08209495003a02c0e0381c002002000010743c00426541c0410b00060121403140044501603501800140280a000314601003680020320342a0020b02d840d401d039001d1440c100403a190340c0c2c4150081c0410721000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 271906339 1250 271905089 271905091
    0xa06080c160609030906090b12090c09180c060406090b0304020a092c0a171c0c11060f0105030709020901110a0609050d08100e090f07030503090a080106080a11031c08 73
    0x841d640e0040155500d01080d245500c880c0140c1c150341405004100030341c616146440d40c801108403c0f8bc102880000110700046026a15140c40701150b80c01c00114440c03c211090700f620301551250b24041c50188010011141d0340100070000b000000410290b603260200e1901030302e0501000c210300354040c0c0061079408180207080707500c40b2003e61040c00b0120b003c00d8440d100c07901b100c00c4c40c041120012070300e40e0070360040406840f03240d0760100d114050401c611918034419016103452480c60541c1d854a8507105c0b00501110b00030128000510164034041008001c882048402503104c503607500040c0c0702d0b13020840c520b03c002c0c41140000b009124541d0082318006010ba4195850500f008908540c10001285c0138030800c00002c1e000c101201514400c1c0754802c40030010f95640243c940900c50412110f680160f807d176002041442c2c2c01c0c90032441d0070005044c014001c0211924180200307841e2110304202401ca10040c0003911020348040c44104010b449100e02c0703900c01540c0c2e800280070244 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 271907589 1250 271906339 271906343
    0x3110d051809060d0f14071e05030f0a030809030f031f080a0c0e0403050c0a0b010807060507020a030818060a0309050d0504140904060e010c200a020a06080c160609 72
    0x841c80551070301d04103829030034041c010140200400a08640b5907111010502004170b520110120034800c404200717000344009440c402c0750360306041da0448000c400401c034a810041c401e0f044507031f00028007540080d0100a055060070540d215aaa441c1842d086004001811004030000400c000b011b4081240904425010300c05001a2035160201d50307030b81d40071059004080000c0d140c0244807420825001a500c24480c0c9402c500c0c14281494180c208200c1c40070440f1610600d0005009a400a2101002601c4a403500c03a007800c0c01c540016400d0f42d00c901c00070740590f40020780080f0100070484030501010018042aa540c4015403009000b02428002621540110503028220a20450480d03084801180d40c0c8102e800c1c50004000b480700c0d0160046602c1d6a481d019120510001e01481c0a05240340c1c58602c51014101d8040c20743340078142104016402800c00b400040c0d841c2001c51058031083c0c80c00600135555854066898800c100a900740d0780100554a1b04110a07900007641c0c0038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 271908839 1250 271907589 271907617
    0x171305040f0501030201091202130905030703020105060f010512060a05030d080a0c03060311040c0e0907020c0a09140c0f0d0207060606030b100905040902040219050307170105010c0f03110d05 84
    0xa41603001e65000c585007800000e000072801503082000f2404040486030140c001011440d004180740710000c101c83c803c403002c4404e83c1001c1408018990284141f9174004401c2e2404540d50352a0000204184540351301c44000d50114804120581c440d031440201800d0060b0807142036245010b0003904c001c9040341c01912030b509184404801c1442030246608407907106203611500c2183c481004050006c422912081001001421001756a0301d85d46602620807a0050100100d21400303003e190003090700700d40310302d60801e688100000064501d081d0301030070b15000c039a1580c148400c080d0541c480c412420080a00116020051010340d512010845015031002c006020f404024020f410650211400101c3c3d20301c44104400d0a15410960310745200420040c47c1c524118002c0c071201c1d480e05102c00000700c001c803c010409030001c400228039925507010380c04561400000030030131013a441e0010310126107466010b0805025200502590804106441011600c8038000341140c2160050800c15 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 271910089 1250 271908839 271908851
    0x301407170c0136080901122c06090a0f150e03040501030b04090f02040b1302040e090606010915050a051b0c0a1502102403050f060105040b060a080417130504 69
    0xc90700011101c04a070440c0e02d030703c1c1681c0d003190701d038400316801154029043c01504481c2d03c2c10605184292544400a0701c2c1402d05c00c42100c10401034072149015542c1e065014100740401c4d4100040d4454100382d00c0750b01070407411068a0721281142c0840c5a400c0a5810004240e0400c03001002820585000b07a808010741c0b260801040180c501d1044040c00c2a40418500e0025040503013048085040103403000b1070144d40b40d03440c0c800701d9000d50b0202c210080b059050000300c10301804200d40180f02440d0a001c070905184d0400484800c204004c0184040041d20301c074031030702480a64001c6c070074141003100990390700145c0300c0d141c1c888030404900c2140c000e140440d00c0d140c102c24040c002032035a0700901c41401c5200e01c1000500d04038220110315852003a00b1a9051030317134000700000c0d52088000d003030110b004d80130041c80c200040e0007045c0300e181070040c194040c1d19503000740c030209641031401e103410703440b541800c001003800c1c0a082d8004500000c0d80d000e00314201d200ca04d0864800b43c60800c88 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 271911339 1250 271910089 271910141
    0x30f07030c1b06050a061d0415060b03070e13020304061505010203130e180303040302100506030109030c1b03020306070f09080c01091205010e0307301407170c01 71
    0x5142c0e0141806484040c45400403c0c001c0c2c2c030441c3e00c4003110700c001039041c0d142c4e10103521070214590b82e00c040c0c0d202181040304010000d020005080e02c00102807142604140c2c0301c1c03120b030100401c09410405941880036450b9604445081c0080c2c0c0043e04550300c0c249400c1c50b0f00070b4005115030034080c0c41030342c5001669510000c11107803015400c604224100782803054001d80620080c00c00000c016a104150304060410b000843c000ca1080c0c0003040e1030a221107038841a030700c004100505c01d0745014020320101e5001841d0522055100c0e1640300d40507030090f00388130410f2494202940600c505810040400c0d00320b000780d440e0807080c0c0c80b4542c20aa6481140755500311643c0d8250000e500d400081140a140c44501d0020f0b43c490300000c600c0f03030007115003540b66410030f41c001c0e150ad42c07010800702804543e07848419642c1d1034140ea00c0300720342c8913002c024001000c02e105905011100250001c180724201d50203035060080361800581e5103000c0b18005018000945c031b00c6140c1c07c804160444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 271912589 1250 271911339 271911347
    0x909010909110f0a09090503120903090306010602070e070f120507030e0c030f12030c070b0a02090a05040c201216060c0206010602100f020405060c0703060e0c0f06070804050303030f07030c 83
    0x21201c0240302c0300c425800c01082001420505c441151f2600c010300102c0108260829140d10403100e6100564840d1040e0f001c251404806a10010941d084800280500082040705036880b03803c41c00d048100c5e4001440880c0d60f0f80c42e4204c80c405042c6480c0c144901140c0c980c00600d0f1080c40c0004446034440c0c2081050307120004007a0300c2005034090700c1d07440020000c80b000785503c01010001541007039100d403100300202070300700c94000d00143c1c0010014140d00d00314202101402c000e80d0104404c1426000241124880314440341c80340c040c01a003104050020040f000a40c40c1d04030113070ba08d401e40032080c01c1c034100a1900c101c070400d0906000030303c03032440003030080c4c100c50036580141a00540342c40d0314401480b1109540d01115000c0101281c5900caa031b008103d06c000b80340082c80390b42d03d503090003002c84144c80b89000454200e911411105da891500c100501d44040350078540e25010b5252060440c415030f4410750705400080f04108004d403407101040d00c6a42191001d100749080900100c2e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 271913839 1250 271912589 271912609
    0x9080a110a050a1409150303040f18140708060604080d0314010801020c1c050d0c020618010203010621060518150103111909182702031c05090901090911 67
    0x5688801400313100e0100d20b403062074242c0100c6080100d140d04030000001c24296401a0042c89022138001c1d01000440c01c0115404808a182e11080012120200341c960043c1c00107440c540402034100046036841c0d440908030f034020000700d0100c61403042e00d84400740103441402c8021225006c4400001389008040c0212f4445440c44800f4007010400701c548103881590032840101004400d108003003104980d482000f1540000d50010842d602d0000070017044805208240d0000e43d0041c00100461500110000181e82002d00414000e680e4023080390014425039008070340c00a41c905010301c09080710721440307002d0b80141c00310322104030348100158240c3d041c02e003010608520070010796000d2003050341034401c00c000b80d26101e100e403644c401c55100511000c0d4154480300c3d94500e044040030080700540c0f80c1140349404050540a402d8001075101c3c03545109401c02e98048180001003d449182100d94004000f00101c40e1940c491101750018000c910701103a80c1080c0100030700961812203612 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 271915089 1250 271913839 271913849
    0x180302030403080a030912110f2d0a0605101e05030c0d020418051006060908031b120a090302120102090d020f03010b13020a0306050d080d020a09080a110a050a 70
    0x1145070924664a000c440c1d40201001070401d6500c441460020b8240036084240e00d03116626101c0d0050812811420207404010342c90503a80141f50380c0011401d108881044512596030720452a000719254608043d80c90070014101850300013008044000d0304114001d0b071341010119516283c40c0412814030710b05500683c0d40c9540008141c804603d010021179501503c0030300082022100c3d09250020702d01c1da11800c1306e19030090114407803140380c18440c4000400e49031601d40300080c502402c480d181d100c5c1c0f802d950036411b5007240f580c6c82800c041001281c00c2c4100c15001d651100034517001000007225000403031140d1300480590000d01014001c2d2903000368018102c4400000f40c0d800c202840c0905002680c05540b0782655900540e03450010a5008100420250741c440d612100102102c2480d08038900c03924017003440c3c2012500c40000d0742c00c804000480141d8480743d01d41d0a8070450136076031001485126210300c450420110110040101a05542e0451400d440b00b04003c2c0d0a1a94011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 271916339 1250 271915089 271915093
    0x130506100303120902060702040c020a200105180a03050d120c0e0f1011010915060503060903190309020907020f0f0304051008040c0504060f0f120816050c0405010f09180302 76
    0x400c40f0f101d6002d0384030810503440100714134038000e415804a0107890303030700d22502c0140e000045088148800314420282b406440c1d112903030011120000a0b01c6801034250758904080c96040c00e10300343d01c030b40b40c4520103141c00404a501e000c240c0b410083c8020ba442d4190407145040080844c0b40a000b079092034090000140800c0c250603041c0144405104561140010422001c6401c0050071081c49400c1d40d8034020842900710302501c0b541042511312685c07100d4000c2c1e201d18104141174001206072500c0300845030340040c4149014a00700e0140c03809000c00b942c045140018000829000174250009010b08000d480707039001a20000781c0c1301d0003184946900a03a0180b28a505d042c455900564403d00c5040c2c00f441842c0c50310003050450b892600a030b40f01110510040c001280f1034034183c0010b040d8420400740c003041c40d549244450107074203002802d007081c4140071002c00c1014042c07400070703060180c010055580c0d600f01d11200c0c201c00b441050308240ca8100d0045442551020b201d0840340c042d00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 271917589 1250 271916339 271916357
    0xc100b0d020906130c03020a09120201080c070f0503040b0909060d110d081b0703020916091401051c0b01110a2a0308040801150b1e09030a0605130506100303 69
    0xb03000d468000280040d078402400e51105803810082d02c10041010941d070380041e04e4100740640580100c202e908500c07003012000030030b500144e034050215903220451609280d20703500e862404401540504000900c54003003c58089590b002c4200a041c0c6480304854171412031f1214400c3c001c0e81d01c2082d0015041a4030141c02801c80c1c1021401042c0301403042c1d424520700141107912003810600d810054910740c0151a0410039442c1c4851041e0700103181c02c1588040d00c2882401030041c984502c11581c40070112289181e20703030b004030183c602c00540c100180003004d0203649014010807101501a001c10550201403001d013000207108501c25900035001c500e00c2d104404203d00302e005895060b40149042c40e4003100042c02030014000601c048000480c0b240d0480d0344100541000750440801704805000d040f468060168095040406d0760a8203a0b5420075100440d0a00c00105401b41c5058201024071810030400000c02d59624018402d81c2d001e070301c6405158010000c0340c40040c0018500c41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 271918839 1250 271917589 271917593
    0x14040f0b300105090a0201170f07030b010c2a081b040b0a030f0803010306060923090712080702040f020c15060105071406090607030b03030d0f060302030a080c100b0d 73
    0x4a070341c0c40e015400429800e820101503107460035103104903482c100507082119880d0443d41c1001d0a401c06010150b00340005141510a050080c00002d05a1007015115048114180d004107140392005400840d940b412604018803811003000c60032001100c981c9404001540041c04550124a03c0003115201c16440581d401c01020300350400365564488801480000018a0390a80341d680f40d2181a00d0b644943c51420102c0c1219240da00202c58241401030b81203186100340300040c0e85404205580305076031900e8040d24501000358004074801c800b0000004103001d03648010b0914140b00721420700030303d5200e101e202e05034019550085070036881011444851603e0b581c90380d40c0140180b6025081010720344641c02c0040320600222983c1d08140c00f440144032060185a0388136030316040500c560804400800e44d41e214215660116071b580e4401a58040c4098000310001e5400404031854820b840c200102c0c00c0c2d008100201451007642c48501c020350031030040711508600201120f0401000e9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 271920089 1250 271918839 271918879
    0x3021803010b010c0311011506020f06060301060e0103020d0614090106291c1803030f0e070302090106110c0301020a0e031509100902040902090405010b2701050613030b0114040f0b 79
    0x6d5508400d0754a0345481c684000c1071088540007800d8a41c0249201044401716038100700b0042c01d00e40c02030341054018001c6615005070107046a9050f504000e400520b402d002d002040100d2040392410080710900460301c40c1500305405850000840b002c41285605003003200380820621122040c1051054114000f01c92401420315121400017103412840c01c1c2071003a001c5410310085012a0f9604240610624103126400c402c035485c034020b10390103007940c00151000b00144a1002005440c800d04003000009004454044070040c000350b441d2a8a803502611900c2c6025540c0c1c000d100384001584007103525103040e806526400042d0860030b1f01c1c040700ca40a440251810307a003003512b40c0048001a00c6882c145442540500c000003080040c240400618190240380480d01400d05926003500344040380845044490441e040307a9a41126000e0090f06105a400038040c038103400000070700030300d000d40b800b81d01c0f2100715020045100c652480e681124000d0310b82581140b0103082510080c687c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 271921339 1250 271920089 271920107
    0x90a080703020f01230105041e0e0f190b06010203132102130b03011a0604120f0807080301050319120f2109050c010206010e0705072103021803010b010c03 68
    0x80c2c41074842a08000e081c1600352203404102d520441000c010f10100307242e641c001640501f008032410b000b0700302c280104104014882c0003450400c0d6803224022000307001004211a000c2c1a02c0c00d44200712420540040380c2d042c581420340318081d0000004205602c04412070f91603c1d0f6054024400360f04086286190100700940c00305045040340d6000b0150b642c04500c90024000c0f2240400c1307c000002c10715081d668011200303080c0c81400c003110f54807039503014181d50544180d104140d000141780e050401ca00801c2c2d0f0005003003c80c00003040780c203009140000303505a030401d508844100e42c010381080621600524041e00d103045034010313400b20300d205401d80b0000ba100741c540304080ca00740d1001c00d40c40c1c054050510320103a5030744422104110b41800148210b00003400030300099071410718508010040102070382d0400c1030002d0703d40c08000140d22510f0a40d02d078101690450864650090000d43c002640710003404000c100401e814a4140509241c1006c10307503070148201d034155010750b03203088 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 271922589 1250 271921339 271921343
    0x10f140912130506030103050a030f140f07080708030c03010f0b0406050a05091f0c0302010b060f1c11030708071701030519110409030306061101022b0e0703140d0503090a0807 77
    0x550150004484e40c2d5000558081c41c00354000d0300103c0118a0b0103400d0106081c10b0380c080c450380000c40c401c401d680c2c0f81620380d0382201ea80d0195403080c0510b45a4003d1282440c010058038001c000d008009403401c01450607650401c4051801030344404060000c3e0003103200315000120200008015a44604083e14440c07001038120031054140008214000c5001076034200021009013540091650900400f5141c0005803846898401c02c0120300c510b5104440303036522610451007a00704410b2082c0d01400b540c00301c803824152a03041c015070003041403030151074440004110030701110a000107040319604981c0d001d4000d00c0d040000040314034007040a0002a03601001d02c080f01d083c251076500818424a11941d0005a00c2d4140900903001d0120540c480b0210b030f1040c005408e2030301c041e5004199101e1089010345084000c91890f00c09010300041c02103072802807010000800041c001c1207102d10b803143c001e8a07030800400c4c07001c4500d0300085030f50f0001a8411402e00022400a10040181e54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 271923839 1250 271922589 271922617
    0x3130204090c0303020615040204080309010f170a020a17090624030f161a09010c060902040903080106020105130b061c050717011d1b06090307030302010f140912 71
    0x180345450b240701d5010719610590140c1c0000301004001800380711003190b610400c450442c289424010000d50382d000f80b03c0824140b10880d550700030824081c2c00100c41003d151031fa01c1ca034910700080158065001036250300041188407845001040030728004510840c8180e00034802641c0300c00503005a01080e5440c5208100308a007004040c1e20140501c02c500903180c401070140e0035084146200c03404580e07102110503440b49074150204c000c1401168030341002480c0100040341c42e0b040250080220700002980b16191001107820140c1041c40c050403600315400810050792400c00f20704030310010b00c1008080f1440b0f40009101847c1c0f894000c02c60400761200c04408024555542d071a004060300b0141f04820340114009007a00240104680781a800c41490740c4036880c421400e48c0ca007090040c08000d050103001c01c088030f4a03440203844081e8070060031a80c9440ea20f04019000b003941800c20516642000360609034030482c0000c0c5401f44180d9001046014a420b12a407401c0d000500c1c000c0e000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 271925089 1250 271923839 271923851
    0x110402090d030201140c0702060a081b0a08040c060905130207050f0105090f0f0304061209030201140106050711061801050a052101050310050106080105190e0703090b0903090603130204 81
    0x40d15405a14081c40b407003a00005050b903502922074a4510b0002c2c030010300000700300306400c010b03100d0205070360352603105007800c400603100c528000310f40c14003403160a0555000800c4110326183e000fa280d502a6001d080d04403660b0340c8480703044400003424010550000030f03024140c1c0c5c0d1444694000d21a5900442c240c03110701c9500590701d82510b00548407000f4640c4200c42c849010700051207208410100d88000f18a020f140c903201503c0f1804c08820807009594031060142890700030340244141c41d80d100d140456540e183d20340580349401c0610700b074a00c556020b16640041c140001154044030340f146000040012142c0116410742c4007000180c00c0007020310078000013070240128001c0c40c50502c00c0141d590b605000c00e00d803a101880b003a41d008e49080c40b00400826801c0f8400d581514003e5880914034060107000d4035000c1940e0b84081462280d602c2080040c0b54035034000042c035481a0004003071a1140088a0303503a00030320031900c1d0303c00e8040020624180300c64461043c500e2001d000800d0b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 271926339 1250 271925089 271925107
    0x4050607061103010f030201200d0804050c0d080c070501090518060a0e151f200a05250f030b0708060a0902030a0b1908031614030406030f0b040203070c110402 70
    0x40350801c1e48840501742012078280110342e0040440d20f51811030320600315813035120031a000c0d9210341c010074030824004000081024000f0600c96129000000f41000700c0041d09450b00072901d0784900a400381c14001c01d44081042c1d88110300d01c1c0e080b00c8000b480544018804c5112807040d100c00f90819500c03605d040e00010704510b110328000e03c10071007040039002004500090250b080003080b82005500350b10312140d400075400c4141081c8014103985540250f06110a2951602a1207103015015210301212600e007801940c002d01140d40360040304050301a911410302204101c2400020300e160003890001e418035114920340c50303118500504400328240d503035414404030383c010703940c1e0b440d015126507010215080042e900c00b04070300c0d141e03070f0030b0301c2585407210450301e9004100c00e1340a0542c203800100d0902500e02c103200e005018580952350fa8076983d090150040c000004448842c500701544040b5a1030b1030300c244c0344a103005485032520313541240d465500c0800b007910096441942840224a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 271927589 1250 271926339 271926371
    0x180f0b040306270b0f07030501031a0c0d060801050103150c0503070302131814061509010503090f15040c2103030b150301090b090a0204060e120a080a080f060a0602030405060706 78
    0x400035005050050f0784d4181001d100c42d0b0210010155000d041c1003600400010f000e0400415010b0402034861809840e2068414004c1c8551404841007505045c2c012800c00410f6000324101d0340300d400d8407070386030802217462400e0352416002d62010490502c0002d240c540aa0000d0500c02082d034070032030803e516136680e03101350600950b0707189409940da120031300c0d590114030313034180c002004440b070054000c20340607250721a224a0215904000001c00811020710041260240c03040a00061f14542d41c060183e0048880c41100c3c29114002003000001e0254401090b401c000c10030740c28400111419600c1c250040c0c95005c88003030300400c6040350b0720186241400950b011300791031800451390951684c10044400d9004d403080c1c807424410032040061030b410003508400494252034100f140d04011340e03043d0a01d8400400602000c800203000c160182e4491003861117040782d41c01c400d104c1e89038442401401810b03402680056401003100388030b00c0c039064007d40402c40c4601008520f414401450107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 271928839 1250 271927589 271927661
    0xc0325080a0809120c1c060b18060102100903170402060c1f06060203090d0201030e030c01050a09032606090901020c0316050105090d090302040b0d02040c180f0b040306 74
    0x2640308000440d0543c0c05203001c1c0d00b90289010300c440141210740000000501d0403603600702c8804000184040341d020401e10f600701025210000b040540082c0e004e88096a030818101d80b0980140902c15101c00181d601e803140c00a00e0384c240d9144484180c420f90204007001015006030707400103060042c48429101003000603c801c0c409907400d82c503070004659030400c0d22090b03048081035401c00d211002150320380400c4c4005040e0240b0340402c4403041d0790401c6003180304480005030254200f4003000300c08031440c0c100381e900c140302e540c2c1d5070110080022205008400d40004a80c0500c40c0d10200d0950328007520f421f504480311000061612145145080c915406010024040c284890010090280030300c83c0301d5101948030080e1642d480f09100003001d500b030601000740300d030347c3d02c00d586605512500c0a42260315400b4004000080e01007a001c0c0c505914140301101c10b840c100ca000c221650310044c5401110b044201044c00c26085513220400b03050150100b0605a101162481000032513403110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 271930089 1250 271928839 271928843
    0xc0b0711060a0c170402062125230d0603240c140703020c06032703040b0a030209030a0b0c0c0c030102070c14220f0e0c0325080a 57
    0xc00040811500340d1801e1620080c2210b145600e4080200d2a4940103110000000d0fa18504c8140940e902d00c0050010701a1010950003901c9040185210b00c0341a40c0c1e690107070b00950303402184419000503020301031034121948000079000b210712118202c0c200c4404001c1d81c00d6070310b4050034072103020103807012141c1030f178410383d05a40420b0041c030000c0080002040071164066007800b500165110207451454440007030001658001181800d25200303114580340c0d814010040d0b582c80c2000384c0030f2420784030a16034240c250b01050241d49881180041103e044400008a8604145103190b0580013508105907080c1c040c0100c4803010002090445034500c55650702660039210102032007298039045141c040d00c0d0290b8410000c8801280c1000d070301500f280c03402c00c8003030001d0a01c18080b0741c03503a1900d4060400d81900041301c055455130f54022001040124000f040a10108050309985410400240380c064015010300c02e10740a204402c0c02c40d495000644801c0e0f00d80c0c80503441d00d441840d10301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 271931339 1250 271930089 271930097
    0x6040620161d04050a14031e07020f09040b1b070b010603020c06090d051905190e0f041107080a09030f081207050304053d0c02010c14030114010c0b07 66
    0x140030a900903002e080294540309001c6200e86490741d6015600c0708a140003414416226280c0f00601d00308201711104804101e43c0b00400e2101d01500e50010307044228128840c1d0104031841701c05060104080f88655000040d48056803525582d01c010002540c02401000208020f8030010030300c410500e5000786002e503001603442c0c0c08000c05038140040506885000d07001030103c400c000c0d62080589200000003031a1a4404251100c266000e11400003c0e2030080e900703900c0c060085822a003c010040403c3e1817410010814030b0070841107401221b046050f140c0103007d0300010449030405400c02d03003120309101c8181c0e601e85c0c90380460090300e4401200c049000044040a03444509a0160031820b0390400030b0541c10148c0d0b03416168a014040c1d400c0710810340d0000e0403d03d1035045400c2101d18400d03d00410b5648044030714000d8034a543c000d00156003803070342c1148264070030480e00c0c5809041c114034600b540d0921207030002901c544080339042140010704a4045102800c0c0716014035203d4803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 271932589 1250 271931339 271931383
    0x1c0c0501020319060b0408070b0315030d0c0c0f0b1b0102090910030c05011d01080a200d0501050d030203070303050c09060315040e0c030a03030e1504030819090206040620 75
    0xc103c0d065841d95088600031820030300003041007900c000b80080c07e403100c040c54540c44e0740c0e075400306207d000c4040800a6052055010051000b90090450300c0440e003c2c1498a08468a96074010706601d050f2290900580c802c204100414050000d0035400d02c801c1c1002600c8c0800003000144001010358001007001750100080041000b940b182d24000c24080c08c1110400790302c402c40074020030480110300c0c10f001d100d000043c044107155105040c8950500101d40215409850300d42e03154106e03104544220f8a031100224140c64040f00c01452954554025441c254840c5e404a002c0d080241c09000f46000c24007e01807140d0340d1790041c600c070348c0b5643c503003402c1d81d0b482404020075901c00314601c803a01e42058000428546020900c040b0030f60305030030046200004554014500090384000740021604e5605100405612602982c052140c030070708140c407160342003160001ca41c100c1400039030141b020401048940d0050a001e0303200b041e40c0800c8599004100700d140c0c100001580000b181500d610 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 271933839 1250 271932589 271932631
    0x1d07080d03090c0e06030f0f010209040e0c030c0d1b0312180b0301150c050a050303010509010b0406020d0e010e0a030803161b1e05011812030504051c0c05010203 71
    0x14041101200c0c5000c0c0701e14121030f12604000300c2180506a49041e01e00006020b0b42c50802c8174010044011040f601c040001c00d030441d00035042000c240788500e00741072812003a420009030060b01d5090040c003401c1c44c03070821410080c51058600007107c02c002e02070200c1000c41200180080214045d202c0301d071034004807120080c00c846500a000c2c800c03206506040c000c054162082d20b05498858503e04030110700140299280c00f0014802801ca00c00c0d1018807040000c00b201940c1201c9080c0d1364148a40d0b21000e603880d0034015030080c003005a0012101c200300603c580c1103000e841c0340604092060880c0074010501d91071090b04180c0f0710080c004184900801082002e5502e592149802000e104010f14111030300181800043e02040000118080740740c01800740c01c03031055100000300011a804211a402c150401c1d805413644000b400c0340e00c45440c044d0140341c0c17042c1e5100e00507011400074100811619504104180c0070064148128000100248021401500e40644d04049181c4203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 271935089 1250 271933839 271933843
    0x60507090306140f01060f090b0d1505090115031a03060f0106020d0e1509040b0d050a0b0106050f0904110c07080129030307080d1e0902100806010219061d0708 70
    0x10803821554580d6400410545803501e11200741074500c0c0b8540a000095440402c840b2050250801c2c40baa0600003441042c0c602a5404bd4220440200215001d2a41c0304200300720b00300e0903c260300301c0440285030a00442d22075448800c91101d1052a5500c0e034156a0210b4503201045542c0d2a411250100611410345c040128080b091028a4202e84800000010410b0b8010201d820a00c030200400e5000f0340307603200d4000461a660140040c1c00c40b240070305100d9542e152401c000c0d14014109000411140e1091084500035081315600510305525001400014000c01c1c1c0000b44039a401d000045140d0002d004c4080140307070910000c5a1601410700030078001c40c010143e148880340c0104140c200762804000c0d03c0c3c2c21070300038030702944801c03036505c0560242c03844000000d240e640344901032401e8004c0e588400c413514002e444800c280148121b00b80c40d007160584010340564411091f180110014418425900e0700c541c41c041018404c1000d9401c0600018008500c81d4208160a0100c0394007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 271936339 1250 271935089 271935101
    0x160e07020f010c050403060e102301091401031103070302091006031407020a03110a150c08060d15020d090203030d2004180b03011e0b0a0503071d070c060507090306 72
    0x241c00001c0003400c0f500c0002074440d102c0c910000301126205d10b04555512001d00c00c0c90004001064141310941c102002192a05030007080d9003219840b0400100751026544200051521181ca01041c16400e50310360740c1c401040582c1c12545071081c804007200584502e090140220803071010070311020b007054406800d45d401c0c0d2150320000e681c2c40c2c0070800403a5000800505503501400c2c07150002d00c0003c0324a06141a46801070055038411302c40515515080e07001031418406aa1080380544a900070071985a012040140118907040811400342c14141d00070061507018281c001890361a41c2d020078116040310062555060342e0388803401e80324000b45183c0e180028a2451a89020300301240c840c65108501081a0394555640321414252000d6000e212140c1d24404d95203664828650f14401070504411001c0c050b02d110034001816003000180307681a55031050b01c0c46000740d6400c007a8140044001c103420704004e180007480e404161a03110b028002d011540d036210100d030035400c1040c00d41d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 271937589 1250 271936339 271936363
    0x60501090b09090c01050306010216060906090b03060d0803091501090207020a0503030708030103060911060304050d02190b0a020d0b1f0f0504030b0402221e0b0102070b1b160e0702 79
    0x2d84020880d00f82004600c095409009090040d00c13503d0380c01c0100c1c074103205800300c0308620020442c081000c40c0c00101780c500701c1d0700c0c0d680c4003400513440c0c00815080d8081a0340319034200f0342c03808040c000262110007440d4006e80c040200c0701c1092010498a4124200b0703480b1495039580054420150700344040d506025040550045182a000b5035851456120510007d080340741d03240c0f0344508216030264900400c0c90000c1c8625201e04150800035202e006071440780380544035180e401114144100086070070141c0001000302c4030742d51200b06001950102c18041070181d5500e000b0702465440712034240c0b070b00120002040d0f090000003030140410008998990510a05100410004500d1680c590b405a4150782e805643c0701e696103801041c0035503142005180b41402107840c008143e8168a845408104c04180b11418522005a849080c1801801c114070f104000d03441c0010442c0e4804041c0103c840c0849a085440c24003150002403540c01c882a0748005030306205680340d04000b001507030700c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 271938839 1250 271937589 271937599
    0xb040503090406060e04060819080d0b04050a0e060f0c0417030c0307081809040b04060207030e0301050114131b08150402030412030f0605090a0c090f24020f060109020c0a02030a060501090b 83
    0x715108600300891081005044030ac002540c0a8008130580040d002d002c806032080c00a0b0800804440160075044400f00310313803040308001070003022402001030184001d50300340b40c905410881082e012680001c40c004103448100030901c01c10702d04200520038503028008103500d0741c00c0140d8400d0550780c0d0460f0140f0840000b4180008191511111038226900c00f00c016510710191034282d0f9101030140603164154600703000081d01c11400c0c5480c010301d04040f22a0038080c004030234150100c501400c445081c5800310a100004540941041500020805404444400440300003000d03a8000c0740d00b1a034000d2452034075142c450f0540074810700340544080600c90315003800080b52060200074072814016460b500b072001840d0043d00d101c40507001c01021b80d103005840e801c881090100e20610006503218500340c00e9104c91000c66890180c1003400007602460b40380190840180d000302c8010031490188103541700c01640c0421000c5100c520580000c078066140c004400d0840e26000210b50043d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 271940089 1250 271938839 271938853
    0x305061e0402010e010309050c0405090715020312070804030203070818090108010e060f071803060b030609070e072d030e070501020a020102102418060f030503070b040503090406060e040608 83
    0x181c0e00045203540f445406c2ca0001800e001c3c82c2032081c0b40c82030358010307250031925050a02c08100004100041907440c10403190741910301d5104100d0380c0f41700e500c03011502c8024003000320b8421442032103056001030103403040fa8200840c3d5200c02d029075210f4420103916105840e10344001d07041080d030303440c01803403110004c10601000c0c0c88250744848005240d002040061030001c0d402d203009220f01c40484000065045c24030351285071030401890f1601e100d502c02c0c03003103400150090000092441c10350b60070466480c480c0d04c442d0030a98040c80402610450020a001c004000d4040566101500002c5980c003190753f030040c074200340c02e050f071a811450454009407820b0001d83d80001d82039250300240d00b030010310709512443c00c00848402000c103400c0e025801000003590070211380500c04003880d50313074100b040300c0e65010340381e6142205200003000f6420900888011605c00040140e0060280069a01d802e15000c001412203000b900300d00041140d0f00000c6810342810b10409002d001000020005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 271941339 1250 271940089 271940093
    0x30b10030312110c03040801090507051915031b03200a0215060a050307060216140a050405190509210a14130f0b07110922030306050a0305061e04 64
    0x3089403605407140b003460700c03003101901c50701c1a901122004480c8038103483e141ca49400c403d40c080c0840742400d41b0780f8401c0800104841c542080c221140600d002e9510010720700d404030b0807103a650091a00310a2503031f5408481c14400b2418242d450405480d6000160186840b000050014282402d11072010701842001419070b000990720208060130403030703015281d840c1000292407142d81d03002035800d40100c07040050615000100414908100d244c1d00c1107a6450b880000300841554a900781e210000c104204540e0405501c5140c020301c1140000b0380350000000d2990603588d00703680d003c100c0d600144004c5a407a01c1c080c400744501c2c5451481c0c92409030012030041601340b0507070007200c08000005149a07c1b58141d2000f00042c801104801109035603900e00c0c0c0c8654100000954552440500050643c580514403504c0340f0302020040e24a14400070080c07400069541c0d0450516581d10340105003555990302c0d2400962242e0000d081e946409054034001c1c0003004101c490958029040c400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 271942446 1107 271941339 271941347
    0x6130308030708071b0f0219080c0f0603060d08090a031a0403030f020a02150c07052a100c020d06020f0a090918020108180a08030709030b100303 64
    0x400d6681d031004c0c280c0e03210440d078800c10b0101031304014000009102c02010044240080c00c04449098041101682d500580c0c0007850154030a00c0902540e1a01c0d81b8a0034504406948850460504030701080b100380135064000c1121402180d0404152207202c019802550003100000a14080c0b1200c04000d0205031015000a810508451000e601c58002c8409400031a4028803000301d80d200c1806850401500144020b107013041200c0210f94200228944030425004826154000308181801d0028801140f40100c401c402c07020102c13a04409410402038040e100d0034100d021340e15158000784a81001140f0307050f000300d51000e409a02c40c040e20203803040c0307500401c200081c0741105203207521310010081c000303500c42c00051440a00d158002914052940461f9042d240c44e41e0313400016002180ca4000290105404005000075110380c01c4d0858000d2000307030401340c00d58400074 = true := by decide +kernel

theorem cover : BRFrame.Cov 271762589 271942446 := by
  have h0 := BRFrame.cov_init 271762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 271762589 ≤ n) (h2 : n < 271942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
