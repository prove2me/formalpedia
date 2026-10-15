-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4431
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:35:39.323284+00:00
-- url     : https://prove2.me/submissions/7b26632a-0748-4f6e-adf2-28e104f3fc52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 796762589 ≤ n < 796942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 796763839 1250 796762589 796762601
    0x21002010507140c01060b181915181a03010314010903050702040e0703060204090e0105061906080405190b0f07020a02030d0c03090302090109020712030e0a0b132301060b0403050d03 80
    0x10b443e0b507481d07507008288090703a81d0140c110610040210230b0052a840100000801d84407501d8100101c1d0520400c60301000d44000c103980b00d09810303e481a0402403a19140e00081e54020b000100c0c02c3c45411b0550301c8040c8002c504a0307000da4900062000b21003403240c02c1e90030940004e000103d05002e00d0000d4649940284e40c00c04d4894101c0d0701c41992669620141d03002b036840307104050381c1c030b020751044030100703004031540103504842c80302117a0040c074405900c0b00071070700810041020f890002010801e0030004601c00950200350010210403900d00030300e203107a0448400c41c0918240740443c40486c000203210792150741c020045d046000009104803640d8803079003019410490f4050000026031501100140600584a800340e40c8642d1410492101c4880080301c0c000c042c0707004c030100e421a00100d20000c1480e070060064a5a03140d2400300d01c00018100c1001c0d201000d100d0307811410303d860050070b0300c91b4480300f030007444a41e40d00d1413540401d0049210241080e0800044127202621903030200c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 796765089 1250 796763839 796763857
    0x7021f09170d0521040501150e061e0a0e1005011704200609120307171c0c110607090315020f031b160813090e030910050c010c0c02100201050714 64
    0xb509110481e249644481300c8191000c1c0d445954401d003107aa07441c140d17405000034082400c1a0051810301e1030204451035043c41c00014107078542040d10040741d50341012280105005680d1301c0e124100400c0014174034041d032090301d003c104000c0d52080d0b94500d007034000b44100e070020075211041160051501c6414401080c856001d90b08000b510207075500d0b03000482c0e000c1102401982c55140c1440d10824070000c201100701212814000004000603000d4501d40c45000300501142d40310a41c0c805841da0312400440003e20b0103403c0401c070000b80d200e80c0000451340124000303000300425032603030404c80c40b13185010b01c603d00c0c0c10000a0321140001d2002c0e03240080c10b600e29071524a400780708818000300c0800031075007520001908010760b581c0d000303104084c100342041005550000000aaa00d02c1043c8442c0e005007441d00395180706900031815200385000c941c000780181841a43d004142180d40030f0121303c200260003a40443c14814418284645540d0300c444150040302030f02c2c0d15103500030a07a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 796766339 1250 796765089 796765117
    0x10905071b03031b020601170f101e06030b040b0a020f0d0b0315281103061e091009180b0f0c041503090201031a09060609040207021f09170d05 63
    0xc91031400142d2020070130000d120303400b919180d4140403903600074443d03400c28012035600000301d61964031000704107040480c001440019071025013404c03841016004558041c6000d25201c000400d0010001e051840389200da00b82004d40e5480c50340400890090506141c1520f906001c2d038044005254042e060b01d80006080310b100d08000321403000f04a20445255519590307038800214015044058030b2070b410b40344181400300714100d00c98840702e400010000c61103507481c041e8100c0c0502508001908101026060200d90301c0c00601c10203d10080340b0543e91401d18004014508010007100404201d612000780d90311910382d0081240c888001030001c80c8141d004210010b0030442c05803002c101c0c503d050300d004c5440e100d140009000c840a12040203180400c4c8185862a40d03500c0d60542d900a80441d035480d181c02071003010600a02a00d0b0001703406c06088000e01410f00c540e101c80ca80e4081e01c65840480a40d2504400343c0002c8014143ca1a036500000300140758a003d100502405680184 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 796767589 1250 796766339 796766351
    0x7050910120504030c02120f0a171b06220b062704050d26010b0a090905090610051009060302030604090b040c0e010b040e01050d38010905071b0303 65
    0x700c1404a0b242a01d088002c10750503019030007103042c8100c800c2017a10080014005981008500c142c441900d01c0c0028040c040d03e0700008107031003d95040e0b8045131030941222500d2000c3c0150540d481c4c00641c0c24201c01a5015400301428440e80b40580001c0d5004002e0501501c5020602c446440d41c04408041c540c02c449a40c140111a5003002c0c2c81075020320010a0703000e0500703c01801404415115802004102190141081007443c00604551007001d05660b5081d09020072074450b807542e04507048c5c032402c110902c0b03035403200001c659005000c009070800c070f000d03500c000f080780c02c0740f800c03010030085001c46d0f00800405000c0d60141d548036031302500104101066a4900701d08407411641215000318405003408154445001e80e40503200c0b154160b454039003031030342e05800769105100d00e0b440b444489022000300100070048200f200344c0400010b5150540c50b01c00301d4182802c01c0d28400800d0614000503000b40e150140d140905029221904e8843d540f940020703a4902540703060b03082c10f440360 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 796768839 1250 796767589 796767617
    0x121e05070302090a022a1b0f030d09090c11070909080904140a050f090c060d020c15041407030b01090513080a0f02160608070804050c040c05040303020d020607050910 73
    0x354030b07144580b82e500c5005070703141b05aa4030907010780b0052aa410401e8074110702d00c01d0407403001a400715007580c90500c09001c864180000307031011000d5420b40782c150080045413158140c000d0f18110598022004c10302600381da20380c0444035545a00788030040c5600104040149054942c070996841d070003007402c0740c07424200300081820f680d0312031042c80d05624820200304201801d0b1003441d800800c1043c11055505060f0502d503901c002000109208000c002070703a03924004d07c0c0e03040ba003000383c11101b0f03281c0c0100c1e82d00034204d0028048a003501c411404140303004039040013150540507a61700610b044616401c000ea40340081c60f0041c96140749890340302c0410302140994016001c8100a0f582e00e500c00b11018030001d0408032050800c14075255002e1050140d02c0d081039407164050503900e020140ca44d1130307003081380c584084070000079005071410210b252003e6101e0300030301c140c078001e03022034519041848040f40d0300c4008440100c00200705201c050140c1c070781312806103040c1100e4508025100c00c84 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 796770089 1250 796768839 796768849
    0x80f150a03110f0108010b040b1804090524070818031204050d0908030708030a09022806200705040f0b031504060b18060904140a0303050a06121e05070302 68
    0x65001a03074110740c0e000586403140b810640c3c4444122081c64110141d51401e21410070358019802080840c20021800942c2d900800d042668240c030010001c1c07280300043e0403d140c941e6060203042c0c5074103100c4000c1907185510340000e5805061560f44070015036407014000c0003c444500c032a20380d14082004071610200c2c9805c5250b014500500190440e03900d500030142020305507521109441e0400e01c4503002240382e80742a00d6000c105058081107542151001501c0004041281d58441440c3d45800c4243c0910201000c15510542c42d0030444546441d0912000703104a40c1202450f80400750034400303810a50880619520900804510110001c002034100001202d0b4020411002820403043c003283d4080c2c94a05281551451541c4444000d61101170130000c100e68003400160001c12704201100c44d0060a07030007081c041c0d03482c1c0501c0b860028080e02080c0c0d03500c1c29103800c0c403001007086503e1082104109920110036404040700d120010b009000c0b1500680c0c00d809810130002c0540c0f10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 796771339 1250 796770089 796770109
    0x15010e010c05160e090a0302100c050c060f01140105031303112812030209011709100513050d09180e0102040e0c12070806011704150e010f050f07080f15 67
    0x7460f001c09041c0303401e01c001207006850040c5503d042d035101c140c0c00004242c004c1061050012458000b06941d216041c0c1901c0d5449030b03030f10a03185407084e10108252043c1c1c802031035041e00e10021944010030a21001113419000580b50075401d100102110000240500d001c5000003401000b85c440c0074804040d11010b22840b606941d0740707030740c2c8100c007081041109042e008988206003000c50421816100007400012914450705204213014081071407482d041000001605041078103010318a045850141c414852000469152141a022019240c003941503a02a10780070789110304040c20340760003039024003e840c03e4940d080d5400c10001c60310001004410b44500075010120f9030300c2c0d00a07191016a4100108098100400c081c1800381903a4448440c280c030410001c2e25883ca80c86908004014003403070007070bc540481c0341c0142080318900640100d0100d00b0360075000c10650b0f0394226201006682120010002008500014030b401440090103400c0302c0801c0740c01c0350b8601c41c00041190303620 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 796772589 1250 796771339 796771363
    0x150b060a030e101a010801050a1d0a150f0311040b03120706020c0706020c090f0c19030f0606030b0307050108060607020405042310061e0608060612151815010e010c05 73
    0x6103040d0b04c00e00b9600108030ba0700410b0240e030498071aa2900d8603041000001c106032080f022001c4020074409541034000000344074048000d454225034414124542a0161104599079254002241c8e00da107070a00c078004031040c02030064044d410000340003001c035903c11041221290b90030301100307000950400c045000303480150001c02d4480104001c01081000040442c4841005501045500c01042054454116001002d013100d100043d90a034080c100300150400e406242a80c0016040d42c90380145101d030300180c0a6415590f220390044411260494007107400050401983c001420294052640b00e4012004001040840d030000c1719500714280f9000000c0e4404c440009940380320f0311541004000c1e081525840d400401d007604486480c902c0751006001881000581c20340321001120050f210b508040c60341d51401422000113070700070f070b08464058000f20100842e03000402e42002d004007844a1f07650143d03c00c010044950840c0362109034104519030080400207881080f500c000c440d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 796773839 1250 796772589 796772621
    0x5030706020318060405190213050a0b0f5802011b0203060703090c0f0b190302040b03150d14010c1e0f0e0f0616150b060a030e10 57
    0x2c100032440314021000c9180b0340790f45410010911001500002d0040c0e1103038480b040c2c440f040303483d03800012148105072000c031200074200010454407001951208007200d4080304c07030034030111040051025034840d210109110150223051040c2006464200031031000401100300344800b02e103d20000e280030f240d51003014203e51007005000b1980c0140512142e01510611a00420700715000241d0300c03c0301a020f80c09066907446031406001440e0500b0001e006c5600001c00da00b0381d10380441c0203aa01c4001c400c43d4104040f00a0034229100c0d00850f02200e059001850440e101c0200700b5003440060510281c3c4840c030000380030002400c200c4042c0801d0848000003800c0410300a0250401914461071510b001040410344034403600303c1403640ea500302c145001c0140e1000702004c220000c2a1700035840c0e1000011074800726411115803001013242c418080c2600203203401c0c1640e029620000112039014400384840d9024074400d90003a02220000c2044401890300364240074101c0d040013501c0f003190 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 796775089 1250 796773839 796773841
    0x102160b1b1e03090c04150303091508220203012a08062b0c080a03110a0201090e0624040609080c132003010e0a0c0e0a030b070903050307060203 64
    0x2480c035101d151240000c1c540120b494110440800c5803001c20b2401c00b1410520080045800c52004120100c2a5a13000c2d104116002140502043c00314541c8000c0340090b8441c08003203082044829031140220858881503444e03111040041940c030b091b6042005600325400484000daa800d010b000100003a40c02205400d600382121100d00d00180d0810301c051150110501c00c00d61074100c0480c9540d0455000480a040d481440d092100d11a41d005070840b980441c000c80c03210b20110344c5036440c2d03100303449504681c05d600140503110340c510807021f40419019002006003007618610180d000c4001814a0710307000950782c100182c980d07a992520218000071a0038040b4507000040c14001e011490010a481e900d64800503901d90a400044100c140d1150540410100b00c3c0900324513804103a40c40503141d603180c100f00540044100c44c400d049504000f03a03122228080c00518420300340180020751060f045440e0030040b1320020b01024200800e145001000c294188050041c10f4401d000169503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 796776339 1250 796775089 796775101
    0x303070518030102070309030201030e070503030d05090705010216030305030a0608100c02010c03181b05180901050106050c0d0806010e13151e06030506040b0a09201e0c0102160b 78
    0xc00e0401c140414001c1e03204010003400300381c0100010080f207509207404140d410840e9802da0a01d000c50340705640500c0003059015160380d50382c0040d446450b4401c00c0300e540175a283e0049a9844c0e103095540280c030440c080500200c1d12420055901003801c40380420036a544410407841d00c032803004000c0445130f40b80001d03010154203010784101c00d8010b01d8140300805040161140300a26958001e0921030148ad1254900c0c6121010344018070004100700400341e2a0071000311810b10886144545510b40400414403900441c180c500350480c01d07000780040200c40009a0700b804004e044981400340b100d0110266076681124041014451000464111003480d03042c88039503030581000b80e9030800c802a54580c010845a84801c0764102d28001c65039840c1c1001040c001d0811a43c841d400c500128004201c0c0c0c88950420fa040455484840f0301c0c84040702540c503154090b00800001070019007111204510105d0090016440f240300014600380e224950245d005440502c12a03410f410b450402071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 796777589 1250 796776339 796776367
    0xf0515040b09060f090c011b020301050403080f01081b0609030109050f1e071409130618020f0f13110906120709060e2413180f0603020904030e03030c03030705 70
    0x13401c600b03411103210b41c0d424290305d9552990841007106040090f5280e81d40201c0c1d0411420313000703603a0050700030481810141030003440a0804c4038245c980800840000078441800555a140150100100c0c038400b09510204034503540600d1010f40d140d07407590361441c0030070800c0c03010700a584101401003251a410051900d19113040d004081540c2e0440780d410440c80301100b03426138500b00202d60715061a51014824404914003078009003000f0b107402e18040a5115030240400428000c80b9500000d40031101080840160142080c2c0c200070f1042c0c107148015082d0b0021001c003d441c0640340d08000340500400c185070844015401c0132a0700d07505000c00c0e9900896504007610349071030040503180c800c4002c2003c0e0301003038034104113184400110b54040600131003510880030b0340c40c1900c0303081d503503502c200307140e10030300040220f33031a0310f8074540700220101841850210781d4041c00101541d40c42c3c0d2030985c1c0d1580c44101d0240c05010420824000d160184000c500c02c140c140c51311501c41425070807a003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 796778839 1250 796777589 796777591
    0x9050a1406090402120f0a0807060f1806050702030708070c03140f060103120e1f080703090507050405091501122112050c13030c0e090601050109030f0515040b0906 72
    0x1000d03a4048018400c00d80c031889000d6620035010b036407801100c2c42250000b46041081342c0a1052170041980282c00c000c1e002c0024a81c003401840140400c00b0065603c41c121400c2c24075038141100c221400760001510754018035070001250058900380212502c0d85240f80e030028408440c081105082070081003a02030004800803c0c11004020045040b03884e590360302d00600010302060903440c014001244103401e21004548041d1005803d20380946440102d00c00100b424030105090718001043c40d031103841000c000c20303004001088614604001d100042030068144d070380030300a200c006601f2a2446207180d00a154503d44120215810704100d20300140712101603400c6180e2901d40c101c2c0c0e6500100c4031010303034005040080e85441d4418100040d01c1801081690549912000400c3c0442c02c0c9185003190070000240c9241e50300c4540c0c0c42c0d1103440900410303010a1f003402046c000705954a00d83c4c00f00c13910400c2200c26000810500ca001e05034110b9044071051982000c100c0499803e01050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 796780089 1250 796778839 796778861
    0x20061318060509150d02060c1014070e09100e1305070b03101e030b011701060b090a1e0b0d0507121b050706151e060c110103020702060c0709050a 64
    0x10031078682441d001031003007100070340107229008802d030141c2515603944946280e495801494a0b546001030281203488a60008484110a11300286015200000e0607483e1254115075900c132030182c424020416144000703002885200c8450f00040f40f0280b01131081030080501c2e86000750401d6040c17030594600101d640201a58010178000d018241c5016074020003566880e010744941c1103080e4841c20651586580042c0c0f02046c20303000043d642400d16810304a0f55024002845000d407140c2820010b4481c1c2c0d407031242c20842e441002c000c001e0503054402d40e207119007011603158650f11a1120041d401018401000c55916030178040110b8101882c4079200200c0c010620502d403145241041c141c80d040001824001c0000e020020440e8a921584007100e81c5000790001c00c1d203810b9031902441070080070031a0030011810104001d4001ca02c00a503159000010400314042d1000440c00303900254001c0b40c000209200c004020384081c0304032406011000741c00030300c510300f66036802c1c1a0303842080d80c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 796781339 1250 796780089 796780091
    0x9030525080702040b01030207050a080309240a050612070b03100603090209010e061c0f1205070c141f0201091e0206030121050607020307150203090a20061318 70
    0x1094002820340d5080c0c1c2c40890301141d00081003825180168080c2c4601c1c0d80003040350142203d004200030140010f140120791003400c407081c603207050520503000c20308044030300300001031348001480c2003803e40c0100c1c1e8040c1c0c010380710403a520910b407202d6141444035008003008080100401c107191351169140b200520451409100a500c0c2e0380105d04268018015540c40b002d03100000b1b1030030386412019448004c2c0341494841c150703c1c1070074800d1000820070b400b1034401240030310348400f0398468421b80f003103250800501c0c20713098034001c24150400a00d8000e5500300c0ca2440140d0003001081008107004040b940002c680c5901c585032081c0344460a4a0703200841c00c0a42d41000580c03a00001d60341510508010010400100c5030303001043c2c2c0311a100100b2074401c0d1030801014942c0170010300145032103088031100840130110344006900003101c503001c00754801c10783d450101d0130040047c2d0a240c100e0481c002c414010f000410840d500440c441c10900900d00000c20481d010b5000c01e80750a890010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 796782589 1250 796781339 796781407
    0x91b091103010308070f02010207171005091f0b01020a0204020a02010e0f0d0c03050702040e031306080a050106140310080106080304230607080c010f1e0515010509040f0f090305 78
    0x91844500d015049006d058012569000021a4007c1000300040c4c101c02c0003650001c12008840359543d41e00c03000d42140b0320705242c04140e00e04030008140504005030f03880c1d541e16061a006402c020100300c024541107100b808420b10160302e40744003d01e404600350b4000300725003416015a61504d24032054600c1164025000240c03042d6105c03890300b504607071500c1d1a03a41c0b11001d0000030064210030842602d41e00000480c00140b5908521801c21520b441e1905801580e5003a045802c580707092161002140c00030018644160b5a4002507a00114128003071990503180d82003242140d40c03a4012441e580e000007814445d115003100c2c440041408141c02541c0407601e0400b0640034012444010507842020403074644c40c28084d0030030b414040c0400c2d0204004107050202d102110a50700b25440a00c5c54070000c100301c80c800030702d42102000d060b1205071a001184050000500440c0401c02d200d0755600c0c01b80114041c1ea0140f05035250103599445c0d00c6400a480c03c1c3c0082e8103040e030b00d12502c14000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 796783839 1250 796782589 796782593
    0x2090f010521120c010207020411070b0703022703010e070618090e0c150408030a020c13051005010f02100912080c1306050901030b0607140f030a0819091b0911030103 73
    0x45900b00b101c83e4a5505031104408a0a640a4022a40000c3d80981007849050501340b1030f60140000c503025a0010031180c40e54803060782207100314035807803841c0c100345240030802283ca102b084011202c003800000d00e5084011303015040c44840d40005002507030042d00c0440a80c1605d0180001c2c040c440d074104603001c06414140d035511008082607000b9128185890035144c884004d032002811004241d903520740d425000252106184445684078141c3c60443d142c1550b281d1042c1407050111030243e1502d181400010746612480b102d00798110701c00c06194414100c00c901038019250b101d00e0140400d5004402d025200f00e034001c1c1983c500754070a105421500894901460445916052042d521159040102c0282c0040003000c1d400041c00518182000100110b0000c036400c60380c15540c400c080300d4072841d104e10a0701514000500030201242c80410f00c0848848401040b0200042c00c40e4181d65840200e0074489200056000502003000080d0f080d00450507030502c4414114a90342c190703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 796785089 1250 796783839 796783843
    0x4060501020c0604093b190312050c0c07030c0e1501080f0a020d050129030702070509180601030b070f021933020c01060e0103020f060c030702090f010521 68
    0x2a22580c85c10a8403551081c542c0b101a440000e001010202c6010380c2e0010000545018a14004224114403901194a2100d580d0700b00340240a5030591b03030642004218141d006c003a21000e005034004100c07c1181d05040c035410030419000318400c043c80000d00b407074402240c0700c5d24401000000090303130b003c440d00174a0ba44501d503603500800b4030010b000d9544848400f48000c0c011000e0141c41c0d5842c0a00108844062040c111402c19641c1c461808262440d204100f46001c25102480540c1c0140c000f4045850a000420f03400240113401408c40340e0034140641c50304000780d0003038802510070000c2c4075007a544003840340040d046a00041c414030014001d0500c182480d820f0203071050702c085070303803680b440d14042a04049400c5001000c01103070800d403e49009601001410010350b01c3e060300010752010740c41013907048a40040401114140500c00d201341580300b81d21028a40c00200060340060f131f598885140110b1410342414144c2d0706100030701c052209000c1005030f40114401c403082101e100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 796786339 1250 796785089 796785097
    0x30a0c030e0d02030a0b090c1e09071d010c0201170c04031a010302100518030d09170c0a05010e190e100801090f021912060f0c080403050403080f09090f0604060501020c06 75
    0x7100702e40f00821f654042c005401c103088908070ba9841040341d00400100c02d050050012152021034840ca100e4803080c0044d40c20240c8681e0384192008402041c030560b600034141806000e0060420620030000070100380d090390400c40b1108464400440c040c8180450240e0090b640c503450306120245504640005851002c00050f1104018000500c800c289050403050030102d41e0280071600821140d95015010460b94084e04000f052113141690300308a00203540c44c2030b03e5000d0091071045040c10011290080b0341d22a041d001690301c4420141007261000e2100200034034014840c5d1418920f000c0c1d004100c81d64800c0d40c440e03040c40700c0c100c00b04a203100e40021a550445080c942d600c00c111916501c121190300c1f52504400c4a00b40b03100b446920f0300064168552500108a480c06044050340e554800b03541c0a00014001d0005200240610b0001d2502c10201c801c80313070608591800184000784d00f224031304140780b814403e21120741000d0060300c0140009002070983c80d6400f0300410b0359405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 796787589 1250 796786339 796786343
    0x2040e100b040806160e061209011a0117070201090c0f090c08070806040b030708010c11010c020706050403030f051b03070212211303050a050703121b0b06040e030a0c030e0d02030a 79
    0x2c001d4550007041c41c006c503034000c401c0402802140d101d45042001e0181100c0803a009940ba5080c044481c3d4801c00c034005103049014161110314002001c1c4a00d4140c500c0020300440c2959645c6051402252149415000500040040810441c200081c450a4401301405942400002d100b8803c100340c1040348941c0c0b0031030a490000d0220b900d1320000e880c200c007070ba00c201a03035481c2c804400708181c0c0c492080700080b000d003002403299902c038a10803640c8021a20541c00041d805002c2400003d01c0361548403c500418500350381000c07600e075880782001c2d141e406086150380c00001c0c48000c50404100d016600304c40c52002c1c001401054450403d030010205020b42c01c1000003415030104081180d0740c201548d00f100031210075030360314a403d42d07540d03801c0e002c1501c006000540103043c1c18820011085182001d04492142c01d403955101c0d03151243c0a00095441038850000a0400d4400c1000c3c010300d10283e603d086a013081030501070141d000300170030280903410341c000e05c1016840008210a030030b5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 796788839 1250 796787589 796787611
    0x3030a1d0a1a07030e0f101101090b180d09060509130e0703030503011802030103021f032409060605090a0e0601090e01090504020a050f030a0b1902040e100b040806 72
    0x306514001034000c021500001490024141440c0032000e00310042c10b81e1074800e40368000003260300f0b02000a0b4603800019a580b0110840c40807440c903202d07651402001c0f152000109450810307580b4610505030881e14004c0340924492040140c00e41004403030080901414004040c9040410050643c030442001d10700414104401105041e41ca41c004146400300c0c0c400c2d2100319840f0315004005034403c0c03096a804552000940c00440d80510032617041f654014044614500c56610000030009814550005d01d5030b1a81e040c11070380035410700c0382c11801d800009c480c0300c0741c2405030580850f64141c001c41d04001081c00301265a0f122200e642080c0c440d68102040c6550310000100c1e0000039942001014040c0c1500005005440c1c0e0841c80c0182c1c821185c00f03800503180c0040c40700040d4005c001c180d01d50320849150000c070f44030040480d08440031400ca034915003100240e041c01d07607005500203131549401004201070160505003001c0902524400700f46002d1034a0400c1c2e03560f03400a40b180c8032403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 796790089 1250 796788839 796788887
    0x30b1e031c090e0a09030f0807020613020d0501090b040209101a13051005040302151219020c0337140a020709060b03040b1f0614070203072303030a 65
    0x250b02903002d40c8028062242c8105551030000c12840117044a0002200402e03641d400b04001c41d030080300b0940c41500c46030300070542e03036569490504031450044020313a04407a10b540030700c0c0480d00a01401d10814020207000c0c441c2d05191040c0170341d5001c02800019160901e140512806081c035004000f024083c280b0030340c840040010108c8a034807142d1003140c1c0022075803805130388a0740080103030003280d008495103484500425016001172050074a00b00300c182050700001c4a18050804000004040710001400d01ca00c3c405028915840b110b4050038841902e0700c0543e0008001d031020018200703051055040130345d00700b800351400c0c64004441d101d140300400c4460203140f0810011000300001c0c0024451640c4e5040c85160560090310151600411308c00080c981c05003d800c1c0c0c1d800c512918512041e40c034584402140c2e080100c2d041c1c454004d6040052201590701005041c0c0640b00010854009040d4840b56202c5418008900d82c0203400c02e0140f41c40300d5400c031074002d2022a81035203a01034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 796791339 1250 796790089 796790143
    0x5090a050907210b090115030c031109060705151e090f0c010c110604030b07030e0f07090b0a180e15060a1703160302030405150403021302090109090606030b1e03 71
    0x5000813440789504606203d00003e014030f00440c0881488a050b202006135040603403088040d40da052600362213202e4100700e402880e0800000404105000705c00740c8481490981c0600307088403041c0c40480941d68034102d0541a60070713540c0a1a0032519a030001d041c41c80311240c807a502d541040070b0150503c003856500c0b0090080c500c1952240680c0203010325669a101d1514641111058400c46c00091405016808036440007407002032000c0c0e40c4e4020404545484045006001c0541030345421807007003d00010301e400841113966801d10b112201140d4180306a00c61131070850150b0011110300d05101c240805078035a07070113a0045d500c00d0f15111680d240070f410001e10b988504003405003146000350501d000d05a01001030029100b0807540528012043c0a100c001c80c062404069400130514404100310755940e80140081d041c181040c00d00715564807130394007c84001d0350281020907203c80c00341d0440c3ca000e03605001c0d10b15045240070300040a42e0b0100f5078840300116180d100c4010b0903070b0450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 796792589 1250 796791339 796791341
    0x201050313050613030e09090604200402070614090706081b1204030c021903081b01060b0a09050f0103050f042d060e0607020609060f041109010605090a05090721 71
    0x1c190848215852801c101d0381c1c1c03010701c40124009400013000c59010072100d2415100c000c0c080c0b10910003c2046440d640c07074506000380003401c0410030094150703421843e600c0360300180c144103000f854001081c50040e02d83c07140c001c00091649070183c1007405c050014503003280a44e80c0008202d403540c140036140a00500542c0300d10050721008410741010002059070040c03544500520a4500760820b000d080c00840040c490307400003c00c0c501d070603ca00b14a134070480d480180d000c60f034000003280c080e40d00c529544555000c00b0560001a601030b0050109051403215004400e00a190801c110300d09203500e490070f1000900014806500f401c485a95031309020718031980f080e1000340040700e510760703403421000820740b41c164100c3d180114800030385018004200e040c4210340b0740001e46100d584240300b0002420f0020300489480076100d00f040340e940c4803441d00c01d01800321a01d403140d650002c0750420910380030b164092881885840c0400100962007982c0020ba40031600c03030302114082c1301807804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 796793839 1250 796792589 796792621
    0x1e0403110a0c0924060c03050c12032d190b0a1a0c010617030702010c15050c04081e190f06111c1802060913060b1e04030c0302010503 59
    0xe4507482da00074000ca4402d01e25400801000383c540d140480101806900c1c15012415104181c0402d041d1002e00c000309004400505800c1c61404c01d80300783c20100d0001702c00a4100b07036003e5084d04403582d03403100c1000c10700400c204940f4000c51482031502c0c1040066030032400e41500404056219070346002251915001400900015150540c2c1c00c0340350750130848030360001280c5000341d600f000700005002c04050440b00b10070030300c800994a420026001540d40980080301100ca900030b969810440c800148a014003270f48440c40c2281d075840c6403003ca5032810011b4584500240c881280c89204500002051100100c613401040404580ca00303100e0420310300c44402820030341c01c1c10202e140c40c10404d0014a880641c40035010240b490002c6881b04554688004007641c54400c60800301500d0003c0184c0007500009020b02c40c000700481c909002c0d80d07040d5005054108000c1184400b1500c80d02e1148203081560803e5030170f2916580700c000300740b00d503071101905020002011070280c016100010f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 796795089 1250 796793839 796793843
    0x1206031e03120e011a010801031a0705041802030709050105092b020315041e0b06130f09050a030806030d210902180a11070b04020909072601051e0403110a 68
    0x3c000244591024501030070400c00f80e580701c40c20852803d0b1241d17004070603a0b811780ea001040410b240d504403041e00c42618025194809021041c000041c4400f0483d490034880f05070711602507200d0030040800340c6981116042141400014084603110352103c004614612813070329060150b50101d000380010070780031608007a40500036014581c280e1620088070034040d1344581d05d42407540c03141c1d00c400242101d040e00300422480619001c104c041c50700c10310304180301500140024521820850b010101c840c050700445d029041018004185a04120745e554000c00aa015150e40010030781d00801c00e0170a0000001410018002d00d44903800304c1d4041e001095000d0b010901d06600d0030f24110030791800301d40c1060300c14101041c0a440001c40c1050301e000e00d40c03116480109803203e50801031240b80042a41d4000c1c4a1140d000440d01e5034150203014213a400003510440c05c0720364200a003580d100034204104044440c500000e40003040c2000345e0300c160540382c240ba40140700001c15041502038040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 796796339 1250 796795089 796795091
    0x815030a0309150306030c060513170615010302030c0d0519061701060f1508190612051c0918150b04080d0807021b0a050d121206031e0312 61
    0xe14081540103503451080d02c0d0001402c141089030000c08800b6508103000040c409011004100314081c02200034001445601d0456195035840d415520141c4413883c08504082c3e110b1001c4c080a401d802000e040c01076400c4c41c040d8614544241c880c440d500c203808440101720740c0c41c400541d01c1d00044150014220a5000602c001a0765402d4144400555035444d10030b940380c2500020710361001c016100443d48401400c5400041c00802500c103000000c1c0541c8580007448401c1d1040341e11846030360003400410081020005982c10098501030303000d0307a52800c100d030f410101c07096503800c2400e07413040f206000003c6001104c02c84400d000381001200c05403400301d00780e05c00b081c0a0340b281d0190040d1820803048a0250540c0201200c0701c4005540040141e0040b00900211102002003075100007000790410300703002d40e0780001c107281c94100e46007a103d504c0403825607241c00758070000c00b500e8024461010b02a0a00316114045101416102e40d1600707203440c004041014002d50b9103c17603550210324 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 796797589 1250 796796339 796796353
    0x50d06110c03070b090a0203060c280210112a030c16051002160501030c0e18070e030714040203072d090b041211060715090b060a03080a081503 63
    0x75680c90700200011902043c024000400fa1107000070766800003500100140060f0300c3d0300300215465841420080c0840041c1a47d000c0a0416451201a408400d9008140d04103038803403131504030341446058440705102005500354401c00c407051140400c2084c111004400500034056145100d404140c0380769010309408021802046c0e0342d000c08a642c15101c11150000da02412a12000941c102600ca080580402d024a5100741d21101201c40541041e001210000c8001032100600d404492262015402003082081e801204c01f040c03980c055008100e610300300010b0444c0041c440c014107000319404000a40554031802a04d2881e0303458a11a40d0301e07003005400c80c4049540f48880d100172901010780000ea4042c0c20089408946004d0a0f010065055941c2c40020310340700002d0541c0000300b400400c01083d10385400d044400101800002c03074003424a0711903506000181450311401681c0c0d41007010a0015081300c032210719528100406a8440e42041e203441080d551543e00741c03142c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 796798839 1250 796797589 796797607
    0x506210406050712050f070c0314121f0303050403110d0609080307031104052b05011d010c030902090606031801020d090b0604110703180504051611070f050d0611 71
    0xb90155006101640e40c444410740103031821025a0015965003070148500000509a64401e01064800318860324115861051400c4918043c1d00440b00000140252070148101d4102c14002d80111600801c800441b0301d2550b04c000d0b041e801540b001503e2a800342410422070340e10404403d042030380c800c03c20070502103181441c0070f5075082105e200300441d2030094542440d00582d02038408903080108407400d4459588903409100c022580b14640442d50301102c040011400c1c0101d91304d9445c810002c0034a611801c8599080d035800480c17000c241440c1c1408100582c48004005a11800a6800b40c1da42e0b107906800034140c694041118106500c04a00303040c40140607001103041c10302030b90040600d40c03078a4040104491003100c0301a90075004008800000c0e000300f80102541000342c0c00a890150b641004c10f083d40d02c00c0704c41c040510900e0900580154124a910119080c03800c0140302c0700c2d040840040711003940d8041d10303100301c003a800c81804020058100464001c1d40c0c08000380c44013494 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 796800089 1250 796798839 796798841
    0x30203070206060a0b0a0e0f120606011808030a0c24020306120f06041106040f080c0a1e0501030f2c06060d0302030f0702011b051501060c0503040506210406 69
    0x40d142030006004000225600b460900b5a110941e1402641e00d840c203040c4a40a42d4650554075005411601c03a0140e00c0d03450fa2000d103a201c140b070681003c0c00030352501c08001440354a10070900c0005407041d28052024560000540d40004000d0418020b5088641400048134071400c4140c402440d030300c580070701c030a91640c0143d8003460040d901300031803ea040014548030340e1038041c0300100341d211900140101d00f214134996207240c0b01409084c07401d43c0303c2e047c03852000102d8009000c1503000310f10100c40f60034040d901d40c004006c001000002c1943d04a441c590605043c810141016100c0c0500d000702c481035402216282d1000302410583c01e0400344590f2002d01d55a01c00050b4043d400008189042904258061640c50f40c0035601e8150b81c0c030312031500398012002c2a03040002000c4011854194180608560b031700402c001c20301c41c210003200d8403801340141c1002040105a0920400140d4000151000c0c1e0388111052a03c0303405513032204e81196800400c29401c0003440c03082c44107004003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 796801339 1250 796800089 796800091
    0x702070801050c0c03030a0c030908030c03010e0c181005042102040b09011503090f02100305061f020c040911040606050a02070b070c14040f0f060501081609150e10030203 75
    0x14500240041e03591501c0e502d0f550700507020401940c1d0810800a600c3c1d00d541d43c0042c0000c181ca00300001c1c0c0c07890b2911049080d810803214403d44020000051060818112420f5031080c4411103843c6004600302c07480820341e1050301260b0044690100740031429000c0c0f826170f005400c043c1810a00d8a00280d017800710b050b1517030020ba02071032408208500c682450803c80d4103030f824003580c20b4201030038943e044008000c2c00101fa101410020b1080006a45803000c0d0030300b078110759a0206450404900300001180c0c000c09544140f0720210600200342e40215822550079800c41d80080c0d50096418203804110400c90b4141c0c1c40b900c2c010340072a0068204000d0880201e441d8203c8a01c503850703203480006803042c640e0103010200a40760401040050503144616032034064008106018074006031001d540504860081c000c0e2034002c107010a503801524940d10180081d403031550701d0b40f10040039140d00e540c1e0040300d081e010400014020940107001c6001000c00203007140f407032500021001002500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 796802589 1250 796801339 796801349
    0x16140922170d090b1b0a05030405030c01050f0a0f09210c020a08030a17060d020d060e060f090f031207031508031306030e1f0c14030f0a0501050d1e0309050306070207 73
    0x1d41a80498105d850f10b070a420215040038010780d1038090f40100554454000600c1110144820400419803250a000740345c000c2c480e140e248142801c1c021091415140c1c080e80f0503200c6440c00c0744c100e020072014024520401c10f5110400e9032054101000c8540d80e51862000c1d4100b61190000503070301ca800801800c1844103a80c83c0b1030401c00200a0403900c12007079034035507030001b202c012742c07805450000c90114440d03100322400100b4078000091181082c20865031107500303c0e500410044012000d00c04a1510100322002d50729150b80c0503025000c21201404080030107558030440002120080d8003400070303081c884212030f121b4190150390b032031610141c09070b4000a81420000c0c0b001240000740041945200e1804560301c032600a60500100940001e0364104000e049081b99180e00c5000110b00600403503030031455600c1e0241d981002c0e55410303031040c1e0082901c0c0724504040b48502800317005081d00510000c62200050404803690ba04030b41005906008103401c8c0f1110540000710f08080325 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 796803839 1250 796802589 796802603
    0x109090e07060f260c071a070905030102161103010902061b0c100c020922030903050105090303010f09051b0d02030406050705130b090a030516140922170d09 69
    0x714040104592103880580c05130f900c0d01004660406440403034409a5010300d13005070050034041d243d2141d20541070310000d6030101d01601c809001406a000d480640500804c0d4029803610301e0200070a20305851002c000f6028480e201100c1c0c01c00e9400390071402ca1260020b00c200d440b0901c10751a040498510003206d0020f10a84181e0007050800c2002d50381944055150362007001c1d200e40a00010090040c4258108002001c00c0101c0031000c29003030710014066565031400c1401c602e091821188003a20142c0d2a90050004000c4403010b82c2a00d0142c88000e8408541b030303114040400c44555070110b44550304034002c100f200a501d11035010354480e500800040c04103132244001520b051165000301005664140b04c03d00007440c890008003040c400150184604075642d4507034130b0070b0440e0340048104c107500c0d104080040000211f92a03103141170490710361040c0d00384191408500ca0107403b2466002c6003001480f002c1c02400f003400800b0030038810003290313203200001d0047d00900340d40400320364003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 796805089 1250 796803839 796803857
    0x130905031c0606051b01060306110705011103010506090d0602070204020a030e1902100e1807030e0d050901090303030b0102151f0b1903091403040f14010e03070605090109090e0706 79
    0xc05031405490111040380d244e5501e001d0095000d00e400d108500c00d035a51641d280c030740004c0080d181e07208600b45841c404461071f49940480c6401c90954461b031031207260100701400107210660b220f008075080c0f004112900d0922030920325129010f409071500c0658010710101b401c580c41c98058100c0c0c0c20701b58400d0700307030f400700032a4005000c188100c228001e500020301d01290500103000302007429070108010402c01040c1c008405881030303044100c03450b000103921a07042c289210301c01c000b202500906030404600304885080003c00925113440301408150716425440d0320399000f401080800d810f034000c4200140b800d10001210050309030f0a91004c040c17500d034005581c10061099511503034282012280007000100c08402034040703502d040d98941842903580c504010100024002814408500c807030003480c00044048031440e0310b100a040c4034070304400122542e8040b8038101079505034244292261070080048544d11096001010720710b00d0b000700c0681d161000075424045451a5858440f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 796806339 1250 796805089 796805137
    0x50c0a17040b0a0e03040504091514070f050307211413080301030f110d0506061809030327070314010c03021309181e02011403010612020913090503 65
    0x65840d0884026007038442d601d011401c500b000f80c1141d0954181e090450382011348030ba0018040f1030404908440a034403040c43c0d218410f004d8050003031919194030740545145001c540142c403116180017600200280000040c41311400f504800c800300755105080d0002c50740d490103c0004048001c680b070500d0b6802c000184480c40031200b80080f10740d21995417410f60b403842c1e0301c0c140544441e000c01c40d14070302004c1018009440d081000d01d0068000d0340103000c0e03400c12606000040102c5100322114610b2030017040320f040c1c8000126504012852400846001d54000210011540d00c0079200e0754041e51200000b40701c0c6e8510280c1180d03000c075000700142e41c0d095409508a100711500c2c0003610301c1e20a03040180e004540d214110036231558a600003e480541d40c2c0c000701c3c002d01d05000750041f64a414003825540c2c0b0180013612032441290480c55941405009812141c0402c0401c0c040f540000d2002060b4a503840b48a904606440c01030011800b1480c00f01e840307401c101c0d98000b0108854103240f40d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 796807589 1250 796806339 796806377
    0x250f05131203022b050903150f1e15121501090f0b061305060307020102130906030b06092205150a0b1f0e0d1a0708190614011809050c0a 60
    0x2642144c684569440b8110800a6401d50440002950f25004030064000381603039090740c0078802d003030080281c00d462600d00304038881c0c1c03030043d0f160160305d140031000c0100c03036400d441140c4800d4804403010705413605c41e03000162401e40c208401702c10100e06000000b03100d108540048100c001032900a00c4042c1e403850910a40f03004094050800c060550010096420000010354001800d480003510300401a5a5884035401d2a0303c039004095598404009014502c2c840e10f80120303003180c6614041c1060300705080c980600c1ca00b00000c83e5202440c1c0c80801c507081002155212a80c90900100c1c540340c800c50b070080c452496414000e0f0b00d00400714910102036200ca20340042c0e940c56145010407804c0603c4002811aa4210b0b4041d100a13620b4070f10307540d44840340c1e1281c001603443d0140343c40d00c481000c1c80c120710584142541401c0a105000803009400b810918000a18200200c0076038265000140481540700e100218600002d03c8426031607203001f01030784909034545080d4103003c030034490 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 796808839 1250 796807589 796807633
    0x3010b1e0114041707210c09020d14090304090b0d12080a090203031237180b09013c15080d0c0b250f0513120302 50
    0x40c0804000c0000000c298082c403109403076104504402418140c59480005180c4007550060029911201e410004203074030700009908064145407100844001d40d0701d00a0560740f83c06491041500404c4001e01d00401c0d5002850b24018100e0b4000035003440c05941e601d07544280209484542040040f00650403e2a030200505030721060340c50514800110407948084040c06c3c142d1500c0e190701902c809607404102405042c03600602408060030001031200090003c82440d440204003a08404000c08904c410316800040443e00410042c0810801d26010890604000d0510304000c05108440c401580b00d144090400c481c0c0d00c402a4807400300c66254210341607243c0920083c18003003000c2820540102c2e402c0c8040350998500941c42d0b81840d420000303400c0c150702c0005c0716000c04005012218400541140c18401006d140114821a0250030281e460b21581400781d92602010701a106038201c40103205507000544619840345091291038005c4c0c131040d80148a004c003008052002c2001c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 796810089 1250 796808839 796808869
    0x50306090309011409180414060601080108070329010f030507120b04120e03010e100f140106050724050a1d1c050c0304090219030207050705040207081b060603010b 72
    0x840c010b800c0744d20001c070154055004140c001c2e4509201000034881c44601d140940d11030740c0301c0c04104c00c4648a4074039104009102a04200303188004205188001c503541b001c0d00c5e000041c1003081c0f0785c40f0791300c2c1c14610003141035251034000c52400040c2600000003a0010303a841401541c4209640d504040110118103c2c061302440300c81001c41c00044409c0703002504094241040d0b2151a40704001900b1544200d6900c3c10366040044044021b5806118030107070304418003400c0201c041407860301c80c0c2c0a04140104c000388000050030a00344000305c1c3c400301607665002600180c00d0925400b00020700020380e42244460f00380100700f007003013a640e808455a8111030005109201111003010701c22500c24040b01b0501000300901458000d00380000c1018100c03101000d40d803040050212110700018418400800d4814450b035000218082002422103c0484001d82c0b201c1c0c85040c0030b03d41e48910801403400c2c840c4040900c07229440031481c0c03442910201d000f0005020300d10240140850711a01e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 796811339 1250 796810089 796810097
    0x5030c0f04051e090c0a051b0c030d0f0f020313171e030d0b091608060f090f04020312030c0307120617060609010b0f1207050c0d02060a1b020c040f0213090605030609030901 76
    0x6002c4074503000d48d0303a83c4411600e00b000c0b510084105c50100e4140161101c01c0300005001200500308c4940040b101e0403811a244001c600c1c003081d42e900810b020005000f00c0417902401070b446242d400301009480c40c1c048541440341d00d4841c0700a5050f507694001c00c1401130150070304c81061050f15040c00524411a0000090040c490031050100d514000050440d944024500030300d141d9034071528809817082c010b00c03050600c241041d0041520f00903807810380c5e0010540c108100302140c4402030580c0d80050b82400c000204142a503044c03c040e103000d802824140c96048034401042c800001c0c0240183c409039060701e242d0340c0710380320200d481c03250114600d00c0c020308010120010030061011a884606403808508100f603e07426241070a0080303202c3c5005038803030400c0c0000754016124100344030780400200d0000000000000c1d4441c501c80423014892a0740350307820072a406c2280c0454488008654240051a4a8003010310080c00240070342e5002c0c2c891100003c80c00b80d4004120307110f034681616 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 796812589 1250 796811339 796811347
    0x20d0f0f0e04240803070213110d050919060b0109090b2b020a06050a021009020a17010e0d0f02150103080f0304050c0607080c0606010f05030c0f04051e090c0a05 71
    0x200384005403c180090081109194800c0e42c85203041c44003000c00f40440c1e201440d40d448550040024244520a601900504c1c0c581001c6604003800112076241100e100045080e60340c11500900742514806030441c600d807003c21a00802543e039010b0030301d031030007602d0304424261030b50000c50448080c4009941c0044000c4042509251000c09000c1c0040d1031000000766040d03036902180d981c20b2564000004920007040c4512070302e0301400f5400e00e600347d03504c0400c0b03004455000101280031500c50344003559034852980301c05400a401010043c88400115070b442c0c505142c0051402d02c15440c2c020060281c140320780131001d402848281225002140c10381400380b84a4049410f500c00741041703071507210740c1c9104511502c503000900b10040c051100135440e103070340c21442420b00800030321040c1082801d405e070302c4015800c0302c00d60350080c2481c09a44c1e11523600c00740ca001e1034071460301724950102c0400e120824259020460032060001038078904031741c3e1100c0c0c50f980240d016800c000008500248 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 796813839 1250 796812589 796812617
    0x314070210020c07150804020307090b09040303020f0c15070e041118010c060f0f05151f0905091006111203220b15030706050901080a0902011e020d0f0f 67
    0x24018190714001c940a80c0d070302c03d035108804020301c1c05d51070780000450045400c10080d0b01e420300014005220f2180148200354103200080c96030300303000b0b0005050641c0402c1c008000f4502d002628045401401120503030503940c015507003542422a0b441000405600000c0c4080c10b1500548000b8100c01d840c1d076050100080c2e00004d65410804180c1c100b00c10440c05101060541c060f5460003484042d0000e0074100d124200c0040e40c000074001c4070b40400c50900c080b0292122502c1c00d0040b0024079202d1200c2c1c0300d001e0f0407100070900d80d100560002404050010f08a0407034000001c0700c1d169240c0445d000444000750340c03613411004000100c0c1c10306000007940380324044250100d415140498050705282070350307101d0001d0b0050758008103001c0c8410096515003000c1040e5406000340d410628204556040000e000704001071500304070a440b00d00c2d013021a40242c0c00390100c1d54030310fa50102e8060100030000c0d580c40341e01400380c00140c2009003e200780e90190680301000c050719912a59045202 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 796815089 1250 796813839 796813841
    0x130305010b0303090d11030a052505060a1b0606080106141908071202040f020d020901020c120c0f04090c0303180504050c040b032a04090b18010509090304051f0314070210 75
    0x28084d405010b048103401c0027507014800e03280c44080300c100391440e1907440307005c0744500500d80d000700e07004880400c4070704c28190308080c610391401d640d4140040d14007a1342c034000700580700ca98064042036003811408114000008d02120501d1400d1b07851600780354010480c4912200b2509c11483d96410000b4240300d10100c0301400354046001610202e40303468404104030890b40f004240705152507011500e040e66680c180440d130f002035000c4860040701014081019141c0380c003c28414442c0032400b290681c252103030b8210f1038225412417400c2c0f000361307500e04014110030a642141d001003441d940021950703190601c90719016010545100d4141170420811480960001c1e08000110b40c41c005030303401d1120006814000d800000d940152580e1405040d601642c0d6104407052185e84c0c00306510524840802d40c0382e0440d203003250144203d17112035034007506510858100766000312030350081c407042c80ca48800401502c00940e40070000c40e017886100c102156805c3d2010001038010a0700c5150042003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 796816339 1250 796815089 796815113
    0x160302060405210712140f03221a0a110703050604060903181404060e0f0402042d092d031805090f01080c0a151b0206130305010b0303090d 61
    0x321650084500f20f241000600e00b110950212014015504889007004425000c4d03100814290000301400c00000040782d4072801402d0010380c2c4101c028140100403088500800c0007401c0c01303c6080080008030990320700702e600024048000c14003c80b18aa404000000c9810440f50014064a4152647d6440401600c03c070b0390705070104a502210075100b400c3c0d400c40b1030020616031045140c27145d0544280410745215510158a851051040290101609100a134030682c100c5000030541c821501c01180804d0701004203c01c1c503000000708240550b9a44504651030040341c0300201b00280540ca250b48020210114040c044100742c2e14000a00488440c444241c1401c1030404882d152004505540d104640403079500702c200f40100070f521800e00000e84010002c0d01d00103806418541038640b8000802030403c100207a00301c10700704550000700d20201096000340801d40c0c07022031023980c46102015000a0f02c00d54030f0059010810300d80001241ca0107003000d071464140803440e481c1c0c9202c0e421 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 796817589 1250 796816339 796816369
    0x525050702130c0306090e010207030e062107320703080a061701090c0602070503060c0f04050918010609062102030102040e070f090602030306010507080319020c0c03160302060405 79
    0x5115182d08418400c0340c0550228040b1960300007401d6440c00c03510100707440f03000baa03c60700ba034410028180801d60143d94590003d0040e10140e079500c64042900410388040c440a00d200704084081c001b241d60700c0944030400070704521042d410000490b051141c1003030f1540ca5070140000400c89080024014003006600800d101c0c0001000e42d65080000311104260303034050800e9646c2d4040b402040001c0100303501034081031005102550519000c40d580c2d41003e0882c60464801180705064000d40c441140c004e460060140ca40c241480c3d02c009881d01e41c141c802242550903c800403c03400300500c12541111001c801d040f0442c1d030b40800d91100c440d075030b000980e0195020400444d500c1c00200b80d40780114210b9686c81017040d1105002485c481c525001b007401c641040080c000140e91200540d2065504418890b81d2901c4200c0d60b600c0d01c0144600318408980041128492500007003007210407044140d0079103e41e0f80100d0b05442029155000003507100c08188800e00803400d0040382c81203240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 796818839 1250 796817589 796817599
    0x3030605040e07050a080105072f19030f0806010f0e011407080306090f130809010201150e09010b06071203020715050c03100b030609041113110c010525050702 70
    0x40e444a0126055426601c0702e0346403940304180c1040320f81041c84008004100080c002c006504080100620352145101c44a00041d03010346482c060700654100700c4120f0a01c1c0c02150b1034102c904811006001d0548825000705040b44c2500710240e000f0f188591040b00142c0d54045003120060701590384444034046a4100420f01941d076000c03d400000034001c007405144120b84038034018041004c0c4160003003400c12180100f0701404440c0014456410485900c101660f4450340c2400041b40101500c161501c964400c04400007980c000d185c840074012500c1100030300079040c4210511000d841010402000a00c1039201094840c3c42680070344485407250407860082c0901d4a00e05054840c00d136620a00c140b400400d001c02070308842d19020042140396801030070340ca00342c4e00107184c0350401040544940d018200742065030303440d1040d000b480c1c81c10303007001c000c08001010858510380100c40d03180f00661038440884c080411140200301d03001010b01c42e42c0c05554444100710745070303007181c48202d800c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 796820089 1250 796818839 796818851
    0xb0a0f090b013503090406060c05060a09080702060a11190b060909030906070c0e0105010c230c060f031b2a031c090b0c091309141c090b120a090303 65
    0x400003d0910700441c0b4101000f1601e51013140e00f0003044032407551200084c4a03100074500000352001c01c440b58421095180042d502440d420314100e00c0c41203040007548050001a80c1901c1ca81110000344510240b200302c1d00b04520780b09620544204500e8054061011040058907502d0412640c59122180070152824003000002040254000d000120f6241546910a204083c1031515a500504091800c1d2803c100d0b00c6c2c0300c580010303a10001c94100720541c0990410010010800d00f10040320103040603039100f204401c002160380040c1c1e0280c0261410450340c503510180752041d190003a00c1307850b1045010f03c08844103590b80c01c52640e11105070000f4000204aa41d181c141d240d80d5001a132400b058400440c40d01050034207004000c0818058180302e54091519001e048201c1a0304031000021480c40d1801c0c18032140340000400d101600c14414034003101c01002e45034400c03a92a5849201c074940d103c00b44070009010355012030344848a2800094400364054001f2032903240242000658 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 796821339 1250 796820089 796820159
    0x9130203060613030c03151806090201090f1403120c030906031317030a0b0d080a050a050706060902070c14010215040f020a080c15040b0a080619030b0a0f090b01 71
    0xc8a04581d04c10b403461201100c0030010702c01015a20980e440f80d4807004c200740e082340b501c62000183d052034081c12030343d81c9042810459001380402009002039000302110503035541c1c004150110341c000014060700030440b61884d4034404400f0303103038406a40c1c009141808032140500c10190001062441c4c1220841b50000200e5a592808400c5546880d40a5904d14281110900361546114201d020315003040030300000c2421074080e81e2941107185091a50351130003240c03c0382c150041c4070000c2c180d00c1c50035800003201700c42d9500500d005031090100b01d100c213a940807000144407010b406140960481148104605450010941e00501c2404142c85804041e00498120181a00306c0e10403640014101116481e101c1141100d008000c0702061030941444c41821190246004100c00d0004c4180424495540c4000f6050740000d420840e0a030030350b43e81000d98000c402a2a00e07500680352240000150082d801034203046500080390789040e03407a0160350007400030304201c1a080e14070b903c0300c1950 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 796822589 1250 796821339 796821367
    0x60f0e01031b232b060221151017040809041d010531061a0d0c050f2704031101090506060a0503030403230c0d0303140606091302030606 60
    0x10b00160461444601e01015005000d4107a48480b0040c01d103000f0880d0102c00d5a420410151400e03034440c20250300c841800703555200380000c5291203000c7e00b800c41c0803c004c42280103000382004504649201e00c9040c0e13210141c03040d00002c00440103080c41d000000d1b021a403100d0060503a4a0080c1001070309803c0342094446401c00114030680d10b9441d00203201040001012524403000340c400c0c07038555000718120300341d8000043d9070001c00c0e25440c2d4030390b018803080750b01c2403802c45030010b003030076540031214940128501c4060151608c17800da141d01050381420810305010040e0007484156403081481c220f9890500750060048040204030210a04081002e008403903009202e44020041c03400d006081040800e45a0480b81c0070b50300a10041011645807402808020380d0400c0b0790302c000e1131401c6001d050440907840c1e2030f00710340d06000100c20035074560f0120030092140035a00380c46403201002c1259038460050705562203072440300d280c3d020300c070540d00450708aa0028001803401400d00c038011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 796823839 1250 796822589 796822619
    0xc0703020618040507020609191b0e0916060905300304031406070519090e010e060102011505031b0103090203010516080c04080706120f050901060801060f0e01031b 72
    0x350703401010000b2842420a4000e0681054107170014248078a01010301c0d582d00c6680b41c490440c00c580001c00d90041c8a03400c114030320008126411032185503120340094048a60540303845410340300d00880003208000c480c0031002035484030b98031684068600000c00040d10100c07100c44481e903007072901980a004103484204071918215001d943c8440c51420718140164500c030050078980c11074030401180a5029003101e03490342e010083d1300c1e0f80e0102c0ba6800c0340c81c4242600403141202e0000700114596140040403803150000341e0082c045450700d0405c1b900191494843c083d00350744110309030301c00c43c10103000c2c40f4013408041c07500082c102c40c41d80009080d42d00940d40300060403000d00c40a01110343c0041415400400300c0d011b50310702494000705550745c403a64850388003041f52048851100c0d45043d001b01502148651081c48103003001000e060090115219848256103000000107000884202400c02c451081000001e203a19503102c0c455140c44002084101d00764407200424010300c040484 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 796825089 1250 796823839 796823857
    0x3030911040509070602070f140409081c15120b0103230714101e05030a11030403030c080a090b0f07142110050303073509090c09030703080c07030206 66
    0x1303180503858a00c2c003030301306000c0da040340110020445043c44000b0006c811244031001c00d036400103200c031160501e11000c4c014100e500c40801c02588081c410800d0942044805c0c0b40002c00e110b56159441303404000b142c44000c4014042c0003024010404509a00340c03582c4004804032070802c9162120341c1c11070030006103800203800180d1003000d8112a0030007420100a41c0c070103061165050060740c05295001d142007131004208a40000084c01008154001c00d8600c117140d40529164281458050054426a1901d03400100c0100c0033408020b014040e0800081e00100d0241c501c4d160040a48d02c144002020a070520026011010b51b050303c1000608600d160801840c103103400c03d9013065000c0002804801c500c14401009002030741c1c000c0101d03031506621510130041c085240d5040352924412621001d42140507400401a00e00e0700c00080032558005c0341c00c120b80307640c2d101003040381e8091402d0b01c40c0c0503070268005000261480d0010f0000c5c0118000302c650640c0e5070b90003d02540c1c003074001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 796826339 1250 796825089 796825093
    0x21207080a110303071e02010918021206030c0a05010c050a050d050d062405030402010c0209070c02281203110d030204170a0305090402130e0a020c0d020604050a03030911040509 78
    0x1140306100c4241d8202c841e980007103020318039280013525808008460f00002d040c0340301401d03507004110781c0524000e4000745640da10500b92001c45404c0303a4000d405c111100c4c84095140310010305980b0b402f0034001c0c20054000c0a00c14028140030045440d03001c10041140c5601c6003003500b030086402000610b1031311885503910740d40d51202c10117403c00d54403030341e01c0701b4900c0d402d44240c0520642a42e03c0c03100e080f03506140c119204d65803800121280b100e4100060340240300082800b0103158404503a00009000351000c5086641c024a15807140a80229860780a1103070001403241000001c01a18058020720708102c4444481074880d040072000c40c81c420129034001801c220710703e1030300900d036410300300340024080c140c60307945010348144605102c251013541e00144982d000c1031012100340141c00f00c403040800750f251980307401c07000758000c1800104038454a00c1180d40f50f44001550b6100e40d078000007408107600d42d0740c3c080e4060030145204440c0b110510064004a0721148a0b1511542c0f060340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 796827589 1250 796826339 796826353
    0x5031f03080f07020a060f1d0303070c240e03120a0c1e110303130b031807080123070e0d060221070306150c0f02030109170d0b061204060902120708 65
    0x304004000007954024002d001e00240850b8600d41c2105240c0744031200380021202d0b00d0541070009003584110b00000748520307433900780400e003000d01c01d107204589254948200e5008404d40c50550300c580c4000380301c0c1d0b8590b00180044000f660050041c1054a229003011f0856603505c0c0c1d918484401c58947d0003441c140e14000c80303010710020b0a0040085442034020b1450000500d0071423640400e503001d044142c0c1d6002000c20201e06000c00280c2c2482d19100903149030b81c0e1a60750642c040c00c0704414021668407500324880c0e141078a0f9903614050900c648030712210146c00000d000000c0f107000c1d001d503021755090061200b040c440d0341c0150300c4624010b64041c1240b428000160460710540c2090800080300201c0c3c42d07140d5008040c02d40c1d4540c01401d0b01c2c21060311880042e000d01010040203002030814000b0300040c5d9901806031005000e50740c0c0c01c0c40781d000c1d02020f000080c0290041c1e0008401940c000c03c01003050b6030f10115001e80054080d01105d01840d60743d614084451740a51203644c4504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 796828839 1250 796827589 796827593
    0xb0903070b070305041212260a091e0b061906080f130f03030b030d02010e07030b0c1e0d0e0c06070305030406090b09030a020c030c030705090a060807060e091605031f03080f07 77
    0x2041c40a5580e4010200c0800072309082200d8240480040c0684556070380ca91050050002c502064107151204491030754810b030343d61400d0340c4040c2040d00c07085e000b1100d2101081482d103040d84540305aaa090740c5001d060360350620407030078a041c082d0060300fa080d10042617101085596009000f114025100801e0210700001490318102c580035000d021640b400b031076004c02c1ea0b40444c88104498000310389200f41c0c0c5400c00f00c80c0d528031802400090030280302c030a03650383c0761410740a0310074400701c0b1030f08001035140121520303180e40145040c7c40d0301803001c00101c8002030052001d16000750042000146828051340c560422090540c0e1140b01c84d032000c107140c194071ba4100300100d280758054000d400090308000100346d60380788500401384505c5a038000a01c02164943c0444000d080c0581207413080c0341d840d10f000c2e000c6030460003114010105280012039030302d400d118468003c0b03c03903641c141c519a25812800c1d40194110001408844100710002c0810b00342800351003800311025089a0f152018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 796830089 1250 796828839 796828847
    0x6050715110f120f01030203101109040507080108060702060103030203040603050c1209300414031011070b0a020a02100c050c0a0605091903140901090302030a0b01030c0b0903070b070305041212 85
    0x4100211380a2664010710041c0c80210703168142d12800036010801d54560144040607008005100740c00a140c0420070961a0b0f220204904131010607040d1041920f0300f400881e140c800902001d40941e0007013008000080c441d500c025032010520304514188001030001c2d0448441c1a0b40189080e0300a06403000d4003c0c1448202d000b40b1500800c039036002107a4129101d16005522868440e910021500f0b089504c09004034403080086490410411111900030040b54100c3c1c4001d82d40050b0420000c0c03000c007042c0c800c0f502c104034142c000b8178501400c007201c10068419000c2540410106201c60f80510008001c00ca880340d104640128283c44c222140b41c0c0f9000481d102c40b020760b400006000082504200c0c4604102071a440d03003a6a9040000142c4e0004c0302c41d030000703405201e00381c429001d1140411129041ea489142074041003940c0c1d0003280b46034042c40040d20740c107410090003000815124401014520700c00c6c20002d040960b20002c070001c218034034100303544444030042c91307138241540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 796831339 1250 796830089 796830091
    0xc2d06071d030d020a06020d0e03040f080c010305040b130224221d04050118081902070b0405061b060c04090f0507080a0903031d070905060303030106050715110f12 72
    0x660041242c0643c60800940d100d40041e00585190b0340041c4c42c1d1010340c503a811001d054985030302103d94440d5140e401c2460004e042c41a00094020460302000c59807103030143c240140d0704458011036603150141600d1840307100f07150403a4042584c15074041203910449213402d0800b51040406d4480050150010002c510b40e851034070708040c058014040003500e61000c1040e82e0003107481c100603582e50b1802c24010000310100302c4004100001c1c1c50300b00003100b002030007040354075864070305282c1d019481a40d070b42c6080e01402c50b40b010305000070f21081c1001030180181c140d01c5202196110b44100d0800e00302141520380441140000601b8007114000d03024a110a02e8000c030104418a0308040007401242c2c0581000300c000d0300c0c0c2c42d1140034580f00b6004905100109100200708821500c0c078290b1f5171226109076941c240c05e00c0e0007d00c0b03e16010041d42d0481d1956216503140045a64071001181d54011005000c41d550b10324403600e80507594003903d41031a08841301e51b501d0b050344013083e100b404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 796832589 1250 796831339 796831397
    0x140d03051b0c16120c090e071a040b0f04050f03060702101e05010303020607090b0313030c03020c03070605040f0e011505130f0807300201111f060609050102030c2d0607 74
    0x801c006041c0c13103111000942301c049032804035034112004401ca40c034a046100340e62002c0380c2c0000208040441d02c454100500c00c841080303800300c0386008040141a140e00c0c080b03544102681002c4205041e1140580000740c1c1010750b8004e2503428095400301004841c400e070801d40060344110200008103410561100181101c10402e038210f107405208007134040c140703640084c20040010890740405000300311040d052140101a07034029600c8010091103034101e40700c0c03030314420706406001030306007100f0301050b040e181a82d0b40d04494884404043d02d00d940141c03000f20050104280000c1c081c4595000b04000e00f00301000f80803080d02e0106600490b04815400b04800000c4440d0345004084050849240d6542800c06400304143c811b0000d082400b411030039000c0c02d0300343e01c045211514039400341080c0c1d500c46e00c40b030314465103440049a40c3e008603501d840325940840344440850708850008804e01c0188101c03800303a0781d24005018117140c0150344000200f12200c07840c4241d9100031441c00d11283c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 796833839 1250 796832589 796832591
    0x6011d10081b0a0b34020d060e030405180a0c0311090405040602160813080c060f03061302160b06010f051b01020c0a140d03051b0c16120c09 62
    0x181c100840c654842d844010304080c10840c1042e4815180c5801101c0300081c00301045041c0c4905244a001c10000b003004200140340750100180200300000c4040c0e9080590003a1464a510240d561120010442c0007800201d502c0309020005031583c80240d07107003480040c03440d01d0142d030600d07a101d02e040c1c2c1c52401d0901c09040c1004000c545020840e03064030202c034422180814180c485003400b0703009104180c10560410003850025041c010090010701c4d4003095030440000d00b80d0354004450300d905141c803560b544200200203600c04c040c10400a50342020006111030500c2950300e003d88200da1004803208540c040600044051190082d48160300020a0070401c6a00c4104040140144540c842100c04024148205042c100c005d40c1511811501e1008076403c0c68403034241650b00c1180e0300405d1030305204500e06041d4092207400780c1e50180320b0280b0ba00705e10000072501e82180d07400c0354403c0d08181c8200d1440041c0b1061084170900240a0011800e59843e0b10342404d4601e912550401680c413 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 796835089 1250 796833839 796833871
    0x1f030203150a0303021b1f27080d020f1207080705010e100501080d030507081306140a050906010609050a150c0f150e010209091f03050a0501050a0605010e100305071106011d 76
    0x21f80c810a0221100310a649403110412100e202111010004c04c60340000ea10601700003c030b400c00d0002501280c42e541602141c01c40510800e1072a96041111019a03180400b88135000000308000040c00d40039100300c001040203a102400c0902c0c20f5030340090808141c0d100c000402007185c0070302140e03058800d24581800385182940c0007429200b805041100000340550f10710052003001c1d4005140c040156502c10510300702108900060703e000e448500103070183c1000024454013803014481290001340c4451165450720b5109403403e01580c2d50072003409002000d40001400f5200140402842011040d408003018560303c03040304c04400384000181e10403c282c1506548000006a011840068100f01030001140c501c009184980c001481032181882c0c0100700501904407900c0391900c4001049003c1d5664011038401d103021100c241c100300701c10710342d40c526032198000560084003410048160421180410720381b1400364003140b554800729030341c0003503c103441d140030b604101c810f0300316040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 796836339 1250 796835089 796835119
    0x3060b03060f010806040905030f0703170403020a0f0303020f030703090501060b16020f0d05030d0606180303080406200a030603110a0e151801060c0b061f030203150a0303021b 77
    0x70603201c40e10302c0e410300446500041d0150340d10341103071111a074090103032600d0f0a110310020030650031094044000c80d054103d203082015210740710910840e0164000c5c052251241c407490103004440c0c00035010103400b00f000800400c0f64000960040b01540c5c0c000449284508010742120426085400b000004003c0000f0040c2002100c03c8025012107000100c1e80d600800118041001c81006215000200d0003000c0454694080310441e007130360700c0b42440010044000c000300c1740c103804018081102a80400c02062240c0d200848800384002ca03a600b5071615800e01c060380e040101160002610b4207014000c01c501105a81941c00003655209209400c021a04880880084c013070004c1d4002d900307490034981c2c1c0d000c40a0301d44500055800002c1d5031201c134018128166508140d03048064400800e010b4200104402d40705400b4841c00d003802e10386a94110040d60014003000c1959110300395041c0c1966074001c0101c0114802d070003c000381e10759007400ba040070780c00d03041681c850008041000d0b5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 796837589 1250 796836339 796836349
    0xd03050f03060a050a0e1f1a0c03160b0103060c0507080f18060d09030909020406020c1009030b0a0207260d0c050904050a051006020102040e04080901050c0f1b030309030703170f0c07050103060b0306 87
    0xb158002c0508c1c0382d16021f0032000c107403440c0154080075070b6804004518a040c03108900009061b0b030f005160a0000707112042060b00c20744212100141501000c102a46001c8096000352010f055400d04502a010046001600980050310170100142d45c800440f130400d5080f0100ca0000c000c00482542003e14100000c0d4a030005005500d0160501d4021882c034035100b480807501641e440b081c4a2442c0c24804410002500120812592050804d1040c032114181ca14011024540844c600e85003202554144018140c038241d0318081c440300348030301e20482d030b11405800d11540000d1320020312442e01180081c5103500540c40340d070a5910411080c403000d4155003681b40c0c07244e000f8480f50703910304403c00103e502d071090941850583c0107400c03a00202100100f081540c50805092407980140a00e00300b54491140e0f014403545070f1f00808041001440e000200002400d88078405402c2401100e00300c40c15a01c00480c00030507070070100f8140706960705131099402074001020070303604500d081c01c0400c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 796838839 1250 796837589 796837619
    0x4050712150503031b19150c020102120a0e0a0b04060b01020c0a0e2809050c130216121b060b1c110f0307052205060d03050f03060a050a0e1f 62
    0x2264001003040b40c545c2d02c410400140240f0700c00c241c402c1d0418000d905080d40b140c1c64030500c4114090404001480b240d1050003030303074111a600e014414541d250b10708004014085a817084400f4003d441c4208080b4007581c400f544030718012200410002003150009080503540d8104622800e01c0d03031014400380610701201580206c4100140041490417442009186009240034074080d0803c68860200140400c00b102c8030b01064800480301800402000140c0c0205001480300d000500e200f10049849041c2100050300c0a080000d4150300a0f0035860040040d02c2c1c0030340b50705d500c8110041140c2440741e400c2030720440500300311100100560b158400450720710001c600c40c202d21760003907402d0703034080c4086001407200030424164451041c01c242c60301910754180c0c0320480d15080c0000c1103820005960100941d155454a00d03041c907400c80c910103500b02038000303500a4609000461a900e450704510050159000d60b02890b2408007001e00780c05001d2119405483d440d40c008015a903010030000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 796840089 1250 796838839 796838857
    0x903020a0e090303070809010b0d050a05070602030f0f07020f040203131203050610030510050402181c030c0b0a11030a0504062a050f1911100504030c0b04110405071215050303 77
    0x10003c0e85a402c0d030a40501070009c0c000d5841840a0034003802c0001c00181d00e04070a100e8019a240955155000ea0303c901641d00450300d03a0500b0407a40075031035500001813403558030040001c4030030618030005c02d00f2030b0401c90362f5546803400154150140302d896000c0200c03004441c038042c0007d00e07100300890b200541c4810b4038001d0548400c0443e0581d0103600c0c085c400f808003e0703c119110142e2344c0003000c070005200c0c02e05000d28501c04880310301002042c2a43c2d0f03c2501074a0300034111009a41d81d100c1a00004c2c400e502d040d45c0c44850301c08012409000310b0060002c0ca2004c6030078102402c160381182d042e20204003100d40200c200b08d42210900d103503007044600904040d9118000d80da46d00c42c2c0c610610704890010480e8074051710074260492000d0004112110860341c3c510144a26041221001c1d100170700401c00c68401d800004080200a40d8010b00c540000a0030302d000e8404507003600c0341900c41c0303004541c070940190b1841005226000414100c5541d41d000c040c5858046502d0744550150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 796841339 1250 796840089 796840097
    0x302040504030c05010e030901090f050a0b030c1e09090105010e03060609070302070203010f051501141c09141509010204050f090406020910020a0507060e062d0a0903020a0e09030307 80
    0x79003418000c080200e411a0810001d00c1400010303202503841e0360048501d01d02017251168003040304a40c4c50304542c280c800184c03883d0300050802e801000c0301e40000b800d000728140204444030424a40c000010a18140c482031291100390510410a40e980305802c22410810121124800c3e0f5400140440d00010291401c48060301d89041c1107020b4881c85002940640c24402c4130700c00200076900241c4102c1880c00b00e4002e903804034004460415281258103481d4005002c18000b00d1070b404140020750804400002d0152004e50310110150502080381c182d542140340085110070b0070140090788003500000840c40e05082100081c600e11602200c4c1d40540d0700c090004081000603411030305a0ba5004121001300c01403000002e564004242040b5400d0040800c0014054090072002c022410010716445c18240b0031001c402902a424209441d01c48000034505580c482020080586002c81d50b103402e0b481d800c40c01404000591940201000080176007007101480021095a80100c41898 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 796842589 1250 796841339 796841341
    0x90801141e071b0809031c02070608060a24020115080709050c0706062403060f050634020a0b0405061b03070804060e1804020603130302010e060106020d11031303020405 74
    0x10216443c203a0540c50060361078200c4208024480c9000c040d0038181411400c40c1e04e282000f956034041c12076001e9491000d82e003c40c03028805140264403141c3d201c00c000e403c0580c41c0b50380743c4007002e548181c03055184c2c2201000a0b91100c90741d080c050070900c00014461001307150303d440300c070541d184903174411054400d42d10b00200302d071001c3d00411070304013a03008002402016160014004030444901400c4c1400d080400520790b058001e01950044502100104030b01a1800b414040160b01c00241140303220440c000c0c002c2030b021100000350001c0503801c101002064948180043ea6025401500d02c4030f609020402165072141d04488079551070030198410344a000400f5031950062640c01046400c0120380465a05c0e8890124052000111204d07920307040c084d2243c0c104c0c00b0701a18040c1d0030950070030000d10f5012010540d004038a20a100008209855002103400c3c10000e030414001070304001d61107203056030b101c060154038200c03001c0503516100200b82c42400615052000034003550b01c2d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 796843839 1250 796842589 796842601
    0x30a111b151605030424110d0e06070b01080d02101103180345031b03070e010e06100504060906030c0c061418031c0b03010615090801141e 61
    0x804000610350200842e0707101c9440d80c0c8140b1185101c00f802c0c6c030180462082c2c405080f480396242450190511001c0d1101c21a03c1c039040350306403403103200c4d0764100318100300b0000050441c100c984e00800b4201c0c041d020340034076850001c0c181441c0001c0c25512504242100800c84c0c00d1008aa0b000041c00c00040d58010080b810541035005481d0041d581011607403240d2080042e81e07888000d00c04840740c402103c03c00300302003030b5910344040d40c0158059101c641800141107681c10308804280b0000d084418685d03803880780f082a600c091304410340d4100ca140600941707041000c8101c8031107030a42009800c160924070000c0007040c1501c501d2082540f1a62840051400350034040d00d0f0a41100080c4140c43c2c1c4180110785911096541c03942034a50581d03400510400031042c1e80c140c0c404101c2c03c05042c203410100401810700e4820301507240d50b031590002114403004070380641039081c0c2d0f00e401072618a80406a42103408400a40b8480380c4080b0030400d603581f030b8100c001400d0b12142c41421083d2290 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 796845089 1250 796843839 796843867
    0x1110f0c0f0111030c011a10020303060f1903051e03041a030406140f0403021002040627120f03030f110702010c030210020c0a0b0a0923030705030a111b15 68
    0x2901c0f140b030704e0100250284034910107400403820056044030302a030760b200404c01c1c04070510648a400340103070000d00119401c0d18190b461441c0f8818020f14840c0e042c00c08401250301c8141c5a801280c003584000940c242d0b100d400c900d001099220a0080c41c2864075144000c3d0b0342904580d060f0303c40e64400400a010000658480700f0f103842c0041555985150504090040d95410781d0164013510600210f250389200c24000c0b501550741035540e0660b4003180702c9150740003000507900f20303440d594544008103a220b007084506003601d000e0b441003500404581005000c807003440c0704000d0b0440c00c1404483c0c000000d0f404983d107040e42841c103c12100d02d0790808038241420380c0901441c1500000308150880c40004100e85446d01404200025844068903081140c0c805c0c4402448800409509540079400340c1007482c444203180e0a80b0315003078960f6185070940c0e01c8002d0740c1010400283e80d0b1083d18500b000720303030550040001e24188ac140c1c4080011700000751130000408864001030f20301000504 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 796846339 1250 796845089 796845107
    0x10f02090d0b250c021f0912081c020919050d031d0405040804050a061806030c23040e0108010e0606060a02011104080601141f0e040b1201050601110f0c0f01 69
    0x104000812440500e000018040000c014099204a1b012540340c018100d14405500078954a611510302041c9498208075146400360415112100140004090a108680d40d1100b0103816280180c4c4d444492040162507241c411031401c10488000042c440c68840300280f090141d0103040040b00b15101d10b0100400a039400f84082d0400e01b0036061201300100203000c0d01c1920000c8a00051880d02c03030700110b524001c2ca144607080c0d10f00100d010880c8500a9100c03141d40c441600d0508c0c80c400c081003e4416408031001c1020340170300e0000e010003e40c0ba02440080c00341103104000e015122880701c4d5195120303800740581d8803e010000340f0884160003580400704880d60315841c41e485660351011103480e11404d10404210114a0b0041102445c0064030341d026112074030207080312030f0640034084554289003010550000d6a511010300c0030b90300e901078100400010f4001192510380030000500d1001411031226050b0701000040c2c1001401051403501c0420a171024001c1d1043c4400495800c07007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 796847589 1250 796846339 796846381
    0x380604150f02120c070b03071e120b04020a02030d0f060f031103010506040c0206010b031b03040807171e0c030409151a040e010608060f1201090203010f02090d0b 71
    0x90340003015102600081a50010741080c0c00b40d81001c0b620000c840c04910400c89020513580000c1d5082c015100c4c81805107802c69858640075072039900c441d00041c0754000aa54907004130300304003200184076445024007852114103881c103600b00074680380c010b0750301e01030806080081074032404001031701d0701582d0040004000c1c0c000d100c0409592030038010081240088028025424500041d00500b401d020f4980d500825500500150313290142124a603000500003030000840c00c200e0841329110714001d18091801080f140d43c0d6003840e482c1409030150300500403411000103100c403120090303004940802603000c91910680e2511308156980c10751203240c01414401d40b0b8480282000c08801c81c41c441a00c420203100c80d03921403414030101c0107000d14420001141d05d04c0006010851081c6145070300020089e220b40303824145900014005076094020300c1140c0e640c3d04041c000d510302409107001030a1031038002c51030b2001030404241d0031402e4100180c140d414400104070300031401590090145 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 796848839 1250 796847589 796847609
    0x90405090f0106290901090b1c09032c0105090409020d2003070e010e16030b100203190503091903020304030b01080615010e03060610050702090109020c01380604 71
    0x81e242ca5040310f00e044401d42d0046441c0025001c41c003004c0180040340c004901c161140d40c0c505207040942400759100140002d841490600032000304481c3c1e000d4124120b03c0794540e80400c183d0744820390480f10005c1c00c4124605d500400c040180d0742c01c50201e07120750300260b07130210300e038a00c50001c6007007614000402400d18440040c945650303070424084072800c0c14114169050a981c800742e17502001400e0140140c0c179012000071a1500d12004c1c100e0300e00e0381e0141401302d00f03070364120002520b284c46808104050b03000015840d12649842c0035500215125050850441c20141106695140e2041c0c050000b1002c140302c1509240c0200207541c002e40d072143d02d0501541e15441500d45074401910034141081d0007040141440d80207100182001c2d6018000300143c0d502d085c100248d000601d91080148130041260314003586404603c2800380011003c0960745400e6001e1442c2114030303910016032021100e840c1461404401070185003002d80106024401080d0f5500145107071041da400704041d9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 796850089 1250 796848839 796848851
    0x180a110c0304090b06070c140a051f02070609080a0602130e011403010f0207020d110411070c0e010501020a33020a020105070801241214100806010911090405090f01 72
    0x190300000000c0c02901c208140501100d4118011301160740505403000300084c054070310600c00042100f0449421400007040e844919543e2808180000400c2140b85100111070518621464041104400500440c50318241d00c40c40c090095455110500e0010501500018a49011f12000d40d0010282016070180c1c8207650b0340b07601c403401d615000e42c0301034002d508100400342d00500300e00c20758000c16000b400180c04100a951803e4010000800300e60744166a108191030170042e0310064940140b01e0030619400604040c444e80b40402c05901c1241150b2140d200140028490240d44c0c222001031410001d1584501c07010450500105140d00780c12740c404500500042c2d81500454001c2e116600c401c0000c0e40c1b07030080b100d10b000307a480320403007856158510150302d02c0c89500f00c0d05644484100020b10301350911490b100384d080586180d40700010340320007030140c01010f02140e8010f0460150411800f0074040e0301ca4820b004500042c0e00c990382d100001109081c040c401e209480c1d000c0c500070441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 796851339 1250 796850089 796850107
    0x212041b36020d110304050d03050114040e101e0e0601030203030f0a091802070605090607050a050906090d0b04050d030203090d08090a0f140729130801051e06060306180a11 76
    0x32600111807c1d9a1441001ca10f10f611502911525058800c01e00303280007951004c2050002511800c06125010f200b014540c0d12000a05d104010030f40000c41c07259003004400f110316405842c101c20140c51079420072401040160b034000110b40041000b502030f903485000703444066904030aa41c0c46502c0c1d09000b812098803005480d80109174180c0709201c1005642c03a80b03c0041d079120001c658280210b90f00300401c0810902400c00f03805030a80c0140198544000540490301c80410503900b140e01c4070848041c4000c000041c04100034090f00c91601311305600d00080070981c2c03490060085024800d680001c902c480d801800a51416a004000311501c21054984614600701c0d00c00810b950303004408000c11501e2040680134250368000100e48204c8580e20100f50450f030000350000c03c9204400d40001d8a803400707001c0c561050146810300b0075491280140800348100080400384148002c000b0420300d43d03a40070b400d44502a05da80c681132565200d6025030004c0c0215489010034000102d06040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 796852589 1250 796851339 796851371
    0xf0405010f17030d020a17010e0f0403081f140405010e0f04022b1a0106090e0c0f04080a0f12080103021f02121b0d031e0504060212041b36020d 63
    0x600d982e1f08060300880c036a40e641120311840d10550755260100d480d80007040120f449141c1c41034100d10380040046000d98091003070410308400d40d0201c01c2d580410040481146018414140101000125083d5510305100c481c01500d20080c8020305c101d84203401a01e06524840364034200c5036501c40300595242c1141003096001802d218042c40140801002080c403611a0741c410040750144500c40107161110000708010303800151903080700401c20300c8001000070f01003101e056080d0064a102c0700ca0340c403a05002140c2c8811022007030a002c02d0500410068565080040a200000000851b9001c22a500700c0c1007610301070100c03509603000301c1c0d100303280d105e0500c000c0d0000480360200e580c48102c619043d01a15074011440201d0171880111030031000c0c039a0083e903401441400014a4000040128180c507407007941e0540e6858811200c1409010078000c3c10005000e841c0140e00004022628618005c0c040d43d5050440a41a0f4074001a03604a50161105045000014000420341500d144 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 796853839 1250 796852589 796852607
    0x1b11060a0519111e0c0625260c0a0306080105070f2102040b0a030b091320040606030b01110703020a05010e0d14010207150605090c03090f07140f0405010f17030d020a 73
    0x101c154054140442c47c84048118080960b0405170343c1203903c10507402d01a990160101c0c4228011107814800d1700c034080301c001c80d4a00c240501491903403180b4103031500400b120f04075041359610741e16000620020b1600465400501400c81c504201c0300d40d03610100c4180400c017011072802c018008680495140301260241840c0b00c0d0b030b503034100600000ca10400005000c240d810a072810103034648030010540c001c41e0307005000d00110b00d10003c00202e0380843d007118090342c0300b100003a0b81c841082d116980d01401c2c01040800174001454040d003160001b4500c0200c6104990500c02000c45000c401c0c1c6802e45460703650f41e0003207149901d0a10030038609000c2c0d03000d00700071191a0908804100d0565032886a0000e036840070b012403600b50341c0c01c0d034466500d60014003010014490301c00300210303004c000c10118020b0980300d071001c0c107504074820a010711101d2501d0311a1180d41007100610030320380303000808011961030301681d00c00342c02d4140e0b0590a503c05d8510305010107000203500c041c450b800c441c8a07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 796855089 1250 796853839 796853857
    0x603170c1005091e03090a03020f0a0b0307030501030b0711061906030f0c0305150f07050715091208011a1e040305060103050601050918030d090203011b11060a0519111e 74
    0x41d140071340c0b5400304a450f446514041e940c04006d0000600143c00c01900700c580c0c110000d4030a00c0340c2601d51014000681082360081c002a1316080144100188441500e40103401030919440700701d0007913945078503464024585001070380241721201340d203042a041000216001500d210401540307062019108841c0d01060702d4520940c03013460003050f401484c00313106802141c044407143d140c0179000c640e141d218035016210381d0031317034580030030b0070207a83c480c00381054072030040348140004521003c1d10f420700c164020216500d150740b003600d42c40c54403012034007a03011602c0d100000d101d1154a46001e801a504080c1061040c00700100402c0320010300513058410450f61440300703548014110804000004418040d50800d101c606025020342e0407a40501e031000300007203000f84005c605c5842a540500180002a16191004103014001d224030381d00b200c0201c0003803000d0310385224601840d00c0c00035232484025503204144814125014140d461801c00301d15100740ea001e5058000855810440f80d0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 796856339 1250 796855089 796855123
    0x19060f0617131e020301020706110706050a0209030706180b1c0509070b0703080703090605090a02130902011b1a191401030507170309100c150603170c100509 69
    0x490700b00c03445042c604001c6a0f2051401d509846161500c0102c1d52110800701d0f0950340034400703400090460301410500c0e40caa2a031407501c50f0383c01d01300003041c0c3d0b40141c0402195841007104004a07200403c24100317550b00b0b8101510440a40c46010204044650180c9542c110204600c00ea0b100c0d09841d51069008400c0180442c0c5c552180700c5446070300500c0352003147c04c0208555000030307001d803100f80d03401102401c0c00102c108483e10340b40e058907002c80300400f590700300c90300410031458504100d02042100900c100079050580d8002b80a0300214818643c00a0440d03203004d04100001000b144900d600b00250f001c28180b04410002c108441e001c1d101c1034078140007845602d112a4402241200d03000310051064070b1801580340c1000e00c918001e03070414042002010f00c40d0322a1141102000300329a58801c1b42004c81c2001c20364180c101517180046814002e0400115000b0300350301c98a42090290300303545544681004d0700c1c140103040d142c1c2c0480e0a10080042c0d40c200420ba165040c213030114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 796857589 1250 796856339 796856341
    0x2151209060c0f0a0e011101090b0601171003020d02060f04092304031d030a1e021c12180806040b07143f0c0403051b0102030319060f0617 61
    0x10100b00030b005000108103041802c0c010345505a100301c0d40042007000c103052005604500e801c0385402e6454442e82030300c0c580d40100600c89a9640240030100d00c3d8a0240c0540d881d0030200514150b4404510010f40318030141403100b429503a402d0101c600364004041340b030360740e00d5031443c03001c0c00382620441c07640100301650818412020700040c03003441161b050307440c80c0001100b40d441540041d0902c2206401d4454400d407440081c0c2620f40030f91400750509403091700c10000384108546120b0503901c000454941c92141c070001034142600c0c89103c0f10b54244101c40480502030850b00048036480011103206410506c420301028020f003a0140d10550740715001c108034200b0042d2a8410a958482c4901d0481e0f80d660101c410030409650400c0c030f19080000810f500c80e1b24484000003520345420f40940044d003041001b0041014031101903618010a0100001400107074403400300810100b1180101d0007082c107241699071041014110b00489070540603120340f0010315454801a003802002d6501c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 796858839 1250 796857589 796857601
    0xb070c0603110304020607330204050a240c0f0803070302030702010b0a060c3206090c010918020318010f0209010e09060306011203021218010f0c03080c070215120906 73
    0x42d04403449a900a0b202e41c0c1380c04143d954454405913040c46051000240c0c40d01022965054503041d144040f40d180c0150b265810002001031a00803a1311103908507a040d03c18400c0e9540c503180b44c594110305402c14400d11016400c144605d00c050030802049800f000042100040e0180d02444c0180300e01d500801003d141070701801401070f650b020702d0b40450341e095072107000201c81c5202c0582c07141c2900c144a0007010f1904a20b0a0100c05680050541e0411020813255440400c00703100d8a0009181032180e0354a0908511a10300003940114500b0390000009811024503403110150740174080000c00001c100502000000c1d007005a040303000458148544583d8540b04040a000d140c006002d086a6440c201c040003910002c5d079000c500f035000300d48402c1411881d10002d010441161502003e440d0503001c00108501d4540404e48280100701c01d110300841c8d809007030940e018400201d00369691741503000150061101d40080c01c000f100000300300e40107004014403d800350700080c0854425498031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 796860089 1250 796858839 796858871
    0x8180c0a0e010e060f03122506090b0a090b0c03090a0c0902210402101809090b06130c080103140a05030d021b03070302030910090305030c0a110a06120c0201060b070c0603 75
    0x49443c6e6056101c031040c6d04030509210003c0c00c1ea0140781c181d040b5075230310403610b84005000c84201502c0b025a01c0a1003014130284d0484240e00500340d0f0010045003a41d030f41d0741f00c041c0300040c0000031120004030014040c0c2e04104110342c00a5001440307001116031b0380b601400650310400d010203c10242044079100500c0007824507002e03aa0003000b0b22020101808210340c11181e0000b50442620141da000403545980e00c54600c1e081d001b07210041c014a000c5083c8444400d003542c84039100c0c0d251060708044250712048550640f94404441d040742d69160041c43e241c03c64008000d0043d000008007000e030a649640104403001117910850080d65004080ca520390040080240242e04104014042e42c9443c16600380203030911b00301a034915407240c45840c0303143c0003880903030304552242c03110340709000c0b00701c0c91100f41403006ca50f9000d00d10304101c801050001c4031407419400549505040206030300070340101001d42054880340d611100710f030401000700240c1d40704000c0440c1c6060807501d10b40d121 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 796861339 1250 796860089 796860109
    0x1005010f140301030602070609021e03010c0f0c02010e040f060b0903240711030714030306180115120e0a29100b1b0d09050f060a08180c0a0e010e06 65
    0x5088030709425a8616100e00d00a90301c1200115080b61b0b85006210059a4081f0384040680092140a481360005418103084a5410841d48103101c00400300e19241548101020b1200b030382880c000e444075000d42c01040c0030304128401c002010f810039001260881120300681200f040803822659841d9800c08858543d002a9403032000b0580d620002030105400340104040110080088030310700316081d201c041d818000240f22000e940c000205003c0c051038242a4084081050381c51826154900030039a1600c40d03204d49250b042c014005508200b89200340e00042c0007102e41c0c02500e9408101d86080c520004041224880c0d04421710b4074083c92800a40d4040e1095088840e03950005080c19002001c0782c0040c3c104543d81c0c1080701c00c24010220a0001c00681c0c00c05885422002d800d10041003940304201c410316000da002800380c0080a5031141103a0f0f00034001c0742c55002030500e5085c4031428410000174040e00b11519050014003d030f66003e9150403207420b2503511031035888034010000a154 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 796862589 1250 796861339 796861367
    0x90b070e150a0e0d111807030b040606020c040f02160804050a06081003080c1c031d0f100b0d1e0309090504021e060d1b030e0303090303010614040b031005010f 70
    0x124403000361540381020311340030010900844159040c246464000350752507041009800340e0030020014098640d800d40207200c1d0070f150460b4180700c8541003000c0259503503420031500748181d07101c0f4120141c804040c0c3c1240c141d00c114920100c1c46034000d080507103c9a001d0f205160140045020001e03100d446040c8a50064500045010080d491a161101d45802a4041c24103d0189515480d20810031341054a003120664074003040c50030410000b101409078094840d00301d43c01004078002414000316195410050750580004d5100408010440b20041580b004018803a5041d0f10f07d000706c00b010720520844e100365100210315032030303003650f100b519001d0350025040440c03010643d05a17584401411040c00d000f6003058100003400c1c4141c2d09503060b0345400c0c40080088001c1e90f40c140c1d8507024004500310290019895400e0201a60342c1e00e1105114000402280e00804001c20300400c044074010700108540d940c0b241020350101508075194461140821410041009841c0c014403000b400d81c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 796863839 1250 796862589 796862597
    0x3014060a03110f0406090c080106020106061112130f0e090613051f0b030111040e1f0b0306041b0329060a051305120a120c150906090b070e150a 63
    0x11400c41e0900c41c589036620002da5002c1c0d101e103c00701e81d1b121580b00e90455032006035240010f0b0f514210000c2c2c215403003078008070101f1455001b140c80801c0005200c45044c0726004451b030f501c5498502e051900c040a0304020700074008000005102c115803101d0a00601e000784c29200c2903110500101207c19030048001c0054102030305070640c0c2920000c106140d0f0200c004045440303c4445c000900311240450800c1c602e41d0040f60500c8a02441c4198903800403c26000b411081c4480d0022000e20403c0c3c420101d014100100180303450b11150011914800c856206541d40c45101c01c0103000b0b0f0240b1100318000180551480c86400e20409000d12502030183c007451401d4241042140c0343e501010a010111952200028590b01c03105030301020f2441603030180180c070340b0501c0c060b0300014240108000704516000b1400c086040e51044005e101a050000200d80165286c0b82005c0d00201d078003e0320000034141002101904007070080b02004c0d04030303500c01e941552a40007001e90301416480c08005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 796865089 1250 796863839 796863863
    0x9050106090303120e2d030903030f070302160e060f01020105010b190207050901080a05070b030928060911010905030a11040b030a050a03050a030506030d0f3014060a03 74
    0x11a01905100e2961030114001040c2170030b07010b03045e601e0040c40144040c04004400e003c817516280102c007141c035440c80c100141d4603141031103000903a01d0280d0ba545202e140000100101014020045540d400c090300754500f416030782da40c290381c0706d4850440310030f8003454540000c03000030b601c10f20600d03040c0e43d0700581c02402c046034004a9402100701c42410825841740c010b010440b41e540c445068000e2003080700030003201300d103803400318100401607002c40e0305082e0600500400003070210780860b100401c0b46900aa000070a01020318540f6007007005443c051501c80303080284101306003c500450700a8844000b50343d0340b10241940c40b1101c09014100c411080039000c13191a007074000b45040d010080c11104003002d00c0c1c07074840c14072081c0034085002c1100007824802c0d07640c050140c42e9002108a0190070340000d030307610140c9032841d450403910070002c61821031088030f90505205802d80205c031066007a592440f155040040c03001c0361202d48507141400001d24585010416036080d291300003c80c00316 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 796866339 1250 796865089 796865093
    0xa0b0a020d061d191116030201060f031e060216030e120c01080f0601050c12070c052d01050d0f020301030506010f0b0d09030519021c05031b031504051f090501060903 73
    0x41441c4036548001c198485c00510182c13000340018091258120094400d2242d0f81e01d406402c44d1165407111094540d410400c1000c1030303916418401c8291003894030345040b0210702c0d04900070301c1180c80e21880407905403056010315500c0800040303581c00a64500000194080d8030607502c080703540c06a0700180c079070b4000440c9038000030b10f9150894070604120342044804641241411403800164000c200081100030a01400842c032000810741510030005405807903281400760301d1103441545107005841c55942d091391140080340c030084507040301002400d40028500c0040c0d8001c1c801544c251003440300109103481c0c2c214081c02140d2000070085d14081c407070588076003c2c164184054040c010309108410440301180329040301008503a000d4003480000c0d888041e80d03503810300c05203810403106000300321607c2212690f490f191808030850790748035903a5103000c0d03010124081005170094140000e11112803c50294100070400700796441649035241c007800803c554092103114001a0309402c1040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 796867589 1250 796866339 796866361
    0x2010e0615011b1a2d04030c1a0a0207051b06220e0a0507110f1009080903010c18060f080a0f0b0a0803030115090e06060307020a0b0a020d061d 63
    0xb0500030008010749038400551078454504032860b4010304013a0b41e02041008000036901c4141c031090044111002d180084a980a80c0d500018401030601001c0000c040c140200c180549055400701e005000031440c044410101a4100407012642c0b445003420410307d80011541d00305480e80080e0485042c0540403070500c4440007001d5a05040c035a0340740c404544001c001050741d10485210901103210300b4402401050110446507400786038002d51000d0303050310700200340d459081d84980310118019507941408403407071003010546580340d86482c840d00d086a811282030007402c40e100300c51644040d030715403050f43c0c0c401c54524180300041c00703000015204480e59120402c05400050700142c4c40e9902000324001489581261400e54008401000040030804030701e5698403541c540414001d02e82a03100e00005400f41050b8440c3c5008000a100d039031081042204490b084070550a85e0308190510600950000c00d825108504203040460740031314651143d2038605010340e81103040e50702e0284400e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 796868839 1250 796867589 796867607
    0x1505030d030522050309010f050a0c120e09090601030302151e0a0603060c0e0415030c150e0303030a06030309051012050a0209030f012405090403050906040f060e0102010e061501 78
    0xf1070701040300403c0b0000070035945104001184650021035a0760640000506000020b2686034200881040500052075000041e06e200b583d00c10070303000b0038182810702550512200804071382c01440e40c000700f260b290030028466040341e010b6001c1d6000c12020140c602c000c503104440000c50344070307400203020340b050707050708284d81c0604c0c1c0c0800065826242ea030703240b05603101814030000180441d01d5004042c0740901c10082c0c4142d0310010145803a1039541c403090080300e03d118014000141110303405030b06020343c901e07400c1900014140c070768070710b404aa0301c8028125400140c0000e0b40242021506060000401303ca540054a8076403200c0112071100000e820010150035030180c082c0100c0d003140d10204280340d03040c2070f0680085220781c1c01d0b00c1e5825814a9010908185049030001046075841d003003400c9400ca5014500180c2e0340d000c07080400c2a621030341d8000d9403a051560300008071107902c81c0300e840360950f0981c028841e151100f011169205010365150113024820f500344111b5600a0701030f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 796870089 1250 796868839 796868851
    0x1e05030103031d0307122108010f0b1e040b030a230a0903110d05090103050c160215040b18040e06040b01051903080a200307080301030b060409021e0102011505030d0305 74
    0x200d10303503034490060b0401c006c00050215183c000440c07041c500b2038190355029140710010301d0030320300540c0340c1007481e240190746110307010b560400007620b20814601c0c040c2c0000306d002c92540c0300b59110340c0d5a40f0300426500c2110714001c45481c1681c00041d110068000001044000a8100c001d03158110118010203c000c8120240301c900d602005ca8610b050200300084240d42d10b13400e0311004024000340540d0300040030041c079940200088401c0d90240e070a0181100d070141c034141250700d0841d007914518331954114481c2d903a4045068116002920500000359209840a214070380310400d003d41e46601c281d0f00107001c064036100600c02c41c181219035415a4206044240b4019a41d4079000c03203a80c8074010803c001000c540b01000c13140ea6030345e00d40300103c00c5c0000651510300d8649078690203000600006001490b96004940d05a0303035034104060440e0010208000030302a003801e2031021f1100b0b08040d0165080c40b0f0340302024110382c0c0d812021900050060b0003444002881240201402090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 796871339 1250 796870089 796870093
    0xf1206062a0708070b12060a03140601060e0405040b070e04090602030108011b051c0f090602030a0603030e2b140607080a0531050f0d1e05030103031d03 67
    0x4188032800c0025045074202031903400c0036070700182007921030800540e0b41200d50381d43e1110710200168201300c4215030010302d0301e100c03546a6071507910014410341032603800a89030800d03103604c038039003186c0100e0128100c8915446071401114001c00b844292401214041c0c2000c0c0100006040c0d2805034410f04282c02c4010030014801c041d03903680782c00720b030001c1c2c001200c80ea640300e07181020b03000150b450b0340a0400d1401c213141050250030303030f031490920309407c00c0c8071544e1154070740c05008034103410104e200c9900071000e40d1030b4686544801e008103668801900020296042103c03281007100020101c2d084142d007000f1340300b400146d40340c0d0241c0b500c6812620924103c0f44546036000c1801818040c054690700d0b4101420001814004e0f1480605034028182a261160042000d52001c424036800c15403074120b460341c02401d0250404001c0485890107004444400c0314081d44090240448030b6807141c400b090380c0d42d2100403203c5000902004000c104d941c160b114207442d441d0b4004a4400c00102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 796872589 1250 796871339 796871347
    0xd09030219050c03070812071103070306060803090306011a07030804021206070f0e030303070f1808070605070312020702060f070809130c0e0d0519110d08130801020f120606 76
    0x1e282803040d62100320680d031075044022408450b290900002c4000c0400c400140420400744400105601c243c6078020900000030514554540b002d01c9240b0040d500030380204581c0380e80d401820f403241e0242d0102e074405e02410340046002d022510006282d19440300c80701d820129540c0d401d03250107801a2050ba8001d02c40025030b0503442c03041144600c00c1141d0382d58648601c85800d00580368070320f4201414030070b800900400401c5540291501003e501da841c02c04107101c00291024403401041c1c001d200710b0f0148000102c2d4190300400102100341c400d03990a0001c0f58142d107488128020f40000030340c0301108000030300783c2229070006849001d0240c403510389410302d0040040d07450070f202d6848090349500c440c100002c00c0c2e08a104410800001d403859072694010707076265612a0089508240f00c1081c400100051180d2400300418510028090b02c0356031b0b145090190164204003003100072000b030a90702242414040c0240d48188203010b001c1070506a0f059841c201c5044028651900000244 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 796873839 1250 796872589 796872613
    0x3040b04030c0e010603180b06120a060e0f0a3201060f0302130207021315050301150305010507050c0c010e04020d1e0605010203040506030a02070c05030624150d090302 74
    0x60006500c140010b481039840d044044022810580c864028140344c40301d000a4050000200c1504a601002d80b0381c82c0d94507980060400c0c04010700090240c81035802c60b40410a466100b03021812403441101d00320300f41d1018031a56a01440f000400503600e00800f04240c05002489004103240084001050a44606c1c1542101c007180d11049011004078010010b504000556a43e01d004c014015850208540c0100e0090001e082c8004600750f542d0884418680a8804000241c000100244403121102201c0032a02581c0e0005483c15442c00c804103c2090040e412200c0740c0ca0341001411801044000640d1416445001943c00c590200303c100f0300c8a201384144410342d160103245084012640da40e00e01181c003584c102d80e0566004110030b000c00da44c1c00b001d0300d620210f48140075a88801c1071810500d44501342d4001c079050310404040c85642c283c03046034415681c10310086d01704034070103244c20080d1000012800c034aa101c5c04221014096699400c254040c03400707801140c00828481d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 796875089 1250 796873839 796873859
    0x20d171207030f110a0503060f01030605040e0a060509060907171c03091b05010e09060f040c020d02010b01090e0406050709170f0f0607090e18100501052110020c0304 73
    0x115003541c0025a1000c0700c418901141c4614143c1c1044510040d00703101c1c0070103000d08284006001305114114403501c82009070700c42d4216401404014105012040d40c0b0540e20b951407c182d60300302d03945414403001451b2000c00060507441100340000130b2044506c0c01025109018402030140c02c1806544070316684c842c0c0c4042407030700c0e942680d90002144842424184000346c008562100d8800b48020300308916a4050030403190604d00b19940da4040c0c03502000501c0d56082c3d03414045e041400c00074041401600820403400100720341c0c00900084850500455110784a4020803001d0400140030030f000c108158440d070343c00461070404035100794803070700003124060701d020801815500608048640050500c0392405516440303000b041ca90400440141200c0441d0043c0a080c66500b00003c40c00d014890040350309242c0a015a1601c001c0c00c03071282d01409090091500a0070b0b004241d401c0c040325444400643e07100380d005043c1030642303d11546e01962180402166505c406d110128800b590 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 796876339 1250 796875089 796875091
    0x9170307033606020c100f0e060d090303060f0b210a390203040f0603020a0c08040909020f032413440406080c161a0c07020d1712 57
    0x2ea07400600220f19180303000b441c200c00345129902403120b02149080454010300c040741e000f041d03424041d442d0040800462554003603100240307a20b5007441000c10515403d80c4c400000c0c1e8400c400440c00030703510380d045030b0240e10500f403110f10041c010551040d0040c0c2202ca0b05a00040c0418000c200608010321030800e419000202100e41c13141c001e140c21a40e18503500025005d00c00b4005107042620b0f25001c80d043c01440d1240d041490307000191712034403038801c42c40c0c080b07203d502202c0191541c1e01e410542c0d0040070622012801492142c00d03850043c41e00042902c2c03041c3c2d10505d003050020204441a40c2e01c0c6000d004000c0142d1981400400188054444a80010038507022119146a000005040c00240b45c4265034422040301003041000c00130100c6060341c5079818568096118107101d80e49078400d1a100700000d800ea6212801004006405031025118103826040280c551182c00c5000344a400c2d0000d5000c40480e20a10000f43c40404030045072000c11141400c0081400701c0049100c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 796877589 1250 796876339 796876427
    0x1303110a0309140d020a03080a02070e090304051011030306010e0a120f020a090b010816120f0b03010b0423190c020303250c0b0a06240917030703 64
    0xb03650b0354244880d840c25003d41082d010110340140700c0d0750b50b039004203060741080d00024100c80400905234100c14001c00105009200d03c001022641ca0b100441c25144e4210b4014a031080c00f030100d0703018000348a00c8100c0b82000e01e039001317540340d80c94003030040d186900c162409a4020f090300c0380018981000000c104012070080222244800c03c2c3d104001c2a0007031900050801403401c031001c245039a10100c15607006111080c884400c1120086c01e031103d078800282d5140860a10310404400000ca421014011005600911506851404100595420b12500c018400035520740b400800103020080c4e42107000d0302203045040d15115500300036a01509000400741e440001841602d200c400d4a00700102100c2d1250041c7d5000b140307006085151102025100c180c10f18089845003120b94403aa000b0701207501c42001400185181503c0d1016450024020900b1648006207103044d1780d60440b1100d801d400610714044d500d5405403409064045841030802803601c01014103030341d004032000c040e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 796878839 1250 796877589 796877597
    0x3060109090308010e0103050c1002010b03070f181b050a0e060d1512030c0303020c1608101d031b0a0f0804140d050d03050705120f0906100803031303110a03 69
    0x1960038100a000b00c0f4040e40f00400c007140020040000c21004261090001c170200e900c4610070a50076012030150003d10455640b40c0541400002c01038450000c007070841d00c0d04401107201d010040d00c200d00b2941040d8241e050b0800010500040354072600040960703d4581c00c002015000c0100030490342c3d040115020b89441d0f5581d600c01c40135507046526402042c40a100e076000488030b076002810340b004c110b001000d140e0086a04942c480d8180302c085d042c107040c0801d02018542d111003180d0780c0c00c181c804117950645400c5441e80200402c48a4400004908000711701c0d0114205036201c03920150b07800e00240b40942101c480000d2403114003004124040c4051903261824004000d499040190b0750b1032141401d94070000c001040030078107410039406420b0005941c0e8668000b6100351042200c402d20301d0300180b040007500c6c4250031009004501600c01c85000303941300c004280412255008481746507000740001a207100482e240c0d040c0003442803810310310b1140c0c1594170b2032a10070310348001c8000c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 796880089 1250 796878839 796878851
    0xc0506041e0c180e030309121809070c06051005061905042105060f06090a0908090402070f1209120b0901060f0e09060f0c0706020313050a0c060f0207060e01030b0f03060109 76
    0x3c00d40d0b000345080501c04e5009103255090441c0b9040daa42c1c1c02c01d126200590022504410b004103420381500454000382410110b41f81901008041c00d085050440b80149403601045401d03000300000d0091b60406400c80340b8001490a01c141d03907e0304040c01b4400c120f4104000300315440c4610150504114900e0950051445454003608280c0010812144074034100200030540d80d804600c02d4101120b00c000040080340d600380f107100b0344281206240c0040c00001d18104028141000f480128058008a500b0034002c24088509414620680200240d4040300780081001e0f0b1040503006403e03803000250740e540c1e0b628481d40c21420356000c000c643c003004040002e0590144517041d40035011201414030303407806096203041070152001c00703420301d80e0200c0000c07012070507610f00205054119040355401305481c03800510014050007034400261540310541d560600014603001503490344e0b2618070803800c075407004400402d00c1e011616404102046012620b40302401014082d010b144004102 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 796881339 1250 796880089 796880129
    0x140106080d32181f05040306050c0408061f0305071710090201020304060513090e010c1d1305041509050601051c080d110403050601080706030c0c0506041e0c 69
    0xb0007100c92031140e5140600040b1800c03208031000494202459030704461020540c1d070000314264108514031500f090403192000705429400c20050000c0340e00c5120309009030758071a4030503002c500582c032445101d030748800003003900c4d600340101102c0340c0c000340c4000926595507511007030318001c40c60780040303060010028060882c03034040c4a080d03050300f84410306001122140e40000c4d83c9101c2d40c42582c0c10048013283c0d186902d4249103229000f80303800c0005110400e048441d0304c0c002c280e007a0585001c203160081708522001c0f4040c40319520140181010591035071042c0c04030142030b00910480740042c0c0c403101851100311038403c0802c15400b41004007501c2d8101000e00c001031149c2e01440306070488410a84002400407411150001c0c4299800300345016030082c45a031600454000401c240504000030407402c80014440c011210141e400307105042c110081510014000300001d03246030084000500030070003456003505400900c00307841c890b00e8080e07180c003012141503070401c4084040d9110602e00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 796882589 1250 796881339 796881377
    0xd050712150c2c01020706081b0705100c0c030914130c0c0506060315150d050a0b090105010b12150f130614010315061407020901030302010506090a0b010903140106080d 74
    0x3210401c0da100c4082c0310303800c0f4001135612042442030404014860000900c1c50700300c1d442121211001c1030740143c940403180341c032507141c4090350901c0d4481480c00c1810840588217040420415406d6218485014145600c0380440f6039498612a04080420390b61525003100d442907400300501a0303100d0b8001d140b2860418144007014140070f101e41d1141100030032000400310120340100110311300b00045540c3c900842c4081d081301d0b078060800e00808104400b03001f2250380252060303400328020041c1d070b0f03254040d09000307000f280000d200410b01e110018100019203190400301040c000c1094000390800300c0043c0d078078914400d1501503103440d030030304000c2c00246060000c058242401e00f030200c0541c4418844018419104a50030455070003100c1010a040b0402c642c02940c020740300188640e16402c002e80038210648076503014500d0400003946580c42445205450441603555510443c6142c444070015003101130a021039558954000805003c2040313003071918929611244050290659401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 796883839 1250 796882589 796882637
    0x70305040f26031903020313050601230103062714090703031403070206041b050402031e070201060312050f040f03060b1017160c050618010b0d050712150c 68
    0x1109560061003000c00d040984c1003400c212103000d10300141c0380e558100b20b020541c4c59507000600740d4003d50002003600288186d03101c0e241790340340705001d40150041004404a45282c441c140b428040078540014100c0c0c4200b984240f0030303d14102044402c03c100c0c01641c502000d41d41106640e01c803560810405d600301803403000652034072801500b10b103006040692101c00043c8010941c110b03200b00c1c86440f500c076580642c007410014000710f40343d00d801908607200040303c0500844c013414010003e81540c3c0305004034001d680d481102c0108aa0f40300405aa082d00030700c80010390070009000106140c010403001c207009500038030000c20901600d000303008941c08065102c2c070070071042000d0305c2101400418003a411034a13000c1c1d07510310607002700f10464401980c0500142540100814840c0c691101ca894685040386000200a10f5802c0740400005a80c01e800c010581e402a0b5401c12115080315803072584c05008030112200145480c400d41c00b00e40b90b0250500c04907800b0300900c40c406010260807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 796885089 1250 796883839 796883909
    0x8091905010315181e020c0307022e030c0e040f330b03041110020f0d02030406021b0d080c0102071110020303130303271b0e0c070305040f 61
    0x914600350a0183d400c0800000007120090710343c4502005241105d00a0b054072a88101c0404540b01d411000f01141c0304d900140d01684070704059800a48100b050441c1900d9006040c0c10b400c203441c1003580298090a401042c00b014001041004912a11140104180c540d05c080d8009140e104940070740300d40d440c03030071102105040552071100941a2602c004415a00181e0745076460795950300e81325407010385610007540c1003c06c2c0207038440000e80004824000310418401d0b200383d4150a401269a4040d502c101c800581c00951040000c0147c245404040e80002d409103c0611a0351200e254942c0182030300fa41c180c0d80081c0107000d010102c0c4855a1441c02141e201e04026406c030f500946e00e0201900e50701000c8a0041c00c01c00305402036100d0030402015040b0b40c0318000c660f20b140081510504001c1e82c041040132071480e441a40caa01c200b05840c0303103060305c2440e612101d031001c00a405c0301c2401c4092000402007c520000c11040b0380c00148005140bc80c0c05258444006078144144840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 796886339 1250 796885089 796885121
    0x180302060a06060c12080a02070807080c01050105030d2012070c0e010506070c181b17060901050a03030c03020328170103030e0415050d0302030702031b0109060804080919050103 78
    0x10b04d0b8000703080c1c41c0c04180e000c0041d00d0005050b171105000040288a200e1004107042000180402040100005010000860703070080019a03030b11428191519001000140050a000740c40d6682602501c1102d001c48400c80403222654028403130002207511032802612010b0180e901081045000750080b800341c0002e54940b0300b40304c1c1c07540d520100f8903a140588030181001c036200c0d010801c01944003a09500d15200b00b15140c80000354043d0980160b11901d050f0140e1071800110b9506003660164101c402c040c01c0821120304c4c54034100c940401c81c94088007140030401400d2040d044440741910180b00c0f5650302d4030b6800c200b0070045c10a0600703110401c00650310200400111b5040042100800c2d026507000c40e14140b10420340d502c030b0101e60840c81d8000558100102071540c00005001014030950403103a03034102c90004045c1d00b4001a045c2c0e80000c0c2c4c5100d0034802c0520446506811510596895041804000c00102c22104e0781c0c41c0c0090704a5884420015581d0500034908500e801c680307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 796887589 1250 796886339 796886357
    0x15020c101119200103050f06090402121014070810090b0607052a06031005040c0323040624091802030304030f020a06030b0919180302060a0606 63
    0x4003040440c601280544140000d9009034001d419003409a0000312491514020040b440c0345081101007040e2414400b407010f00ca40d05402039400f900c40d46019019050f1824185ea80d5401040015100140100c0e004400200c4010024000b00400308290300075503004a1400100c0c0c0141e4110040102554100502c4001340022a401c014010b01540e943e114007080c015104c0300400d0082c49500002043c0307100c1d038650a1241d00f0301c20219803920455035001c62a01c208082001980e0001b6103440d54807045100c0c2c00c10452030b042c5e020035403200c41401d011400c100c1841c5050701070790059a00000000c0170320100b10800c240b03031040310460305003840303510718400b13a0383c3da00c580e159180d004604030181d88540909a450380343c03024402c0250b00608499a5a0b100e00c3d221503552480f02e002c0303005c1c01002e000400e0407402405010351603d009040c45105580340f0070411030301e220140e0310100159075904003140c0200c141d5081150607010340c0041c0f803107082c222148000c44500313074080420881400703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 796888839 1250 796887589 796887613
    0x30105030615090628030803160519050904110304031d091012080d05280b1c140106080c01110c030a080a030b0d12030e0c0a05061b0f03041502 63
    0x2901c0c82e03030044016504103a510100e90041707404500003204200b4100700300c0b100081000b508600440c0b040d9010150743c406840b201300d00765001e000c0c10801007614074480046030359141c86400580829a001000400c00c0741801002084513881540c00390001050550310f24494140782c03408040b00f030000d131003600103403518040e4542000308138052046102c5e07080045074240030042083d188407403013481d400c014906207081e601c83c90003000005804115642902c8045103031082c4142c90a8800c00b0781282c0010200008040d0600c0f8200c4049941c00c4400104007854042446130b0806400050010074250410705c001414040001c004650590302c0244050115103020840c0422903034414066603e80351100ea09070060a250400b103500410100400c0003400907e0503c0d00c40f140281d00c04101c51844403030895200d503a0903c0494000340c42160402250820700c0082c01d90040c20ba00c4040200918000ca60a0801508056040345e001180502103031040d00c0312000d54640034001085c17030746405 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 796890089 1250 796888839 796888849
    0xc0d08090709020a1e08010e0f0f01090c12060306050a0f0203010b0a05070519260a0e1212041418040b07052503020a030908030705100905160b030105030615 69
    0x2400303803000841c3c001c6510903259015030703100c0089012030414a11a8480340c0c0000704000000d2023601e40c805144004101c03e80d14508105001c0d01940029019680c01c008042c4007400380021700d4810001c0f072b0078100c81030407564883e070009144100343c0400c0d1030911001710000c0d2100b450703405120920410041240a096400700d6040c0f0101d800e1043c1c42e000603041803810840403035440159040b000345000304106141c04200410200206e60352801000a13200300e40900810088401141145d00146120314000f1810f500d03281c1200c04946451640007001d01032500281d00601d6084051110150b0f18a40036180e014140500307001d040c985e14140e1124003040d24090002014010005010064099203d810040c80015000f15601c03006140c40d000b95a01c16954082c0c0009000b80e1010510200c04002c03144007035044030080c03e2080b90098108010501c00c8030496103446200d00c0780c0f0341d80042007074071001001a401c4594403589807206040c00c20000510300c88140030030709440400f40c0e5403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 796891339 1250 796890089 796890103
    0x10e0106121b050d05010504051506030d180b040e090c03030f030a090c09060b0d060e07020a06110405031c1409011d01021f0c1403090304060f03060f03080c0d0809 72
    0x40c2c408000c41c0070101d5546504406508503d8100d8028266442031200540009028600ca4407ca131009991110410b222030419607406505400c41c9000c10503031403091090749042c8401303441c00065155645907142040d4032903406041c54103824000c000b0020b20902c0f13040c03084d010581c043e516144c4298410340d10b030b1100502e00300e180d42d600c0d407004080c001c440b405000500307065102082a2501d5a008140b00d800c01c1200000960404101158544078130f041c1a01a825640040a40303070a250b4403240504003500c44105c54040900c00090180d800700442051102c0a043d000440b101c5102c000304909220880300b141854204012031991740e0041d01c00c0c16102007001040040c0c1e0100d80101d0402038141414a40b4404801109290780304962043e041c0404646602d62150905100b00e101f60004075055041070f001030100f00012400790717880f03c4428105150000d902d07911141414104481c50b002650351100104840c00d01c2c1c81e0800c101d410303481c0c1c0750030030403094a00100c0c0b003aa20b40c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 796892589 1250 796891339 796891343
    0x1302040303051e07061107110f03101e1a030601080d0f12020d110319050609060108040f0c030317071d01031a0604080d021507021527010e010e010612 66
    0x20f015a541480d039140c681510405988580c0c144031a81d4034100700c812035002120300ba200d60407011003540d1640f0700110109400c2c00e0103002780c9030424800003501c0c000c00d80c9008040e100b0302d034a2210340081d0403512030202c9000c0204400c2c0c8d9091804424180340c003805070440748480d808002604040c40e040340d80901e070b10b0540d00c0c01c64030016411070341e41d01034062410082003c42c00e1070020012518904080c40c8640414403800c1c0302c0c2d003c0c40c0004825107a0950b6015003115048002c41c0c982d511030fa8000d68814000d540a045105082d910101041c10a60080e0002010f03c4003208190a0000700285c111609103084480c1446140d501d4007035000b001101e505141d1740307a81c24245440a010708d402003110040c901c44d25a1360311034101d51070f1980000d400005006500e548845008603140483c05000d40ba1300a09882d1303c03d282072280500d0103003001d4054030300c0f08000005003241444040d0300c1401c20001042822924441030b09441c280c0707055404c144d040c00c2d801c0c803000c04012402e4112035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 796893839 1250 796892589 796892617
    0x4090b1f1d1003080a031e060b0d0e030408100c0e0d03021e0f01021617030408182b050706050306010c061806150612020702090604091b1202130204030305 68
    0x14641500c4401c0b001c1c00c5910040040001251381d40401c1d415074409a03c0182c1c0c16213610415002400100c1240c6c0c56018002c5802e40c28480100c402040e9030111100d5030650301100e00c5c0948800d625032400d000704c043d201110341c0305c0402841c4640c3c0714071401c0003480c094907101018859560702940b10011a0382c2e0801c83c0040c595840c1040508006596400d5900c02c0215900d0b096000240340482605500361134501743ea080c55008003c1c440101c9100f1034002c0411414155605004030144140940f103a43c000d4003207946110030424201a020380900402c40c50104d0f4056103000c6003050b1480e0b101400b840024002c200d0242d0f013002060740800c1c0c0c0000c0003e91447c41010465000c2e80144003d070029260510280008511b050103030309480c160740300c91503181359a0700000c043e403140f000003e41000407200440e5440c20240c006c4071045129080762900700382008804610380e031b00b41d48a1140008008020010350034940b0121800c100180d02c150326090950318058000d2240c024024215 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 796895089 1250 796893839 796893841
    0x804060513090c0c17090901031b03020603070c050c010207060210020c0a0b07180f260c09040803240a0311030304030506160e040b0a03020907030b04090b1f1d 70
    0x70305006851500a000301580800a0525401c8028001810300c40225150951300e104070b0a10117048050385c10341e031402070021000742e0a50780c481c4081d01450101d00c00760904140c012006982e400301a61158180da5120794a42480d81069450b019003a2841c5065400041d0b0511005901207100400031032201000340c1c1e5030050401d12403500c208180003030504589642804607455021030a04014151110640c411644a05a0782509496131207103107001411451640b803440c0300c040c6111301e0f9100f420f0a0314114a1402d02207804000102c6085840000c00403c01c80100c0100480354440303082828140720a07240d40d800b18065016900014101054842628944c0c1e60100200c0b0081c40d4000142e07812424004030f0381c401419812228004140740e659090b03070904007807040410f10030004004104003407654090103421a0051f0281040607100c83ca1901d003074813580204503c1030310800d00721100f454403810000110310020803410304560081c00c10049115901085103900c4000480c1020f9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 796896339 1250 796895089 796895107
    0x30c1b15180411040504091109060901080705090c0c0109151b0c08030a090f06052202030d080601030237030504120e03011503060509160b04120206070602072d08040605 74
    0x3da005035840580c2c042e0601c1d01c20f90412000340701060713102ca0141c03000b415135180c807000c200d0160401d01034000503034041c400c104620310341101c1081d0445285402c507071809107813904050030340c1c2020800351078580465100c0f00809541d0f100d41541c4110841c012014a0a001c0004000c0b400c48680580343e01000301c0442c02041581d0710081100744d11005441c3c0c964030700c4c07034020013a0204503244016001b0300512041020407021500c1e07201c070390081c0074120319004a5025a00a01d02902c42070415900b0b02c40703804a82500300002c10a900b107001c1003813660309800030b1403420908402010b01098184010f0100254001206200e042c68a0810100303440520006c01d004009500704030300e440101d054000280b040d50350041d40076105c4c41003511443c880400c5000e002c500c0c00d01c1019807109042104010402003c0d155003c0716100411035490a10aa2510001d07604a40000d803034400071a280c03490104d0390220a02d2001d10b10f4410703138071001001d031a03526860285110304010312900040c1880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 796897589 1250 796896339 796896371
    0x2a03160203100207030c11060304020d02060c0f0708010204030c14060703081e040c170604031d0d0b0a020301080f011a091f0603050a0b090f1602030c1b151804 70
    0x1c00c14050b4411500c5141d01d04008058840518043c0c45000f20603960181d10f0502104492203680c006e003410810342c0450b424425190300c1100c0d880c440e0b00400e00034080c00281402110020503600c0000340e02d0790304600380342c80300e82c40980c00030708202c2015040740b80b580c80d541d094481017074060500f00b8095883c0e038114016089070004a5170015240c1c004c1104008900b88224140c4140380c21a1030703001441401c055442c00259000b501003000340c0302400c2c42d0940c0c1156000900d00242c80d0b454a2802680c1d404c102c2d1400303075100d40c0d42a802200600c4490810041206401c4062000307014500000c0310701d8a8400318404203500590301daa0001da007140200310030031116004845440d6510b40c4d1000010024042541c0d812085810441c1843c10351519001c21030107604501c800740901c0d1250036004d0809482402540c0c1036000621070b4055402c410320001c0010300700707180b40c41c6038500c8000c200700c0401030014070103035003440500c10000758a00601c507a140209095030001200c83c1106880e030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 796898839 1250 796897589 796897603
    0xc180623040308042d0e060f030114070e0a0e040602181011100b060306120a080c070e0a0504150b0f040230041214070c0b2a03160203 59
    0x4403010005000820002101c0c0100102c8009603482c14070804101c02c1e1103013642c0707264151070010040c154244242d410710054280c000000400010000f4401404a030030354410703c00d002e40c020601e5017000180381e000b61007150107030001c030b4680103a1424280e004804200c00341c009806558042800c2c016001c180244c42c40da135074010058100136100c50b00051144002d038011803090300035801c00e408680c6541c01500c00c4c94100420050550b80c42078240241464241060707281c0c0d11584040d0b1010543c03c200610a1b001410003178201c003420543c429080351405481424068582404c03c00410030f01913070040c09410300640803410041d12000121701040303030b510300e0741c0c494400251400070f140700c5043c0385d400e051009010120302c0a02e04198400c10b41c129400b8028140840d072185580303215123160038815240890950402580d03499100000c4200c0c1c02c80c0515500004500311320510b1842d42c601030010414919101c05c042540360364070b902402c400301000100d21860750003150f400303020700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 796900089 1250 796898839 796898897
    0x9030a0f1a09010f0b03010c050405060304080f0f0403050c1503070c020315010605040e060409030e090a020409020a030603050115061d010207090c02010501030c0e0702030a0e040b0904060f0c1806 86
    0x1d1200c0c1070410900d8024a110400c05821900d4843d9100560038103005903060000b00b03442c0c40341800e10307000030b20245070310080c0200d8030b50104010074612003141c0e0024081c59400e9154035a11907055261075840c2483d401d1201e0306c59803040d0000003809281500b180d034041d50a140005c6003010301c1c80441d1070300c440451304090a030303840ca002080007a072100192003241c0c454808410170b901c507032041c40119558014041c2c00a40940040030960808015154000c0c03030400f801407a25a40e03483c07410480e001345c556900041d458850400070312409010310f1183e40c602500c0308142d10b142c8080078180400400c00f540c00c0740790740b60303d2370541c0c0c1c0284802c4000b8050b16006002c00c900043c4003e00a0200b408210303002d5a101d103020600285c0800c005100e001181c009610300001440c090342c280c03c41c0c0c2c41c6d4661264451803009407030380b600e02c4003a0185121304000b01d0602d2421038148140d40e01c4500c0c03038007080074445441c204401160107290486109042441c5412900005001c91004103a01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 796901339 1250 796900089 796900133
    0x7110d150e0609010606050910140c0a03090306141302040c1701030609030f05040e0f042405040c150905100207050915090f0105130e030d0906020702030d0509030a0f 73
    0x1920000da0408034900d0701c0340011500170000c290720b524080d05c0300e0144164294012000c45030030359925000c0ca5007003407061454004241091003c40249142001751141100002c0c00a5402c004109250080304440201d03000c2103200d6140018506030b415501c03510192096031155050350707482d40140003000141203900d500c080e5568483c248080a0200d4a0301200012054141c0e000c007140f0840a450a8594030040d010481c1ca40244111000c60040c0c002e98444075036141c561b502c060a4510081c0b4030300b0f500d1000c0b8a5180604041c4800b000aa00044282c8404003540c2841070307001180700103481c411a410320391802800c004910b4690150042038000c84000c0500003070b801607510b615000c600032a10200141e86454000705050828850141c1016550034540707080440b80d00240c17440c607041300032a402c084c80c1d184844141c41c0110011b807a0564001600420340c2000e02401c1074590460409528100049001c00e40e54030303031b519010b444800203114140401151011242d01140d603003038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 796902589 1250 796901339 796901351
    0x20f040905070f0b090303070f0c09051e0705040501020304062006090a0b15010c0f03120c0909140105031e0a0503072d020603130c0503010e0a140307110d15 69
    0x1900780c2d0707154103500902c1000054010009501e55400b000c4662842d0302901442c00c101c00340d6207140c0305401883c0f04440712003035110040b03400b4845200e007901c504d9028540c12a0915419060490038038040d15174010058100414020b81c1d8000088400312400303880c00c010100b241ca80700303089410004034180258010241800b1f00060002501884180079003541b520702e44038100b689040c16039085099011400e250f130054041a074240d0030103801402801e00403612141074445904940810303002c64042001c00f40184440c910034884c81108804448005c0159410301000a0359862784214071040740c2c030403240414512005110712040355511104490300e85100c0d1404881070502c040c900d101402e01c10142003020315080c80d04c2c11466401418991031510303655000d0a07903404800c4142c4071041c424000184a0f20248102070f401010000500034200c071900e00701122540036041c0c0301440c0c0c03041c00000c000c60150445203003100011500220140300b946440f5000b60161036030038a400380707041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 796903839 1250 796902589 796902593
    0x230a120e151e010f06030209130509160f0e060f01020a0c080105061203070309030803131a0a0507020706140d06050402070b15030a051c020106080607110c090c07020d020f0409 77
    0x1c071607640181081004841400500d07102e030300080e00e00344101400c0034080c100412441d4000d40c014004404007800700c14080d000c054024098607010b403006451a40408002d101858900d541140900140302208803154603041c0d8502e0403a4028280314414400d11492140c0f41c2c3c0200940e40784581d000e6416100b0701d603600c19a134000c7ca0100c4806004003ca10f2264141000202c1251a015496100c910070740b4203541721000700c4e800040207102054984540440460101c80440c4c403c00c482c00710a0b1000d15054110034180e07003010b0003000a55028000c00d01015401c5401e007a407041c2c9180000d40c50340ca40c414180e000c0d0246501c03c0b5001880040c41c202441182c0352618070501c4203032002403600300034600b40742d65803060503006006a044864420701e8004880341d50f03a1501124400880d495444491507810104142d5249010448600a03004250b900340902c02c1103100454809007a45004803030342c4e139244540307100240300d40c5240024100b1503650200045c0a108054020455660a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 796905089 1250 796903839 796903873
    0xb01030507090606090302030a061109040e031c0207051903120c1e05042303010603060501081b0901210516140a090c2a0203100b01230a120e 62
    0x740c00b51540c40c0d401c01d6004035a01d80030302034040c2102e601070010b1114540301d444001c000c0000c0080c1e0016440104042c13012642c1c0c0c0d00900c00f107400504099543c0e8010990894291702c203c0b001309100314010b000302004181c0210304201c0d13a07a07107460984e0030001a032400b19000381c0840d000c1810b00f0303d803e441905040d40040382c0045050844072220504982000507145d40c0114403850247c00002c014018007548980b0113120400c10183c000b0454030784aa44031029140241c2040f0110f42c08001d10841044000070701d2208070000351400c501550410f2900741e043e512800303821103500b6041002404202c0d003044150044a030203403d110600b915882c207054407a10180c11207100d089030045c040b81c03001c070900c16000341101c22f46803000801d41b000700e01002d03a0409520207440381c408107820700258030140b000340002c0481d418001000044640090700c14110103460301384401920084648901001045411030002414040d0405074900d0142010702100d0350044054050760403007207442c5182e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 796906339 1250 796905089 796905103
    0x50102120105010e0406080d0507020301090c080a02130b01021e031e1308070806060d2f0405010e1b031302060c0607141c090c0902071b05030309010503160c0b010305 73
    0x240e035241341180343e903000c00094403480d001e0310986420241c8005501402080246955407001d0004507161034039450380740c3c070205940c1c8020f0780b07504074034100030451802c1444d1141c110000030041144400210000303580d00314214500e0400904c64802802c524000c100381c0d8100784c900340c070003481c0040c2c005052403540c01025107e2041805040c01294071040070803010305a9030f090740240169030f00da00400405c4521818145c0350004810b1300c40301c00c01a442c06001d00501d2485030503014005101c180070440c1c1050f806541206405014864200c3c0c030304840c2001c842c41201d00c0750703c940f1945201344d12248031010007503108000040d000b038100070214101d4407584030341d15150005c440004da02074007485680442480411004155655444158044120301b03000d2030100c9003594540100604a1f03012800c03c1c0c40c42c100701e98000d0500d600840200025040a40c007a5080152a000103006404007500c1c1c80d040c68407507551501e42c3c0c0e20902e843c80356290041e41d02d187d20350b507d04140e525449 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 796907589 1250 796906339 796906349
    0x1a16081602030613110102010c0e13061a03090d09080a0b09030f0705150f0c120a0204150c0213060b040905040f020301090b0906061009140310060f0504060f0b040509090a0501021201 80
    0x5034405c1d041942c01841481c420b064640c5070040303414810710800862048041820040594451010940d0302d4102e0b0f02000f40044208071980c0d03802d0100e28240381918010a410402002038020320520b60040341e428611544071920038260345802d01d039603055004859224540c0000070802c0e00a200d000200c1c9031514030007042134240307501c42500b8005030490448800c4d0b03090b84100705181101001c400c96540c402c20340da00050506840d84041c040d00640483d00c01c0000d4030780c91182e0254079104139100900310f20341104005091511840766100c1c0918440c0740d840550f41d100040612045015503002c030b0358000c00820001986150a44e05d2075400e0301c68107030750b20070f200004804d41416100d020b0880500e4a9420b0b01c0d5290003038070200d12020b207a043e901402140c0703c207100321000307000d550041e03d2141c0700e54000d1414001400220380403a03210700c929a1265804119100c441c1c81241e050b40c1701070310740102c80d903904040070b8501051440c0003807240d840080e4100c081184040800d060711 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 796908839 1250 796907589 796907603
    0x20f0702040609230a0b151c0506100c02010201021c060f09020309030d09020418081c02091c0305070b100f151e020a1401061a16081602030613 63
    0x3644809803403048580d505485038400b00030013404c1c401c00a800354015440f00c40b80740007007040107505001c030300181115000e03409400340c041400c4524407008060f001e1400300c681c20070440c40c03038a00005208078800c0e114140602c40d101d08540c0543e4801e4049414600651404181d410b08031161240100320910a4003d031a20070003000c00d003002d0034001c0300d0041c54160015414013030502c1416000740810f10080342d20940d41d03003596420000ca0b4810501050051040c183c682ea40107410b0119289040101100c07107104015072a420b90300c94402d11681d0400030012080302d1141e14040e00c1d21701c50108041c103015562001c00144440450b640f4048d40c200c3c801015100b039445581c9074040c1941400c0c440403413a07440c076011103150407242030310854800b407040720040640c54a450901110404028107142d4490b0410300c0010f942022a00d0000148044e042c0740c120041614094400c01c2c5400070200c900004000140e141418071b400c1322250001e081c5d40003401c1092210a00ca000c101007101c00e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 796910089 1250 796908839 796908851
    0x408060103110d080d02030c16050c03060a09030804080304050c060d0207060c140d1119020102031008030a020a1401060504020409021317030708032d041505040c0e1801020f070204 79
    0x707400c0401c3c810600c558050304160800d918a56214040d4100400c400030201040c03021800100c203078101001100e01a80180150405407024541840307001000001d41c1824541d8850000707038000d0486600caa000014542c5030344440c9012410800b2545070f4136480100410f140300c072000194020400148100020000440d01d180c09450000540b5419103442070309109800b84855107402000910070003c0c07545182000300380610103220029214400180c2d4080f08000701c0136030002400001e051071f6002581440b034042402903545015140092a0880c20459410110700c01d41140c0c000e440020b100f55100c60325607017044002c1d040403050100702e11b03080c1000100000c010740900451140c2901a61070001141c41d0901150701c060419010030081801307d584020002c42d0080044801480c00c040c0350406041414400d6564a81c258540c0e24100034840050503600300d24040310907800011101e6a154000b4410000e50483c8400c0e0a500015103000320784421802803c0c00c603c00c590401517 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 796911339 1250 796910089 796910123
    0x50607080702120703050c1c0302120105031903050d0e030a12050f06130207020105070b040b04030206160503010620070f0801061a12130f05010f050f10030314040b0408060103 77
    0x2488052144090f501d003c100040c03c0401e12030030081104000c00800c0b1507111b40c00c00381d010458802c800210002a42c00300303c50603805000e05c4118010724040b80105001140b803a10341d0307405902120000e05100d00044c00003034540c0300307400071a10081d101080c0da1f02c0ea1203544001d40380c1189500e00c10740702c4e407808000440c40241d4101a6000d808083c00f0b00b000781c005188680020741c070400c3c0980c1841820f00180c40055a1010000e100d648038060041240c2440d250192601401400141100307a00725005001e0542c44030030345e4116002c3e440d2103c0042e03075041c076400d1032221800900d0028002c031440451801210b001c0c401c0ac9170a540020409a030f076a0203447c1001000000d900b11003038007000900e000344084500281c001105400d0f00300d5941c09555280c5000c03241480031a680d945404200107020064840c09070311042000080d401c038546070b4045000340c00303203010007818040380300c0c00b400c0c0500d40b12040e40c004d00b900b003803460381d01c0c1d840d0344000d40e852400344401c6450b4044200c603210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 796912589 1250 796911339 796911343
    0x1106161a060a12211116151b060f020f030907030b090d1d04230a06140303070b18150f010b19120f0c0c020a0e010b1b07030c03050607080702 62
    0x4101904100200c4800355402d03403401c120100714104c5000c100c2c01010102455909010b42004050501174489800707250146001141307181702151400e00c000c07101d0100c4022980008805081d52246001030010b0740450402c2c000d01500d910000a0300002c0300308641d0000009400303094074060258007110f541c5d08445247d03602901030f003843c00030710000a180e44a034040f0000400c181c500805c0442d40c0d10143c1058021207821100a0132450081e005004c000d00ca54418000900302d0120211381210710391012039941e1044940041c0040440800111a081e80d40c48030390440c0e10107410748200e8280806940040c484c1528090189940c03140005070352968601261301500410307010f042440011721055401c62500d6842950f410b0702c0320b0344000390704501c2c42a1090605d9a40b1540c020255500608c641d9042d03a03040050070f803005400500c4150380c0d240c1a50000148800d00d8140702c1c000100b900d003002e19692008002000f201c0011080000104034031307101e00710750740c6c4e14112942c1d000310480e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 796913839 1250 796912589 796912619
    0x106020645010e2802030703021f090614070b1e09011a09060a1a0903010906020d1b05090411070501020a0206070f03060f030f140715030b0109031106161a060a 70
    0x480152030031004c0709121000f00c030140710781c00201996a0b4681c1d07030300802d40440314206401e44900c0b480d0650902550000e442c1e0000d41042c0c903029160341240c440400091043c450003410194000d000114408045917511041030601d51513402c1c2ca0400350300f1107003c0d00c403401c1442400a54280304402605040341114810140100b0001440e4640060f041c45079004400180c182d4074204480740035524240501c68144c2e20418005a60310b04001c0d0403403c86000b00c140a0000304000b800c8005a50703c442900c405042c111000180310300450030f00d40c020700c1040401406540041440e520443d000f0403240d10800483e100c040350040c405d0f00444c105d41d600c0c0036103c02014204014030204c0c1400000702030340e074070440e803040c0d0007045400154507112107a030002111485010240240941c14011846050000c0c240002c141e401c603a221040031240c111540c0c0101404190305030394400c45401a4034240d0041d90400e082c400c500d4a200c0421012100d080c0204801400007a184c20401106 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 796915089 1250 796913839 796913863
    0x51203130b1303080a020601031707050607121806151703040306023001080d1107141c050303010914010308070f0201110106061e03050106020645010e 66
    0xd960864203003210300e0700300d800081d0340c2104080080b5002c80004c0304071004003141c9503207800601041d0b240d40341400001c80b130b0503a8000d070000240320080028100240c100d800c44003e04045c030f240c01c902003d00c801003c07081032220316844030305461018003405d60301c03000800c034109030072461841c1c41c0d400b040c26074980c068841d5160b51041001300089001a40070785108180c0e411050396604100381138110a1546039103c1c6001e403100c030f0040103100030801031000707004410b0400b180c40131901c465041d241c0a00344a07000d5241107a0000b030304142c2d1122110464105190302d595403682040c2001d0344e0742e03007090195044032032a21302204c04001201400318101c0385d101500130326101349552503146c0f120012000301d0600a40158001503544203006a00280c061580d5282d544001c06000c1000c80c035500c803080041c10b15202c01401415400700711280d000000b058042034170000140381d40300e508030404001e1451460b603210843c104120145403007080130031900900885c0105007100d91500d02c0d101403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 796916339 1250 796915089 796915117
    0x18030c11102705060309011b02010c120939080a080703030903030b12031804180f14010c030c0f03270f0b0a0203180f0d1116030309051203 61
    0x3915182041c8165a806025048480030040d903d0020600d0b0f900192412101a5141c0c0c544485401c4000041c020021242c030003400901e80404000c0d000c0800c84c40084083e68540e041e80701172009500304002d12420140404018000c0d5504100319540708203480c0ca03003589408800a000070002401c07007207081d048021185481802d0390241c00608000030300301e0506894144c1d829060392201000c00701c21440101a59a5080200d140b0910700c1e107503201c40384110310740640320092903482ca000951407030388051440d4040c85d05062480a030f42c00c40c0c450000c10f600342005d424809070325410070900700503d52542080b03520b0768007003901070710442c40326004075010310071b040b81c0f41d050042c9002c00c600d405801c40d07d071070311400d444a81881c002114480e114a40000600c07032080c1c001d00020240c0520000503120f0200030706400341c3c40c3c1090700ca50a0401c8001181010009014088050100d5400380700506440c1e80345000340205407184a120b1080e21503050455100b040170003291038810000b10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 796917589 1250 796916339 796916357
    0x31e0b07050901110109060c02010b0d0b1503032502010906020d081b0c06040807020a1a030a050a0b0909070e0c09010210020d06080d08100f0506090906010318030c1110 74
    0x10301225603810240c1500d041106040d500c0c0d82c81e0000f840340616040c0a5400403d0180019002a007542c4490100c5401008101105008510a06055600840411507810b0340015010000380382d4001e020301c80c000b0703880710111f0802180080e143d180c03005100780c99040795582e9401c001e9869544203458103010410303132800162482e20341c41414418075020312825050041c8202d0306450000102c13411617030300100065000031b5140c246229002405140c2140c8180d03000822401002c0c003024211400d1161070b03401044600699030011040542d0150802201e031600200655072222980318100d10300c140c5070302051a211040003242e002c640180c00030008403d100924030004e501240041101981d80e002c042030020040c4a000c00340c018582e280c4403141440f1610f01e040c075100e54042c106044244d00d081189480c1e80d02591481181215548484e0b980c1c000140c2c043c000b079a55444220304c0b02c580c094101600400d18002c1e060040c0014118007202505004044242018041c00f0034400c01c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 796918839 1250 796917589 796917601
    0x90303072a061710050a09021e0d41060a08010c110c09060f06031008190c050901050d0209090c1f120b0108060402070203030903031201031e0b 63
    0x3080030941207041e011900d1000e000c00641e20048107068210400003018205000b61003110f48035040d4000300c0e00b80c0d20312881442c0c800021120001b0b441a08180340d00400c252501011b0400b81030a14000d0880c2c4980d201c40c9034140784000c04880c44e40c501241503900c61407800d2001d601c805005031007680042051890314400144005078004d00300d682c80805000c0224074074000780a000d0303450010303455210b2851020507900d42031024006101c1c2c02440c865080085544d20490500003182007500c840741c1d0790700c0b5021080315107105500200e9491140220109080710b00812070014a4000c02c6200c00d00742d1198208014a0000e100f030a42c0100800481805481c24006650f00700c5000b4040300c0c6071914500c003013540200c281001089031048521141c821a030810300030107a41070107180400905442c5000a003508001808040c0266400f04100382107440802c11a112040c004040302e803034041c0c1802c800701640b0240800c59558140000910b0840f59a070384421b44c45901c181a034203c0d50f550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 796920089 1250 796918839 796918853
    0x80406081003080322060c0f090905090c04090602190e010e030307080a1407060615030c082716030f0c0b0403080f130b0307030e0c030a020d11061c05090c0609030307 73
    0x2803502040b100404a00174000801a12402c41c181c00c0c2501c4001c5810b0061401406440f4141e2009010314241401c11400043c04500c00302c03503050440e80042e01c0165400c00e00c00900a00d40300200002d613100001c030842e1741103141180215401d0f6208503148802c41c040c55100c1c0560400104481c8081c0603001a035070083c0203821081000350a07213400c0601c981c03a150152a035648c0860300b1380c004801000b401560601404c400c3c5203c606006003a42000300450f406080b2548019241a000b24014a07021005000d1040030940e4407445d000126228144500340e090300d0785d021104151103020004100000100b035808594110144d1400c0401c1550380c0e030203a500c2103102d48000041840d0100d156203041c405107000d45544d079000103000145105031881c004880b080c441c402e50000c0c440c100113a0b1000050b41615a00001d11701c007014a0308003245441c058805100c000881c00091000306010700d42c05207110712502e40c11541f0b0b0b48034030341c184081c0c1d2080c601da6580680042000707034081050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 796921339 1250 796920089 796920121
    0x1803120103020d290f0a180318081b1201090209150609060301120209060102011518141602060604090314031801020307051e121b070f0804060810030803 67
    0xd548030005a001e0b8980a0380503070030404001d013840f40241c0c107020120001e83c80203603000030482c00030000380c0703000000b082e00304980450040c00c01c29260400840c0c0340d40c90000b100140000000c0315401c00052a070810070041042d0014040c0b4660703066a5406141401000000d503009400d203000c9071200c0d01403007902c011100314a6001201013284480c0764990100560080880140881c40e0241070f1041251800007e0034040c1160304003002c0c0019050650105000c035129a841b0100202da1901c1c2c0c080075000e41403c00c151030a11800b000410400e0041d444e1101003158265400e507510b03281000101c40442c5405000120b80041820b078907440c890040d03400038030a500c3c114520010424442c26a0f008a80e044001000881c40c0c1a160000042d40c4800405501546084c05510300000c0040880201030600290320081e80c441c00144c1d0104480c0b40700d4020b10100302c441144c1c08d000515900500c1441c0008501c0c00008800280c002010010340c1c3c0c1c45524145162a44d2100c12040b0a03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 796922589 1250 796921339 796921343
    0x602060f0403390b06041a06090d0c170a05070f061b05510c070c12030f090b0a020d0e01050d0207060b03010c170f0403170403081803120103020d 64
    0x30591051800c07006400511400c0341c4244d101c0400751038003806000c1900c030008440800300d81d409105819646e98003043d1030700004180c8204000d07107900d00300307900c202c83d0b00d921401000203200c640ca2110305020802180780f90154040320011641d41241e181202598890b501c0064400785003040344a14820501000a01031030032110018100007500e00064102032080007001405c1d2110004c08800c0700203480d8450f0f14200350720000094003044012010004d010076000f850016440c0d040200c0b95400c0340140c1046a027040d80220385240142202445500e4400030500b1200002614140d4000b2508034001507405421503504410007980c02c060b6020f0b0036810700c50140306088100ca16440603011a0f805040702180014507102030608581a00b810001002829441d03100445905196190014861715865902e540c46083c00c0f14003145004034100f908175640103000c241584140f226004040c081080d2600c0d003a010203d60303507071180311001024a800d280c010005031801540c00c0129038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 796923839 1250 796922589 796922657
    0x1207051b03031005031006030b01180e03160c0e070e041517031803060106140a0302040510080603120316030509010902040e06041208040222090203030a02070602060f0403 75
    0x280c40288590840d001200d00d90000e24424000308802d1404200705c440c4804a007508000d014150344881031000e005008524060703100301002c1910150507071005015030480300c107517611104015000c004030b2005040a55410012080c041f54a030521391640780200d41b20b4840ba4101c0c4080014480130302000c41c004400c2841c810000951140d116141410b40d0403407c024541d01c024440013010152a1220300e0360090f40000b005000d89070f044003155448038034103e002038803001682c00c1200a4032031a000030340c01c000012200600c55411411644c043c0030101c1c2510314040300e880c544006800301b1101e0320003601c84440d94101490085e4030071604400001c0000c50118034503000706041d80d082e032152101c154060001c002c01e200601a4000e0074000c14070f03216241d400c0030b4002451103d20b45140c0c104129403221014202c080c00d910010308194041c00b5a512901300c403001030340b104254400c2002502500c0002101800f0140c1e0300c2d44919030540351102010b010410301440c0d0410400400140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 796925089 1250 796923839 796923877
    0xf031a090106020a05010e0c0f15070204150302030d0f0e060c0f0706050a17130303021c060e090f16090b030a0b0a02090a0816061b0807080403060b06120705 69
    0x140c54004503540038000580007030218000a1900e142140c02030100d002d41034214002507550343e40d0f0340d0100290f40500301d450302020071800440444900c0742e180000e602a00d00418130305802d1034074030304a00700c900071400d84010b008403031419160109900d004100003454210010940d01d000c1c009088003a40680031150f01c86900c0c85d69030b2a20940703411603404900c012820035807150b400080c648202c112001030300300b20f01b880014420b6091005d08010203041d004640c18000350b01800510f9440c1221600c24844259680d41c074a00443c420380d444e81d014050049480e418000000d0440e246201c045d03006826107180c018034000408400c4c1c50164540281c841c808080340848070001e016082c03400d0f0041e5181400800c0018106465010348a9604105040302c03c59a200f0881001c8134444e041a62480d015102c00f260340c44c010001c01460800040f99034400d20801c0c0e4003038025203106090070001c1601c000100f00d6203000307a01400110481e01c80000360054481d1003d410190084c00b844240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 796926339 1250 796925089 796925141
    0x312010333050a1b0503190e0307030918090812040f0212010e15011212050f180901060509090c0f0d020703080f01170705010c0212030f0a0e0609010f03 67
    0x80000340100c0484180c0c2c4500a10003058020710851040c48618482c0080c4200300e508081c2c900d0100500452500385500001070f02545a9085001901c403000250303681c51005140250822000b8003034140b42c1c070b1280000c0b00b4480706610a84540f140c11982c103508040c100381046c462403000400031510000400021001a22148400e0f2004560000040b071402c980e0791200e468140c40c07034180341020141070b00400c105840600b131060101c1c0c000d465045c050b900d5080903151441008103146d0300b09000182001460700d0001c1440381420102d5110007a81d99034403040301d150054410f80703540200a600440c008001050042ca243c0b03880c545020704002d511000e0000b2a0002036082c1d000c105150108150385064500c0340d0701501d800b445101d803416410380c00c1c0d580d5100350f001e018180180b0740004415503403000d0070f80b100d800c0c80108a80d49c40402c0d034466106500081d5821004c075003a951080783c1d51030f085060b00c2110304103075105c03010fa500140e0308901078860084103401c80c20340f2022200d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 796927589 1250 796926339 796926413
    0x40905030a05040905070912030e040603021302120903040311010c1502040b0d0f1e0b1503041101020f0a0206090d0f020405090d0e010c05120703090b181203120103 72
    0x161007040c50700c4040d200d5281955032420f480e00280b00c6400c010800074240804e22145c01108881070301071070148071140f000e1011a00070050343c2c102a611504c140e01950b0624140c0d001481d07908a1040c5000741904c454601c00e90720f000d0383c04018500d5070451190380c0c06510510b401103207203001d0a0780092401c54140340300105d0b88160002c2841a20018102c404130b1054000c04098212182d4200080580442030f040d044580024105216849140104c620380c3d0b40c100d81d540381540040c245540c1e0410b4a08642200c0848a095015025010780700020a802181c2100116000350030070b40b07070000d10700400000c11146079040340c001e08201c01000c0580c84d0ba2184601c186842001000200d40013107026000030700d480303e01070410108148010001d00d01041d0808004005c80000e615040e043c58103941081d85504014051340c40402e503443c0c100d281306400000d01d401030300c005c82003000d1f60300c1654807072050803002e861400c03e403001000090303e0b412105074013100ea01e08090748000c203065480 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 796928839 1250 796927589 796927597
    0x203030a0f0909020c100606021f020f0c010f05060108011208120a0207051c140f0403061107050f0c100503042006130906090f0603020108070315031703100e1005040b04090503 77
    0xc030650102500d46c0250089106010180920740018140e0307102d1509401601d1541c444c1c0318490035000309051080d01c0004044d24040001c7d00006c1c0064203021440380d00a0204171401400114490b00000d002c0003856510780046400c030340c8030380c038002d408880d009000c9000b9040b4006645d0030000700000c640240021900402042003154001b00c00540003003100c80c59072140f00038200e08010156412031030100301c0e0112907020901080c8600c01c3c141c01c1c80640030354100903241b4024003445001240c4040703a021070a0b02c1c211080c4d50724440007202110076010444005225681c1e80d51046d81d2044459110061454000e20540c5001c8100795070307450140607507000c000d035503071075207000c3c825a0b22a00540e0400400a00100031aa00e9038000070550300d005005182810740d90700c03c0300d031170b6856601c68070080d5030044541c400c048101e42501004d64001c55216140d8810720f0fa0204a1000c141811801004404c0e418103815080000b000300804ca02d0741ea184d8480d030b0340c0d00d45c94001074051000e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 796930089 1250 796928839 796928857
    0x515040b0711010501061d0a0317040e01080c01091412100b01030b06092b0215090315070212131508100614031302062110120203030a0f090902 63
    0x50182070100010b0075a104965203041280d0608005100c0517500c01608060080b0400c560b0101c48000008500399102a8001034000d6040780d50141c4e0b1410650010803c40740d5190300e00310f091313984103202a26452402003450000324800d808000c032001c603101450307020500034241c0c0b003850360700e00340c00d40f0f8050707401e89030509540c40716070410b01e541c0c1611800700701c11410b0b075060303240030f072a040000c28080b4601c1415010200c810707840341020040d8107420204903400b909a1040e410717405184401034000f645014401e00c03d80e84008502c81118480c14022030490b001007624203002d441800300c6400003c2c40e17a10591148900094400c0c004946403840140ba4a0b00d0740703141000c80303000b13040c00d441d0f4014009000070341100000c940002070450340e011701c00680805003d503052002600b144900c280d9000018038010540b4251038160081d14015041454030641c1c081e580d1079542548855004040c0d0706410038080e083c00030b0b0164030302064150440c07074200441903c65449000b260025404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 796931339 1250 796930089 796930103
    0x60e0f091c201912111002030f010501030209030d080c070530040b040e041502310506030c0a1e0f1815030917180a0e06010219051504 59
    0x41e080c40700e840426031002c1030b8001c402030542041115002c1c41c410801e29001041148400c5026440e0381c81820b000341100c0b0382900781d4070603d0030000e844000c0c0d082980c840b48001c1040c0e0001600390300910849030f51a1003e00134040d041d0303c81a040c0c9030044000c0155803086000c21203007000800034009140c0c1c0c00040c0d2134011400c2a03000b80380c80400000c40e41d1882d40315007000107103d421a0201aa8125162a2720049041d035035841c211881c41c103103482058030740e4000f0411548210300d800175005403907082d405414004a141c00c0321002510140700395900310a082010520648201006081d005030904103101c10b100320989074040400001c2c0c0a1340081c05c007060700d404c1e2a511240741282c05a09101164030179041010f401c420180950320f800038141d94907103000c200204c3c0444029543d1a14210301d440c2c1100100350a0003000106080d4400c2d110280c0104203c60f261013518015041a401440c01889001005e40c0c1c455840c4020b80f1180b01c1d201e040c13251b1000e01e10710540f040c3d1045507 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 796932589 1250 796931339 796931357
    0x120d030b01050910080a061a180d2109050a0305010506010e190909140a03021e01090c050f0d14010911120a03110a0b0c0703120b10140f0c010c08070201060e0f091c 72
    0x50642c0d0300084458800d2080c3c0c4880340ae500440c04da981d0703004205001d070b10390a945440618044d21000c000340e1256400051000000082c0a810350005100311000c1c6c84041d9111982c800b002501e41040500d8410142d0300340d818030031001c8a600c42d226007441140c560890700020391446113090690841140141c1c030459801c0e10003071400b2203400451710b018000b80302d09803840d51204118843c50041501498180c01410300aa8074280381d9070300544c2001003078105984e00000a4042e00d0164410789043c003c2902c40d4200341085003102043c3d40340c2c0400350001801682e022100c50040c0fa0184400d4860341c04000041006948643d00901c81d94040765a2880c980c5000780c885002d5000d0000c03110700d04010500d1907102c05050342c02800d0103142503010b00508542040d080c0c041c0d01e030300810318240400c8094000d4415401196071080710f03201c084403555854812800e940302406070010102c0c101011410903108150815040000001a10302d01c200c016400c0840600e000c044000140d4108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 796933839 1250 796932589 796932607
    0x40305030a0f0504080c06030a0b040906061403070803030a020c0f0f030d0501150e130f140a0501080303101208070506130b100b030f15120d030b01050910080a061a 72
    0xe8502d24a01100c0e00744103041c035144c00010380e200c40601044a0050800100041c0d110b41aa480300312002c0e00188100a030410505004e40100840d001e201030401160403d00da440c580000d4650444400f24002c52446c0c0d68040b01c07401a4200000a82e0184254090313038203070080c01c0c0701c90f40340c10320740100842d02c81c84026140811b441040e88103428a2140c03441ca0140c170f5078002940104424161104016144c1002c20140201860343c0000b1084c5d1600100d030b031595150803c2d25014003415a4244040d0362210310064036807000f41c4403844c2e40c2c290050100104641e016426000c180165a080e08040d17050f240c190074558102c4e03041c09541d50940f480410418040e0156030041601541081254101a1002c0d03e911001d00b1500465082c0c10024081240529014400610241c050b684002c8180d013600d40d91901511040046802d2100f407180c3d5510882c207985824000521011100c0c6a040d025141c500d4040c11205200c0d8440001083c03004120004000b00c9498041035652031180c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 796935089 1250 796933839 796933847
    0x180c0d170d02130f080a02010e0118030501060302030f0f061f0e0106020129030a0b09030c01060b0c1b09040f1406130b223807031407020616030908040305030a 70
    0x1504400c400c0134a001e801e126102000481d024899070a0800c1c00b6520220001a6280e40003008000300c1141c05007000b004010064110b501200c0c0309404840328452001201a02da10600e40200050361004000a1203004118800f00600301d080060404007622540e60f500e9000d002d0708010701503074462560654031062114004140348400c2c0002c84c40811200000e91a42d440580161440081b88089141241c050040354401c00704003008104581d941d1103000c01981001000711241d004041c0414080c905242c4000440403009105407100e540f02d9545400c010400c40c815601450617040821801d501000528090002c8087c041c00e140554945054201c1000300001c03c0148010030100d00c421042012180095000f80c0d103615500d80d02e150075051616904954801c2c010003030018039000002c40d022400780b03515035018010844000c81c0d0703a00300d00041d104000141e0207c40014003003070710011006040015480d010130b8000c801d0321040c0c02d07600290001e40e810340000991400300340d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 796936339 1250 796935089 796935127
    0xc0308060312030109110c0703110a0e060102030403060504060b04050907150203090a0b25080711030312040219080f030a030e0a1a0c280206180c0d170d02 68
    0x100c0082c48800620024200c443c0818820040100d407074860721408142000242c6005020786800c0320102030b5a070506a40e203a0f09074181070301a024404001c903180342916182341c491032040c0c000354030701446c40e540c0c00024040140705451491340c40b0f1100b4440d55032030080c0d034054444100140211410031260710041c1d40c01c1442502954000c01400d1051384600340341404a42044c0d44441d140c9001c1e81c6034101a550b02d230084000300c034014034600b0400c01410b001d4813041d40a0035030802d540d10488181039803407040380003c414039188900090014548501c0e00d9002000a80115025559030219640b4188a000d403803465604003140c10203a20f68584148140b4070307411001482120000d40310800b8a03c1902402206000050000340251203043c04448180404088422340d030301640026030303081404401d10700c0050046030003154020006042c074001003000740010704020070b050020400a00c86040084615150b00d040c21445012100702070104040381c1040503a643c01503075030103080404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 796937589 1250 796936339 796936351
    0x40b010915060813050307242313060b040e010506040f0b01050d0c181205060c0406090e1e090607090f1a0a200a1109011a03250c0308 59
    0x59011820424030f079203c14030540000b42d50b41c418140c0500303410503d081d4411444050300801141000b0141d980740d909030001702c000b4024041244500b0145407900089811001c00c41c08640761021a814000d00940000000d2044100040c21401c44000c101519041174605031b290f5900c1e0200041030401e0300174039005660600e41000452504800600340e40102e80b04040050365600f0038098460140100000e401d008003414078a44e82c2e10b0300344410414244070200c2d0300d0301480012908030400801940c0595030940c5a10403150b080120f0020544402007014811501e407144002089040c40205c500034030050700a458549010300000e400501e1a030710400c4100c6407864100400e00b0b014910002c10003842c10150b40d00c2506200841e4280300311000e2510f880750300c91100280300350008951048912941254071403461b55401c00920b02800d1007a03a51851103450202070070050f50b401154402c0c00445080ca60303015803890514010300490102d000308a40e00010030901d074100241c19407010b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 796938839 1250 796937589 796937621
    0x80709140a0b0603070513050d080c162402011404030e1e01020a080703030e0f07080c06040315150b0715050a0b030c0910050d0b07030e0714100302040e040b0109 71
    0x102c98035010920034031006041a04100c004600d060a034911b4200c1c0700e0051800407c1d21186141d5400e100056601101d1020382c58482c1482a400c0101c1000c5180c0880f15400100740160352104500078400c0c5800280c102107550724031486010b030b40420110707409030b4025952010016041000d0101a5a01412002d07074a542100003040680c2d0000c0c1c0ea01c040ca900045142d21600580b800f0740c041c1119040c4000103004026007081c100200242280c00c40d826481100d2414508805001c1d85200c0c600018182c40b81408085001e0384080e000f01014000480031040480c3ea1103121030007681000030116041321a514103141a410300c2d006182c0c01450303134042081080b114000180d0380d029118481809143e110001808075014425404004c00e03016145401100d003a10748042510822a03004002c41c3c6031a04628402600182c40010384009029101c00d8440c00c3c020000c00444880650040507001c00010035840800780905020b40d105640c0014154100211130040d25110301c0c0490403e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 796940089 1250 796938839 796938851
    0x3061311130605034006050f0a0902130e070b031e01060518130e0f0c03060108060106230d0e0a05010506090c040509090309030a0c080706030504080f0c07080709140a 73
    0x3244448a00c440d02e500340c403014001052202c1c0c400b0b4603105c11140001113070b81003410242c10701006400ca0f0380f042545412101c656a965010344c01112507044e00030f034000040700b58029200c030a640c03086845050103421500c6155907107441400f1a1700459500300065030707000ea03240c0c81070b4000341d0540c05007500d03050107814100c0159181140140c00d07000b151049580008a40380c0c0701c0d55600c0582c1c0012240d0659142e40680e2000130355a40440c3d107614003a218403000001c00d0712020460358165541c5a448241046040280c4071304040c188913001403480081143d002498924031a086010381710102403c1c500045082550854100610190192101504008890711302004a80c10b40d6000c4034290029160510f0a0f841e41c01004030b03035600762184041d40c40c00d0182226130350080b15040d10403541c0c3c10b9242d940460039030320140d400600ba03420900040e4011803001c400780140600030412909010758510a4926140c0c03a940312040c02030340c4444034a8030106c0e000b8826445484001c0c18440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 796941339 1250 796940089 796940101
    0x80132010e060f01110624030318010518031c0f0305060f0d0f080f09090c0711040b121203070909020f120606161110110a080306131113060503 63
    0x1c16000101224030881c115600040141c0c003403100392102102c00f4089410502d411040750007006084074501d000d0302c030b642d6030a8005180010850f80c403031051070007400141485c00015201e580000502a80300030340615a1100394400308031480c01c0d40060a08501181c0c5130410261aa02d2030b22600c10170541440200310031900e0341c540d804044501514005038030b440d107042407010102040d07002060400c000541180350541c840181c610314000f00c1e9038043c1c0384c03180c00702d401c058403c1c00c030002c0002a1602d408002d41c541644004080301d006481c240445d04400000d0307040030a14408108466004000d002866621400c420080c0400c2d900441ca465072050510020340a0300003801d10034642c0d000010060745500b015140d000008140c400c1101c404e40c90071406412a042030140283c004034034030100c0521550184d1100d600e21009420b01d008281c0302c100c0c00383d100420b02504004c040e00d48041c0c8250a1046010340d401110b41c40b500d6031910781c04806100d40d01e52261040040500c01d10034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 796942446 1107 796941339 796941359
    0xa290108070311011b110f1003090c120c090e03071202030702030d0e1309050f030720040504050d05093709060f0308090a08013201 58
    0x2a0f0b0010070401101c4100c2e0f074070380c5c5189510318a45540d0100e40614040d2481c108054502e0400504440205965078404809000000d0380c60a80f00180000c0c56400400360031450380c0c40301c02c05403a89590741c1d01d1169010756003850356a45810210b00c0d904100311a41c0359170181115201c45014000a9101e40100d031059010f0b000e0039044500043c4070b030241068941c0020880030740c22103c1e08940c0e004201c001d00480e0244203040106030788c0b200410180004501c1007600240780010b403200c2181090004507070b54000d42c00c0c501403100042e03003c40c0e00c400d21642e601e420707604c91407003000065102160203101000c210190b5828044d01c2400100c510b0200c20310740c14400c1e40c0d035840c000360f01251280d210750030310f4004050303003030001a480d200240104000206069280750712010380d94211246443c0c1d4141c01003e211315000001a41c900603c000280d10314010a036624215a400d = true := by decide +kernel

theorem cover : BRFrame.Cov 796762589 796942446 := by
  have h0 := BRFrame.cov_init 796762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 796762589 ≤ n) (h2 : n < 796942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
