-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3398
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:33:25.39116+00:00
-- url     : https://prove2.me/submissions/65e193f4-46ec-40f1-8808-5331faf23d67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 610971223 ≤ n < 611151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 610972473 1250 610971223 610971323
    0x201020f0703080a061a070b0a0507320f07030e0d030909090809102f0604110d02030706030606140c0d050a2106050a0504020a0f14090904 61
    0x18490070307605031400c0351499440808040051040742c11000e103e000c10544c070007041114034000d01071540306600841c0151500101c0340191750087d51803101103481c0440c504031031103410382031a40c52840d8480c0e040c02c070000d0701043d070943c0d0b000f101d2518801c00c000407804240f41e00035090015005c000d883c44000007a29450050115200c0e0107040b01c4140c880c641c0754180407808064815082d00103000c00c82d108e01900c000340c4450a100780c40c01262200400c0c3c098442d420595460814030303010080d282c40e944a03515902e10341e442488440e40000c24a0f4080c0141e10700b00301440143c961520000391660410305c01030041d00541c1c81503901c5001c20090740550340c01c0810090404801400c02907100c950b0440c2c240d0702c1940302d03014449244042a269061400540c0203542180c1040d41c03800100d0b620b440900c020f074802c0401d06800704107440304c415111841030001ca00c04d800b0840c41c5c142081d4900300010100d030b0040c1c40a580b42c0c042c070300300395540c0d901c02080007082051402c128403c2c21240481e0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 610973723 1250 610972473 610972477
    0x71703090d14070e0c030603070f0810052502070801150819050a0f0b0a051602030702301f02040503060411011704080307030e030918090111040e070f0201020f 70
    0x402051804075411190610008003c080083d1881c3d803020300c4103150030685030110b42c004545a510030b06c0382c100001a5502c20550900035100088082d006d0302284283c01c40103464098408a0b040081c41080101c0241d064039005907803800e64041d000c05450085c00600f9149d103094404800b2603103400421007030b02d000444801041155062010650141c00c006007404172501000c0c1c0840c01d01002c1404001149820030310406013502d040160341c03500f0929000c83c860f10800c042c00f40c0d20806c00b1401510f0000000c1001034401e2040090070f0001801c0c0000710152070b0344222003a0702500a410f08030f540c14104607485104c507a030440c10b01d031409000a0b40c0d2034024201070580c6090002c0d0700082d9100340f01026030514040c0b41c0c8200c600b058030b4500c800f90f004803071100c00240352200c41c209403100402102c6000e0001480700c680040c00c4144c202503403070040c146040942d40c0f0784400c41014801c0c005400284000302c0300d11000e02d0110b001511169100c2d1501c421a48108110704441240c502 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 610974973 1250 610973723 610973749
    0x9010e13020d061503120306060203090f09150423090a12050a0e040c050c15280f06031202060f01060f030504080c0f0303071412010b03101707170309 66
    0x10b030748005584a0828000a08810b813180c040c028100001209210720303c41c07030305038150155804210082e03551031b0403a2031b4010360b601e541e48404020f020403420300e04020255008020002005010ba403409d001604690540d000449145502c1c100310b1220840d0401c2254440c1140020f00180c0f10036580f0703014141c210011710f01c10b2041c007207134101e002c1e4411030100881007800742c020094800203207009800c90f08500b85c41c40c102d00c2160040301680c2d541d6682980100381d449603040150002c407050210b80d10701c100c229900300303a50324000c18007004079004400003103010b0f130303a00d0594010300c0310000e00b401c0d030042100c1118101c00c8010003540c0e030300894140e42c000c010315001034a034032207250590042c4203221041d000d900ca6603c42b04100040800118001c0460342c030741d00e41131070300201c50b4042070150f1a55013820f1031540340104050a0f4010046606c00b241141c586c1c0f60710b403a4511500007460700d00a00c0c540754469007043c4082052031007043c85040b8100300950400c0003000005080d800700360 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 610976223 1250 610974973 610974979
    0x302060909041713091a01020a060f2004060e1c020d110315090f0a08040e04020d0f0b010812030105031b03070b0406031e0e0709050c1201060e09010e1302 68
    0x10006050002c1894800f444551001009a80b6a52200f040b4502e0225001380c15030541744c19440c01020001140705090040107802926a0154540300d05c0001c10010015000442d1161400610b482440c0540c00807040105155900c45050460050001c082961000e0003a6891444814810425050705403002d078100c0e4100524180ba16145965019005c0311035058403482801e400f0503051351000c036104044030300c120b070034640144203e15500e02070500080c0c0102020002409000030502ca05944680041c050560104455440d55018004400c05035082081c40b001400a45400d20185070102c04240680d8110f50400d030000380c5840b0881c0241d0000009640324840e02e8030248131420041420740101602c03580d4400000d4080d000c402901882d081010489480d81d80092007142c0c1481c00b035200a1400c6820b00b040d40c0018080a440c040072440c0c280b1018102180c0f4004050107000c00b5680d442d0381008178000c0c080b80301e2041e0000d4240e15500b90420034044034007001c18505c15011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 610977473 1250 610976223 610976239
    0x40206180d06020d0c08070f0f050c120406080411010c150b0d02040606020703170307050901050d020705060408040e0f0622060305060c070210020309030624042d0603020609 76
    0x41800590824070111000b8101400810500d0301001c8680c000c01d000701007501c0e4100305507030b1500111800d00c050300500c004165071a00d0418158442c10280c6110460401290902c08800c140381d242030700158400b50002c0d4100040200300210b024040b12403a6007070801190380b2009030384080c4c00c207610029003403100d41c0d190011a52039840120505003140c01400c1000001e464000003511182e0b14042035070081119106c035421100400300302c911800300395a4179418500e0450044555620003030521030f1082d020300039500841c03014002c660050340715419041d92103241c80e402004101c0010802c1100b0741d811400c0184980301d200d80a8600c0c86213841400810143c0302241008080c46e030005062403245c64100041690700000405185000302c0d80360044104400341243e6130f1282c2c1c0e01d4107400d034110f00b000c10440c1143c01200c640c0e07080c0103100ea0400400240c082000c03641a80c40c0c015800c40041012001d20040c106004580d0134001c80c11b003d203a00b10380206030385124600b0303058050080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 610978723 1250 610977473 610977517
    0x441204020d0f20010206060d1209080102040905060f01021908030604060e0108010e16060c02130207050d02010c0e0f0609060c01060b19120501080c120718020403120305040206 77
    0x4841d2004400c9a0220740c10903640401e00700140c0344103490811800c3d1071010702860100e90300000d2418411600100003115041c450799401800d44165035000c000d00c00040d00101c0c0c00c0c402030000c0d00190183c05c0001480346080303030400c0401600c1c2700d003050544d0003210f100080c801c01c0c00381d4900003540200810b85d50362541c00218004050f640e02c008407949080c1d001088600c41034002499926081003201c8110041d040c1001a40c40d05115290210f14003905000040c1000c0c02c07202d0b00314070011401400c02d142e6444884c1040114061200180d656036071082100ea0444461a07640a041d0f0320070b042d0f0400311300402c7c0f0601c50300c4000b034441c100106143c0001d40c0250032007800303000c018404540711480d200b10401510b1064104030049500014906003110b84d03489014100d900000007000c00440207814051a0040180200c04a01403c0d6011a40c4042d4201411107410860707801a55686076051a4241030242000d03001014100018000541d40b100e007941c01c000c071110b010301440c2b05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 610979973 1250 610978723 610978729
    0x645081e0c0f060a0c170f040516030b040b01060206191505030111030a1a0a0902130923010b131a070b0c0702040c02060408030a020703020a44120402 66
    0x150710881c4515102c1d001c80d1691a500118401340039840140c000d0002200751181540c40500c00034170000800d0400002600e8092000c1c16643c11602403426074009004220403151100062340041e51814411401d10080211104134140180348034401341440741050500c00540800d1102c4c042d4001d51503181981c01003000d240714000400300180200081c0342c0d1400104079a41088400f2603980313107401403400f05035506040804141400420006225040090b04c0c03000f500032100d480c441118202020400d40d07111300c5100b61401d10f050f400c090380c2600d03051486000783c0507000800700c55014040794000d9001900b808081e07030107810141603401966001d000c3c1038000e5807030181c50304201e141170005010200b801890130ba4000e07141480300c288407030800d0303985d03a1081c0d60003450290200000364881b502ca81c0039091007440380c41071b41d00f00c145503125564075a000e5080080b20700450904540104044140c44a4a40c0300a405015190300f48104940714010840461001130214000400310f503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 610981223 1250 610979973 610979977
    0x1209251221081909030210050c1306031a0301061a03070c15020a0915090504110c0a060221010e0c070c080610080706030b060906070645081e 62
    0x440d0380c0c41070000070090080200a40c03419a14038100b0655586054010302d039900803040601d4043d0001c0450162100070389000344401083d40000400500101c2c0030000c0ca10b404000511907542d001c84c0003904190f544900079012800e0f03d2180c0e26104080220321429900f907500c154519409503140d0790ba0141c141c81d2080c1600000b00884074a8840060805813a4041c001d048102c1d55222400c41c0c0321408850703909001d44440c0041801c0300c004014600e0301d50405c0d00700b111000142810501440c42e080e03d00b40c01e0101c100c4030300d5008111a81c030200d81c07820403a83d40c201c902008900d945040410000000060021042050009045014070580001000082009030115a26032500f0304c0710b20031010460103005450701800b600000d8480c428005d4940020004104625000c080400c0003d00c0c5e00a950032100e450320f81c044041001c10304c55030108031050030044c41012403440950041d0350001b450203101d9003805250101c0114603824190758015101200c101c255104590054182e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 610982473 1250 610981223 610981253
    0x3240609130819020c0414180705030a060603021e10080a180f0b0109021c020c0c03120403050105092a01031b030c0306210201080c0f12092512 63
    0x10302c0025032114115076424160803100c501c0d400e03604404110001c00040c0da0901300c0c00803c41080c44049410b911428062244081182e011502c031180e445c0040f1b410101440001d542a941c0d039070080096090401e2110011000c0240310203000180900045640c1341040c11141009030750800101c5200b1141d001280520b90003480800415591070148030240c0340c3c1104662076105903000091b2681c03940203843e800c0343c880140c1c03000c1d400300c1c5a0f041d0003904010007840d55440340d1040b1010503201800b12407200007100340810b6403207045081140c01e650019042483d241e100603100d080c2c0740501d00030058011801c2e20480854215140101c0140114480c0c0624541d12403c40d500745540550ac00307a60703030006407402e101035965081181034810316201071408031815080100c0040d8071071010a030748952080c4400341400c61240004000f900585444c070729590b1f0701010f010601e281000906101c0b46103064001800d0040300c050300256030a403090141d0081c1142020003041034042c004001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 610983723 1250 610982473 610982483
    0x60112060b03010204030f03030b0405040308130804090501080c01091212050d021306052a150417030a02070c090c09031b051503160f020d0e0103060914060324060913 73
    0x68641303131f0030000300c404144c407030850200e0f01d0b1103102c00050a01d401400e00c6543c054036903003c0b0303540700002c0c44c0c95002400ca044609090400000c9100c8140d0320420380a4403080300184029280040090000c20b000d8102002c1060800c000100140c400c5404400420651030007545072412040108041e0041e2060840300c0301c003012020a404d58000040e00d000030854004046403444c90b503401020840386000d8155540044501c0201107000e810b0080e002481840711151001d0701d524151081d8006844454400c0d40006425090100303840714180034220340c031400c1204400002015180359128440184000d54005c40851041d2620010700010803015101d0510340d0384001e2000019402118030308407041c040313241c14103900d21410100440700500d030020484070035040f0003940c10300040c2a109040540307885010a00b180070b40030b0b50407440e1211005141c1403e041041509040c00d44240003030360000304681d020041115940550019021380c0c140d10182c9640070681e05c0d641c1100700140c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 610984973 1250 610983723 610983727
    0x705033901090b12060f061c02070f0c06270e06010e031c0909150b070b060406030f0f05070e0c040338010e0c070c030615090c210b03060112060b030102 67
    0x21304e4400c0145107205520480740c1907942c0080c401040441d020302052014044210717484100007410590007401418016184442c5080b40e0344d480300c00101c0941c0106c40041c04400f069000da48003c4a80402d008580744d1780c100c068101800030320074080041070181000307808a80190180c4060002d0f005080c00e40e00c0039890b40c507401c00c001c0c00c2d0140c0313403103620b403e5440c060840b8125a0010707650000c1c1da10b124140c07072401d08661181208034001400c019030180c0d0b10700000002400358842c0ca0111845024850304101c1035003895424103003141d03c00784a10f01c06804101c508443c0400712429207038807045600101c0528a0514648002c3d0101c9892140350006603464501d142141f06048483d41640c003403150351140c1300c4603418007038100c0080040300e442006000107002a040390b4034640e8144d5003032410320750300c0000405660b055104400810242c000c260040b01c1e8880d12026614001103061090609240101e5580c58052240c070001c003a03a01484010013100b41c0003040d170040300800940d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 610986223 1250 610984973 610984987
    0xd06090503130602150c0301030209090118151505010503011203090b04270b060f0c03070b10091505060d15120308070305130c0b0309030702040504050705033901090b 73
    0xb01034107041c2c020303600503100324410402c05202001c19a407003040301101076820341c1d1a41d403d00802d00400f5001c0c1c2104c0d500c501000c02100030014202d41c496000380e01c90240101c0e604c0c030440486440290005a11107296414001a604042141e045a01c0004986400b01345400c0c2240d52814039007004038480400100003940d0020342c541c05a28140480303480200b102c500600a00715052081d0603500100e080c0800841502448040d02c409a0b01d102540c0c1b070702225070740e04212a00116054081300d540c0a03402e10031071850380304641e0003417808400b0400440c08c0c000040e520340201003007607040a8461003003070611030110341d0f81801030015100c085000c140920740609500d4089401000080c42c00d00001c3c2c102110f058520643d542180d02c5a58580c01c0c0720920362141c4c0020f104442d50b200c00c0180340b005844038400d1510540c000c0d00500605400c02c400c040c202400c141d42822000380030300c0c0c3c0b000001f080300074521005034040c0b1018508415440140e40000d110743c480d1540f82030108280e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 610987473 1250 610986223 610986247
    0x408250b100e070206160e21060106020a0816170705010e0d03020901120504050102041205030405031b13050709170303181204090b060d050915240d06090503 69
    0xd4051a4040d8030702507490384540c1d424603010380480f076078001644410003081481903042180000500c60341b5000c41e1615118003c580100d14000515a9020700d019640210010500403a40506060305c00360807030014a0300c4400003401801c40c01c4241d0f081e050004810400c0c240ca011012000481410340c6500090034041e00a080f1346031880e040d4062035441381c2c0c0c058403c0c8212500c0301c2c0d0586599800b46103280364039004002c01001100c15650801c40418032801c244d01e8820058410401907959a04100600d0f080c9501c00c51180d003030345901c2806021540d24612209201d00102d040060b0b150b686149c00c80307100009502040207241007498003805240040001e40c4901ca100640c50f40c1c803643c511081d0341c6e6900e12808590f00c1001400248805a03e94218410808005201508001c20348042c00304469040d940c00c0620b0b44a0404032041d98000c890480e130001c0034482c10303841e40a1544000301420300192020f846904001c41c041c0402400340c8c04410140c3e0441c00f01c86e2107038850261 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 610988723 1250 610987473 610987493
    0x30010b0d080310050a060912150e0a03090806100b1305090a021908010305100b210c151305040203060102030c01090b0105010e0a0311061c023609040825 67
    0x4030078070f0b4140c0034008602801e0a420060880e0b12554030134524a1500002c0c08003102c0302e19040303441c0200d490700103a140440f806810b4001c030702880036103d181014078018108441c42e50041485800500400c11880d840c1c2d54000121460a0151595128207042c01d52116002c3c2c1c1003294400010800e110800700c45a020341031180d821191100fa0322200310040c1c2d0348503001d110042c09039001003140c2c0898911600035001d900c0c03000e0180c170352414000c584035007500744400d4030315001c1d4444444500380e407501c0d880908000e00c0580309180b078050a9002c001c40502c0e640100d60142d500040410b5160f442007044a120404100c0208104100ca00d88080038170020700c255400030300750040f4a1100e01d0b14286110072a94402c4045030040e07940811f1000c00d070800c142d2480c0d11350784c00e090400c1c1d10609000400f4049040300e1f41c184c030361a40c9151a1284201d00007080c660018032049020a51a4014070743d41041c0c0200380d441c0c68820103ca03060584032551190a098000300b42a00208554925 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 610989973 1250 610988723 610988731
    0x10204180501060e0906130915090308060108150f060409020c0703060506010e03100903020c1f26040f02150406030f0f0c0c030807050d05070c1130010b0d0803 70
    0x102884281da85031400c46804c13914402d01039000048002050480c90f104004401c002604240481e010384103855007403224109059a01078141c40303200043c2050381c40103c481d0300c24000d0800c06003d042c012211444a103582c01001e00030405254441480c0d0344010980d80244694201599100c40d038074121911034101d44400c0701c006044c440800c0503580a6400c01216107000b070010200440b10700b8000020346000d03c010b50640c01070010140050700c1d80c440500300d85104003591480c0785002c2c43e005041d030366060410741c0038203408003103c80080b24008116400c00e4020810b151081b225000003840d007954640001d94a01340040c0010394250190070030342c0a810107040401070244a400040141c5000c0407041d8005550b2201c50340010b400340c00043d40008851900c50f09050351840400c045500c00d80341c1c00003003030204c103070441000040f5002412080013690111385550020004480507081800500600d10a02c1c1c078210320540f0944c4440310401c0001c001c80303114540e42c18009403690042e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 610991223 1250 610989973 610990019
    0xf070f0b010501030b061204021201020f120c070b0c0a12021b0c0406080718090c060c02031606090612020d1109090f070203030a0e15010f0f0801140711030c010204 72
    0xc000022590b000344540c0e401c074000500f00e40e00d020300310b008584014070010800c90340607912189e41001c0c60000d101078065019407644159451003a101d1105032a44018034000c1c1c101001c01c0302c2800034085410440d0442005614191202040c400036521888210700503280544003061020f4003005100740380801f060000155400414501c080c0001c0d101140113a054561102000308142103c1440d11101c0401d48000011a032126954104d80c01d2840e80c007036400030380110140025854107021180f0100782d1100c0e04020f0920f02503014000403820b01c90802070142c8101e00c59400203c2c0c0d01140d0480502a8041180904448425405800400e40c1501490301d980004642070714100d074a0f409084250029419030780c40e071108101416400c90660f0302401a00103007601c0d0f001c418080c034080d000516501c40b0a9040c10345d450405030803540318a0447c0e041039050312640807892203243e0040210f14081ba07070b0402c180c10041c60340c0b198000c2071070190710024001032031205c4842455100c00c05a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 610992473 1250 610991223 610991243
    0x81c032309160f0f0308031e040501020706110a0e281509050a081b0105091908010506010306030f02152115010e0325150804050c030109030f0c0303020f070f 69
    0x3400380070000030a03134010b01040c0e00102d039041c408540094003456120701e01001041d00660030000201404105a504444580d000304000c0b0030003401c0d02880d0050210104441c0c05c1c6100400c0c010070408000c010750340181c1102250703103540707001c244c2c11401040308000f1113011107a9802881b01705001c104501d00c0020400c04c0c0124951400451000c101c0d0000d40c010b0100c484c4488415410090780c0022506000040090400684035002c044851703001441c600c0e0320b01ca00d041d4001342520802005103042600d4a541880050f000c030803041d9110f50181c40300c56850620410401e4188641014401001c1d09c00d81920390b201024001702d4072552800c058951001d00420056501c082d101c0300865054109d401042c03a90591700000d10000ba1040411541c156601c05c0048200254020800c001804400030841032100400946d244001c1c2507008001e5246143c6000f05240301c0c080043c0100402070010106040c4030f60103881c811200d0b55805907680c0070515112f0320040e00c1c03020403114503140c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 610993723 1250 610992473 610992479
    0x1103031809010b0408030406032a02031207080118050a090614040c0617010b0c011407031d030f04060807030b1923060d020f0403081b0601081c03230916 67
    0x340006503002c0b17404000045040034103140c425006440c03030b2016000224048204008007426070350a0081c800d0058002e1683c2e1a040c8010311800e400c010045000d0000100040102c0745803a986c1000d041c40c0f4800018843d00da5540c81c0e4050b01a800b030103847c96040c001107400540480399910b0007148180120303110983d841100b5541c091014410140c500c1c0c0d00c800401040c480280103142e003204503000014042a0210041c600910665907040002e9540307040c448010100100720040c0c4405000450900c440c80080c083c0c2071041c0d00074042001201e4021a0006000c2d0f00440c1c80804000d0441040b21841204030181e81c50b140303d4410915070400180b00d001c5c446408000c0302150281000d4500000c80401c24040d5126840d1686014400c2100002044000f40a800f001c3c180b00801c081c0494010301c000e18000f41a01321708010f0b007103040d040502c141a00baa480084003203040204070030880f9184190642d08951503900f4034540c100c104010b9480c00b0403811011001d0440916080c0d803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 610994973 1250 610993723 610993739
    0xf1104060210091a0601170c030105150909060d0f151b0c0209010506130b040806100b0a08060904140d020a060f060509060405090f0a110f15030a09110303180901 71
    0x1c072412010700f600034480b042e010403540d0f913500240d12443c10b05001e00c040030342941c1502841c130100c607180400c0c0c02c04001071200341f501d40140f511114500e402c090801c01d44500080710420301800407032140c031541d05203404100d0280a6905000d0300b189550b54205522860710f4050028070703842c034400052440d00c21580038041c40c0341c01441d0744c01030409000ca07800c0c04140581640640c0d080580340540d120b000548000580040c005840190b003c2c1c03600b4108840080030803003050704200701da604107100188804c1d61100c00c60754056001c5940002c0d54486040004052031b42c25500c41c0980218881304990980018260160034482c1c07104200cc00380000c00041212800c5c014640d1000008000c0358039468039812141d040340349882513950303c20f8498496480c100f4000403c58200040000494161800c0000d403603200708240c80310071402181c140c94043e42d203c01043c0310121a41c4060a5044c4071036552900c0403503070041c00b229a520b900c3c0c0d100304500740c14000300510038403c0b2400400c641c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 610996223 1250 610994973 610994981
    0x15031e020306101e141b2103041509060908070b0f01050316030807060f0c080a142511070f0e100b1b12030109060303031a0a180f1104060210 62
    0x401c2e00ca148a440d03001d620310840b52901da400039204460006c1c8065100019425581301c018848140100341000c00021260114060001c0520301d0070300600801002c079079400d19142144041120010742c004075464014000d1540070009020050301068240c1003100e021070301350207031004040c041e0b12684d03038404069865200407215005040e100d0002c000280c0103030068204680300786001314945107001d92150880300c10f510580000350001d018001010350611a0340140d040e41440d980b814a4400100b08801e00c1c49845200c903c41152401d203202c03445560f03068090800c0105890003540c0d140802008100b150042c10015040300003c03414895846034250100c4410040041c00c00b000600308020540359012071440d18000d1288020030310070305200842c00390480000000f841d6045090083c1144c0790400c0c0300380c2068400240020643e5202242c0c03045403401245e00401141e200307402c501134000c1d100c001c0000f034100b1440e46081800540548113941981e400c490400411808102c292 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 610997473 1250 610996223 610996247
    0x801022b0b060a0507230607080a0e072601050a021306050414270421110709020c0304090203040f0506220809120a1101020c010f02060115031e02030610 67
    0x40707101004880c0500b80108042c0c00700c1802141341150428921008a081e000c01b0790580e5142d40005c0c042040e0940c0007501140c204241a400f04045081c110301641d0b1025940104070040300008440601107404040c1949980c80100c0248020300f00800300700003079080600818034074042c0c40400314296100c1c00c281c5046943d0065188003503030002003401fa207643c40710811116070805a07100740005015204082c022417144080d48401300d03807036002044020014094108002030901000340c401c0000800f181078800110006a0340c03e80c0222051851040760301803c42980007204000c144006038240c00b00781c900070010b50b000d642d5941b42e012082d501520741c00b02213030079045440f4089900f060143c0400e180180c056a4440c00b440310152800c121100100d441d0b0000c452a803d4079641400180103000e000e0030000040c0601c40b02c06920703070b98140110524540a01c0548078403078803e42101e1109070940000e2110300e014134814a010798003c03a0343e40d006010144086c07020503ca00b0b03905041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 610998723 1250 610997473 610997479
    0xb1902072001030e0f0d1214281a030d03020f040303030905100603151407020c1e0d0305071703041a0703060b04080706020106050909030a0f02070801022b0b 69
    0x40903440707850100c808031001e14154100b6030781c3c03800300f42c203044100442c080204001c4010b1807000c0342018002c0c00c5e006034100f8070700914102503500c43c244a024003403e0704414141c00103003030f00184c0c551505800e0421210141c0c0941090070035810800710601010050506a0654402c4a02e140c0250305a102c0c10765000a160010802000400d00c00e46c0154501c51080c010340f1501000c0d05414000c2d02c0e0103130070036038000380074007601d1055040030b00c101034a8114802c2181c40f1441d20f01e038041c1d190051506207d000b07540c2e92401e9207502102d01d6640c6202580108401031b2035486050041c00303a008410100d0381400b00340c103403026010415050b40d00c00e41c3d1100d4800e8201503e500484400e5a01400ea001407544400c0c0110b95110070b0740142016000500c018440c003072801c040282541c20640c0018014084d0009001c3c0c610004411140d88150ba03060492501307154450403407401c04540c1c4101c6255101140d071200301582a03000000510f0080c141300d00311403200c1c0541085402502c400ca40c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 610999973 1250 610998723 610998743
    0x1806111504030e061303150f0c021f020d020906072937050c130f05060414060c0d0903020a06050a08010303080c040306090506091e0303040305030604090206070b190207 74
    0x10f07080c5030a0300142401d0900e07603240c1d074196941e5640c07441e8480f0800056500261526141c1c2181e0041c0d00c61180c05c071a451000700303070040801102e41d8000651004008116800207140403400c00250101c0d1441d40d0b015080c0c541d1800941800082c64109036900480d820461080d00c8080001c003040310b0042c002010940110710504140c00301c0072070b5075186d15854099940e00304105102d984211071003403081d546125039036415003481c218401da032034005810075580ea180520154441006035000d1303071024051841192a030b08001241d40c051003c220180d4030031000005c1d1402c0d40a01d4010840340f01f030311001030703a603219a0255501d005520365040011381c04401040841e00c07850710700e90400c4c1c4041909103060b4030303502c0702d1050710a4880140c075180d200900b8014a801c080040a01c140070341c40550810604a5450741d441c2d00c00600060104075010002c50b1260f80c40794030805146034001d100d03e80d280341c941ba04059000040b00c180100301000307000985c000500e03000f1036003041e40c0b040442c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 611001223 1250 610999973 610999997
    0x1080d14030717130b040b04061514040b040608030304060915090b0718051305041e02010504030b07090506030a0b01030f0506060a0804050f01150905010504140f0601180611150403 79
    0x56501d01e8014010306041c0790590343d45005c201c2a4010a01450051050b882d440c40d041c1400010f82d400b02221010400c01c24404108a00711131030801c0a401c011a000b14084002d60005005000b180c4c00c050131a0100205010400c9a103900c81c03c0a1446003840030751500c0001d10070b604541c02500040c01b8074030b283c0000307101c0724422143c0004140c0415226100300340c890000c11400fa80da4243c5440342c1c0c0d40c44091205015201030400442c500750310800302112079a500007001401944001030103044010003040c000c500a01104000c0c01002d0a4541c41b403401040350380103001141030060100745072240021183c541401030794400c0c07402034812172900302142012148044c0040041d40c180c02142410514071200380070b1900f0f1107850381c1c00081c046040c500720b90200ca07410b03440741d40300c2c0d490302050300010000014a07544c4400040340200e5199034110060790208c5c0800404541210142c80100f026600001400401d00c00c4104444e003507000d003c40e0600078001170b130f400fa02145a0b03c010b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 611002473 1250 611001223 611001257
    0xe060c07081903170f040326090309010e030a17030a18110f0409020105090f040b060a020c0a060e01092312210c0a0b061207080d080601080415020306011701080d140307 74
    0x80a2406000c1500341080d6080c1079008c00c102074680003010303000061400203543e4481c00e0640505c80c1100034180541d21951010b94041c0c0500015403a07100100010b104254184d000040c85072075413200f1400c00460340f40c200100b50b8991681d610130040c0c840b2001403801e0920400100c541e042e12040d01c1c02032040c041200c2c5941c0805103551182d110226544107407110b41c06000509802e400411181000b5010801c2c249180d80000080040709020b11155030b80c4070365501d045410f94400189071a08440d0102d069040150185410401210300f07000d1605c000a41d0800c042014242007072851022954220140302d62004042035030b000d06810303404154000040c0350003c8c0c00030250000c17140507020540c00d000065000c84187d07007001c4003500b0200d81000007143c0c071460910b841c0000c0d01e042d0ba5000014640880040045a80440001d12a074090310700301b8049590203036072400c1580d4440c42aaa14103090384440001441d10740701007030710446801964010600d03500c40303818140300f0f0b580e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 611003723 1250 611002473 611002487
    0x1520010e060c0d06030c2301110d0f0903021f03061424130e01030308060105120f04150f0e1b010f051312050102030f10060e060c07081903170f0403 65
    0x2490510356580b02d000002a5030511a80007c10300c1007159840c0c5507240b1841c0c001c0020088446040c0040c01c0902010741c1c41c0416411400d10480c01c1c00703805460381c0502160b0680203900001d40044070601031100c0142054030280b901280c50b40c0500110f602c550004050400c2007a403250043c0e044e0800750310b80301e0700001c41d2041301100d104650806403078441741c8010071859401301200e1080b0320014070a165010300180d901450a0034074900e401c1a48420070143d01004182a40515400012500f00041142c3c10020035172100320030f02c810481c0c0e204400043c10b2007c03a644403485580140c00340300004495841c10240161202c491005c038181003540d1903072007002e00740d000e40e0340700901113400c10380244d03448812801100016100d00d440501d9203d17601c8090107118062420751001c100c0954800d08882440e041036401684a1818030000c03860710115070005c0c1460700956101d614642c00841030003520324060b5550741c0d03c2d0040302c0882ea03203103c0140e0764140d41d0018040001c0100c0d0049034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 611004973 1250 611003723 611003737
    0x32109010603171803012d0b06040314190c0e040f050f032106150309030405061305010e040b090c21090105250e0d0816030e010e040203060d02040c091520010e060c 72
    0x2040d480018000a4010350140d08200c4cd182d04105416000d0790b000c00c20000761100000f41990344803eaa00c5d00102e010700c5205484040301d0a0000408103c407101070000959442007c0b60ba91413a200000340d03c0340c00c8032f5001410100e15142200020034481c141500424010305650328011855100d007040b43d01c0241440558481044001259240c0b10000d000307130040b038a2611909414000010210304e44030a000388650305120030b40c0804d540d102144e41d0042d4040c21040d96819032440d050350b1110390000034030150112003040007034208041d0005807140325100c090b813240701c4036860510803000014440c40000740d11010032792024180f202c40c40800b18082e59119041c0018071000074001500200c0450028601d800301c2c401c1941c210200e0107805030b04507415070862030010f01052070000d02c800c02900c03a640310b00c10022400d00072440e0340090b009210001c0f0b4801c0c00c01c240a0304881c41200c4040d2405205c5c0d00c900c440d8841841559119240200541a6a1603a02c0060007a4005c61 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 611006223 1250 611004973 611005061
    0x2090d05100204060f0509030706030509010902090c0a1b050a031404180e07061b02061318061409011410051317070803210901060317180301 62
    0x408a0404240204441c40c1d040c40901405039946040680c01801600460344100c180729040c00070b0603c0d07940100b5641d0550b086403800103040d40d0744a551501610000d44060740010140081c880004c04001c01030a00e81ea66444e5210201140c09a80303071a007108110140542d000500403c00003845400240749844060342601c0c1803c2e00d40315003032828502101042041661a0054502d100003403008400804e40342c05c1000c0e2555000054225403d8020070081c4035240000345079076889104409100a4134080c1903500e00380d03441850610017400725016091511400508d1050a454030080d12410780701c0407220000303e0f00040f03003400071110200c049801440000e00c041e0000a010703524507070062161090380411024403104081c1480010340015116801c20001400a00080c0700e8050907002581c180a00d6070303440d00119401009a500010b04d1074264815040000d05207002510031440340076012400d408000e41010b0032101400010703480c0b041a03102c0b110b201e5003400c02850401c4002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 611007473 1250 611006223 611006239
    0x90f090b0102031219050c030105060714070b1201081b0d06050a1b0918051e071202030a0212240609010203090d0b040512120c07060e0d082d06040209 66
    0x10881c01c05071100205d441c0d111521010b052028141c801c2d01841d5005006041c0c50707885e650514010030101d2040380c4c006004d007400b5800d482d1859504101820060004181d91038452a041c0c11240319071300c1c06c0c8030b07400292065500e246044001c6480c50300121000030304d5000030356010341d6107102500d401444201525603400300141e6084c007003002c83c4507200440d03032200d0b0f41b40c0c104400740c1080700c41e04409001c618502801c0106001c1130501c00f4a84043c000b160f0b40803a0756030f07139080318002d142d078101c07142e03160000c03045c00040001c58010b40600a064410000c41e681d030316000c1c413000b00701100b03040c000b0031440e182c103026030078980014526080188107807803a0000182c0400e140c00900e0342c0c12070f1074103c3c4038100014050144035801641070b000390f40514191004070401e03405d180140c8605110300d8001446400c021566210103004c2803143d0079569280c41c41103000d403504c0001c40d12244041581022071041d080d040c031100300c603c0c4140c56050395585801c020b000003904031042c02d80d005150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 611008723 1250 611007473 611007487
    0x6070b220b1006021501030f021f050d06081605221b020105071d0f011119020a08010908040b0919080d030f06080c120705060a0519090f090b010203 65
    0x30414611582401051030740300724203018a10032201d26196000c40b00f15080b0103c42d408102e541806241140c3e04005103108600c03c0340006525101700d000311825044041c85c078103403010741040c090040390056210030440150f035468041d8031070f440d084550640002c034079800d1155107404ea91020b0410240d0308044116071042000100300c070100b140d040341c0c01c0380030555520031560900546a02c40e45034a815072800070080c4058218081501140384200e40c850810340395039220b12000425100c0181c111040104034045401003810f04407000c2c3c3c010100000d0110306c03180305003e4aa8901c5d4090641c514280c82c04503000c4d0550881500d031580007a1415401500c3c00203002403101400681019080346200004041d04940516207109a8603051400410501c0c0022038034011580040d9100c0c5c0080c00c1c404241c500381803098001540c804404a00e04200a500c01c1c090701078280104000140c40343e51000a580e10103651183d100c1c261096007060210f0740c0b254005c14280034040c011a420030f00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 611009973 1250 611008723 611008771
    0x2061b0309030a030c0c0915031712010e070f03060f06120605040204150e0a0509040305160c26010e0601031b0b0301062607020309040b12030307110d05040506070b 72
    0x1d403c5059000600c0c96a00d03c082c40a0400c00c5401000144010040001001c640fa00c02e0101444003a05c116032a0100c038045486210841300704004005020714a9038540400c11001c04041e640d80001803108110481038500034440c0d0416180c0050503405103a25001007200e9000012050008082e00c5100006e12503c50780090000f50859980f564440312403407000411018200382d0840c4100c410711000c2040351a903848960304035805262a5581d4401a003c40d03d140c03840e00c0000700011902030000409001400040074202d103007140e817090400f01c0c060040d003170303450130f08030001e06070861001040001d110700800c0d00707000d10100300c0150481c0e44000c84c0d40f00d50001d80c0114080b1340001782100741030b05601000e0080b00f080401c003c01d03a041204000359a17002d1808000d00803035840d005041c1da5900c1c4016140e0814045048968034038000c00c0041805c03144441c400c109124500d2001030081c050000d440542d100942014240a03090702c2e80c420408000c4d0014280d80f15400200c003100b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 611011223 1250 611009973 611009983
    0x3040503060c04080607020c0901030609030e03120c010f021207180308030a0b040b03011407080604060305010f15051f0f270303090f05090c2b0c020105060a0302061b030903 76
    0x120000e502c9480314500807446042290040c1031204541101c0d07071920590b6201070045042d203802200004442109150a4450b01c203140341d456410722518003800b1444c0f40c0c0390f005010120661000b8040c40030151010350903070182841a482020076000000c0380d1903c5645588408000b0380e8001c1041035494030f40c13140c194400d0365540240c1d901ca004582c107a040078011451088000d8008000301c200c1c1c0603c207a41e4500140141e000c0102c1003012800a685d13640080c80a190020000c104150030f42c0300c00b00042a01d07035044010038030341c0783c1d000806161000205a9641c9140d00d08170501011000890304581481d15070410b00080c50214606c0403012062004a60001c3d1190400c2030f00351304001d089040554045100070b02410401e0040d600c465040c5508416540c83c041d40303450003180080c1c8400c00c1011192402c07118901180c6501510303412100c080c0071550001c01480e2034000c1400141d4240d80806904140b040006425074100104001500c0c50110160b0f420a5490300000b8104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 611012473 1250 611011223 611011231
    0x50d03051308071a0301210c0801020d0207060b0a0506030a0207020d0f030c0212070b091c08210703020301030b0c090f060409021804020901020a2030010b090a0b030304050306 77
    0x99002d000180000102c2882c62441000c4c0055064250341c50070703d02c0c4240b5000040648040d64103024100d0401c99500c2900000d082601c00a5440360302040f0004029008508252030031400c0620000081c2483d21000082e01d00c050040c0b4515a40c41d01540c001c0e60080000700d800000d440300310740202c2e0300c2074400d4001a120b641c40b00191180d078010040d00500b01040c2200a41001204021351038440303048824284081d5071040701181c603441c503207a100010b40c1c0d0103403200780300250986c4000d0411905000d03007024040307180f1700381c2c45220040341203010074000100700e141e00b01e0204030b00f118444003400312214018603004240d402800420242d41283d4810021107401040350007980d010100003001c0280195400c5051095940000350b503030888420107881030b54030000300f441d480305110440801450140461548030b00040041720b61150060048000801d86825400d40ea10b06004c2d1400400e40140245d0030b41c1c8451003000020400c082d42640d1503c01000300044c0d0b03850611000e846 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 611013723 1250 611012473 611012489
    0xb1e1e0f091905090105100c060c2a2319060b100c050303060904381311040b0102030d09061a0109060f03020a090b13092004050d030513 60
    0x200e40707900080c00262001d41800c26401040680184030b0b5450307000c481411114119880080380314580720948868a001c1406041e442c144880344107059040020641c40c18406000b9408040c0302900220a40107046001043c01001b4040103100f6455041c3e003000051003403003074510f01c040c03110500041500100007150b01c01c0e11214884254a80700201c10b48000590030111701c5800c50741d44064172440000c040b1489003a180001c103040c41900d6450302000040b0040922070000c02c012300005c2035110030040c4481c030382c2150003c1c0306002040e5141194541c000618070070022000c017004042d2030003041c558118841800100200c1c40107000e881140c90140c4400600040d0003d040e2503000c2591041034140000c03030728200927560380009280b0341c601a5150058642c1c0d501c1400f114030320000d0b8401d000204000ca0309046125000d00c910301100e04d0340c44c04200a081d0b4110441e03549111141107458000180403c00031400d00d2256808035a1003490540e107040c3d02c48005812118041d001002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 611014973 1250 611013723 611013727
    0x30b061914090627030f0307053f160807060606080613020d060e0717010905060102120c0709060312030b150405040c1e180b1e1e0f 58
    0x44255005422030419a0700c4840720351804542502241841c403424650f1580040640540210709041c5100e003101c10100074103a8440030700701440c40e65203801001d0145c402c0c0c0035800003184101c1402c03510102c6050250150307064080540408149209030070070100f2610802c202d41600488102c680980d146c0c4103088294458010341040b1080345c440390030803400e101d5a0014802290340700d40500884400d03000016903910400801c460103400d140c5c1c802c4442c03000320400d000400303030021140c1c0041c000144c41e034020f90382d0b00c90f210b005964045d1142409600b01d01c0201d154600080d00400051500600703c504040e9180747c06821643c89070310a0380c001102c20300c0c40c00600c0d0715018010b00d008040b40d04008040d0308a040c0e000c2131245c1d1040d01d11455070b412194403031a020f01600604803030b00c0031a18424000c445005096175034081030072108000b1001c00441c10222120558924100c0e044103031030003003034200d0301400c164000041101d0f805044a00e808915032048000c180c8425031840c180c5e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 611016223 1250 611014973 611015017
    0x9030709050c0c01140408030615070f0b070807033b0703080a02070927030c021f0318050d110703060c050d0f140a0c050c0a0506010f05090c1801030b06 67
    0x81c01c40b111317600e8656460700018207220219513913005407500210b0803200b50498902900300034032148900c51008003044c00d000405000d000c5041c600d14800d110310f480e040c140340c1e990902102142d40c43d000c2031b0080410441040e521503886440f41002840c0c142c0c100b6200c2c0780a41015140958913071049591030400a41140b2040c1e05108a50050491007024007a60010038000e0441c03900300310000604406a4040c0410715107d01d940000b10340d00501140c2280d070002d80c030400303103103215003e40340800e01740020741d40034140c1425000c112580000c06440030382182d1808031010544c161132040548074801010001c01d2941c0702d401104590740d1030701980c03410b5041c501000c2d103c600301c800000906c0d14460741d41c43d10710003001d540d101c03078295000030f40500d00060030b4502c0e020b4141d0f900c0d42c030304c160035a20042004c0040e0781d030705131f4445140030031003c0d5490007007001410085489000410007841a881e4000300d0403501d10409005050100d060260440403c8440d00000103011800c90100382c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 611017473 1250 611016223 611016247
    0x3140c071205071d150f0415081c050f03060a030c0f18020f180102070906030c050f04050c16020a050607150614011d040603050a050d1701050a03030509030709050c 72
    0xb0000d080c000100000401072540d40005010010700c0b180b00c1701c00b00404400c0715580c02202c040a10002002007000d03001e0600c21020900740d50041c924a4410303100c0b08945040902c0000894101c960346003481c1c40310311440601f1640020300b1060300054940000300c0002c2c3c0c00d010440c09810009141d55280d80313402903024000c801140311050305841048402c0b030810504041b1007494480c94a51040c2e401c41c02c0040b0f14003032065006021440c0b50100c0801001141c03a1108200c460440d05070110340b04900400080b940c041c3d6044484000410640c074160b48103810001ea400d0000301003621030342c2e407800444c0c0307581d01c00f01c001c07228201a4407940c14401210311464029044140702d80d50004810800031340410000d25014510907008100e04a10340e903550007000c060b5034000305451b418041c5150455442c010b410f080000314007500d44100701c030320400303540504840004201800c500e00e1074400740e0b4980d20110816400d4042c155000c13070881c1d160b0164034016211406c401d50366503980044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 611018723 1250 611017473 611017483
    0x90f050304031b0f050a0603091401050a1410050919060305151602060906241302040602070b0f03040605060622050f0409111005040f0b09090a0b03070303140c071205 73
    0xa0050303140304d5505103d5900c40d640f40b00180c40b4182000038886503d42006c00301c0c0c2c807181141c0341c5550b08020402600400f0742d0001e80303e80b00c400c540070001c3d440d040c00c402044d080b50f000340c45c7c003c450040024a01201c0340c15001c40c2c001441d000144140d20f0b030315514200392182115076070f60b4500d182480040c0141b6080204100d000340f0152240d0700341203000341e84400d80030300030a40940007049852074110902c4440403d500c0028910710f200303014000d14801030340040c0b0880000d400b405a0025080c03170342d00111800e909440c54031616594507907030345600038100071b032040d9004481880400c00d0402c810400300000120900c0c02d02109282c0b0342002482425500c4082c011070418814200003814410714030544031045442050300111102d04503018040c5601c0192000104140002c0801c0d00074001c210102e41681c00c1c1a0a6640262640982d0002d40d05141c160340081001c00200e81b140c401c5113010a100b0410b24a0003040c240810329000d01500848860b0030344028003410401c003040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 611019973 1250 611018723 611018729
    0x9060c0102071151220b0304150f06030f0b0a0507020d0c0b0601020c0d0b070216030209060d0618050601090f0e150403171314011e090f050304031b 65
    0xe581c4403c0b40301c000c50340b03c12959540c0b240320482d4100300300703044542110031507051a0201403e0b8844400d00c1e20000043c5c13101030804e00403210030b140800e0859240302241d104603002208140e4000e408a0305400400c200741019050035911503020001030715844e401a03040d4003070b04480d81141002e0551000721480075103030f201550700500d01c030100b494010400e480c1c0d09812808810341070781c2d1000140e0a202c208003a01d03921a505130b610070104a07036034034402e0003068140c2c03c9902d00d140780746000218421902010307501202c0c0c000011241c0c03a180d071040080f140320fa000480da6640084413010b5101900004950a0f0422001800b403038451384101140d038415079400f801800c020780320343d5880b015480b91006601d0b4003030f0300081c2410701991072000c1d017950341d0303a4139000303450b100c91a940400100c610807900310403000c80f6800070000501401c4802d60710782d2100d01da94984d030300c072560007014406402c980d0b410201100101050003800901f0003940600c0c0071030555248000750498111441d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 611021223 1250 611019973 611020009
    0xa0506031e0603010f0207054801120213081504021503040501090206070c032303032701090609140303070e0904020409120f030f0b0f040209060c01020711 68
    0x300401404030404000c4007480d5820825441c09030b203070440801e015040440c001340b6502d0000410b181045800100c5491030b1070004141c0c2d40b1030790b100b1691024815203545100702803401042e200070100e40d011380c6001102050514101034214948017009a800415103e41e0028110380c0c1000b5201d4240700d505000503500c00405000d181550000d035580b0300400041c15030280c0403000a0400c0790950141f01c43c50b030002d1503151500000e24080e000403001e4001241d41000300110146140034001e69408400c0d0144050750450741e40c1c03920300904141e032000b0740c0320220f0300c4180d1a01c007030020321030340041070300610010801502905003825415814500d081c071540c401c00c1007003212030f40b0a0b1201c54174807007242d1910343c90721103000103406024412009031040c0041c90220030100c3e0040098040300c070719600d05000340302082582c40215045000400e401803041200c0b00c0311440c0641c020444004000d001c01d0920006c03081090883c0c012010440d0f803034080f442c500c0145d290850606204007220 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 611022473 1250 611021223 611021227
    0xf0f060916150c021305090d110a020901230402040815010501050703050a0c170307030f050705090307050d0503190203180a0b180f0315100501080603031605031312020a0506 76
    0x602d0142e100c0a611001c04104810143d200046560308010840041c1c0c1492080c441c0d400c0c61961551580002040807002c9845064900b0201c01c010811000c0743c0d8008100000e580e103409003142c04c0b41c0301d04280d80c00070b103000150458140c2d0b8a10290003d040e2400041c503041c41c6810410223508410307000f1a05008040c85400b00080c2d02c83d089402003500703494121400411407600304004540b014044e601210080b0800c04220b506a1001c0e980d80c17144101404103032180603007510903100b42244c1c6070b016007040c00c0601640c100084400e04941c8a14102d0340350244042800014054554240f40141c00c00140300310800f0041c004010b01c180c04803001d444540c03500c03440c248540300e078042c90743c5486840c021000320341d681c0401c1d8000c1d260303000c0c0948052302904d00103032800d09404c4880d2131450f032071100c01065652203904124480c0c0c101400551a00d02511b00340c204000d27502030101e900f48001c10400350500388100c039010007481c0c0103220b48420042ca104000c4c038215140c01281c080c4100f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 611023723 1250 611022473 611022479
    0xc0a0806010312020a0c030f020102250347160e100e04020429090603041b03061a12011401090c05092e0504030b0a0e0f0f060916 57
    0x4121a81140c3d4040320408490625500582c10029104070242c00307050840c0c0c0000520091204070300d0058401d0f030a803002142600c1d20540541c0d40c206043c540800c1e400010f10000303100038009c116154150751000140c5581e5030040d40900c0d058003460001102c80b505503506030308040c0c0541e4209144900700c503204144001c00400c0c140300c000b0754a11400300e6a41004820f80284896000340d03070040c00039951503464500110841d5030340c0d807100c1038250581009008400344042a42ca420100030401495030300c450700c803420210078021500d5600b1915100000c000780c84c9108003c1c0f1441040160800c5400140800259881c0d407202e4501030b0b41000210b502440c041c001c0c07141900c07034201001645180c0c071001250540211400550010518898543c0d2882d03581c0070380803810f451800d849c4591000309803c4900d400783d03100040403401c62002150220913250000104801c1c0c48045482d280b13940d220a0307140c00402060700c05942c00010070b000c201c41050000b030b04011080d41c045880685 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 611024973 1250 611023723 611023739
    0x50f1b01050d0b0d0b041112010b0a05010c0221060124020d1224030203120f040905041103010f09020306160203031b040e0103140c0103060e0a0e120a020c030c0a 71
    0x401c88807141d40c10383c0e59521198990740d0721034662120a8110484041900d02440e007200143c10550a0b544104010800440d00000500030801c03c150017800c000d44803443d1000540f00d03d082624101c0e48400030903001106541d4074881040ca541c00580146101e5142041e8107400c0050074140d0100c44080250050156030001400382c0c072418a840c041d9a241100c0b0b442d20000d250040c003122444424005e800d003112016a0400203881c001c406a0741c0000740050710000a11501b2085000a8001e010030807079142c45500080e0f01c035020305166800100140700090844030704442486116a85140345015810100310f106e6000c0005001c01001c1e29000d0030296403400001c0644c81810301000c400d040501e45101540d0044c050b0050042c49540c4a00e08040c000010768a0002940703c0e881c803c3e00e1543c424000d040c100c13489842c031441c0ba52030b2648458003801500d001d04080d4403a9808101c216422100103040321040e507800f03412040b498904250030054200030f403e1140c10032003008c1c00451 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 611026223 1250 611024973 611024977
    0x30c070f090516230a0905030d030204061b02040f1b08100f05330d0c020c130b01020f19051902060306010c0303060b0714150126030412050f1b0105 65
    0x9403c5040004441c100f00e80940688000c10003580031302c4101084840d40c660304400f041060381d404400f5103840b03511a400803130483c000c0d0300c105000a04503404c4060801e161251003180107001420100d00c0042c07107910704040d00c880d6904000640c15580c16150700740e0303210581c03d0f04103001c000482c1c6031502d003c0012050381c910f030180610a50f44846030031900e1400741960076810180b0003e26101c0000d0515101e000d030040625800224100719028403014400701e03444221140003001666002d10f98038a60008003031f00300e40c05043d8031840c1503081c01058200a04a0421103441d020f5512407034030319000d400c0005459800e000c10b8007001c00746c1c0041e5915000e80e503201c1420329100b01c0c0502c55042c00c40c042c2c0560b502c016005c0f90300241d50018070443d00152000c00300428210754403c40300034200030044034244a420b108003490441482240c0429014200000c4030204582c20151104062603000c901800304075050780c800a040c0750401814400300c200d01065190041070030134805d00191542c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 611027473 1250 611026223 611026261
    0xc06030f06060203041e0906030501050106081005031209041d01021b06090a171204030e1804020f01030f0b0316050103050705041a091804060b030c06071a07030608030c070f0905 78
    0x34103040e0506c0100d90600590b840003030001000074002a80d8a00345180204000c2c026000003902150015508280c0c40c03542204446014000300384147e1304000844142d0040215642d2094840300c04c1401c00700c04503801d90800142d040016990b440c07a020030401500c048a05190302d0300040c1c201b10044801250840b80e064101e15400025071a403150075111b407080100360741c0b03d10040820b010602d90b004c004c031303c804103055070b0001c040003104200c0c5040c180100d400940c042082d040c140b009503c0b94024112100e0003441c049020300d04500080d0920306c8650b803101e02c00030b4410003042990ba040c06180d8001086091003450a4103024122419003e60b10b01038554120010740402c2c25240c0101810a02d4008411031a860810303142c14405405100d154900c00d1094505107103a500d08001102c00065005441f85100558003070300c5c2c1c500b410000c1c4560241aa01c0200241d038031414030040204c1e00c900e070060010281481c0d11441924103035044104594035150810588503000380b203000359 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 611028723 1250 611027473 611027489
    0x1290a2103020a0b1905060f0d110a0f180c1404171507030203040203010605121506190e09060c042607050a14030c030a030e010c05190c06030f0606020304 68
    0x4048a9003000c1e441c1c5103c440380104800c01d540d0800444031440c04c55010302010507102400b140d20b03103201708800710124010310b039400300c4441c1000002500c458000d90a698028001c0c10040b40d0342c1081d1000800d00d85e000281c8807040845441094080e4841c0300b0180d00c00341440000c0f150b40c811085014000d9008455441402e45000b10f006042002544044c0200b034460544524048000a010b0b40040d1801c138080d41c00d001011a0b0b03403030506075246003611408001c02004181c10025112010050000e0b0740002460080042c040c1600d00441c1c00351200c03010313426450814140851800c1d400901d01220100184818003a44e00b24181c4141c81c144400310940c1c1d2510086240c80c00d00005074012a0304c0070140030002055170840380403456022041301600c8030003000c1400d040d12034404480c001d00081c2c0b124181041580180002d024a90040003103504442040b02c40c0d0f03150005e440c1c01a10010f403000c03030401ca0303281e06005200140c1c0795034506000080c50980701941d0b9014a00403981 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 611029973 1250 611028723 611028779
    0x3062c0105010819151514030105010b0d24060c02091503030d0914061f0602070e0408070804150306091119120b04021201080d08040c05010503060d0501290a 69
    0x184464540032a012140c1c1900c100141c2001c504a14071b00d030040d1242d0707c01c0403240c0c4100324480c0b0701845254100c03902202075030f02d0090110180030090107021014480881040d184030b10842a59514070b0283c00f0a4440104012140c01045600400200113a01c16888090391107030f9a140401a00e041140b030b03040c04140c2420303a00d4000c3c0c42055100b0f039901d681c4190000c101e0098650056092600100840c0844142d19800103d81f2000c0c1802201d43e9000401c0100340059000c0000308a458050750a01d0f00302611545403019001c9500780190000e9200e0400303109004552068080303121a14901d14502451400e0204543c0c41340000b43c01400340e034807000c2c01101e81701d4000700080e00004008650b00c00b01c0740305500c03030a4000e001e072140070b00c0350071480003595024100090142e80c00410800f486860b10780111090b6000521040c0c00c850780e101281e00140090103014002488000f085005560712800f030400c1e449022141131090070400020008441d2240301081c01e4415040c1c501e03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 611031223 1250 611029973 611030023
    0x3041707080a0c1a10152a020d17030402040c0509091501180902040e0a0e03120402030109060f020306041103070c20030a03050307080115050a080a0603062c01050108 73
    0x4002d0800e150841a42d003001000b045164416280b2000584414030b0081c41e448500000c12690002d40d5587d00010800440e208185c42c80603002220b0014802040403030340c1d0410b540d4015801503140307206146c26a01006100840c58540207004000c1440d01e412428422400d0000b203071000040e10a40b903441110b0200041a48181e062a0001254080000b889940c0301000c1d4025402441b40340814195180030403500f5035640901100303400100021400d020400e01c00d00c03e240c4016100301c1c0e0544d40c03404102c00060b058040c1110b8000c0900005031680340540c14001500c002e03503080d5400701810420062429046100e45045541005000c1120048001002c240710524040d0b140d05200c3c0240200070141e02c24011441903c0729901c035030341d40c0da03904100040201494904408240207200450016200d03402055110710300b584041682076480c2c44a03000c03600114603184a00c000b0698100c80d4800c401200d40d05142148002c000a61401920384e480d00b00f080003001c0c12000010382e030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 611032473 1250 611031223 611031233
    0x90a090b0a0f080d0e120303041202011b0e010e0d021f020a0614040c2705070e0d030f0f0806030c1512010603150504050f0f0c0708070803041707080a0c 67
    0x4500600a03000c4006440368540c20711544e50b120141c01100040d000d040304681034104070911080340c1041500440c10b680703d941d54541010303210b480d603004641d600c0303502c299400740501040748460740c44e840d038111106500c1c000505030080261b942d40108400d00041d00141c50301a00e04a40000f140e4059400c4040d40b08103c0c00c1440441000e40300c1410070580c0103002c0190480140501c0c03180e600207841d907950300d1000f152391076800e0b002268036407809207a080c10300c0c8a0300800c0e4001010b180c98032041642c0000a00f011586501c10380001714411680e0f185a0380040c07560b00c0041807410034042c0c3d46044000260703a2000c505425000d0302003600181a011450b030156141c40c0b941c628010705660311903000030300070f040c10008081c41422200000840d0f0801c0c0c03113828081c50080720b500002e81d98481f05844800c50151240300303800401c104000109072100050a00300c1e1140850a40c2c1c0d0400d8280340e000e414140344083c0154030304002c2000080c20500844041c503071207003402c00d4200128100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 611033723 1250 611032473 611032489
    0x18071502070810051806010b031504110a020d022a0d080403140c210a140c0409150501051507030f0905060301180507050a021b0406030812010f0803090a090b 69
    0x180b600303403003424101075aa03520781d0012403091414690b045199026000c0c0c03281d13100ca0a220710355400c035042021034010518005503a130840b0700a800030901012900143e06180e114415000043e0440c40c01082007581c1407015000136411104407258881d0704000030754101c0840722005103d86c560141c030b0700812800005450041d5042109590b500e05c100c0c2d980380c0c48210a40c0ca8a125100e421107440e04a44554803540510000000400c00300320107584440020f422070100116034030461203c00c40d5135480f8003c110304070f0700ca150290300c01241020500c0c1078940c1a0801d0f40f09600c1c4640b61030104213100141d45006825182c0008000850502541d901090ba0040c0f504040c0010001c100e1b4401d91112127810120610100102d0780c5005084a082c0556010100140c110f01b04030488031ba0300c1050b5101d28800144005010b80d40d27541e40181c81c1d401003003e90074406400c80100500366802e00c109004081c02c2c0081c610700080b89d00040d03000111401140e407002d6440340500d43d00c0e00d0f40c2c26 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 611034973 1250 611033723 611033729
    0xf090601320703020a060606021204030602070507081b0405090a03020607050d06050414070f1719020d0207060603050f0106030c05060d1409011e0b091512010c0f081807150207 77
    0x58165030300050300f4002d440c0e4030002c00076180c10b81800c0d030000c1e900c2d200240d41c19040744050003d81c10036055945102c060360101000341e07070a110b480404918001d040c03100c00d159458003509001141c07003a40070320042c1c0700020103241c503a402090342c42020a4003c1142236004025190150755282e071103130706d0002012950042a0400d01d012050005d078085400e916000340c1550711144000003240c00100e804021000404412030000c00201da0b04201e041341c0100c400b420b80d0b0015080c48503114046040b0b80184105840c001d03101c1d1020010301205100e020001d006c00f030024088681992950803034900548152030140c800011190100c40e96a400ba6022006201000310182060182c0a000c5c00803851042071085090040144928043c8100444401c0240c915070180c1d446402240342d80d95442c2c49641c000b03c2c0d081016044400a20998a041105440792440400001e00c001c00c508802810221241c01ca026040f006400016054017115842192041910b5034160120300b04262a4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 611036223 1250 611034973 611035067
    0x915080714030408040906090203250c061107020901050102030a1e110307030f0806040207030219020a0302100302040e1302011d120d0206061219030507050c09010b090f090601 77
    0x8403d000c00c200c1064001c04c102c503420101480059228402c10301240b200352591034002030507803e480c03007241c02c0103038a20601c00c0c5810145c1120003941c48842c1074905030000c46429181c0000e0070000c51600e022018090300e800e100650614000d2007000d003504c44620420106403040c8103003554500d100c0c4030848165020748d410380c4c5d05c1d00181d03e4080c2c0a03c0c00381d046140400c40810010b00d01b4246842559081a0564000c084100e0965605100c10404040607604001034220102c05621514071741000640c0c150340060751140b40c00f90586a00718041c4c00d08001c80e006440400160303a01218484582c0f506c164003d0740c0500140008189002d80003000e00b4034001c0c000c8403e0842e4022070014800d090a4888225441c0712019445c0c07034010203c0085c410100356907a54010920900240600602c5002110490011080018462802640306084606001810700c45505140050001c0c81e102950422980c0c02e114001a203245101c52150326854004c01e004004040104030400c81c0260503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 611037473 1250 611036223 611036227
    0x9020d06020c030c1b061b070f0b070507061805060306010e1e03160312050a0e06070b0103020f040b091302040f110a08100b0307030c02100f0e0d0915080714 69
    0xc074105075100c0d0800016100c3c0f601070800c2451a03020490b14448022400602c00c1d458506118022540c6542e4a9a406040d100303400010440e22440c0340c0c4074014095030040152560823300e0654a041020740100c0c4c1008608010340703030000d403012420426a1000c07904140c6079540c01c00100c403010740a5405030303030181581d460405c2407040141c44030803120b000c1c0d00b0760f0303229800f102c003540350715000c0d100040c0441d008000c60300c001ca00c40d5020340080031443c60040c42c0712440c00d0004505400c009420745900341150010411407038075944c00949aa0180e90500034a9446000500c4c5003038010a084800008001d10004561301c1d584982d40010000f80d08004404440d44508003541000c415140032500a0707003c900c00c01420003054040707406e482145851603441c59002c402030300c90075641c0d10030361081d507202c25050041d0b401a00c92588444100007048000d90b0011407400d0021003001e401d0103001102480074804001445004a40600f0045441d440b041400c5500c03d0422002c608900c0300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 611038723 1250 611037473 611037487
    0x1602090408030a0b03011b0810090e010f0e011e0c050706060b0307111506010c08040e09160506070503030609180d0305040c09060e0417091c021e1309020d0602 70
    0x7070745020b18000c040d050341c1085250783c448141422102d280b00c4a0381d4450115101c0426540302d810560b074004494600c120072260f072959003009403080343e08021a265101c2503107102280551003034550740c4440300024460305002002d00c415200f840125414820384a48540201e20302a00403180b40e60762044082000030380e506490111900251490300008811440a881114000030b00b02c03001110307485802102d440f44401540c2070214501e044811020602c400514052802c07600c1d4464942100030301000c01101d4482c056415094000a104020603c031a5010039070010503a580003005503641220350300d5040300c2880d0302100500c41041445450b02e134400550f0705400c2a4022489136414014140c2c442e20000141c814a00564030188000000540460300c9900340102c84c800320207200d0b01c1d060340000840e4a04110003240c2c1c1c50191125002c10460070100030700094050212030081b16036402c0c200242e00100c402c00d5919460f034407005290295035138007502102c0da5601036400c542d5040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 611039973 1250 611038723 611038733
    0x52202040f08100c0302040b0d0903021009120f02030c0c15070b01030c060801050f06031f030b1303020f19020105250b0411010305160309030e060a05190906090303030216020904 78
    0x4040d000001100c2d0501080c150001c0c040c1c0207442c1034a00000c002c609000c00e43e40027400914412406408601c1380744001e040c3d1880c94420791005600039800310b004500c020001520448008045008562082054042d1000701059840e250a400c540303100c00030556507030103500c500800c4070140400c00d100d0700000811940072110002c03140c942d11100c019a03600d03030402070034418032118107410150800014100001403804504a803004207a0b0000f05512030320b803203031090742c21074a0a0521103126040d1050507010442c2c0307146545504000d10620202d60300320031070030b8070b2981c000b41803240124848a5205541d482126070341d043d0440c0c9070a04070142401c040740b00e03040c0c40030f40b0281040114500d40354400e016007446102046290b000440c0c100408600800e4072010550412421903200d000d140e817210000d2014444560b110b1351a4010001c8810b80c10507000c0e2180e05103d030f0b0580410140307400115010440c0e40609005882d51803c1c031000b2001c5645140c020b511904a004120800c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 611041223 1250 611039973 611039983
    0x71e140d2a2916080601051c0c020f0f0307020d0b06030f030309011e05040c05090606070b0f090106080f1005180d0c03030606030b0f0d030e0303030906061009052202040f08 76
    0x90001058810341d2038043d8102c41d00c844084503680003562140000380c1950203400200441e40b169002d07010242160540001101d46003040800160090a02c40071141020085070441240c1d001c081c502d009800d9000a0764200d050400034142ca40900c00641596814000408000c42c2c44050741d40d6842c00c034010074000c010402c2c000c14580e08507034860110502c02e114051041c3e921080440c6160b0801e0100a513040d0020726240e0700100c1001000004ac4001c46803074081d180c000f0b112106070801d001d202d0f080d91102d400c41c3c0c2ca03e5001c0e83d103444507418002640e04600c0801e080004242e03e400c00490440701d40014000c000b8442d2003a0b0304030a950101d2300750391041c0a50703010012551100d00c228207a0307401160083c0d002103042c203007204a140c010401c85032203110b800c1c0441e0102000d40840d0850300210390028003900000200909800c00c03110210418906180a04159040100190ba584e04000c500340d48402d015010b01d4014650b58119170150540001c4944410380d1030450342c1d80c0f4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 611042473 1250 611041223 611041283
    0x140d0902010e030d02060f0705190e0f03010c02030909010801050705030703020c0304032004060611031e070507030c0915030201050a0305040620040812090d0b0c071e140d2a 76
    0x102d100328006500c48e4030031819511051900c0c1100407400205ca40d048420700c1060000c1707580450340c0400d04905540034400c820030060150023030750320f17145440f0070011102c405038040442c507410001005081a070140840c2d034415841d04005888000200c10f075403450283d5000101903a0b03488014810b1651810781c00f54a005c4d080703905000030794990104503860303841d080d42c8078465070050042e4100074001810100200200300d0072507040c680030740c80361890f01001c0c0c0e00a07594818903042c2408043c2c4140146450000c9600d002d0304d0051030755000800323a201c1c0030103403001c050791500460b040240c0d6410000212000c002d036400300c1c80c140200000c09900602c10030403503115040c12405400200340c1515500f0100070043e1101050f40c3c1c80707480c485000105881280715040004c440026104000d122020911040301178110049141440581c05152032420341e940c00035a64196550f408607510250150120080303030481045181e06059000950000f00740040542da1645680c040300581c803d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 611043723 1250 611042473 611042491
    0x409061409090a211e05042301020a0308060303190305070207050a0e0a020f0f070c03020108010b1e0a21090302150714090a0902120403030c140d0902010e030d0206 72
    0x840d02c9094826684281811004010000140030300201ca070700408005081c3c03200d81081504054281241100c140e00440080c000c5034011500340300c020159204580308104044c0d41d5100c1c0d00c6138070000307540c956544000804203c00d010008000e51800d00136660221201a240400d00d242040050090b06003140e01000501c142a40080c1c14549601001c1c11034030395800146c0561503119140000e50301280c076244100404014120b804a041402085610f02500320855414210310004114000603405001c07241c406001a588441d01b02450090040140000d00d41c0c6500303412050ba00d0980382102c82100a82460100c00b40000390b42010b00c0040c400d9003030714160380701c0c0b00c40d10008000c2a074100c0d0026041d110200814540c090040c4800200140600079840e5144039030421b03640401c03501c07200151850140400c05405000d454402c100c10b040144448142c0c0703807010b0043c00703a2a0900302e00c5445510007015a4020224a281c00d05c000d0195000c42d10032040c007964581050703803c0c40c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 611044973 1250 611043723 611043739
    0x1e0507150e060906041806210804051306081f15141003060f0e0a060b190c05150c070c050102010e100f061d0103050d030504120f1101151403070b03060603070504090614 74
    0x6861314112350113440310342c007141c0c00d8141801d240c103006068002c1060303400300c50380e81c0ce0040b4100c01d01300413040c40c501d14052011f011080354120304042d106420071540300101d40d82c000b800b24003440c4000038003244045d00c511446500c800b0041340542a10b40c00002020b00048002c21594400e15035075126080641d014408a80d40340c0a100c01c5200e51207043d00d480601c102d0403512039200c2ca000315402d5002e503085541c003142c112601480132409407031004603a40e0025910702040601c81341c00d00248000d000070000410104139241e11040031509c0581410703079518040c0c40004059100c076014007200001a003090100e0004c00001840a01003915a48200b4254000880c07080c0109845240c1c801c02527207508800325030544092410031290070034489210310f2102081f000f40720b000c802c0ca514134000c940301482d124140c01d14824134444070f80203400001060101012550440390000e02c04c0d98119980c0d554600200c443d030140345c00850300c0030304040c4001400d98581100700400142202d00794 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 611046223 1250 611044973 611045009
    0x41418010f1a030c1903150b03100b1906201005010311090a0501031511070f050c010e010203031006140418090b0a09120503131e0507150e060906041806 67
    0x1180c0d1244080c821003094490351400d000040940720003409647d201000840d2185031500040d08244180e1145540c403581c81d0b613200314602d06002407207120004910404486418a80c0c0189681110907200200d10005503100c086078800b00414282e261310102e00304515610b80c5004d20240c0d0310141c21602c504a4040410150303112485424122a4045d4042c1500301203819080040c0010310400c00c1d0800e02031001310081307038000146c0c2000c0347c45080a01111078100300050000c2450581150440d4014420032450014440c80c04003070724028203102102da410790400f080c21f0704c515004624601c4103030b400d42e030122209e40c01c003c1d0803074441d10701001d540e9643c01d09030301102e03155080a0141e484481402d00654002c8005542002c10610940c601505035140d074100c00301c101201080c040c0c981542081800428800f0001034103d04134100b200b6044003100500741c48456000328130510001503c008180d03a1030003140c004000c10f03d500007030308a900c06c00e1002002710303110703034101440c66900300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 611047473 1250 611046223 611046229
    0xf0604061a070318080a060f060f03020d0809120d030504110409031205070927050a020f0318031605010b100504150c060b09010e0411041418010f1a030c 67
    0x12903400c62500784264100350168070110361340782000b80c0c548034103040c2a0f0302044500e01485000c402e00c0c0500300c0403c007124030818500031030740c0c0f6030301520400a841d038040c4016078400c03030f074915283d4211034455180c0c81a80000380c0c4440d90b03203050f149513100c0c05521824054040e00500e2146009004110740c00c0031200911094411440c40200002d40c4c01034480800c040c20303030040d50030158600d0701c0c0030f803030f40c40d0440001c0d03040c1800c3c4e0445402c0140a100401e00e181d900800d90702c412110020343c20030350040da0f104500d0102900507000802c810860314400c04040041d28484c50b42c008140905a0742820003600070808411418062074000a03140d12950182e412582103d4050310784440240c80075004481d04118880111003403a00c507044210582c1d5032030b40031703401303404804074060442c00c082ca080c14510108a24076806603040030600d10700e11800c102c005500400c07103000d14031a588000c81c128014803041e10240006450840d06aa0340c641e944d5501075014026011902501c0c1e102c010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 611048723 1250 611047473 611047499
    0x1b04060b16060b0a18150e09160f03080702060705030702102609100e0a05031801020607030902090106050c010f06082103010b09100507050a060f060e0f0a0c0c0b0f060406 75
    0x25511118403c40e030700c4c41d800d0003140e1206c40100303a242040d811183c1c45040382403038002d00380e40f0700000d43e210b07403013184054001d02d41041c010031041407813004103891599101028058280003030b08c03d000100e003030310511a042c4106c8010700e078000c084c0880c02c80c0c20341d8080c08050340c40007102d4a0036141511045180080380d13a07a03006d00c2c6540000c265240c124010300c0d0140000880e02c0450b4002c1d5200c80740018030400107000c0940041e00e5116010580000081ca070a00c018014000c25082078110400350f29070320042415508940303041965000f04c1158140902142c02040003c0c070320f0300500191344600071500502e44900302c1602c8842c001000342c149000d020030b00440304841c0007001242c1e4240707400305400030040002c0c2081400e290386501c90b43d017441900b01c0283d42030703902d402c00340518000d07610400c2c01506428511500030306000600c500308040c002c1102e1a4541c2c6c41b040004a20300400c400900d5541c1f082081c0c0191070f2591220055913002e031000d900a80c2410004541c52908080b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 611049973 1250 611048723 611048729
    0x190f1e03082701210e12070807060509030a050706050406140a060501030b03030705100902010e120c1c08030406200426061b0901050d1a0f0a081b04060b16060b0a 71
    0x6500d2045020001140106442003c0185c0382c8185441858140f0441e00642046801000d45c00c0c3c980600d4103124060b0b8800038108503aa400401c54602a140c106040c0d03075105030424030008841d43c40b031409000524551542c03a404000d50300070840d880c03640d6004001540d13000c0e40c062280c80401400e1590380d0181010007010380c5c2000e2100420b404c0c05510518034903005242c0390408070140c0001c1018034881440c1d85c00756400120361914039040180500d05100d01c6003c20708441c50150f21244000e003c094401400f2545507840104502c1445441880168140c03a20a0f80ca0759280ca58955980000901c030100740c44060b4000d84100340426264464410350040300340c1c44000b599070120b00d92209941c107061210034052900043c0083c807035510003011590700b01c6842c00502d01004803050500001610a54401c10248440600450b900c160940947d210075045821040043c01a10300d513000b64070703154404900581400c4207070540125044c0590b00030000d4038005024402ea10322640 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 611051223 1250 611049973 611050007
    0x1502010b19090f1407050304031b0213021b0304080a17030906011a25050f0d09060e04021612080901050f01030b040f0209010b0405190f1e03082701 65
    0x12040040d6111030700030283c01c0a68110029040d03000c1540a44603c80603070701000010004010402015080075968169490b0319008421081c940d40c0007d103e80004074020f039883d0380101d0310104a42290803c0e008080c0380a0980340c80e141c41d195095650344000c01c0542da05580703102405400c10a440440307014002c10005064641e082034001c080044405880740c1c0d8001c81000300d0b108800404000440f8441c0c1541c130905d0035001403c3c00c40c545814920a220a500310703244081030070344c1200c00b0400712122420607506a03240385e0700280003070280b03ca001d041c0100c5041c1c0401000740704000b1607207962a54a85407155240c8459080c00c070340c0100e861049e0031034124014000710784640d070b006603c144250241021039000b5804030b48400d80a900408101901282c00e010a00c0c01101201c200c132181d41c41405c400346085000580034000d0f1044104201c00610100c1600201d41c140304059500202c0082c3d0394103150b648840700d520700c11a105096841468000710365841075040305007581d031300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 611052473 1250 611051223 611051269
    0x12040315020715090f02010905030c01080105010e030f0a060b011b12030b1203070c15030b030a0803040206040308130807060503071d220203150301050105060f03040c0509011502010b 80
    0x12160000294050501640c000004401030703581c02d20f00303000e90050036102d030f48440c1c1d000c102480050851446900b18030310a1b01f11780840245a43d000c080d40381128400d04e8078480c031010110104c0d0601c0c11204d000041401040501000e01540790462045402d081c2d0f21000d4000780e107558140c0701a00110700920010489412500036032080d00000c1c83c01f20300400b07990032100212812440e40d4000c1404403040090381008110942428074120b81100c110b0030140312501c1d0400001e5103070104410b00420081000c004034003591626016100074560090040fa554005030300d0640c0490a503110b054464070800358045010b51080d03040d28001d036a10344a09115544c40e80000c5030301242c031000741c6d0708021070b41c007510344551201d0701141440c100d100b030040c0c0d42e003812640d01011101c229001c41c040d030306010040040b034403994225814003494804282c4c8070b480303520381501d0420341c0c0c4e0701640d070003c5901700105800205d80b10446644030550020807410455600340300d030086001401210305401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 611053723 1250 611052473 611052503
    0x60f050f0f0906070b0402131b051b031b0d020d12020c0c04360507030206030403170f0f1609061805130b0315040b0c070f02090a0509120403 62
    0x490081c084580d81e0408081c100503120011440e160041102940c80c00700007002d100550405210802103001403080911a8100c1c07002443c2d18a04c40040c1e01041090008400e0204404403440000403030401d03041e00e0742e581003003a05a0b07a03e00b182c0d91f800ca03540610700407400301c2800082c031010440c5a54589403180c42d2414215002034021001c1c00e00c0a0003500d00c544459a128804c050f0034031a0785140144981c0060450100c0c0c10744c1e0506000c2d080314200401004c5200000c80c00126507045803602c0c0d40727036142d2608484090510175044402c0003001309010300b45401b40714061045c08111841941035a941650183c01c3c5a00030160012a004210034441e4a101780407102090250542e9207410782d6035a0003141940c1c3e4030404528034144d59002c03010131460188202141e00c040100040000e00b0075031036210303128101038951101c6400010380c640401030f04100300c107640c80c0c000301040b483d8608280c2000241408603038403066400f800b68942146001c0a00340d40682c0c1d00445440c0552034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 611054973 1250 611053723 611053747
    0x5040c150c11010507060603050d180f050603040c09020c15090c090c03070512010e0a06060216050d150f0e0706090305330c0702040515130504060b1003060f060f05 72
    0x302e5100440e04100c003c0112001085242c056400110700c1a0020810700015560040400c0d00d07015034600d0303140001608204158400d507240040e46c0301221082d94a8072945445804030046034040c10b000c070b0000c50751072135109000c5540703121030a503201a81c2c1d00c3d94903260000d4036190307820010f030f03800300e0800040380c1030840d50800b5603440340e001c0c207101e403404e000e001458032008400d910a045c1540030f0810016070f00024000c0c40c0040c03010f80010202c802401c5000c1c5442240c40c020103010703a60240b801800c2c0f0501103051200e14134401c1d010092041000c85000c080c010414940166128955000808500c00c003407802c2160707003050180c03e00c0100c004c00c80140481d0403280d1180341c1c3c2c10a0841007144070b580c66860141031901170103661110b0520520083c3d550084c8500100307070842024003520f460f8000c0e5580301c4a00b0a81c00213a903030319442c01e6001000d1980085801404c0e101a100f51a50144d1000081d6148a284181c030b503a41c0307240403298403034400402c000050040c443d0983e100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 611056223 1250 611054973 611054993
    0xe04110f0315010e120714040c05120c190203030f101202040f061d010e010e0105010c02010f020f0111180901030819140d020301090e120a0e0f09010905040c150c 71
    0x464149008410307080d0600004ea8917540d2510f000e001500300f44801c10403048115039480500c2e078191024007a03213001c00b0029119014808441c00a944144009030100c904002201e149500c1600c03880100380310f4800003552900202c07a4000c00c60a11008951044018682e9004544802076066211042a400d100180c02003444c5510300c66142c030400700da44c80c2c00342041102011100380d054802d40c5042404840b424060b800404203a284400501003640d200b40c00c0340307030f243c1c081c2004040c20036034400403450300c20b10400480c115464221620b140c80d0b00c0000516110708800c40101000e0810b50801c4a014002e200051042608008032040c056010010b112078001078240786040214084841d071300d980c0020855240154000018401c0c014184900071a03082e41e080244121450300645100c0f07031051814050601074880300e0109240d80b0035140e07403a00d140c0a40310791855603441940fa4082e00b001d50f0100c41295040c0b00101380d0f8800c44049459010880c0c1ea0520862559215a410340c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 611057473 1250 611056223 611056261
    0x2505100c15110f0301171506011709150702010c0f0201021213020316061809090c1a0405041a01020609060708010b090103020c0a0308180a0b04110301060f060e04110f03 74
    0x441024010001c3c08044400950300a0a02080ca503800f02070340301040d0308000c00160f11a0b10344039500c09000407640c0c0310084d032080b560480054412910b4103000a483d110b001c00950612450304c40c00c000071a9419002000c007100d0079140c1d000c0b02e4450280c140c0c203034050311590000075124100010f481440f07802c40c030381e1f0050014040d03400c481a48014902c4481d152740019002c64840002d0802c24007000c2000c20081060b440d04001c0002d00f0b95410f041d00c071051044001600f441512241c000ca090000c40d030007085c008104001c1c440c8000003d8a07000410b6940d50302501415001460b000408146103105107460380e1220480d81c2041e500d500c01d0381101c1445410140c0c00d02151201c5207080000500090098503445040d00e4442c044401c45c6081910500c5550000c25010001804000da0260883e03403050882c0104100c0b000441d00512055001c2170381d060790800000b40e200d030040000040e025041c1d905000300c24000e54a81000c0c414104002c4105104000185401550242c1e045074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 611058723 1250 611057473 611057501
    0xb0108010803041d130f080304020112020408150601120c080901060801060e070c0501060e070e0a06030221040f0c030804090b0102030f040302100c0b0a0c0e031606112505100c15 78
    0x81454030344030310000d441188021104c247c2c00000303010656800042070300d140503102c00309514084c102001030761144502200c00d444004040080385040e0300881c11850134502c40c460402c00d1411500c001442c00340103607a01c034125464840301051000741806024140c400080f94100c980c1c860700740c2241c2c10409200c058503a95078a41e4042003d0f10a600418064a51036483c00740950400f02003001c0420749510090616204000350300625003003020f01270b440c003400d0510041030b0307403142048030740082c243d0300040000401c1c850200400c2400400f900039940c1c0001c0400c4400b140800699580c41100010b02000c1e200380820801840c0007018209480300720f18008902c1708d11a620600c00300d006a4248044540340c201003a0a04d506c113014510121040f40149604104460804801c036058041c00080041d070341107680d100042044072600d24020341e03400d1a000e440d0054510b050810318041c06205082181e601c5d0385103442100c4810000d034110315808130b0240780c081ca000052880c1810303020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 611059973 1250 611058723 611058751
    0x207021810031e0303180c0506090d020a0914090610090e3a0c1a1305030f1b0c0102070b0903120408010b0a12050c0618040905010b0108010803041d 65
    0x2411070b1402448855003c148403c50189443c0242c1511030100003007007846054a0040c02052008520320122182500c1c01d90b554503031200402c0d004c0c0050325011b508000c0a54000405c804181d10651040603502d802c0c00c03d6440780030319162603441c1074072841c035600003140e820311101e442548001c0c400c0a418007118000c031203100c00c11010041a225440d003003680507005000040542120040d00d040d00c1c98000721701c421039500d00256005000c030704442c030715078440010303030205080d110040c07803175000001c4940352065a81d41d0141e40e8001d00c204000d00d03421015200280d50700058045140d00c050700038151060400d5941602030700103040e0947c2c1480754658189851411a005101a00c2e04400114074000110184040300c030144d841080f00d0103002211001040c3d010402984600e0300700d91441d03a54500d58841015403f84001c83c41c1e026107004640d5040000542c040211504d00ba01d40c1c194903a6030b042c48035120700641c0b00e5000b01004800309403410115030140d41d5802001411010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 611061223 1250 611059973 611059979
    0x50906190b0402091f0f03200a0504050316090606030b1e0319030207031a090a06020f090a170106080607090314070b04060503090106050a1202010e0f030d050414040207021810 77
    0xe0603d0400e4681c1c15100001703080d040100765110a101103818040d040a12440c008074607030419600e0340d034046090101010420042c07140c442c1003150024003004080f108940c444c04c15940034420b0512a075940319240410018525019004403420b9550050803a8036005110341129602e881d00701819502d030050f5641c0b000031107007441a00341207a000790f0081064500f10b15043c0600b00d8071310100000c0680c040100f001800c2c0020b500d9510507800b803005602e030400f04000d8801805003001440d84401c03030020100341036078505000d003004c08141d002801a1503544803440d4684800b91001000920210380c00c1c000316085040300c0308004041d4044800d902d035110862000c640280d00325000040b000810312264503002d028441c080c00c0111a008500c40c40d00402c540800001c0c00028180604404102d150b070f541c0070700c1110081c1014090302c039103411203100200241d01601440740c4186180d00c48101500f081d1085d034180d43d41c09010700382310503508290190710301070040038240e01a07140f034804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 611062473 1250 611061223 611061229
    0x30405070e070f230403020d060b030703030c05060f01050f240a05070c060504081e030918010501090f080618031b060105010905010816050a051e0706050906190b040209 74
    0x641c400c20241d80c07000040f00c0c2c8564000c0c92040d2031004546199000300c0059104002d00017200c084030b0b070480e242c107101801d078a00800500b68100045516000d0b515000007072580111907000c10300d02c00c009032039280d6181c41e0b00440520013802601e8002e640b600f03180700c45007481040e8180140340102c0c0c001c0c44101c000d80d00066a0300c0180c80600281c8045400390401238506820000380025062290030035081c040741540d11404200b0b003903a0300b188010b05002d0364406201b181d441a1700904094200d9120f81003050b4400800e1084600090f649000000c1d1805000c0c1c4040a655503040a8401a200c03444c0d420b48041d00c0310500706144c0410800d80d00b4103070f0302c10940551101c1d048050400e83d8502000075141660940c4203070b0606c144403042054032407107600301090011150401a40380d442140c0111054000c6030807270300144440010114074560010302900f01d030341c4184400c1c42150350314410b55841e00301c20f03960098034002030003d1016901681e040a0355041000d080103003400024400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 611063723 1250 611062473 611062499
    0xc060414010905011a0315040f030c060902060d0510211b1e260606041a0406030606090f0912051c0903200c22020c070f2111010503040507 61
    0x10000c0c03000a4070810356110308050102103030307450301d8409407c4140351a45850346c206203030a0004040141c0c03541c0306070801c601548012030307807074010380800c0d1170355510070990b001031200f0744030201c1c01d0600781c0001403c1c411110b66440e406260314845014135a036680c4040c1841d10070003800c4500c43d040800814804400d03401e10060307114040031190b0103407a100c90b00032213800c204003840e0401807441d0903042c2c0b02d4000801c84d42244090364005a40c140d205201c9107405141c01d0b80690060511800009210942d003003582520002c1a04001501c40020804100d03848481c0050040c0c6280c040c022040340a07002805001000000702c020300e24002c0021001c868520304200c0124942d2032080c640c2c10300030701c2181c0144100c80300400184911000141d401503041c201074bd03c1160b034a152580c412290b4050b10804c100d810103c85603a0384a1000381b40f02d1240740504400c0d18030300645204145080ba00720400e07950019904450608224011101075200800940d0103101e01a0001220001c15003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 611064973 1250 611063723 611063741
    0x90b130c0b071a10060e060c120a050d0b010e0f131b0e01110f060f0c1309020a030b0f1f020a0503040906030201110d050a03050405191101090f080727050f0402090106050c06041401090501 82
    0x1591590704e29612332994101c649140815041024025032817544da00c0d00d800f00810b2050444104108000100008000d400300352510000317814110754840c0003540018901040402c244c8502c0c04c0c840e814100c0e03d42d1007041804000c1550701032404030f06d1314441c42c4131081c1c00070044031400340b070314000724a02c0d07110314107592220024541c00940c0b1100c0c190b041c8101c18003041c0c00c07200420300160040000d89030720351003101c2101c500000b1240307003034250007005045411540003054948543c0c5e5008020002c184a00c070507400320704018000408100d01041c1c1034800c80c5079460b03250408600100403401828004c0003100d0920036440c40b0100e40200300d100b407910b14401d2000d0207005000da400100000c405500052081841ca002400a20070116201c41136460041c20340c4030302440c42407071078810040c405103030ba059480c6c00240034034601c0030104248118000e9030711210030f9903030302c1040387c3e10700c1007080080c9103801401c081800100c00b140316018a041820000ca404012038540e1307421508011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 611066223 1250 611064973 611064977
    0x90f05060c120105010302070f03050d0617010c0206130f030c11030f0606040f061a0a0915020c01031401030519080408031602040609090b130c0b071a10060e060c120a 73
    0x100d0101c40c8103000071100b6000d0301080c6000c3d41403034020f5680c5202d013600e4a9000f01800000f0840e40e00c802c4c42640400000e043c1d800f41c622a040e41402c0d510b00a044841c11980140100c00014000406011b00d0140107603001d1000325981030a510101e035464810002252a101410303203618032070f0380411529250364408070241c0360380c0c18410200b00c02c4581c040003035a21b05040c090308020500940e60840c80c141d8085070100e9694095113001c0b01c54000c41e8100c1152650341e43d0a551200e5800103111040c0d581c2a2410040790a0441e401e601d110002d100040903648044003005018a4104440ba9068462030415003442c0d1203d21240c1146c00250b00d07240740042c01855803080d86400d0151500914450004201410194031081c0210500038a503484208501015038100700f1088003000003025059203260b00d0b030b5540d103013a80c0840d5540304120070b04400e0b0004502e03076011840011342214a20703255400e800c81040180b014580000ba85580315002c1c90640100c68440c8200400050f540c60b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 611067473 1250 611066223 611066227
    0xb0403170f09011401180e0313032409080307030b040e070617160f180906120308160207090b13050408070c0f0602031803100c1e02190204090f05060c 66
    0x1560116003101c5140d80d40d81041c04c919401002000280b0340380c4070054040c002c0208004400d1699149940728000c107516900303a55890005c1400340304c0d5640380e614178030140c40c01000c590307804018007a40c0c11024007409485040001c604818000d5200011001c0c0c050000704150440c8810701d1300344490783e400000800c03010b000c42000f03030001d0a1065030010012118541d0101e60700c000508003000d80d0310710003e00003003d41001d00003082c1030708070004120202007409031035118590280f1443c0c002808030042501034002c0ba400400906210103034609550040814501e080961006070001c00c1e00590450002d910b00b40d0801a5401151300c2680210181c070340e100d090b45040e029804d029880103d0b803215000c000d0101650120072503070103c03007a00d4425480c001c444002800c181c442d501d01e020355803034642e020380b017690000900303103214003801c505404074103148000344d8907031500b20040210f22441c00481801031500e81c0c803418656004480b1140d605902d40d40d018034202c400d45051038001c1d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 611068723 1250 611067473 611067481
    0x412260a051806040b06150f03161b050d03320718230a090f0f0b010525080c0d1206090903170a020c12090315060d0b0403170f 56
    0x60a4410b40385903901200038003aa00c0c00380c0390540c0410006d0002c0d03109102c110484840281c0082c01e03504440c20002d000d558034201a110000070700404581c51021907191f10207141101049541281e196030000c0281c441c28025900840082141213000c0c00e044810b200505481c561700d000105410307140e19121003c0b070030000070107402e00c242c00c1210a0046094001070001110050410206c40040100104e2b41d8458100242c0701a1141e04866004d80c90070000070722640c031541000030b5010500c8410405c0c1c114580044405201d0a4640c3c031000d2110b80e0280a2502c02e081074041c0b090180e2486414084a6a01c80d4100210035186000240b0310040709041c410951213a00c00905d050241017107181013991300a4181c00010a07460028145140000c2540c5d0941c0c0480da504415403050f180340100004020105070015284d070360080c07103103a80f610044000c0489190103880020700d0b03c402500c03035660b22140d90000410460400414040c000c924a044104c0c0c40d0007158000302c0b80004d454 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 611069973 1250 611068723 611068741
    0xf060e011104060929040e060f0607051b04110a1101021201080718060509150103090c06050a031407050f070804090c0804050c030106320604060c0c0b030412260a05 72
    0x107088011105095100000400c1c44100380c04036002c076a01c40c1408642541c9088c0082c80c1c040340b10b01e910ba0042070005a0340700304600850071111002c641042401000d45035428401200c072404104050080c3c100000da030360a000714081c03250030542c900050300d480b0250150015010082e03100340c1c1d40d07500082c018080499902a00f034516003d80e001000041d1500d000a00c501b14068103840200f65610482c100b164070030340094402c02c3e004406104055614540241142d00104a030000246443c00d02d000c07898220300654000c020507581d01d07040200c103110861003540410801c550307110b410003002a982c0c07a40d01980e0286060f54a50181c00c2c80c140c10060300707100e040800035200743d145c0f26040c85100f0014080c0007020741d280c085059114142910402034114100301c00b40d10400204e0002500340d4880080c5011610401510742207542d10a01c10740140001d90b0700600304803540002c140014401c80078850420303d9200c0c48024a00c0b188400f1403030003c2a04d800c1566600c0c0d004000c1048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 611071223 1250 611069973 611069999
    0x1a07060c030501051302070512072901060e010813080318060a0f23150303160b040c120b01090507051b010903110d08041412130302010212070f060e0111040609 70
    0x72217201c100350310305402036444a0b10f84d40428000d07410100c01003901818030101d07201644d042548100c0a20007c1000444244002b10900c200800500c040c1280720a0754400c03030415008200c61241c8210344180760341e6010541c3c00080148107882c001d00700c2844100340402107640524040c090016141c040326010301e0696800004141c0c0e1034007410456110302c00c010081641c0408841c0e08500c242d00c1480019065100b58583d050322459410722001c1482201c0400c20702640c40b82c0c124a07100d40d40c0e05041e0a04d001c80040250a440e4024010043d2107520b401072540031501d0300c3d0061501c20503009585022211a00f4141c039a03549031112010103030445544000207884d10020808260796140042c02d01c440100000c02000804600401c2c40404002d00b130381a1440035121501d030401401607052560741d512080e230052041081816200701c0000071161800e4010010014510442d1550005007101c00714403002c644d03a0b281819036907032191020304060160756503044421490f1403000c1c1000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 611072473 1250 611071223 611071249
    0x1801090b070903030801051503060405150a0b0d1b020703060e011d06070201060f080a020103151a030f10030803040807020f030d091a0a0c0b0403030b090f060423011a07060c03050105 80
    0x1e1441710004203c40c010100681cada0002c8119000f0a950751040094000a028000d0b81604500d4002c80840c941c100070016103840d00740041e040043c00c0680014141000c00e00c8461005a001100103002180c0203401501d00d0307001600000c945c05040c01e045203406445d5224024950b0010014403200c0ca0703083c007501008140d8603040c0780d00541842101504c41445500003030502d03039108814101c0401e0240d00324014500002030096550761a000c01800da8811661000304120050025140455140741c20041d0382e00070700041c3c2140c0d02c41e65a6102d0740d00641e01664009220701e21009155420000c8100c1c59095a680a00051401c01428040000c0320f100031055a014041032000030381c4481c00351086c54200a947c80e680c0c50706d040071340c001d200a190058005440104011444607480745507401644140c504000d4104840d40d014000c0340510098551111300e8801085541d0004002801e0f03802c6542c100e03450041241e0701c5c41300325001054480082611600108680d160101807024a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 611073723 1250 611072473 611072479
    0x203010e0709060f0f180f0315060e07081e090c100e0303070303110f0d0b150703090b0a12020705010e070f08100f0915060504231801090b07090303080105 68
    0x1a604000015000080300c048078010041c0b06541100164451b030f14105504060007218440562505110710b4212441e000583d1511188070310000401d0703403480b0b940e04803404081400c03866126810704a44000c0b014055044040c810071000c1c94140e00e400d5528001c82c0107100500740400824140065a40010054024090b0707a4103000c0300c07074501208495409503d071a00103481c0986440711401802003205c401440580841c4442c0c01e40f41c0d1fa03019440c90102110302c41040010154003030013900c20280c00500091001030108421a4054042d1034840d55a00340001541e49483d05002203800c409401e881c280c2d150742c8840d001d07240501529010f440030500b03201070241045121556400e002003881c1c5400c0d940c41002e8040c580741e92140b0300055100007242c0c40800d002d854000502070364014503220324034004025411714040400080f418642c0c8042032640c0c2c0c2d41e000034082c2822110a40c0d072a654031050382c8000244030003034492084404c0c2c0c440000345c07429820b000700941416000640 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 611074973 1250 611073723 611073737
    0xe0402090312090a1a0310090515011202091509271603090c03120905042c0a0c150801060503150d020307050a080114090a030801030213140a0203010e07 67
    0x8540d140030030205032182c1c1c0781101559688404000c1000d40780305910414a030450030301c4800091203034100840c002c007080901c415906488904000c1200c0c3c0683e400c10b441e02a6000208095002d0f81500030040c041500050030711010501003200c920403600c405030203100000d50b146291500855101130f4181000e1046548421400764065080001e000002d503550300680d0000f034207100717801207248681d0010000402c0b0b552481c0c01d030301e62181c0021100110f0307058040440e0078140386c81000c00c80c650350f1410526003410044041c401030002c00b0544614080c50800b68049a044400b4800134600001030a0321042c101000a22058042c0c0001c4100301042040c00504802421540c40394041181e03075010781d80716440081d02e4000380e50302c69a001008540d00251b08130040d80180082840c03c20342d0781503642c3e610b98250302c4400c500c00084c08076040000500250a103150710a03810b00c0a400002000040041d40301d14002040f00c0d0810020f400100505c2400c8103d50300300d81041541c24018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 611076223 1250 611074973 611074987
    0x1050a050d0501060801110703030b10050318010e0a0503190e0a0302100e03100c03061d010e061c0602180108040506041e060905010c0917060c090a0510020d0e0402 72
    0x4024108900c18580304002803607201c0144102035000034000e10b942d4008128000c85c2408821042c0c220800a134003180c90510360502c0d40c101841c2c8014409030580e1894039556480d4240d1070b9840310801020015940c0b042068000c08080001d8042140194015512401c0750200340d101085095041010042500302022140c4c5913800000300343d99040f18404145119030ba0112001c0c1440c5413095072510482204583c46101984851144c0040ea42c0501406444071416001103071000c1c070245101807050010071068040201050b00300764001c1402e110107841070798551181900351400d81c0d030107034000b03220703030000c00c01460a00511000703090280c02c602c2d02da100c40707840300c00040000e00051058012200220310800b5001e210750b0f402002042001c10382c1c01c20318024500c00d41210081801b000c000304d01c190743c0460b031800504240c8010140c55440310414082c075007100d030710150403690308100890f041e903c001300d040050a60b54000c110580344020014103181c9070994203800303244104a40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 611077473 1250 611076223 611076229
    0x414120c03040306020d2d0e0705030c090a0912020102190c11010807020723040501060806030304090b01050702060c06091002040614071e03121413020904030908060112020102070e0105 81
    0x144044075001100140c0b103611006c1000d020340851100841c0020f01a420a00d00c221640190740034011094410030613011000d06460303490407a070254560551280003650210b00c2d080d60126031005c0c032000041001031465480000080a21240f000580d40108000d1599002100f07050b05d0f0040501d02513a240c00540c0321160110245034841e4100000c810000380701038002c0080400070612a111011141c900e40040040f000c55115000c0c8140d003000000901a403154814500401e00180518542441c0100c1305008000004405050203402d1002c440940d81c0c05000c2c2c8000308004001c0e00350361501034045070411000d00010241c051040c407003840a1030740040c41212a40380420740d01d681da01c0504000303942108800040c0c0c4031034241c1c8811410158080c1d072500d01c00015500c02e000d00304440c402c403000c00c0c070115600c1600604000105001d0701d01612410b070068002c0c00c01304c100c00d445480041c20b00009030001c5000b080b822180c0e40455034100a100010f1041c50340403039031380d4100800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 611078723 1250 611077473 611077477
    0x906072103111b1f060504180803010b071104050a0b010f141c0b030a0311070b03090a03030203130b01030507172a06130f090605030d1202160203060414120c03 70
    0x40301d0048089580d0484a2041040100c0d013401400032601d81920041e05994041d00303e90040301d00490810b83d0701e0059025190210300e04a40c80090542968244280144150011042500d6002c030807508440651214402c080c01401c100301c2c0816049034050000d0a07842213411030b0820000000c001e8403d617040b10f416107401100d031a11442c0180c4c040085080030b0a500103030180d25020b0f42c20983c08058204076907411400b086829600d01c0c0e6521603940d106c5000884500c0c00700d03000440440c0010f48294011a8440c1c410880c5c0c0344803000e2034485880005098000301c1e0700740d1050030288a4880c40a101d40e814402c030400600208100d004130132100139807180101c02a89400300d520109594900680d01c45241d503007207001400395120b801d002584003510504402d10300e00400490141800f0680000c06c5c101600d5800045000d2034a0000a611403542c13401200341060184005030780610001d4010b9006059048100d400c1040281c2030102d8140d41501c410010440190b001202000f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 611079973 1250 611078723 611078737
    0x30c030a0b060315041d03040e150a1a070f0609050c0406090e0a142e1d03161506180b0301020c0d0c0507090f09261e090607210311 58
    0x8010802d61b004486076082030462035041c4d480360001003000700f2100c40c01e05000348100480303038200031a00d1503802800304d58038660003813002194640b40c8400d8410810801070620500c11740c0c00410700d94894443c2803c99840200442d0b00d03800119440030a448d0501981000c0c0c214444108504190007600070b030390790340c240c8000b4a020703001c015141c03503800c0c140002072070b00c000d090b5040700ba021070301840d03502d43e1704000401a40515128100e000b81c2d040781082d101c04001d490045181c52009107610303c10b82040701040b0f0b6500141c401c003002049850049000500e08540d0180000000401c444180c807150b071152400ba030f1041c041c2000d070700d000060761002c0c40c0207030500106070011070400c10b080500581000d004182005800450b400e00c03944514221402603081512040b000b1304201c0300c00701840c050148000c4140301007d00903129011403208840c03400d21413490941c0000c0803a50381e411502050340d0402c10b540041000500d519080c0c0c00600c0903150810515104024104090084403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 611081223 1250 611079973 611079979
    0x206070237170406030c0c080a051c0204090b15093003040609030b0a0c080705090409020a0f24020607080603010f150f170307080915030c030a0b060315 67
    0xc0540640000e903062101e040503001001040d241ca40c048501aa952040c811a00080d01c1c000c00e44079400e218801041107035901c10201c81c60580001d0b401c45898101079240702440c599038040200881e030328401080100515440840c12805040803c030f1181020300c070485079a5070030408244c0320742d503040c00d1900301440310b08255003142d6003123034041e06050401000c03030082c0b00028010a000360081c0c0880201d9200720705000184c0d80302201e00058800d078969540c01302d030f400c90101d50744030b0181015211a000103400050100c07001c1e000180d01a08642c0000000d01c242d400a002c81a03808000513641038096480fa0500306030070758000d40e42c02000340b4020800080c100443e10660b030070b4108402450286105021440c0e828145081d4400584a0f00750b04001070348000030704000c08003a240c454107546000d10704103c2e1985441c4601c1d8450b075000365200c002180541040e0800c000a9401074204507452502d030303e03048502908480c03e600101c0e208010500c1000300c1e80c018240c144041c0803050b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 611082473 1250 611081223 611081293
    0xf0c11031204031206030f0c140a1401020307051c0e060f0a030207060212151903050a0f06150b180a05031e120a0e0f0d0b010e09030f180102060702 65
    0xe0400701c44c0f1910100c400d000143c1492000000e01c00715000040040d0b00498200b0344141e602c0d5030600b040d240441800760095950300e801c0007000340c0705940500115040c0141c84c5011451b60780c181c202070000e10050341c5d80a0203491031800b15403184901d500043c0680320145400000c0304514402e014800d2980308054001441c40100302498040d44d104006840a50809082512128140c000504082409600b0801845522907111103c207070072644c105000d8403082c546074a070030341000600002562050340b0b51118042d102440040c0000411800c074840307443d80110032000300c0464110f076000f84206900f40c018003040c1c0e00410741850001c002a60516a80c0d00c044440b0b0070090b520b43e400d0f80706000424521075654000d10b071146984411601780c40140300410400002c6c03440c011010b4805000c0381c005100007050141255001254503040b2401c01400090401c16507011201d441084000d030b039150300055804018480c0c1060712400a00940b5444110b40c19980c400e020005041c0407070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 611083723 1250 611082473 611082481
    0x70311010c020d0501051b09180c07080403140c04020a08162016050a150f0e0301051612110d020a05070506010603020729060103230a0f0c110312 64
    0x2100041038240d40500040b64500e2613040150080000311484450041c0c1048046084042c032001c444002c08024260303010754580da072101da0f04203070090101d0210703682003003128041105007000d8801036100b94203806010b80034240d02c500b81600307681c400d4065401406452883c64200c02e080d9440a03114082d4207000c1d404881c01c81d6a0303856a000751943c9140105000030410020a459400c82c070106095a945607030f880a12010350010311a00c440c884801c1c440c00b060910850302d10045803901d15110071940d105600090844205407052543c2e44802c14005800303507004015214400040c40b02080a50890142011039210310301c40007110540c0020107206240c05081030351040c9030000f04980486d07071a008068001d42c082da0701907906080c10f864000302c0301405800d10960704903200c40c03043d858407043d00643c00f40601070040104030b07940c6141034100300c1295203020300c142d0803c800860300501117270001040f610f0a016040410205c004400381c03800d4000211804110005401e11003a0f40f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 611084973 1250 611083723 611083727
    0x1103070b06011b151d03070f0201050307110f06070e010c0f151e090501180804030b19050f06190503120307090e040c0e06040612060902031011030901061707031101 72
    0x1050010084c40703122022204c40c40d00d0505e0344400e1100d0524070030010301c6014402d805a032805210401003a0300501e20013040154464405141c01c00624208220300c1d6541040c000d0070101d0008403081703e60700c510108001c00d03034402c581c800015028241003050700f0701611001281c8000d01c00150040f00d80e10001d91203c0d20035070000c251003507100d0020020041180280d4003070802c129060351b04e13601b400d0031a80740c44081d4016994295000581e20b01e07152440c0d48181281030000c0ca810000580e05801c00050f024600900380326000741e0300341c80c0d00c41c40c0000c10007415030304044038510035680d280801c0c02180c400180140204450300700141d01c0c1c2d070340c0720b00440d200e10803604164000a5040c052101b00094801e9490907517429007003e00641e5540001c6c84100e03030300d51040c00d02200d1100c188101060071903010014140c000340945000c07444203040c6409968000c0744005143c007002081120800c07003031195a01074800c6000d40307200c0c01c581500480e07503903030b1a0002520a0000b003c0c40c8041d81c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 611086223 1250 611084973 611085017
    0x101106070503012102030f011a1201140a1e06140a0e0c1218070f0603051510030e010e061905060609030d0f030b10050304030f08011809020301090b01090b011103070b0601 75
    0x1f0702001c001e1008a544200310382c568460030091030b0003541c0802d98400c03508810f016030170b241510380746003240c195680c1c242c1002519a1075100919880030305490855444580103803030180201c104007855002c212030a0160711901540608140d080d05030501860303050040444203144111005410140c031040342202c43c7d504908011244c1c1d2180001c001440c81d4807103401c40032140c098070100155600d00701007070200c540508019034010043c40140750070301d0007039200c0c0c413880000f0800010f242003c01445490f110b8152095403460307140b0b015000d843d680138002c3c2d40e4800400e440160802c480c1c0b001080d51034002d020680e081c04059491070080b544a64410309150800a101000e603502808002c1c05680c41680c00750001030700c101940100307500070780e021030480310500d55001d0000d070003c00d40c0c80140550364080360b142d500c0b01c8521000c038a032036015501904244500040c218140c0e0005080302c0382c59045003103d1b801c00d02c9108081801c0d029103aa00c05020300303201c3c2c44140444441c42c031036 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 611087473 1250 611086223 611086243
    0xc12081309050f090303040507060507240b041d070b1b0109060b040b0d0203060c0d1805070e010e01030f06050601090302061c15080715030b10110607050301210203 72
    0x2254460300c000400402603008540960401d00c0a64000c0d00c1d2410308988070321044401400ba68000102044114030620041c940a402901c4004040e00522036000c801ea241c0d00c040d041d0703a41c41c1c281034107403440d007032107041c183c81100d0703034000088052001002e895118500c5144112080807400e5400034001d214001d00d8049490000c0102010320310b081c0005141c50b80c1018081d070b1805058000c1824580c1c21602c03010b80040040c6a103a8a80c00c410104d81d02030001809200e4a07001c4100d0310390302825890340302501c01d1015181050a028503400307481d04c141e0000d40fa03216148010400309400000100b00590040700c04501950340a005884040c50f9a100a40000c0300140e040340d240c0300c1c141c0c4900401e42000050012060401c0000c44482007805120b0107500540310400091201c5140010340003141d04012a00301110000500c01000034005540441c082c04402142510248006c5522880070b051081c00c40d410900e1041c801450002030b9500301c4014001402555402c200b0380302c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 611088723 1250 611087473 611087497
    0x50609031f0c03050f0103030503060d0309090606090e090313122906030c010503240a030f12020d090f030204021e0f0a02150408070f080f0d051f030c1208 68
    0x545a9040d40d140042c150240c0103000039282c400800c10180d8510395141c101ca415580709030a680b60081000342c41e9075030340400c6050080c07a00000454915500400b8014460340d110280c41a2600049004e9050300500e061050b400c00c00c0240c014031b41081e180d40a4034412030246042d801d440c070b0081072100d850180350395407000c04181000444501107030640304034011b8050701c014480311001943d0320f010640701140f480b206140d03407401c010b240b80c003000240d0100910038904e40e41e4980f240000c07140c010000762111454070b026051055010844c14500c1102d615120381c1d5240361458110b5090010301000b481a0340001d0307000520a0000c07000720300800b003181c03444c2c1d44080448525510303520160804015001d5007a007a1005c807682c20301c09120f5078200d04100d1030b1110a5a0300610341031025003c460f0840103106015034400707680041e0050720865100080d4030700306005440507150a4144445d540c4508000070303c0000c104513410b404455400383c56108000451030f180480340161602100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 611089973 1250 611088723 611088763
    0x706020c060a020a021b06041217180a0f0308031602030909070906030b031603170f0a0e0909190b100308130303091a07170904090317091605060903 65
    0x4022000f58001e124002c200e808035298030400071121440403503108000380e44210213100801c051440d50740050843c4e44143d4030031183c658250300c04051900b00c0301042811000c0f0070000b84d00d6050180100d40541042c0c07502503900d41c078503590081503210042c00640798201c00d405203080700c2d0080050b6008040018219402032920fa070000342881d200740300b8800043e00341030031402d15042c041150107182210900d444517481c11921528509500030461007a0311500b000200c0c44a20800080c00d082d00c015520a111007846004000b40184041c10010ba150461044012015500480156800c3e80301d60102003541c1c40c108441301d480c4039580080c241c0040010b00003013424180f49420305a91007910307810241a1640601400c8580c2042c2c849404038040009802048107608404000c0c0c00c100e007614505844800440d0664182c00f00480209100e401342e880000c140c0c0700d016a116064000034500080450300341d280e800c45038031585000b444002800c1546880901002d071240c201546554 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 611091223 1250 611089973 611089981
    0x303090c0815040512180607030e03060a0b150f030609040606050a0608041407030503040b09060d1b020d020c0a0504050c191215150810180c0e0f150706020c06 70
    0x30035902c0e0122401c482e64015005118004081c1c10299101c280c0f5038080c070b0499041100c107000132603221403000e0f0180040c0034507062031564104815442079410501c04a0010b0075030341846103848030142e0820359034409105800300c004c22682503a80c00761040300d0f0003401d03407a541404001043c01d604038a42001c070892010844075003004459004500c00d540d45100200c006401741c0c0c994160b03001c02442600208020030200ea6008060083c51000410391854541e10031980411501d01c601400c1a05d00021f03001c403815501480b00d810403000d18006000d16600890000d050b00134680900c1c0c1c0b059940350701040100d01080306544180c190410f181c40c1c5400250b00152003814545000700040f4100129644070702e207401410021155800d019298480f1916015188410020b100200706542030300b0001d243d100c40b0b1350355009a86105000110b00980500040c10700f6104555180140081c8a00c41f500d0b40700c0c160300e00c41c503c0480b4441502d1711200c1c039095003e40300b100e000f0382c41e51061f034042c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 611092473 1250 611091223 611091253
    0x114030604060510020a05070f1a0304110306070c031106061f11011802030d050a050a08180109120f090e060f1f0810050111070603020c0f120a111204030303090c08 72
    0x2444019003c7c00454030043d58031007510000910601500e0142e005800c0c9415651b00c4001c051034000748280500600c031480c80c801300c1d1801c48226640310000c0e503100c64190500d03030172045030000104d0034406011a4901704001c5810003042140300108561203880729181940b1401d47c104a8450705002446000c01c000111041148038250a9100c0c1c0a001c40304000307540240b00721000345c819904c9035814001c96130000d82d000e440081c2841c07401c0301440e4109098072000c0c0f2410103028414960110900302090008241d600702c4101e05d814001400c10501070000c1c0142082e52011044a20103001c0c202c1c480424042d1001555480660b81d5108030290306030b41200c0154456100310b000b01005030b0f139660044916203107113a0041441c3e080028203100b09403003900249030785000d03d400c484e461581c1e0038006107003805140d0000808807003c122919010360120301858140e52030f030010082090326910300581481075200044c1896a80d0254900700300030800640c00500b2207400713807050003005c0204 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 611093723 1250 611092473 611092483
    0xe0d0206040306060e061e0105130305030a0f0f02010902060909090102070b0906151e010c0201091e0e07030c0801120303110a02060a0c050a09060e04090b070c050c030a02011403060406051002 84
    0x245e001c182da6190000304581403080c0e80120364a420f0407500446031030400156419400032a079504800680c00c00480416010401404001c005545500702052040e50080018542618480440e4145600180503942e45c006545035494104d40031a0a5200c0784040d44c020321613040000c24100c0301c20100002d5020220344144154002440038491060750810404100c1401c041541c8003454070404222075485840c03140030a45c03041c10401c020030b8690144440c40000b000143e81081241c0c1002c2c884002031100c62604040f842c20148208003910002a1a00c43d0501a0440c1012113100a106140c0309411202003004840d10b110b60f0b0302c0703184030000e44481d4101c0742d40b580e640c205000398040f6840390b000c5501085603581da0410203810308070304840100404050541c06030300c0d1111440811030381103165022b100030341c840c03000848403845c2c02c1d8142240605541d00c6504040045030160740c00a4402211440b601043c0703540c0d0b560080003d0040c80c854220344c0e0002c1021080c0f005568002407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 611094973 1250 611093723 611093729
    0x60311131d0702120d020d060504020310030204060f0303020303071b0f062403080316112b03140f061c0303060513050c12100801090f0204051608070e0d020604030606 73
    0x10159000d41d030b076220a80c0c0c0c80d0200c0c440c0e0524030704204000328a444842e40600b041c60b480a1000c101103581d07000240c20790300142c4405074480041c0e10f04100310310301480381c40c00501c06030300b500e6601840c1da00e001e034032030000030145014043c000d061441085250707041d01016590042205a201c01c060800f4402049290004214404500c0d880c081c805e40329015034080301d038400180c1d0714540d02d603092882000b282b9140c0009110064603804c207440c00a00003000c0c010741c0041204421003481c0082e90519040b0350001c401c0c075160507109420030091104003540700202035983d55642d1036040201d80302d41c1c0201800c80d164103503111f110741003642c503810040c22240200d400d0704125014240c908216803090341c00604106d41003182d95050700046c0c84242c0e02000070855200c0941d5140c02c540d0a580000394110342c0c10302014004070451030684071b070701d4205402440d0031064502001000d841520040c1910062118017100c65186981d203505840440364050101611540c1e00e142081c0030309a640 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 611096223 1250 611094973 611095019
    0x730020307200706050a0201180506071b0b13140a051e01060608040b04060207020604080106051801030308060d24020306150c032205060403031206080c010906031113 73
    0xc02d000c840707900510204100d01881014043d0759103001c0060780c0a81c081c440c60000d5540328950303038070465002264020f4490044c2d028100c0340c90701c500d0040594503030402d2180e0b071403126400500401c91503640103078418042c0d041c5c4c5032104c0c990b0614405400b4a0010043c031403043c4d110100402c0070206860050040b8247d400405076010502c89003a00c40c0b5024032400101d0810006000c02d00080980e034100d4020380006113824a560042281c0da0721942104981c0c0c1c0d1078000030002414541001c1d403202e1030f015001e0100e0350450354000e00408028000500c00c1d24800c80700e20500010400d071141c1045484005550711007103408000c0a034000b1615035224400388003901443e40451403c4400502c80c04010714900504113000c034a02d42081d28034000c00300c1401c00041031a4445500420140d4043d80b1880420400a04c803e4243c611306d40000b00705411001080c0160703604251140305175400303414013041c00d40000d03403400b0541c01840c0311002590b50040c800111040242c1c40d03c503030a4600c5e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 611097473 1250 611096223 611096237
    0x6030807080702030633040f1103041b2111091e01090504050303181203190b0a0302030d030f022502030d08010f23210c010c0203060730020307 63
    0xc8106106002c404492181b184003001b0b00c26030007840c1060700700d103400c0001000000c88640b000100000c40e0300d68210b2417504c01d000014071007070150046551031410382400d9144c01c2036050940e00340c2840300c4200003a40c101f0008070440d0070050840c01411100e00003a0918001d89000c00c4600d038441c56103187c00d20102c800310b00100d2185614015148502d80000065286807103169180300fa80c0f200c0c8030240c440303014a040110322054884d00947c020302186e11002d10655082003035004844c1000307a101e10900b01c05c1c00400040c1c034085824003124501d8100003d1151280b96503c002c0c0c410309807402e450140314020319809034440040c804040b8001d9088464840199009460142c421b00410070b80754102c035420051100c141c3c40050080d4002031002c034040078160046070004c0b07020341100010406000c00301c20140010009501000320929110140c8081500401d8440c40017030020010410301e50481c42044406000100304c089030b2041d0060160340c035501800085d00141c0e11a00000c4074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 611098723 1250 611097473 611097481
    0xa051c150f1107020603010618240e0d0b0703021c0f09110108040b06090703060e10060224010b07060e03030117070905040209060d0318061e050406140c01060308070807020306 77
    0x1c8060f500d4542c1d025104503d940d003045d030196501d10000c602c6031515950b020000c41c0400260308000c01042800e0600c0c10041400003003c0d20f0900c4039203074140543c0a040903000811b04049046400c007145040043e0344240d204612001c0d1400000042c3d41103040c2440080f0014169020409140c0500c443c08850044c000045600820588003d043c03d14002d02107255440c000030300e55048205d40c00e00280d455510b1040c80b00ac12030841c0e86c15003245d141c2c50304201040d01403007985441c40400b00d11802d01903e40100d4900120f06008100c0e0070040407504900f00151944110418a03001c0304076510796130354020601269202040000b000c0c026100b0010f02664640113244c00703654000e060300300a58508043c040210700e1688184d04101000c07012819110143c0d010401a100719514060f070914004c1050f502d9903150660f107400c12400300010883d80391b0000c64560451041c2c01880d030f8400340260024003408580e0030152644a000540608010303200c07000300380492082d0305544150792 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 611099973 1250 611098723 611098751
    0x4091a010f030f110c16050d080706020a020336010203041a07140a0c1406041401030e010b0405070c0308090c06070314070512030109140106020c040c090e04030f1d0a051c150f 77
    0x8c8114001031881c01d040c0f0200d00020300b00c3e0003615181c520b03403040764188514614010034201348417910201140514101441d2444a0726015901500030b0000310301e0585403190700d880c1c03124482d000003005140480c91008200c41e18110450442e00700d400c45250003100c0c180442c01d61150f00c200809240140d545071482c1c02d0a0055400304c94601c07260046d01c4142c8401074028200c5000c880c070a0707550f101c0003883d40303036034601c0703a00e00030481a6a03000018441b450301401141000e0640ca810b64809803c1d003807076550b08401c4030241581494680b403000c1014541d0071543c080c0303040040440c080c00341b00c540d011000f0320140d4101c40f04801d086c80b85031100050030b40040d000380200c10058002c200040490b041942005010f201c007454034094556641268410540e400c0c0c4003240060b118481c203010b0070b40d11500108200d04280c40f41f0b20703503034403040c002407150781c6d2442618041c072028860f201203c42c0841104440c00d8028851014600550075644002c5c43c4640c10464840d10b4105ca90030184 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 611101223 1250 611099973 611099989
    0x30a0213080706231e031506190c150e01021812120c03040302130509010507090b090907090801020a020a032703020d020a08030f04091a010f030f110c1605 68
    0x929a62a08040005132078108030301414146071403c8940310403c054500c184618071200307007082141c0015034072410880141d8104283d81c1030014800c0c0000d0100718245c101200800211100354201141c101c1c00500e03110264100324030390320400a00c1c10705c401000310810340013007070914440e40c40e01e901840f906040282031000c030b0001003529440703514403c015001c1c000090091000400840e81819542d0340080e0302115407070504180907403950700780044240c0034090b585e0000c03d6030070300e03e113a14105034500c0403034060703009070500ca600c0950100b8401c50044c0c0040c0c02925030300009650354a44820041e640d00ea2203036045000802c1c4240907000001c0c03000d040c1441010980c00400010b00d917800300048100c0220080e0703480f5620000020340b000c4e0410040c001c828002c0031582e240c07458070084004031024000b00034071000001800c140160317805141d81944425606000426548160040340200f15014103038000100024400c07440b03501c0050042d5200f00c038049100e0f000d41d1035106020701c00e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 611102473 1250 611101223 611101229
    0x70e160e01030924090c05040c050a2d020f0f010506011b1104020a18060512040b090c030601062a2409020a03060b03060601030b090a150308030a02130807 68
    0x140e40c0c0210000c9580310750007400c00a4066030301d941282941c5820000080d41c0d80d00c0c0400c0069a6542900c00c000c0c054000000500b001c407810000d1250306480a040792203554101e50030484581170300080c1c02c0c0c010f4480300010012049040c40c01d080034501a549203000d2006813028491544120000c01b014002c082c1b0503541a544c19070131b0803494120304080f0500c0d8500304c41d000f003c848031032103d880f6840505900d1030036994098602e146110310590928507034101c1810003000b0030031041061100307036401c0e80040e4008010406607848410050502c01b440464503814056103000062017613000c040001d0241c4800d4007501c90b00e082e280741d41034000c40040000d04d00022440c0100720300c10448a11f00c0300c804e040034007151402d03880e4000380c050b041030340045400642e120300134082800c0810600c0d50208007800d0030044a0a407500107001668010b0406081944800808019100e1246000300640c1d0000c240354072410200343c004040d400406101c4e2049946240004810340005000021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 611103723 1250 611102473 611102477
    0x80906070207150519020115060e030601050108060d020904080903010b01020a0f03050c0717100608061b2b0b031203070c060f0b10030e0d031401090506030a0c08070e16 74
    0x1524034002030003c854601d03480c401d0074010103000140c5102c1d41c0c0419401811456400080c00c0b400c00c0a0f182014192500000300700300c408448428076407000200541076403400d081512a50340c0c0c00307000885610441e44002d400055240a00c4100085034016080d007003421030007481455501d1004903030340c0d201c560000d4030034444181004c0100b4000c90041001007001425a4440c035241d550906003004c400013514125403102c0c034002400038403441039402400389000500828204040015001c812000c10035226480010720464855051180d01d0b82c0320029070501508211a840079070014102c004000e4020701890041c00340c410f41d034100700c0e4441c100f0754880700e18001c410b49074a0014010400f516403495558040c40c1c0040c3d070703410920111030560313541c04183c03a4840e00c91a030411611055480c14541440c1c0b80308001190641c900381500c0c203a09000466a0314140064a02003013510040c0004000c0080442c040c0c001048510581c2e130b504200d0340c2c10382c8a00401401100c400048000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 611104973 1250 611103723 611103733
    0x4021f080112020a050a1212050301081f0204051011060a06030807060f09020d050d110c0105070611040b1204050c0f0112050907030b10050118050303030105190f150809060702 77
    0x3190144542c40c2440050028144480d00c58032500803810b00d0340f9a42040b074100d445000d01d01c1c00c0010890042101070740500d41281554904401c0980e5007140c50070f48005081c5d481e504404108075941624002d0000914240300c0000c00800a000c040808058101300d014001c0069000e0400d4050f0404982d401011135103894550b40385d02c0010220342c0c180700c10003a00e070203400026075245201586640c4c000c00c082d28860b44e4110700949600405101660300c0e0304061400c600507030b005001d4421968000001182082c052039440055228942186100c0034011801c400310710713102e0540612981c07055086415400645040156841402c0d10b42c2e4006800003003044810360030342e003200745c103d004402141d200c00e0320b0f590b40b207085050441c0d00001e541d0032403501300070300e60303020884000c402c806244060b07103607091502003626403005010356800368112802d0780d9201211026203500078006540ca1403d1551a0280d0381216110101124000354844002c00e40104011848900812040d00200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 611106223 1250 611104973 611104979
    0xd0b04180305071104050408120702120417030405060304050a0b010614041a07140309010e090408030c03070207030c0e0f0a140103170706140732090a0b0c0604021f0801 74
    0x2c81a0340304202c215160180d9a050074640c3d1910301840d07000700e201d0200365446810080e06c3e6808098018461811903010683e00501c64410504039800d444101d00e0005030050030908003460b6104940c806600300b140003080009115011444104040c07244824204599031480d0844180c0100d80c07085030358140400c0200a4544a52002d9031003801919100c0d08051194440e4002c00c011080071440c6c503080003c12a0b00340d0313401810110b502c0f0702150010700600b000c0d1200245800010400700c00070074000041082c450003001002e008542c4440030f030541d1601e401003101041002c1c4e4014444041d040003140004a01e80186003529040d0404001541c0c42c649401d0b11400310744130f01c0c482c3e82c0c0c4100a1000820000c0c0a003808004103541d801243d402d00d40c10040510340c5d00741035107410308480b001003142ca9203c1d58446007000b011400c41070b244d04501c0001015100c2950121200c5d070000101091940d0303010030203a03c6a8003c989080b62900249002d2254425a4100e0000142610014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 611107473 1250 611106223 611106227
    0x70c120507170d2f1c0903090302041508030304140c030f0d0806040e1b0103110d09050c121c050f03010303031b02160302060304060f0905030c0f031e03040302160b0d0b041803 77
    0x41c040d42c034482041180ca800100b1a414100c1e241c40201fa40003480025051040d07040602071005c0d4001d11b0b04100c07520916010420f078983c000a480101a101c0d210109000038a04021a0082c9140203050350881016090700c20b43d540b01c1c401c200e00201c1c203000006065840c00e4480c10b418443c840c0040d1a801d0940d0510007101500220580d06041d0350742c0c1d0202101c0c5034a0050200e480c040400000c18900c01e0805515114984195600c01c0000c441c0000d0460790204040c0c0444601c16801814030900701000e03502e6004144041c082240c01100000c00c0c554107401c041d0665410750b05204141c0c1030120304070303117a0202e4013421001d40b451410400050404100442e03000380035800025400b00d040080c1c5050302e83c2c180c0c3c2550540e0000c0b40e038450300e070303024405000d84000910017940381090f404411450443e411401e500404000300014040c94020b000090620198040840c1e9040d290101c50343c0f0f64005d118450121450710b041641c3c10309152280c010f0034421341076080b0484400b5681 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 611108723 1250 611107473 611107477
    0xc200607140a090807060e120c06070b18060c0a1112030115050c030f0a1205090a02060706091a0106091707090b011403090a1505070c120507170d2f 65
    0x10300c8041010f04040000d00b80020301400b0080c1096039a898404e407800c100b00701440f222050751100f035070040800f00c03045646070710484544035880b0b00541c0685d501c0c4c4c2d07900300702d450307540400703c656000748000c12001f0354202c4010310b03a040c441d0b154842c50703500c884016a5141103000c0c80c2001c00c00208014480720b642c1d100c00c4403200d00325160540ca861210007010381150012a4000c030415000b141c0100b50540191146403011100c100c100aa403412802d410f03511580303080017034020b10303000600c00c080c040650003640c043e5411400c421045114104110003000007441071000040203c1d60108120b4154500356500c080514002c04046080c039000c80002c01c1c903a2030040c1400560310205d51090310501c050340c810b202c500c018204240c41e5082150b1003075000c1004440c45890700c1d0400c04403d401c00d8000949a8200754550b140c840004403d450718420210054240c0c0c08480c00345c000880e424008007100c50080c481440f1201160010424802c035101000c01e555201d4541c9800108410300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 611109973 1250 611108723 611108737
    0x20210121060e0c0a0f06020c01020f03040312121b030c030b0a05190f03030302180a030b0f0604020c030f0405100c0515040312020c01090c0506180108040807060c20060714 75
    0x65070f40089940d4002501d000490740808249640300704100031013a014400d8950b41102800502442000140391640340c0c8100c1c00010001868959109100341c4582c80240303140010900070412040011605145006030351544c3c0e00180c1480c80200207140310740941e101200d000f0b0300440c82e180c144010002155442030401e074681c2988240011714000702c100800085010741c40041e9103400118048032480400d54a13240183e01c10351003080041c0d05914140e07400888140e501c1700c0c60700c8420000d0040c1c030660341590210310002c500c0340400c01101d0002c00403598202c03511005580340c50030a507034140003040053300e1038100d044002115140c00c106540c2c0309119240a2041041d884001d4040380c0100c0c0c592241340e952000d070b100c03c0013030f0354100001904040b00c050b801c12550150000c10b08862a40507410404080081b80820000001b581d28160f8488814450902c1400008241400e10728200d1850020b000f046240c400d00401c0807409006a0707542e06d50500e403984c8075040c01d507114503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 611111223 1250 611109973 611110001
    0x601050a1d0f06070803010e0c0405151c0e0d080a11030c16050a0606031a04050d030c0201060b07260f0a0e060903070b0318150a2021012106 62
    0x99240c841d50783d80000a0143c00c0c4900c014541325414901603420340c000041500301c00304003c02c4244015079640b4514000410541a5280d0750b140c40300e80c07200105400781e51064910b06050245070007810101303400d0200021a61852883e64038045c0348025221040014180c00c001080032a0284201c3d000810f15040d0300c83e015549842d0720f54440d40740075010501602c52903a01e07101441080481c4080061050320380e004110740c2d0a00341c5850380c9901c0c026210009055640103010910350003900200010503a6144c11a1030b104a403c05042908480b00e51507020249030b03810105609295043d03030310081440f4104d500700100c54034140c40183c01180032035440001440705400a59082000001501120036600d44a0178191240c0503d48450144000c103600f00003a1210281140940180d10141b01400461120840c8003280c0e5507030101815103008000020303180480c01d0242c010440f52140010300303030095a98400074895405a64510b00107410b540081441c0401d09035004110300890030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 611112473 1250 611111223 611111239
    0x60405040c0c0b2703090315060d08030901050702010b0a080604150605030303091c0c1a0a090b090607090905040503120a230f06010c0302060415060b160b0601050a1d 73
    0x9030322180c41c10181204c0810300d04008a00c84100c800d080c00d03010040d008000f000f103040a241900003500c1d002c812440d49906020140000c0c040c1d501c401c15065010381040402c2d03503905241600d04d018100c125400d0b8051360800100b400d0a04040c00c0d41030841d0880406007101e500c85a6954644c1d0f2075180c03451640a0310b40d44041116541440118041c034080c030001c1030081c080c051044140304080c460301c0c0500540c150100041848800c013100e2580401ba1100c000742e49401a1000801820b10041c01c0c141c1c1c08800c002d595200020040c1c0180d000341c40e5140950b03034584d030580581c0c8040360014425041804400220325009800c25080580c40c00c0114000ca180e54800c4100c49262146800c5a00d0791402e0008424000d14030907009903084c80c0400420703910b910042e5460102400080c690039035502001ea90800b036501082c060004403d00640c0c03400c485466101c0b0b00700246050303507922088004901a0b40c015070460702c0c0b4105945510b20600c0742c1c2d9014100c41d8540480c641e40007400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 611113723 1250 611112473 611112497
    0x60818160b0703090f0b070b0a020c03071407090911210d031d01090503070b0405160e010303030507030c08011412060f10080106050d081b0f070810020306060405040c 73
    0x40020025000018075a5101c80c0e241c1030060249034168043c044c8006410401c0c002000840b0441c3e0b00d4642048210000742c445d03900c81c000078401c001103c50140000f0581c80100400c0360f02c0313000300401110444401e640c4070070301c4104684c3d40c0030b00144440300300c1d40010b52504000c0c00340d098681c00507910407400c10703420006508011990071240d0000c5e59400c41006207038500d08a034450800c1010081010780000c2d0348060b502d10908a0103007000c480170002508000c4100568000b0803540b2141f441e68992781c00300b10038040402c0c003003100440e082c4030004071980c0c420300c54080c02403501e55a142e02d40e46440c0d201c00c1a5400c03034010035080000c40c42d0080c540711040046c0b43c025040c051030300305203181a16000e880500a80c0201c2e083d80d0610384100540d980307182102410b95004006607589442900307400d0451034540b4085110b1f401011a80442d55074040b5580d001c4810040c2078600780b13400c4110f200100d102c1111016030103102030100b4006800c0a0740001191034840c2020054011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 611114973 1250 611113723 611113753
    0x203160302210406020709021c0b0d050d0507140a0c05010e0103090b010b0c0c120622020904061401050103090c120c0b0708041d01050105070209040503040506070c0e07020304060818 80
    0x2408607000c03402c0354000181084042e0b41000b21200606455138114180a0740f4a1059910001407103581c41c07d076116000300b036a641e030b41e8003041007180d403000844602e0844900064400d800c0b4103070650301c90101c1c41e600d0801681c0852401801d6901c01e5604160318182001560701400500800b410166244003840014603400c00c0103019000b266000341d106c040000340340386070041c04412203001d08600c4600c142052000110a9045030702c220000e6003a50420520300c803007403c4000c02941c000c510f00305001c24010f440c0d0010707240540305440500c0da070b030320780d80158181d07060098020609846c0600402255210340701000281d8030a0454404a0303507900441e007020703001041f0a0300c80755400141008940c2d828086c520b241c07881a0301510702c542c5000c00107030041c01640c0c0044e000724804000034040010600464001c0c0c01d00074800d9460364a603081c0030b0303640411409074640e205141e4020411850002080e1800c40c0d08594400302999108504140500d800c00620f800900c1420140c0c00caa103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 611116223 1250 611114973 611115013
    0x804110a032105041d04060b130209090a020c0a140f01060e070f090f030f020d12031505030319050a02070e040f11010f121112090105040c0e070203160302 68
    0x5015000c002031a00c01c1c0301a0074051602d103422541448020007080280309081c0340c064150750504010002c40b5070316800c10b0b4025040300084140e00c524442000d030500722940d800340c0224101901e1508190f80d5038801c101c1207110f00301c00d80071075612407403a100004401c0012034080003500016a44d054200340300031400d6031482c3d00b0114130300c4120001c102150b45d02c061b0640040070a480c21000e66440c0c04a0040712071f03d0381c0005030848000204030360564440c0500480364643c4821584100105510001c009001c4040004d640600fc1580041c840c074002040c1c41c1e091010318074400000451034070a03145640301701841c5040d4002e204e0001911048480003070300c1507000301045031400640e45820003232034410004203410b000000705400a0f80d41d10102d0900d0b106294080000d01c07119041c000c280a00620012100900030f2000704424544107421440c000d40c4507c2500700300300d4441005441c8807100f00d68100060784288514803107101e0111200d01e0140c001e005851a46581c1c0416045e55 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 611117473 1250 611116223 611116229
    0x3090309092d0b19030210050d021b0304052e030e1603080a0305060415030209070e12031213110f060706052406090a03060b040612061a01080609070804110a 69
    0x102e5a59000081c01d4200006008451110b504002ca11281182d00080455101c5900403003040700c08258541e40480c541d044400c4a44d004c50484035a011048030f6503520f80c00ba000d400e01a5203800c0c004d02901c0d080080c0401c0081c80401d003c070740d1207080c02084004111341078440d0114030602c948101c031045803443c84005140503801c482e59842005101405407003015003120b014614000d10f400388800b075a21004207883c0c0c11240030009807150382c0c0071074014450b0000c1c181d00482c108072048442100000801c080c1c0301050301402e00350b0702d68103074011a20141030007400001c1d030062495441e140c0101440180c02d030040c022401c1c10b049031508400ca850403189e581820240d1048000d0345403029184103c1640d0440f51180344c02c1c0d034030000c118204910302c0005c005030345901c4007042564864214101800204424146007601da040450103400c1518078412903140f03da0b051a100e500c0754aa45204241c080e007418803544501c1706c116055180204103403445503a80344203d80c103540d070120310001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 611118723 1250 611117473 611117561
    0x3121b040f030317060f011805120717121602060712030506090109060b0a0c02033c070f0b0d06031b05040f2a020a050303250309030909 60
    0x1c498290302c0c3c00381c4900d000c0e80b00c0180a007070030400c02100c0e0352090811940c2c48428a0100c000d0000401c041031802c4068014642c000b0801000c10716039440010f00c03804546900081184010200e01520344403800c1d2000100544030800c0000c9004c04083e188668051024240909d07011442e00c81010075941880b05400081e101d20500150b450018106400750000000412240d0701d882000c6e40d06100c2c03c07a48109122f00e072022a001e658007844001e100b030707102d00c0c03d1603844041d00300e00d01c0c020420707000703001d42e001d0905c07000b9801600001400819610825081402c082c10a902014250007201c4507843c0c0d581c42c5c4902000041e10642c0e59101c4c00e0100c851034140c282000104019518224640c19031545041102c85d849680d400d44d407607000038a20035071051202c04c854224141801044098814403002052202c0c4130326020341d0603030a1180d0303091100741072600c16084081e102951000340001e20031800034044802c41350301007002004442c82003800440381858042080d003c40c42c241c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 611119973 1250 611118723 611118749
    0x3130302030c0109080d0c06021303110a0e10091a0d030f0201180b06060702180c030a11091503060f0414043f12090b06030d0f0203121b04 61
    0x110300381008042c000c19024205294128204540203a840301039004000c01c00280041c40750074030416604442d100d40701400f025402c0c94aa0070700704c0ca0000200042401074492560025041004482c070b0345c00b80c5000007450081c01c0c80c01e483c42001d40904076030703455006980c0743c10740d94569070661480318840c03194a8860b40000100b002a00711000da01030001d074003054400e208000742208401aa00c5402242c0f89a291040341c004141003100c241c281c0004241e182d000e00c04100c4400024511500d44484103003c0c25074010b000403600d000303000c003254000000c00da01c5482200754002650380410098039000c5104c03110000101941c2c6208602d004807440302c014827040c0940b050408951820519010010803504d074002c21507601106281400600d048002c600018841c2c0c1041c010341591038010710010015090004c000031041e10610b2083c802c3c203446265050044000c0300c5a00302d150061410545005070b11048548010a00c5000d00b0040c10034240c503030291006403001e0141146002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 611121223 1250 611119973 611119979
    0xf071e0f031b020c12011401090204030c15020a0b09010e15010e0a15090b060d0e0f010e010510030b04020315090616051c0f09140307030e060a020607050a09080313 72
    0x9021074200503015054040c02c10301820b600e41d00092981e0010806484480400c200048414011f1840100c0304031661840f0b000050036820340c1c0c001c2d0054078011701c5941d01c400d5039a9501c0c640710407124561400f40e0021904a00800d003200601d07540281c100001050820b00c0c0360005042103003020f038601d0003039003403030041c00810031300700500c0d03800120322008000960a484144807550814803660b69520f480c1c4042008e907031540001c0e00c0c50301c1004601400140c40003c1c001f51101c000701c2d241c400c01d40c40c050400300b003500305015007801803034107001c044006801d50700d51107240240103005a800d44500c0c080e8600302485042c0311480703965018051b000e01e00300100b20542c0000e501d001e0508012050000042494101614a41c2d8034006440000c00144145050001e089000030290141049070360f562803445c80480280903443c030a5852340358481401040203d6406803024003070050707012100017072106005074018281d2003560b0034401002e9036a40100c606e1035111381e8451140c0b0182032410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 611122473 1250 611121223 611121227
    0x807110c0324060f090610210209120a020a1802041a040e15062502030a03020304060e01090e0a2d09020120100f09050610030b09030c03030f071e0f 65
    0xc0c0350000400c031410315100558200040c0742e200d000c0c044a12822459a0b4000242d008100c0c0c100621300540496140c58845055080250040d0342072b54003c4441c0034504030301b011f020507000107003079000308480b403164100016045d0310a00c00300681903040d400c0201094254000c1400610b030b1540c041e05540e914209819400c403484046d00d0040850030200340b00704035607030f140151394520200c041079001c64020541c103090300320409000a509401110754110506a02200400c1601d4042d120003100c2c0901000466040f2850b1040d61004030000021824800061304844d0102400000e00c0048403140f61041c1c02211860000c560070395913515000d021560001c44d44039803081a00c2c0781460f508800340d0400d03158078070610244220b81e83c070b14600c9030500c0954415400d6542000882f0640d140c9240320b1070341e200b003901040d9080841ca1002508030032001003156624000e14000c2d5085031035840d103c41c40503001400c12800d00c1020407100c04669a104507203422044c096550585c04032000c000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 611123723 1250 611122473 611122543
    0x2004120c05100c1e081909050102070503070302040506060403240c03020903030a0c03050d02040305160807050d1b0e070509041a010c0b10031a0405010606030c0807110c03 75
    0x200768061421161600d68058111034040d0009070050300c41c250b44031a034200c140603410f4058000313048070301c0401c00c0d002c3d070340f440c503640c240c016800d480302100d1036100c0c0010f903500c1400c2e01c100781d07265214413002c1c001414150007190b080b10380640081d041c20344a42d0b542d00d0906105248022200720f4001004100d92a0701030140303400d01c41c0c14114030b0f03d4140001f0039180e114009494061024803140002014850001c40d003108660400841d01d494482c0f626645030020407844d0860200c84050120700d411021510300101d5400510700c2640d98039a0356110b501540004200c104002504030001c0d03080d20b0745072040d01c118801c2d40c41c01d075599180c200f00002c072400310b8021009114082003444450341c02c90f840300e2807180c21000c150069520200c080d06800351302e8200800b403105018003010001509100240600d120f400240003a5444070300403801c6031003c1883c10001260400460012400742440d249010002d2007035070b00c608200c1002c64500640c400d049400c09a841a040818120080c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 611124973 1250 611123723 611123729
    0x160305011d04020613150e040506030309010207032010030b0405151318050d17091b01050c010e070e0711061905090a0609080403150b0102102004120c 66
    0x1c0c0311884030802891485000704000c000900802d00051119500d02601842c00010101c4800c0c2510034002e848008001890f0300e040390b80640e0405020404500d804000c0e80e44018040e802083c029180d600c0c0c84200c120709454181144110b2107000300300340c843c0951520b841c50b9580300881c4201c100b030144422500c0081420314100001003400312103070354a91040e46c0e00b850000c00400d04030400d02e406801c4c04c601c00c0c0300810700e1082e20008160303070f40c026043e240d400e003190041040d241e5a2004880d1078000d501075140701e003642422400740541c01080584005454040001100e04140703040c1858150980c202072a100044020410300e41c1d4005128080c003101c4002920590514203030410262031100f240d5102561507400140100d101007080c445003e030020814440c0c040d590820321346c9a406800255945001d4100900000c8200d00076460102c0d0181c0c002c05850106c80c10100061541000700080900c0c1c440d0701121424150000d000070b80a40d40002a00407075601d401000c030b001d194 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 611126223 1250 611124973 611124989
    0xa0c0903121d030615010302030c04050a0f030b07050313020d3f02030702030303010510140a0f0e010806010f0f050f0c010e070504091a0402030a0605010909031218080c120316030501 80
    0xb03030401085171078401031021014800e00b40035071a500c40312404a528016500100d800510800d400609148135100000842e401564a91040e0b22962005c0380c1511044400c0f440d01c0c03c0d004401001828110500c054480c050003070455030b005002803101d4004080c112444420442500c0d4607480f088203e00d00d220101680021883d00d03d842d40402c1d2280414400d0134440c0d80d20650000c0c02d10f00540c80a802c42640e89080e50741c40d844400c1c0580403d1122041384002544d0888003480b40d402050898006c010585510410380d074003000440304040c0340e042c9902040340138840d043e00c841d920000b0300b000701e200030004030388142044195454160b00d940414492030610011602244556001c0034800b5080e183c112056039039400428a81701050324001d10341072034a800040c100a05a10070081140b0940e00c03030181392580b9580b081606c140110359440160200c01d1880001c040c003000340f002c3c40001d815900441074402c110901a002100c0c2d51414240702c0a1010b03061307505114060142900e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 611127473 1250 611126223 611126233
    0x703060f1b1b0605090c21240c0a110102030a0e15010f151b0b011d0c0301050d0f061b080a0606080403120b030106031b1d0a0c0903121d03 61
    0x142c80c8100d5010300d885000b80c4040e03561004100d43d0b500503c070700d5413041c201514291481440030311180381800d0050100a240c0201652954480c0b40c7c0f2641d2445213155002014268562620340010342e401800c8242c24402c00c802d100201da2422f0001d90f103c1c1e00c204400242c2d034040b15001c4c90501d008014000e002c1086003005100840d050444102954060850961740302818182038806a12000440400d40e240400e00790800c86510300c3c481c11307118440d10340c802060000f00c06000000007500c80c0607002c1418801070249040024030f01a1041c020300c80c103207642001c2d8072940200e402201183c000d00415503804000310f500104020f030850a466420010b4a1400304014036080024000408000718407201d01d000d052240c221138030040006008120441d81e0b8a003040c4c1c3d2182050041001002c00c8200090303101100c0c0c0000104894100003822a9aa5801541c014001c8404400900904d041e0103c0030807500e541200501681340c0b151600300c8040c400d40454a80300c11030052090b448 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 611128723 1250 611127473 611127497
    0x50a02090a1707060e0307030506010f05100302120106030b22020c0607082404021c0902010e010f1403040609050d1214060f040e07091112160813050703060f1b 70
    0x20003d4148100c2d5440d15000c4040d4100300e0000b400c01c0078546c0082c0541c4214000810310810305682041101c0c030481380008003a0420030141c0c140c1c02400078500740c6220603001049401e0094001e0086c4c614010203e030090308202610704040b05003104907541403607001c90b8101d0b07108020485950040d569090950007441d00c117501c11444820b5401481941c074407950504403d40b00e58041d110610341310701c2801e1242c05090348171070007010000d0040e80094080d2006565a50164510310800031540d41d600512002c101e03203075103480e8405441150f600d80d403005000c02040c0c0500880b140101240d6400c201781c3c1c06415004203031000e1340c280705c0c040401c281c1408031541c0c409001c2e1084100036140402c1150300c2920356030501189a10400445040400f003005001c00c41e0000d1080340c1d00307008800c00715294400c21180011350305c88083e01003180c0c5400304429409034503120300350f94450022a000f00340c6a541c0c0341c00743c0b034003103002802c2c507600d43d81c091007070707008602c10038040750b07228980100d409003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 611129973 1250 611128723 611128769
    0x609031002090402090907020a03121a042324062809030516030201090b03010509280c092c16030b090f07020607050c0d050c10050a02090a 61
    0x1100c108645015a00003035840050701d80f60181c0300e080100404400c02c40c9032104000c0d44440c944007048002400c0c0c03100912003d609489071072104405100051010080c0c00f0a1000500700e050145408005d1404162101c4804040180c801c43c940c5d02000c42a0822800f910708240e0400b0300780744109000d0061a5030801e444401ca503003000101c0100160b200c032075400b41c0360301d12241c0016086004108000014084130781408040ba1301c05e0342e8024115940b500c1c0c46260b404203008140d40000c0480218064441d03a10070744001c8000020b842d04410800d41004045409864401011412280003001172510007410681b4616040c0441d2a2640644005032000320005040510496200c03518140031032003644109690799004d4035120060800d101e481c19600740c111411401440790400042c0c2051050741507904c4182c502d401842444420601a01c0c90b800c03094684480d4401c20b20038241031200b6014042c02044080700041e03940401d203041c005515001e8100011080c0c0060b50826050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 611131223 1250 611129973 611129983
    0x8010b0a0203030408210103030305071205240a0b0406021c020c030601030201050d1103011409070c0309030f0602091c150c1b14060c0a08220b060a09060b0c0c060903 73
    0x80c0d0059900382d50303540f106c078618040c3c6003013011a074041c414180007100b01505540803a020700401d803a162403151100031210251501100e10315845409041500322078840941c16000d40580106040d0582d602c401110109800940c00140180c1c00001c541030000203001407002174084500c00b51003108030340800300e640d602040c4070080c10040005480da200108552119a2260b25001c042d540d82d656400c180f41c11000102d8402c0c403681c4e501c404036000601441d0340820355039268071a038400900d1600c0710b0381803030300342c1d07030280c07480364080190300c0c09551120b44446208000340b0401441e500d160410314048001e0b480043d00062a10fa20f51f0708080d000645070100d4100040c810440c10480d1614480400d01070720000b0303091149500b8410f000030350001034100040300740d451001c030703a5456241d0b00c9400103c541595030034000e141400d020501c9400511350202d40a4005030111755904581d100311141a40404a052000b007a58105103409200640680c5401c03288181020308060020341c8074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 611132473 1250 611131223 611131231
    0x3090503030f19022a03130303050906070b091024050d0c0e07050304060b010c0210080406110301082404051507030f061701051e0a110403020406030309050108010b0a020303 76
    0x90600e000841c0e9407016281c80c0340f88000b0220941d00e681000d026449100156964142d41810086031040c01e03020000c240d4186111010350000e000d45907480643c3e0541c044500c5580000c02000000049018112000d0040ca1004000c0806501e0340c280e80d4110b032480f24681310f1103512804e40541f00309100400d642610801c981d500700c0c2d1415403400021085046d40050280600782d02041040c0742c000d0051440b40e400b46006021210b049001100d0364162100001e500018040d28505294031030000300341e00522039140080c1040a03005400c865401c26400b0720169401410040b04071003601404981c43d85943e05607030601e060a44d14140c451032070199a0001d0403c0c00000751045100b034100c2e51203030030390040820002d9120f06501255640c0d004180e00158207140100d002911401c851040311003282611a40b6600d5140000300030b0490021000d0031404184000f00c00340e6503d100b4000210721a44501c51020318080002d8050041684068410340050001085130b58010003101c1d88 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 611133723 1250 611132473 611132491
    0x70f080601110109062c0106060203040315150b031503010504080f21151c0b0c0306030c09090601050405010608090307030f0507050316053a0c0503030a060e06010309050303 76
    0x62215202e41050040a0001c800342400c0d0416034100b4540401e803041000303070104040419102c1000c4208036081c1d82091040a00690042004201003112035102200107504040c020a0140b110030426000346100d4000350071048000013070060f45450f11901c0010404254020301180c0340c00c0d00c0f5265140a8810000c0121a00041003807200c0228812608401000508103155007000144e401d10340c15040700c1c403402201440011b05040b081090000c0c40c00ba0b0252020889a9401c2d400180301d81010b450a9090300c50751050001540d59914141d124151a8000b407600750f242c00200b109403032040c0d00c14010320200c0e4041c0002c0c540040220380801d50141811203001d8121102200e162058504c050198040440c4900e01501c100030a481c035207000da01218030159103041400c2d5407095840300c18004120155114505480c01c145105400306203081c00701040700d25458040c1180d00072140290141d980740d07000d000300400d40c44d205401403028601005660382980d200e980d01e01c006807500700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 611134973 1250 611133723 611133737
    0x200711011b0b04060b1207060509210628060608160309030804030c050a08030108010203040311010e0705090c0d110309060f040305180f0622050d050705010c0609050d1205070f080601 80
    0x1403540310b005072002d01001b404111404199240300c0244560804150140708020321360002b130540300d5800000c568804201c0280442d6120385800242070441e4101d150b0940240d141e135110800841e10610004104039101c1603241c0c5412540b00210056013800c010a05240c070501e140440c0d400710480758031680c9402d040840c1110b605000d440e084001d91b0080004200100108072a070040d0051801075101e510303504402e05070004904d081e00e260514440d40c1754000141040a4036000b41490303000303d082c4000500d40021303100c2c0c40094400c51001221002000002d0007061001080007590080c4030711500b04031f90400360f600a2031440b0302050504001d2200780311010903540c41d0903c0034941c9000348500d945e82e18441000500749400c1c200a40d400c404100c00141e503080c0405520310855201c030107891864200801940c4052241109895407551024140e001807c1042140c1400d403250b20384010100c0741c5c076910b00a45070003c000404020b81d541d801200d14be0003807600c540201003400c01d51 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 611136223 1250 611134973 611134991
    0xa080f040f0204021b0f07080d0309031209110102060c0906040306020d020c06180106060806130c09030f033605150c01060f080d05070510200711011b0b0406 69
    0x4121030700100c1c06980b0920010b8400b81140c03005001c0941c052070401070751030302c100e94026507880780c4051040c24910f800550a002d2036512aa0001071164171a0801070414910320400c0411a00710010856807004030498454040d80c0400410b9032045105800304c2ca0803001074040748550169100080289801048041d0745035081d0b01502e5507020104126003251808480034000c483c04030710064004e518044000c681c4074400d01c0d40921a05000d042d00307041c9048400c1e514002d003004421f00301000140040400000d0490303140c0241c0e980179580e80c041010380240c2e000110303036600308801501802c611040300c201450f5200309040b191300f201c81e40880c800107202e040c507030b11800c10400019442c082000c43d0200e019504001502c4c41791044404120421605a80c0b900c1781c01e00180081d401089404800c1c45250402c108580d181520b00c48181800c84980b541500030040c2183c008814075090091964403107a03400007101000038442580c2000c1d190051000c40284c4050900c0391100541 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 611137473 1250 611136223 611136233
    0x50706181b180c05211909020609060313050715020105010e0415111608130b0c151003120206150105180103050a02090603130b09010c0905010507140d0201020d110a080f04 75
    0x3a603920300403003036004401711040ea02582011011692004180d0020b008070011103072510980313981320341c0502101c2c9008061800c000c0d95070402440100c060180f00300b80c4c000110184000c00040501d0b000903881c400c01500040d0130b481d0140c2220b60f080c4008802c200100701d0241050300021540307140050a41c2041d001c1000b2845034840313912500c500901803801300301001005151500d4071203d1000140d03111031340c040f428450800c0392040c1e50712000c2c5860200365000310300b9800c261950100c1c0f40c1c49549544c0d821214841c84040780c00b680020303007000010040140c10f518041801d1a00c146080c4002c201b05174540c214581d1141019034850000340025407643c11200700d000d0003061182c0300e1401d1301e5604070000100000701c1d410b1900c0c1010030300c805414092114050001d45484070311604090046030640c01040302580c0e031846208c03e0b480303104400c0c4a61700b4500800d07800035960344015412003059078450084280283c80400034082220341c01322100750001891000c0341031300d0b1118101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 611138723 1250 611137473 611137477
    0x160507061d10060e010b0306090703022215110714030a062d050f010308090409150e07060504080c1908030f0405010e0315070e01050706181b180c05 65
    0x580c1c0c0c5654000710001e151050020b01200d4200312424180112619001c0c0c2c4d0301c0011080c86840c07403e84061010900178600600040d61203001d6207401401d010190302c100380b0140c03400c0e0010580c2807130008c051010010100c1c50503124a0241080c0050441c20040c1607a280e005100d81030a0190a10003440c01390307014840c5ca0103030b07900703c503090207100e81c044a140300f01100d0301003d40c2144440b034100c0220a00ca030085a01c50401d0700200c0b5440e80c07841e180c0955a80c0801307892a4815900d10042d000610300000d0096002e100910004150786002e400c0c5103000354a400c0402480001e120400c44d900e4005542010010b0903103420108205ca01441d0100346e00350b400c26940c600011a5038040d0034844809001160005d0340c90503403a402110030b2545452101c104c00402c80d072020700041c20305006150600f84100189800e40c0f8242058a681040300d12801903203e008002d14401000d0240c10080c807070204080e0818040d8861801d6150704003c80b0070b40c0d0f6800055201c81a4244190044003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 611139973 1250 611138723 611138741
    0x141504081e0c06010603060501080903120604020d150305060105011106041403092d06090102060403030b0114041410020309030d11210a1701050604030305071b03050a05070e16050706 80
    0x1d0a070b91144818088075440d62424016200001c1c81c10314009003d61181141c640586060300140d403801100c0e4441583c8243c0042045030415020020001207902900c5250b4920900302010741040d4111314200e41440c00681c0901e04101c4401c0150407442d0000c51001d80081d4000030026010600400f1241103004000c100c41c2e121740208001c114002202c0c801d00c4920400d0000c400c84500c02d2400c00a550058881041c0168030910028001a01941c403c80581c0014108a882d02110f60601c400740c0c1d0094010103010703400c05c0003207000c0f4141000201c200c8036450000c1d40c10714000c140441c0d99a08074140c002e08100100803080d070803031020b00024000014245e003500508403d44103403100b9606c05015400003d0385244500da01d020349100f0305058460040c200361825156450443d0140c01881c000d440340500ea8201d0101c00e07001007400f000a51041d4041c0031004464101070b81840680d50020314080c0d40001007000300e04818072525025031480c200141c4404090400100916502c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 611141223 1250 611139973 611140027
    0x22050a0b0907120606090308030a0e100c02030406030f0e1f0b1e12120405060d0f1a1f0503010510030b0a03030210150b03061210090c0314150408 64
    0xe040c040d00b280c3c4085039030761041601005010b40d594904003220f00c80601d1001416100062000c07960701003407500b0210212703d032401210381c2c0780680e000c01d0f401c071043d44d4090405a0720024080000a4041c011410740d550055810460f00d000e806103107896030600f100c1414000418110b58603010100d40c09020405c50241000300c0c400304041880d017692000744c086a100c0e044504800345501c1c0c00203a94910003ea00c00030b181041d24140503c0041d8001303112103042140c80b002c1803c0d4140c807920404070f882d480350901101c400f2801d4180803e40d8032401910010110002c203003c1800c1e00582101d0455a041c1c59a11a03800e8085c8202c004000c007503049a80005580000802d141e8001600b44c440c1406c0507040000c7c60b40e146007440f241e1301a01c1214070005061000805a15110408015642c0c0c0601a2408200c00e5007504080300c0380c0100886801049400a10503c00c10700f04500b44543c20340e0003414901101c004d1400c550000400081040702e00207100141050318a0786021068160 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 611142473 1250 611141223 611141239
    0x915010311270a06060801050303070515060d0204050a0203060405061017060604170d0e03030a0207030f02180109060305190b04060f0f0c021005220314041a1822050a0b 74
    0x508440f020f4a00c03407080e400081c90110011072240f03000b10840c1d05159004006008452109040c8000144020100c0390701c00d5412042501688650040e2842012003520050307503032500401f00070803500c01400c00e43c0201c61101e0804a401d80044281c0150301d071444100040c2e80e40c11001035000d1066402030650f0004003240b08202010009441a124516841e032580702c010031014581c6c0c0b8000c061004005a0200104002041007410302d030320b03440e00240c2509000800c8210000d22802d0a0380000e00d91a80c0d2001001400018007200200c40e4a20b4288003010a06840d01d8401000190016000c9940c4298844000c010341d0300c03008045116920078004260b49441c00303500c13100740c194402052414840042d1030a00e07014043c207012139800c081c0d8500848251805c40d0341c0d00c403030010f4014110b8200070109039581201e80c0365010315070706100e8640d80c81405044518040201100b5030191090300000e48072144020080505000c603200c0001d22503031001d00400240012501064000c1d084c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 611143723 1250 611142473 611142481
    0xd090e13050619150311010e010509330c0607020c0316051011060705090108060301050124050c010612150b03070612060506181206041106072405091501031127 70
    0x9960380203461b80308240c8404a000c031808006441600c10040b0f0164400048003c0c00107902600d40383d103075681444540e4044440e84d007078038002c0c43c2c4d001c0142c2903102c3e031081e070130060003d0381041074410504060740a0000e081c0100d112101c810981c0c0100c82c0315244101020380418070072a0070101030701d5210110344184c20001400b4096a00c01d41c101c6001a0002c00091000c0c101402003d040329840c107000310f09035448080048410409140041c20850200282103084500740500d80203007011103005000405c4d0303840c10082c00f1007864200c41c0c5081c28607441d040e05580100f200e408454160412141082000350540c00419407600203a91201003c00d50000d01d46841100c044008003d0300c042c1031401f0f4200f040780e070354802100c0007003020441d410703980642c0c103000c006000014461156900000c0c400f9442d100d0f490b840326100340446030f4510400508010070001c1440c45403000b094944554155141c1340c8075044510380e040d00802401804a2803903200500c80e4803113035429806440305040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 611144973 1250 611143723 611143733
    0x4030905010e030109081e070c080106091a0d120210050907090c090b2703030d0c09120305091e0d12090b03010b03061e030d090e130506191503 63
    0x119a01480340081c0d8801c2281c0c42c1414148694440e054001c0415030805502c3c000100704503038081d08035180681c0a000e0b240005101410110143c001180040f42041c00d0840c81c0c0104c80f0800c1c400d0500b1982d084040c0c449494004c0c1c01700c150340d0410741410f0600c962090584c071744480c05203c04074892405c8204404107101207040c070300740c480384c9906001c046100c9504964004950180ca05101d0007005060003518208508c826000001c1148002000c410f000080c00e68203c2e003c01407040f602c42d07020b0240c10340d00030041000340c000025004090500c03520010503e004500c52940540c004007005c00d4428503004940c4490b1500070236801c1407841c5460018807001c84581501c000c201c5207d40071621240c0302c0141c9040e901100c180c1800c0d99524410411a5030000c0071300d40e2001184010307a4542d03101403007d04804d1005850340b1000514181544000c0c2200410030303038680020700480800203002090340f0f90003042102030b20107038a149c108100020300d41040810340701e000100300001080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 611146223 1250 611144973 611144987
    0x323091606030b100f140702040612080909010512070e060d060603030c06050c0f031524040513090308060105071406010603060e10030510230f0f160e01260403 70
    0x32809540360030307404504d0682558400031004040001c0f5040386400940020302e6006409450f00081000c1a82e80c0d0391480740004014810054518540000718200e440c00e0994000e401000103451020300701440f0f10b46951904a01e024a0344244109d0020070031a960768502070b6100c9810a404104117960b074500034180341d041e500200c0d8070504200004290700369440542c1c2042c0c0180d00113914513580c050010440d83c0750180e00d60f80c0b00f440d24090b414888450007651441c0014510203641d07a81c1480200f04000780c080c451a0100c0c0c1c20305002e82d0000764804461a08150300782031180c1c980a107440c0029510b42502c00c079207840d219210000904036030603040071085400000209070207484070891051004000e02000d000ca6214035140112043c0c02c0e4001625007450034272590700d80d42441d0110641c81020b44001e540f00080302c082c0f000d071842c6040c0480d080342c603440c501c0c41c0380d07a500100a891103020024540c14460b421803070042c090000c0440e020f00c10819890003800349017901d0058114 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 611147473 1250 611146223 611146241
    0xc030316030c171807090510080105190e210315100f0f0e030a05030705070b1c150305010e0a0b150619051308100c032309160603 57
    0x2040610a80c2900d0103845070b45890b0260340d803002d4220740c2c3c04000b41d02030300e4098003101d9094502007440040d51400d001883c00382c2400d440100350360815000c01c01c03001c02640c1010303119134900418011004401207007025400c60401c0085240c50341240326900308440c60095402016081c0d100404451103000214400c84540303a185070b5840107501403000e20102c8441c1000400e0106044920f454040c0e14400c04800161a2100030340c000c140110782803803000782c01101c4990001c102141001001d010840203040d00302030300341c100f901603550501d0b800c030312400c0c10107216a5902c52080001c04440154013442d003110092001244000c60170fa44c40c2c40d680d0303003604c0d002e03070700750100d504084032051900781a0380c0201200d040c2504940305138403800500300b1031804d0010400903241d11400d03a40b100d10003031038400050511200d08900d0710043d6043c1049080800d841d000400f02480c1079109440040d094151000794665202e003807846c9400001d000036901c08552010000307200764035410035190 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 611148723 1250 611147473 611147491
    0x40501021b0c1903020f0f030715020606100e01050a12021912050114030d0305060a050306090706110d0516030909021602030709180b1902070b070f210207030c0204020c0303 76
    0x43e1142c5075003584503002400000c1d404070080700034100e00d06d0b083c0404505820024156045640c3d20300150058101d904110409030b0800d50800115240c03242000d2840149814002d410001e26000203001e48610100e400901c5040b0100d0540501c459040e2221419008810310451840350000741c440d207404e00813490810300300000484c2d445070710425010504c90107001480f803a0000c0e20254064038000381041d420034070480f400212aa401c2207102d02a400900213014070600341640101400e014807602009035102480d00b410180c0d02004550040d05008480300480b4024a0226080482d50b4812154180085003071a000c00035040244d141d14800c030121600c456440f2180790a03600000e4500c104000121480400320324070780c8185512078521111510710155040041b000c030b070090301d01a00c2103100c1c1810802c015400490703e85a005150070b00e002028411600c1a2041c0364104481140790f801082050816010b00200012180d00400964543e401d01041700d95030b4004803242d0342 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 611149973 1250 611148723 611148739
    0x80301090504050d02150105040f09051c0206011401020706080405030d050403050405040606021603020405280605121615031d03030f060108090a060b0d061b082d040501021b0c 77
    0x1c2c0e0a0000406d0341d85000c00001c00490b03a032074481000000e000308246100003039110100900007800c03d1200d00c050110000070f1b208541c0c69460002e1404030141c2000c0354000003082082c08507a0001441d50842c0e0301460280c0c01c50340d4600e001400c3d800f883c01a00c2c481d5003003070103000030182c1081c0a402510015101001020f6a0b504100d0340c40301c4800d510034081450350402d10241c28a034110651012003500b0050740c01424501040341d00c14407001540080ea07903981c06000628244000428040b07000c6c008001c02e200d1041059400b0a0511500c1c20403618002e000500d14041e030024103005015240c80211920583d030042d84075442224450781c3c1d42c1c005400254150b019032642401081032500804091000780c1c1d61030001c3c000303d01c440303920540c000310340c20005034140111152100c618032030308070815107130101408941e0b000c1d1030411244022040c840110ba1181b45000d100e2201c840a040e69071a203043c100e0080c4a200c61600c4a4200c0c043c851b40d1951000038183c000075002d0315004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 611151079 1106 611149973 611149993
    0x30c023c0604030806190302010503180106080f010212091906020a030906020d0f060602030a022a1807080603011b08060f10030b0114040e010b070c0308030109050405 73
    0x240040c4c86501000b02d40d0804440030390200c1c90840d00421101d08680c00070b005400700401d100c0070f40d00a01d072201a0b400f002d40211000b040c00ca8203444a140c0c9020a046c082d62280310021160030f6404c010481000d00080c9010038040207280d441c00301d012555a072806503006114103010036498010140c040748103072001b402c45d01384401000901c041ea9445000c26104150701c00802d40d00f0520a40e80e007542c000c20071002c500407496140e1a03810720840d02030100540020a180c21502205240070300c0c006840c55140540c11035140e40308155a008200f6007614412000c10144c4404400952076460042c025a50081da00a103101403001450b004120028040740d212400683c40d040708000035600070005007000c409406101f8a80390500c0e852404850341032040c61100303000003a41c401070181040c40c1c00c028540c880d16007030362540d407010303030002511066400b99400e0103011034079 = true := by decide +kernel

theorem cover : BRFrame.Cov 610971223 611151079 := by
  have h0 := BRFrame.cov_init 610971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 610971223 ≤ n) (h2 : n < 611151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
