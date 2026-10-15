-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4908
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:07:28.868604+00:00
-- url     : https://prove2.me/submissions/b578065c-f14c-4b17-8390-1046f2da085a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 882553956 ≤ n < 882733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 882555206 1250 882553956 882553967
    0x705030406030b09071d060f0a090f15141309060b070c09202101060c0b0c18010c062004061d060912070f0f03031d0f010e010507050109030503040c06 66
    0x1100040030450020045006c40c40002075a0035580c002402245001406038a02d045904102008130010741254402d1102c48420507085000e4100b1406481c165800700c00000c00014a10050040004021904084000101d501c3e000a0f18000700c081c000d40ba212400d0310b15a40011070f098514024042000038100c100b84101d50b0b60301081c901e9121121072030415200c56521002d4100603400c0b42074803c80300904240300d614003a02d00d5542e40420340905007013942c0d12030009800f40c5507001082000c0c0036009584e906d0001c1c441c07000e08188141c034485061584c01000e411040e2074076009101d440f00303800c004801c000c00c00d850440d140d92000d011012441c11140c0342441c12a80c10013010444a1480d181408101440d098200d0450b8491601c400c00c00d83c081400341c0c401034025241d0201402050f030448503040a02c1501110207031005000800a007003020032004180c180024410300e12600e900c074008581885821100a012106482c03170020560b0b030089038240c50020190781c001c90043d2044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 882556456 1250 882555206 882555211
    0x120a0c08150f030a02090a0e0d0e030616270603150b030703110d021305040b030f0a08130e150a05190b0d02070b330a09090c0503030705030406030b09 66
    0x401c40da0345081c0600280a016210364200c154903118044902006a940e03141c041c1c1300d01c134130320008540e0000c1102c0c1c483c07400002582c0c400611401085481c020780300041c40300c1c0c5c071851079824080c0080300041c040d54254100883c3d940c0035980b0000e07900ca1680c1c0c1c0c98441003200c001d03503410004c00d03003136042c40c0203400200d00400002160810116103807038800c0d00523121844100c06528070b8500e040740c000080381d100e0b0054500300d0500074402c21091409100d52803d80c0810b902410110607000c0740c8a8407412040401002d8440103d910f4515510110b0b54402030054004544640d081141c501d070140c240301c0013898801e08410001042c00e09118120407500301800c0c100290850501132031083da41c0105070800d94465003400840c0204042c0c4210502410307007441d41040700381c00040304401c000e00b94003043c0200b2111422200e040c0d11554007240442c0c140c042c0c0042e401003640b500c40d03047c241d40c2e40419810301c80490403401b03015000c8024000c03506e0580b001c0080f020f8201c107010039040d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 882557706 1250 882556456 882556471
    0x170a031d0f1902031e0304080f0a0615080307020d0618030306050a0b04061e0e090a05060103060e09030724050c0307030c14030c1629011208070f0309050303120a0c08 73
    0x5a01707014281842c40c0d42e61000c6840d0780040d2070410341ca42400b98540247c64260811072341c00b840e04242403000314865200c1d00740809440340e000a0405207425901e2080d500000d0040d144040c5160074026258460206040e1103400c020b80085d4905004024003400d00032548075110054002921480800460703003103460680b5181d84e0076450103001f4211420759440b240600103041960005036451001080c882c02095100043e142080c01c001802c440030ba070070142c01c8210150a00501510020664000aa021001c0500f040440c452400c0c0300ea03044c440040b041d401c14041c01510190900954842e0080c0d80c1d080007009a0f14100b180c0750000c0440070941648208007040d80c840380140100040c1910ba070b20011003940560b1611000c0490325048900110780e0134181c43c0c0d4405645100c0e00506004c1c0c0d609a080745a0345644169103c0c040700201003683c00304c4110101401002c52030700415005054945a01d201c003c22940030305c0858581d20755034609140300708100d00030029980503140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 882558956 1250 882557706 882557713
    0x121a04050703030c050c040603140105090f06060409140d0203091c0201080c16051f060b12060d0f05060406140a1b080a140103050f010b03030403170a031d0f190203 72
    0x910340b4103555102c0681c0045c3e62500900e0b004c0c00d41c0d81c6580c041e4600642c407480e05005501c24035040c40c4d084071000740c074460443d009191450301c0d1640010362190055001c03a00051500a40c1c5450409240015817080650113034003c0318403500c0e00400600382a103420713180e9100e441142d444814120703040d100f00030302003611900810328000003c006016680d1032114070021815054955038581620401400200c104480c403902074555680540001045140030f02e908055098103c01901c11000704024041d9520304100024440201030a40c92503070017800759034070b40c242800c102c00a04000848aa410120400440c3c41440f1500c1807002d00a900c00303c005010203510021110f0f680041d1400d1122a207481200c0707005108e03000154000c601c9480103003900740c2e06140b602d09550740e5900140c82030b082440108080391000c068500c2100120500075690001d1070010780040020081105101d41200d00c14110131000041c0d03020307006400b401712111b003588842c1101c1c00c4101842d00941680 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 882560206 1250 882558956 882558959
    0x12110408010e061518130201110105040b0106112e140c0a09050619030c020c1e03011508030409020903121c050c03071205100b0a0f0807030911061e04121a040507 71
    0x400604001c4045205250020343c01c0522798040b0f00b9980203032400e41d0720810b00401000707a01d82142c04019520405070141c018549003201c49400c6101d0b02e8098404201c94040d440b041228681c81038100040404404000c2e0038030048000c2c142d0004003140000c03440400740403031985002415154400b9000c21518900001074004030003800b0144d00003420f604c205500c81040b5900c0d101883c0c00081e2031422900d0200443c0209402e5843e010304080300f1343d50110f004d01180901108450607070342e480c500540e0303030444032010900e0504203c0c0c14020741c10011a5401d54085c0b03100001c2c1201c84100424409902c0303030107070b20046200681e980e4020510070001d25400b410250841c5e6030113490011940c0368290713142c0281d011a4401d0840500141c40c05c40d07140c41154006007070a030001c140307140400140115039100c4002445c00c01c450f901c105004110b68000c1442810344c110001580400162039030703034407503004004c0900c05034222000d030311003a40a00700c00f500c00420307445160400010300081303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 882561456 1250 882560206 882560221
    0xf080304050d090f0f03263106171b030f09010b0103050c0901140c0708030c07080c01020a02060c011b230f040b09010c050109050604110303090112110408010e061518 73
    0x1f810400900403203100c2d038000b942202c004840c0600038039900c80e4400b180d00485000d041c00000c0282403800742c3c4e940f050900344a074a600072111194040c4208043c10a629003c25800c0298903035610700355100c1002041001c400b802100c49030007015810000d001d14003540c07006509a1390b049507090400c22060044980075031040c0501015160050041440c10521640c00303420086190002c5100780d000059103000f0550402c0404010071854010303003400c500442c0000e45841d00703001d010b8400c80c0302003403a5070030200c03e60080320101003c5180c40021142d101c005007a010340410751103002e065800304030080000c0303e4211616a401804d4a40c40d050400c200352a03d50411246107040108a40000c5e000820034415550003600030030082689140c24500b413070300f45080840642c040e80081c0482240c698002051b01050405001d0100c2c0300030307029007402d035140201d6001110030b40c20503807003c03a00c1c0c0c0b010403064050030325280403155480c0c501d420301042e10102c1c0d114240d404002c50004120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 882562706 1250 882561456 882561473
    0x51603060b0925120b041505150a0c06110c01150302010207060f09050d030507150212060f0108070e030c10051206010903030903030807020a140f2802010c0f080304050d090f0f03 78
    0x2000d44c840000148030354404041000c03945078581c2c40e0a103510015040c055840d00c4001c2d0328101100e40c3c1da070f51800451480041c00060b03451b2004004545550703145050700100810381d00041d042e00c2c000c1204148240b1250072031140b91005902600400f800820994071a5010000d1781c007107a22443d20542c9004180070505200d030200390200001800000c4c0003032460400560311101c40603000d41c44500c0ca0b4240442e0369400784c03045109200c5416500400d0b40c2028040c1e52040503400c03c20702c040740300380210b030629140b02c40066000f60903d041641058009015040c81c0d02c0c805843d006668501c8010b5560311b01c1da0201a02181d181482080013038402c01007030307902a02d03e00c1a520040c2c1071340d44481c0c5110380062081401c1c2c02040c0c000080b45010484806241c95082c80003c8664104056103001c84d40b40da0040d040200c00c0d0701c07150510011004204100d40c0c84861181e80385424240b50f0b07213403110410110002580e90350001001100b05181320f05131417044584004803441e50365240360 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 882563956 1250 882562706 882562727
    0x14040510050f0f0f0d0b030705010e0f040603021216050901050d0206070303020d05240307030305160f08120f0903120703180507030303020d0b010305100e04051603060b0925 76
    0x920400821481400d4090f5401415000c80c4c006401c940303503415003240e40203940d0900300d00e50080e8070101c800c010a81c0d02150101501c8030070f0341c05402c10310811000c039001d440160800b9401071500024100314040004141d0300413260004100a11a00c407030801901c03100a06c01c140d84180b80d1414440075142c044000e00e0781900c80d040051612034603a100e80d041d6070084a070341464003018090702e060b024640303040b500d18a4013140501503544c1507a03000751182c025000d21482d28080c65400b00200081c06c1d120307645640d00b1812140e202c80302e95003450151101100e40b03500b4040320102080a5034400130541d40803800c101a4019160381d10841100100030030f001e00b00c805032100401c103000c86d8003400700c00042c5000340e0b4007503035a81000d91040e050362142801d503810545030008102c1074498a01c015010740d031104c00038021588680c1846c52408070b03c0484609240b0880f8400410480075500441004400380d8403580903540c0e0018500070020080d08810800020311644900705115000644 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 882565206 1250 882563956 882563977
    0x22104080c121504151a09190603050118050c09160e0a0e0906040507050a1d091518120c2508070305060a051602070e19110a1404051005 60
    0x140f032410071070207901091100f51000c2d26a1700c20341e201e003080381c00070380184450078005004407184566213201040300300c94000c2c541d580803a403410500c3c02e03d05045c0c010000460b080802407101c041d41c0d90102904540c1d1410881d06440742e003031400c029041c404019842825400004044403020840907542035802c6016140e00181020001c50302c01c24882c0f095004207028401440e480c41c2c50b18000e45400c1c541d4110714842d6030259010800c6132088110400d050b80004984c40e09525110a51460035600030800244058444100401c20341d901194584001c072081c100d074542140300404045510401442d90f01c2038000d4028400e00e0f01040030b11200c9502e501b180310f06901d590740242401c05415420490b01c6030005800d022414105000307142c1c00c0041e41c41500c0c4a0010b201010355a042c8a200742c040d1040d81c3e4001413a0181c51043c00c940c801030211050160741e0700c614203146190f001e0704446001c41c0040b03042d105441180c1d403d07034081c4c68000d0545030800a04100940b01d6800040030034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 882566456 1250 882565206 882565213
    0x13150f0e04060f06080601020f1902130e010603140c0a14040b011110091419140a0203010216020112060b0301091d07170f06040c05040c050903010606022104080c12 72
    0x90314168943c0010018086556014201d041c62400242031a6a2030340505c3d580d80200c429000910300b40380c000d090180d04442455038040c01c80a14400b03446400114942135290503c000f003845458407090310300410703250544480f110f40310f041110b035a003580500f41345402074091101082c20f20742e06c20104144141056502401210241d500c0c101c503113102814202c0d1140c1802c8204400e9015080900c491b030805401840300700c18400e2031144040001500007241104111020103003404030240c141e8000d4000e55451540c501d07032056140c0d01d46000c88c0010100d036042c2808200c14807544003071329502c0b20a0b510b035910741201880541074800c42c90a40402882c1c2c214405c50b810880c0034001c0c081544d042402c18100b50002c2e0030800442c0c070341c1000e60010810071000030480903265094500c2202c00180000200034225000c0c0140c5080541561801101183c0250001543c0c0000309281742580c01400c503103005d000443c00f4910848070342d584011040c0f029440c24003000780036101c111044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 882567706 1250 882566456 882566459
    0x1170919060b090a02091e03060705070c0308030405061b270102010f0f061a0310030f1406100e060301061d0403050f0304030809100e061f09020a020313150f0e0406 72
    0x180f41c00000fa14191a480d034005210342d85400c1c0140c164002c10600c07684500c40c144c0c0f02c0c1c08a91544002000c0d24100100007030000104000c200c041b0020390341210050741c40e481d06240643c0d85150a0780c290208171321003c006151080b4050882e1100a02c2c00310304118810062914450b03040300405180c10b65482d80244807229038584140084100011004900c0c0c0d4a000b29a5601010840d44103400030001c008100d188105410102c04a03035014040005c85007850600d03014211200c0c00200e0207000f80030a0059881031010b03624140ea2150041d001c4580303031a4100b6088565500c22014040e0020110b2600c003882c0310b4409900601034100b2a1802c1c041c3c809513055540b0840303044011912080074052109405c0208400591503820204103030701c030041c251079440b80d0041692030100c465150a10880803040040350090180e0349040d5180d1424103c003075100d4008a03003a41d5180003103000050404601c0c501d00409601136180d6003410311600e40c0031188001c20010060300140c40d40d50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 882568956 1250 882567706 882567709
    0x9030a0305041113140a27050304031401090201030e03040f0b03100b041205070f050604030809040f230a060608070f030e0a0317160e0d0213090b0601170919060b 71
    0x401d205030194204000503d03080c103d00c521100030011b800d03000098504480c0d15105c2d04002160301c06c05a40100b0186803031038501d4094a103220380c1c0c20080c1b0b081c2d0f0344150115000c4054111a00d154400d80303040c4003038a24a40c000d40e8a002d94410304031541602c074002c00210f40d080d4000c60700101c0440180743e0854445240e8140c070303400303a4800b02e4081c402610703410501c1824086080a41004000424207600c4c060018826018600021b410300200003404c64956690b40c2c40200701c80c2c8000418011158860440c04442c1d924500741850602d014001031031021040c41010184c400e240c4130094140c50340c03c0c2c2242d012000b80e40c07000600d030340d4410301280444100070210215100b03640340340700360815401c0c081c070b205130152a05c2100b01958402d8190550030045188100d80c081e104400000004c2c00051440c200f4552412600d924103080c0b1010300c000c2e122004e2107202c003a00c4030042c4c0113615003041c442040490301013244c0d070000d038160b0b80a5180b015851401500a060200ea003d15400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 882570206 1250 882568956 882568969
    0x51c151814070f1a0a111905010c02010b0d0803072016060f0f36090c110a031b080d050702070512071a0c010612080a02070e09030a03050411 62
    0x40a070350340c03206400b00584900c082c60b40f8080d01480350f510518074101c0301e419446006507020030f002d0060400f244182804100010448440c8005401c050b40100d8103009008120703040c07032800154207048150203103090640746000c1040d48030980c2c9144d075a441008544001d01445003200318008900010b409010030004411903d40c0420b451030301a28115010709248600c030240401d001c04480019820354200004126a002c04944910003101544450301003a8801c0e51b07864a03881c0285011400328101e9001e400c1404030b5499076885141482c40040c0e84000701c07913000b800500503034000c0308002da00140b07a4404900ca4048981041e929414a409441c03045510000590080b2010004c600d020030208802851110141c4904c500b02107040d000059504101401c40f2000100307002c48480c00d40c4070b0b40003000f01c40481c0c0c200192a1400f072032175501003107001006104200380407a0031140310700c02034011744164004501c0c2443d101800d6000d420024426a0003807807a902c1d501c8a5103815 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 882571456 1250 882570206 882570233
    0x90323030f0a08010e0f0f06040b030f030306030c06070209070507110402121504060815060d020324090303010e01060f0e1f030e0c030c13090f03050301051c1518 71
    0x880a098460316542d4000b00a400141c0c04444590400e9044c0607400b030140d0203480d0054400740041815076508008207000d000004040342e010300c14507203560a503120210145000704000c80c241c0304901c40d041c040103000e01503008080d61184242010480d00d5020300014503600f8415190000020410030020301242c01c8074004610030701907801003103903101c0e207140002c4e450402107400704483c1d414200b14641e60845020764404401c011000314517103a503140e080c2c251043e4001e04503100810180402580001100c1503010b6681e451801305031115004030950341a84c0d024404045180c0c03070f101049810180d00c040e642c060180711020304107552150150100c00f0840300001044d4214000300c01400c442c404041e0341c007540c000040c00041690301280445220b003080b00d56041200c00321191800614100000a103031403022300140c410180c1141c00745040b05c4040314084218050301a90101038203618400400082828100e440ca00340b460380824131408031900740080c0000266181c00c10107008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 882572706 1250 882571456 882571477
    0xc0309050906011e1229031506010e0d0b04080c0d0903020609040519050103030818010603380f0114090601140d020c01090501020c0d1e120f151802040609032303 71
    0x2c07003c0c003c0b4003c028861151b0000c426030051002600c0d06050508003600504403c0c1084640a0205045d07520002c3d01090781d41c002141071030038103080ca05820950710020500c1c18074081c050841a501c2d001e40080d0301242d4015108614040c0641c00b004024000106008508136000325410581c500c1e078407030136000e18840d40f40c44086084c01c940c00112001a9881141e0b80ea04140c0244001980c00004035075400040000302804620310411110f374900c0305440c17068090303542d0704106180359070048031130480d500c070724032a148401200203108074030408070b03180c5001c11514044c01c1d8030001480011b040c04603400400504029034043c95500b9074211500944580c0c0d008140c1c004106004c0c0b1404d01146034508101e254081c000a01d0390310480c00b48942014441c0c0005030305441c0703581f81c00080400d040c2c46410828403404040070001082540500c403020b10045100e00c000000d28400c032400d44540d85c4030b64a2081c656030b201d800c4940c0c0347e110081c60b400d802c42c0c400d0020100b0009048403500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 882573956 1250 882572706 882572741
    0x2a080a03030519060b0d090201020f0d03200a170903130305010603060b060a020712050114010b12070302090d0f0c120312050702060f04021e030601060c0309050906011e12 75
    0x400b500e43c502160030398000c80d002d0616141d420440b2101940481e41c00091250011a11a00500041c1d0074106441140d42007805181c140c080b1a65160340501400540004852400340405d00090982d01542c02007101150003085d0004802d101466055030250150040368500480000300c40607000b038652044605039110107050041024501420154600a84590303081002c3d065000707580d03122134030842030792001c00d80d803010070300c1310a4101c550000007a55402145507511102c9240d11b0f0f0011503207982000081e0b0105900038824000c40f00c8203540101140341215040d207d2068540e51150308842c1030280e07590001d154207840303207620807a501070744881e290b9043c641d0004040e12001442002150002ca082001d8598143c0420f5001601a506240b039481039031451400a618810803541c07510a060002594076440f801aa101c54131035a107030940540e450090044041054407480c0c0403031a02c03032031088000f01820205a09400b1890514110400c04030380c0c0045071052034034824100d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 882575206 1250 882573956 882573961
    0x181308190206130b0705070f020a0e060906030f071401170a06061106060924090f0702010b03010e0c3a030f05130512070e0c030403020c010c2a080a030305 68
    0xa070148400c5500c0212080140e401e65515a156100f000000b0300720381c1888400301e00c440510002003511070499501918540040d5200c00c0705c034600e12811210180301c0e504d15400500107050100b4290550b03181c50009000f0b00c0d00307000c414078444030350041060420016124800011111348080b60041540310310000c0da25080c03490041c660080381c050001c0650040c400d20140c0d464813480035a0000790510943e0503044480c0c2c6030341d000103100da016940304203450140504441100000f0b80118182c0c4c0080103603848241c14142070f106c000f41080601d0704104590210340c1000c502030300e01e40080d82a140c24148000c040000c0700c0401d69441d118841032050f102c0308054000a90f0031031000d65090182c280090f206061042e2a118040d203409284180c1c07004001540400c0600060000c0402c000c01038648440100c0407608200d4085e4010b02c03034400c041180d5409218406806074004080c80101c0b036440b610b10100a401318484290020091400142e42c1d0f420700c5043c400c24869a008584c070f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 882576456 1250 882575206 882575257
    0x10612111005040b03060103020403060c0f031b0c0803041b08030309011422020a120b09010b040c0c290a0c0905040506010c031202040f03050f010f0b181308 69
    0x500d0400c10328059041800510001904042500c0c1280e1003120199a242d0f1a6401280a401194401052141041001448207400c00405114810382c1c2d50100141340d0145225400c600119000ea00841c400b0040312010450110046500901a2080d10703010141c00c001c607010740c500366001d11103075000401071101d07940003070007042c48207021065403c0840c1131203020901241000e94140140e0a12001140d0840d21440310003002002c00303441180903000307507003400425140c0855040c07200354604045103006107854400c0d0181d200040c0d440000305010b990314043c440d04614800403100b0154080304010140c16840c09105102d031010201c0c1000d40c48401418400303041d00180d1286041c00200601a42d2182400b6945605403603d101402440d96090000f80301b0368124400003040900c02005202e40001c00786038071f0b13136001c008000c100002680d00040354880340c0101c0e80070825004400042051740d142c250800038000400c603190185903508140c913400302050701085070035403010140c070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 882577706 1250 882576456 882576473
    0x703032a02030403030f0c0c0e0a110c0706120221041103010501031a070e150a030b090709030c080118060b040209030d090609050a030510240605090901120f1112010612 74
    0x20700c0642131043d0f8051f0b541c3e8070000109014040d9080459100307000a00d074400c283c00a80704895000ea1695480d20095071298030b031308090090341c0100c2d0440d95030f03c910105900c225281e0024405102400c541c1400390700450b40c0000d8000e0f1144480344c03400e035601d550300f807250900a6100c1c13800e4042c40503d10140341c1c450b240040c80c3c80c040c480a482041595103038030100200d07100800c44643e40d00d074481f51007a4002e00c220075130290416440403c0020007500154541c090382c0c00b440341c40d01c40c19036410406007038880c04003480551503010240040041e210350498107180d8030041c03016040070b00440100e460181c0c055002000201007c000f0442c044e008070121014013010380f0107140550031500e4065a0713240340c1c010303042442d545285011020407410414550102c4504888980300d9031248020015013105c1d6040b0312812010000141c82155100f144082c1c680c0000c00c4018101c40741c46062014110050307841d00010300c480851407061080c0304401c00340417100035140620a140c00c10200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 882578956 1250 882577706 882577727
    0x111b04060b030f0109020901051b061f240905040203130b070323040311030c0a120c0336031b0602010c1704080403290702030f0703032a0203040303 65
    0x541c11000c0003402416100b0003603080c191448250050b030f84401040040700c00f072040241031002030075811443d407007125000c10094060580d1090f034040d510034030803100740c14104078030400001e8142c002c0e107800d49502041310052034140d0760400b0814a640d400114040c0d910880e00340c2d010b80b2220b908401002111104070b0303040942494200110500052813070202c02454450049000c41200051b0800d40720303401110b080100d00c1c0640c1d440d09200d501c11641c44440d504210350814043c0c08203001241f181c40e0050130290140c1e10034000c01814940c1c8450f00e081d4041c0c000c801c221007803d030f14005401d020280d00840c491200008506c14989128081c00d00d180c01c02400c41e41042c2180110704d62040407885c142c1d10364441044030b40c44038034103422a0320603640000c15401d080c2500c602c03881d80c0d444c500081503900c542c3e01146903441400032a140d1007030442a040c240401d211160200748281d008503508194071014090900075040b102d41c507090b0b07211b041e1005030320019082c01015400010f0b0781 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 882580206 1250 882578956 882578969
    0x370f0903170907090914011107030215040b06010507170a0207050f04020f03041e020934020601170a060207050304030510021602150714010506030f16090c111b0406 72
    0x4600342059010340780c032410f0134810702e00100d4032001801c0601144c4c020045410903900c000b002000c01d070044001c2c3c0764002c2c907400e40240c025441071400501c00541e0103440340783c0c4084d21200302e64624006540903040004151912698600001c28050200c4001c0004150640080044030702d040200030078071a01c441e00b24003070350050011048030f0005a042d40d03000307030340130550501760030801410204500409101940c0030f46d000080c000c90101420915239040d000004070105550810080951181103000399001603109000410003004410b41032081d5400c600c007074405941c019150001a0b8000c10030540d101d4100040800800c041040450220f003c2a00d01394104580300c0e03409416a0300030200a4000c03558a151100501041e10031a40c0041e401072084000804c1180c80f00c0c0282020dc503003a010340b0a4030103081ca04203001401009039070307201b03241d41844c070304041c9010081d1001d03803282c00603c6460f9500001100017480f04a003000d512400d22000c40d0f09400410056880c954010b5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 882581456 1250 882580206 882580247
    0x1502091221040e0a0e0a0812041a04050d110f030f03180a0f020d061d01060f091116020f1017010b070b1b25021206370f0903 55
    0x400814414150240d03100c000344000054110500305e9450810886a030010800400002c0341e6124412101a0f14000c90280002080c4400c40034066a029441039070050400d6000300c104010940c41484a00e80b148850402e4580b845042403901c0c0c035540024010520020300401001810088000500040c4e2071030001402150f245444044840c03e910700302134010031000780c514003441180d400100d41c0800c0c0007007051082103904003681c000c08081c00b8844182c404501c0000311070700c450144ac810b201100c125a490200e031245c003036012402c5140c0882e0005002071030000f065030341d05207107400c5482ca074072480c8558034860001007040105821602420b40180061404a090814000d5004040c104040b4210002d00c7c1c13000814000c810000d128841c4591024410a1500d03450b5000c191090b141e00d10428030b50039100b03440d16403c403520041400351244da07070088020320300100391068403514400880018204c010b4140c4505010345078496448071500b804241e030201884003408040040c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 882582706 1250 882581456 882581459
    0xd0f1a031903050c03090a090f06090b151c020a081e010e01060e0d0c090b1e03030f0a030207020d030f1101060f0b0705030c160501080112050a150209122104 69
    0x30a400c00c1c818200903080202c0804c0503003104c4801c0085410001c0c000780b40c82c0c49203a03a103602e48054250034107807a148a0500ca00040c0e071480600440f01030b41c0004041c54000c042d403082c0e045503500296141158402c5840300501c08900600c006e202c1890140e80c1c1c20414a400900250401c00c0d402c00c1008200f00030004001203c0c0c85000d8a06541d1913240c031600703a0750888006030188144090240ac25800b8480000b4003d8507030340210304403039041d900d0752181c02501c2131000e8a41484c040c00358054004001c440701c6000881c0c02030001d00c03243e050040c1410965000b00b10350900c508002c502240114480560281d04904011958030b200350084c4805401c00c80f0700d040200d41440741035441c45010441d202000007e1050b40c00c1e101c085002c603640000e0008003500c0c085150710915000c500400000700c0c0740e040c03424841150941000007000703800c04c6603990925500404440c0c41c50340e40d080c042141ea0356603010700c0c84001c070880c1e4002c11800384454540036540304902d039a0031010104100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 882583956 1250 882582706 882582733
    0xc010e01050315100216060e100302032d0f0c130e070207080a1505060616120908012306040608060f090a0c0e0a150602061b0d0f1a03 59
    0x1084424010078a0801c0e1a501c500440d02c0306800d405568503446148110842c00c01c3d6800515011140040d582d4a040c03140d0700d51080d103540307030360082c80d89e04802030141244500d402900115044982c058180d48040306035501c0d000b21089500d611540040f0718014031014807a00030381a5003200721f82500c185041000d42603081240c0061281c6070180702080c0000d40154000d011000c020000c0300183c440010251800f90080c003a121a8105464641001b03d0680d0918006450b068421030900001e0b1403080d84610301e90480c000c0b1808200324000c000840c010340c0038040c0185c1000c0b810015900355a007640c5c482c003c0c00004000601582c074100c020001c15000007412038111911441c10b145545840840c1410210301c4d0401411b0071a124000040060400070044d01c1741580c0c1c482004000c6200068000b440c1542c03107003000507403010010902c8025040c000780f600c5001404854903000207100a2020b4079064445200d10f00c0d40c8184601d200070140a80c2c080c2c0303402c200c2c042c21384000e000300c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 882585206 1250 882583956 882583967
    0x20a090204061b080c16050a0f0e0a0218060c01020705060604110a0e0f040e0f0c0301051b13050a18060801020901091703040819120806090604020702180f04140c01 72
    0x780030580100003c0071036014020303000c0480386107401080990f04211209900601c0c442c04612485001d001d030a0000108110000c4d640c005031181c200d10203440d40c4403141d00340d000e50404220501d100000d00060420ba81c0d421006009030003600c4009604c4007041d04000741400001000c2500550409041c40050300002088555900d003504020000c521000c01140050340906040d90b04585400440340307501100003029102d010329142240e01c0f07041c3d0b09007803500340d98040d5801c480c6078502a15031003081044601a054085040001100715961900018003a4407964080301d25007004003000e2a0101c418080c50b00600010002989442c0d8014002000690148111345175480050074104a03c1410700458000b852017008440b0443d11411a00c103104c0c82c08003040b00c040e1010300c0c0890703085014016040c41902c0040507034000c0c3c0d4808052001a6201c05000c0360b2240f002d01e8a860140800156035001d10040d00741132000b4079281c50800304034a04210341285035401076190318441c0c1e9001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 882586456 1250 882585206 882585227
    0xe040b071d1018090e0a23030d112b0c091d1e010303020c040c0804020f0918120c251e080a050f48030303010f03020a09020406 56
    0x189088400a41440303000c0d070304810f080d045418a5170038070b180282c00e040c0009041e460f60b8007841c641d1074a40c0030414081c0203412202c8110000360018064a040440c460740300032060040c80754601e141161000010300001031600d800c0c1c2c0c0d2311804040c060300c010083d00c101e6203214018203044054504006040202842000741004581d148100040910080c084c4489066450b10390060041d41c491038065140c00222140a018a10344080d1014442c42400340c18081c03900940300341c070804070010500a241030018a0041c0b003034020180715002440410107014100407010725242c88244203a0b0703c0c0d050582100680001c0803110708200306507950300309004200e83c00e07109940074101e81c010030b10f10340758002c1c0d00070410f0f0700071031880780e080c01008038450082d2001034050740c084640190442000c4080c03041980640044e00c203401c503c41103c569071207425110807461011034800500020b242d64401d8001c200554955001001107050410706c00c0040c1c90b140781e05600b02424908001e10101c803c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 882587706 1250 882586456 882586489
    0x106050316150e100801060f051c0f180506150109031707020d0c06120b0415030f05010f1b020f03160807020109050a0b040302090a090f0f0c0e040b071d 67
    0x403080b4180b03400d009103244070311864080c0016208016080000c0d1800ca424441c050100d43c0381c032000c600d03c900c180200d0712180d400e1141110440041501c0400418010b402c0c8400c0700d507500e6450040841d80802540001d00c40d0340181894135001c0490b5401c1c58200b101b0b079040c400c0c0d01c03000b03100050110001041120000391103d849008500001d1424107504401500702207100901041d42c0e03900140c0000020151181481045586802c1c007003180d50311060500c4507260a0000e00c0044c00e054100c4822601400c00032070700441e4586001c0403108080b130040c0d441310a60750b40d03480c4141c061080407500400340e00594101b20b1039914070015a810100e00600c40100000c0ca45c00310380c050860071016210162164065580340d40e601c0b04c072548140026440751008500140c40c40100340a204e40042e4007060041c084607160f611840e800030541d10880c1d400c96283c0021854103402e6021301e2165002c0e942011147c24140006088020f85615401020301d642e040c5035856100c0b0116070180290 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 882588956 1250 882587706 882587729
    0x3150c03010e040302100501060f08090c010206070c020604050a240903050c0d0f0c09050a0b0402090a0e10090f0507080a090f1203140a0e0d022410030f060507020106050316 76
    0x140e0713103412424851080d51404042c3d1030f201c00822096401280300b484610b003a103403403503207031260004143d07206180c400035801079100e0380008003001d1003903144090103480503040e41e0401d6100c00016004402c4c90300100b90610b442580400d402c9401c000e40380243c181e50030304c03807049400c6450380d5884000c800d00386030040c1c030704d640981c00b040055040c80881e2a0802c00d140070454940350000060801aa01c0940741c908003501c042007844d01d44200d440400b0010068204a484d10f40031880b40c0c000100508228010071070001091000707402000c0c3c20f450307087c3c00000c480c582841c0c040c04a040150080782c51901d00102c80c0005650741c07072507070607050b0020116118030ba04241c3c1200070f04000c245140d201045d034400c0c00201036070394002203c03017650380d1700740d0318025480c40c0b00b01d075a45000109650300b554004400c52410070301d03440342a000752039100d40e01305180e01c03038840781192504000c0417a036060740c40c401c1182d4960b080c414039001c2c083c202c014040031120352500f03462140c980d0207101d040d500b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 882590206 1250 882588956 882588961
    0x70b1b0306060f0f03090604120201020f040e0601020f060408131d13020406080a29090303181203041511041401112e0501120321061a070203150c03010e 67
    0x403041c0c3c1504e900c0101110f80f290344c0c1c0b034040d80030740c3c40f050103840455890300d606406450250040c000e403546104003040d4075003040d103040e404440e10140541041c0c1540030f101400c40900c0c406014070ba10443c096215607136242510401009040415400b11000e901c990341080d03892100d8142e15500013030300207080405249180001401070040e507115005138860f1910440030050800940c00c001d0848080070564270055030340449860f50115086000381e00104001000400a03100d1450418011800c80c1e203284500440d2038020b81c02564141e404c000c510141060700c0d111400303410503000190b14000c0c01c040c9030a5000c046540400540c2d81400035450310400e05100c108014000c0c0c242d10b515018010341060340030f465091130540c048007101d04140000c100c0c141000242c0800d41c0c1e01d030b82c5402c114041080c0f070780034585c4e000b1450007105807519000074a007408090301d980350b1121300146c2695101988109031524000c040645034280130300d0100881c201e500700580c0d0444038074480032201035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 882591456 1250 882590206 882590227
    0x12040602070c2c09060907030803090f0312010503011802010e0411090301051f1403060109021b0601060207050301140103020d06091e030302120c1204230a0503070b1b030606 76
    0x400300c1d40140740c09048010b500c03580c05034444071221000d007040894801c103840e52403c1540345d40d4100c031820990340c403810b401c00002c0d4000b00110791120310b07141510704903920b1504150540e03101c800301910410f04030005210502d02031284501000d403195101c61600d049038000703010448850b088500c01c2f80e40724160700c2409119400c0f00c000000040c0204510300e490351040854a205200302c408801c080300000c1041c100054844204440003401000c40d60320741842207019501902e8012440b4980101c504040c28040004a028100c05d030060050f03941410189401c490582084c4c01c60b0000e00300c010005a150603c4900c5800e40003034011074807810f14244800784284078101c0c2042050118010024194140e02501880c42000346481d000e444040524410340988411040c03040880e80109000810403804c2c40c0d40c402c541e08600d803a15140c94483da06026181009072800d403c0015001c0800400c0543c181d8019910f40e0301e03540300380c9000080411400002d206034080d40c0300040481c00c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 882592706 1250 882591456 882591473
    0x18061b0a03020f12071806020309090c0d0e100c02011e02090103020702090f0a0506040506060306040b0f0307090203040c1a04090b0a0b0c1b03030913090c0b0703180b1204060207 78
    0x10f040c4074150f442c0e0310b42010484209120046640000003074981050440300c00e40500500210340d200c0d8010350810002c0740c20001c0348040038100e420400d038100410800810345000f9600105d006001030416851148450002d4030546441d0004591600f0b02e131030b0080c0b4158450790170b041e14548005884245e00e00058009200710000a94004440710820401415440120744517200200090103181c40d40c000b40016183c007079038181d9210a013813000a816050562025045107001000d4002d28040c2c600480d0510f42d480c4c0050769001d07000000c201c280074400180d0302c000c10a28070242c41500040003039500b640154051020817903250346c00c03004550f8034440500041e010180c0c409680c0d00c3d040c4461a030701d0400e00b0308207521482031244100d90345000300550340c1e81e000240c8042c4403504003004560040c4102c0d4030441d00440400c6010a00d82e100c1006001414400d031640c00503012501c40031044a4202c0d440714a403d141002129a241d50640e000383c3c005501c40f0000da243e0130386181982e00f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 882593956 1250 882592706 882592717
    0x270604080105090a150203040305030705070c0302040203070302071b0503120d0204260f0a020604050f1305070309020a14060a080705070f0501060906140f0f12010203070818061b0a0302 81
    0x420307600700418803c40d00f102060241d60f42d031062110380041140f0300040c10a9000889018010500a000041d07006d4000e800900e030043c0324102d4042841c0c0c50ba07000800301e030030076070b1490002940400d5800c01c12201610b07049076000614925001a40340000080c1d0300c09940c003c003050100e01240b40d242007c443d406440141800342c070354030002e410610b489202004413030400c60961041004170200b080020030f940395903c2e0046c0ca00c0d842d060400c1c0c10302918010584c040b42e0080617040e0b906400701c1191003018061800e650b40403600010301c2c0108808003e158204160010132404001051b55941080b103900f403c190500c054166502c07401540c26015180f00546490f03031045104040041c10b600541c180d41100500f0428692940b42c811020a141610a134012018514094552030000000c02e0312900041c80c0c8101881d805403002d003660815100400811400400d002d003400e4081c008900b4003a01c0002005c0f2858000d40d03265401c03280c140e03071445060f0002220120f541c4250120351 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 882595206 1250 882593956 882593969
    0x504390806040b220c080c013e0313090e0105061206150109030203100e190f1523040c0e090604121e210209150a0e04090501051b270604 60
    0x300c1e00d50ba686e045500c5520704d45115001503105160045c580c111070782c001466400180d08049845100750703000e4652072006010041d20320082c020303d0a204030600e5103c0107480041d8001c2070050015045909482d0068080351050480d00748602100000017a210352180108290704540120000103072208122600701a4050083c0c1c0c0c4420f400c242c00d50011010041030008a541d107904c8141c0d504a245991030005215651503448140411841940d620001d1070140380002d07248110006200380302d040c503402183c0003007c401000240f00d403040e0424020030301c01030f52501e0b51920b40c50311034462100600c000d120b1880c3c0508a40d50b03503c00c041214000c030003404c0d8050f90500c007000162a030240b111130480f0584200e480e5558089a9001390380380e10b000a082b2803c1600c1410b04401e482d000010446d0420040c5201c0102c19134483c0074000040d030040000003900d04000b50700b8861501c07150003482144001700212004180601c02102800c4203d6006980d0441145c00003140d501c030759440311 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 882596456 1250 882595206 882595223
    0xe010501030b070e130606030b12120f0d02090a0f090e0303060906061e0f0c161203050a0c1b032006040b0a031b090f270504390806040b22 61
    0xc11f25540662124a85400480312140d005400e800255075818a01ca800004004103200c00b0340324890703c202401910380b85203405401d0000e100049071b03022070b0b10f03801110380c4849180e007044190001e206080c84404904059072071031500c40d01064800300082c0c40d10f030107550300040c43c2e50300351100c0b009843d00700c8403013030490703602d4410210b10000c541107510004114040d45488080040c00c502400003155813001c00b0440200d00d948080c2c590340c0140b9550400c1c49800c032003000014902a80f401852640400800340035410b40c141902811070708204090507600c043c1e00080d0581d207000588003103d140d088196502c0d074402ca0120042c003840000075402040c28107403164219004007000080c1c1d0403000d00403803000c1e030b03801a84001240d47d5520f141b002c070001d900c3c0d24850f00c40d03400a81d4401e004071002e010240c03042c0b4034140355410055095172440b8141c50025203003840050f0140091074010000e00c10303400c1a1703d41d62034007100580951901c00c000b80307009503180c480481d5150042e81080e0308 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 882597706 1250 882596456 882596459
    0x2040213061808150703090c03140304031502090a030b0a180f1e030e15070b07030507080105030106031104050a0e0d050409050612060f060103060b1b010e010501030b070e1306 77
    0x2912480200e0b201c007101ca007281101154031400007580c0c42c82c00b1055413500780c040e1149042a00100a011030590f101c0c21620304c0440800c182c48440103150103144011903a8a1960a0200504c0110380a85814500402c1400001d9460301d95600c103981d040101342e005a20b42c010310300010481213400c625280d088001503402c0c031000462002d2228081d242d01440003180b90902c25405011140060103c0d902009100c02820000b88100100103003000d2941303403214a4460a0311120f04488100020744c8440c2002501d1b60b000c510359006103800d90080c00300e60300b5030f554005010424400a401039517258001803c1c8841500400c118455420507207400b818803800042c160f074094061610381504180100b002420220600100058454040c00090708c800c000b0840200c800340800c0c1c10151242c401048164001000b040d0540b03003c0d2941003941d0107003420f42e0940b428002c20a0742645080010408a104041010380c01943c034600150074118010000310600d0040f40400c2c803135840c00a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 882598956 1250 882597706 882597719
    0x506090112170c011a03010507030603080f03191803030b09010807061101060b0a0807080f04020a0306050402040e01050a0902011704170a021510050f0a14060c01020c1c110105060a050d02040213 85
    0x481172590301e4140c009000320340c4c4200e0150261f0b0094800246000010003042e03807e14107040c091500100c0f90014044003c08500a40c01940c15040320502600499a0603608160705442190a5880191101402c641c5020842c6460f07880e03030300c100c0060102042606420300c00a51016003c0c03c60000381c552601d00c00303007006140c82d030101c40303050120b4011400700d007440ba0382502d0148115401020408003d09558a5102608000d00101d030001e4417601c40344540ba50a000c2c00d88240b2184d0800103500803140001400808181410310103028000c00b0300c00411a00700c032003982120040031056440c41801f404a03c2c1c0951929041410f00050f01402181000760646100301d82c4122685101c04041400300890000f6911810946155440c0c3c03180d42c40c20102c01030044140f00900060618021a6071f440c1040c3c0101011840714140740503481901350440039410800a54070000c004c1da180a0303000c02c07200380d81e6000d41807140d4030303c07030303080e001c550359901140c200819101314414040d90f140f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 882600206 1250 882598956 882598991
    0x106020d0507020a1202030c131b08040c030f0201180602010b0a060e0f09070e0306160824010c06020c1f060b07020a120f12050d0506090112170c01 65
    0x410005015000004140a1058080d5180b00d50003c0a248445150080b16600d002204100302e070140a6042030700856036800c010040c02c8841c0c110041000030743e9000800889135003036086001d0142142c00c1c0000b0031501d250744410b40e039100b04e02c0b45600800e0b00050390780f401c0110102010301c1781c1030740110b0400d6064006580740c0c00240c42460319141c41da40c041e01c01c003010003a5107402c8204410402c01c10b02c0d140d00200e07040402810105d046d041d040000c03909110f030480d00711080c5072003070000c180000d0344480503d5001c1c1c030740744049920440031400c003109003a80300a8941000007190400d0709001031179044900d001510304c2202c0440b46202c0b100c2c2405d14802d010b00a01d07a140480000361644c8080c2100c41180d4000c003280b100b6801d04070030040341e400e061b03000c3c0c0e01e425100c1d00c18400a0100310304036025115648819464840130341000068510041085005503081c1c0010807425152004001d106580082d4490040300c0d003091025540c029443e40d04499030a1101d0956182e604a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 882601456 1250 882600206 882600209
    0x3070803070201020c150f041101030b10030209190f09020705150103060902030609070b12090a0b07020a11040c080a3602030f0d140a18090515041a041a03100501 71
    0x100540c1c0c030110006e451440c9880b411120501000a0800040e000411010b0f0303a07521078005040c0040c100d40444045010714040c480341e50b0110381d00142e1401d9030f151100b125054070303110800241c000c50600082000b0700d80c840c07040059007900801e00c182000f03014004000046c0c465030050030151780da03041c2080907003045103080e4001c0c05444046102988041141c0c4c080d9010340a5841c500080e40390ba07260403400080000c03030240213109066001884007804640541450360082421900c5030a15030520641540b42070311861400c01c01c1d440c8250482c000320340c025480c1500181c502c0c207081401000e601c200f40110210044d004204420313000114900200500036021109501401e080d001d5503601241c40040c0401d540c1c154401c070440340140107002c1d4001c24a088070301c507540049081c0032a1f1180c0c2040010036201c0040145458800003611038501046034180840e00c0454040301c81010045000e40c007903a11a030006200740d980c0d001462410700302070100d441343c61742a02044000c0200b0f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 882602706 1250 882601456 882601477
    0x515030a0e01110a0e010207090c02030913020711060304030509091008010c0203120f060120060105040b0f010e062203080a02010e070b0f0d0f020c0715210b030307080307020102 78
    0x1c00a0320701405a0511800c5410190303954414607000d0049420390b6140c03000000207045102e03244001c00d18050728002c80c180d04d102d517002140c6800d0a8001c004180f90004200381c0f64503c107212801c0481c030b40f00080308010348103580c070303a270f5903180e034181100d480c441c605501d5003000741c02051109151080704c40300d0880741c0ac1802008401c01c0c80c0e400303e0304c80c8940740217200c14105c02c6003c40c081c4d01e20380880760341001050601140102034a00c040c62503d10000c1585215080040100503608080c001c00e401840c0403100c0c010603406050003e4000030380504c03200d004090101d04402e180710701c035007648640110340c4004207900d6640c3c42c01e0358455010001c814015400e1000c002e45030040007400d4002d488522450381d09000e0702c1c10000c0120b030020700e484d4040715220b10f01d038500201070b48020060032060300d005d05201408c1c41d060310fa521500c0c015030340c06c0140b00c0382070342d00d070840352000030300a01541240800c42c03000e202c0001e4603500070201d01508229000042c4100503405500810a100c0d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 882603956 1250 882602706 882602711
    0x91c060b010e030309040221040606150f1d040b0d110a140102061b04031e021005182206060801080d1d040507090b030a02040311030609190c0515030a 66
    0x94180c01110002020a080d81d056802071080c02d005150a401618400469052404289541d01803a119005042d0b9003511400c4da165800c2c007464501c00d5030142c240c00a0b040925280c3c92818000385141000f44440ca40b01c11100740d121800d9942d50840c942540000703000d500c0300002030900d031409031f00d5100064441c4c017940c10002800000c25200f080244c405801924181d6582c00380c2e041001541504011168001c10000c000508940720388985421102c00820a403a03c0388144100c40c86403804000910409201c15012681c601c0303480c7c180507009460000b8441c2c2616120208100300da62000c8019040c4403000c02e0141c0d00699850481d82c44408865403500151801d8640d000380c1201144603140f40454200181841d81000390003031b107075161680300305559801c80801034005850230448136400107000c00600c170840300507c200c00401ca014145606000a8060780c810f851807190301c0714941030000c4024840ea401172030005000203001005003404041c003202041c0c1c02251480816803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 882605206 1250 882603956 882603971
    0x30d1401080a020f011d03160801050f062103040b0a210c0e0402030408070f120e0301050c1b0709020703090e1317030c1b06160804030906080a02091c06 67
    0x20400038540c000607401800c0345000b04181c1004451b45c00c4054120288110305030040307201d60318200413176940e400c4500702d103a10640c1820006401e542c40902040010a000424411a5078071020201030424006106414981103031154509500803540050507012021602801864010221191010b2000050020032590440e40303812158201a0480040c82c0300c0e941d407040b0700709a4011a04580508110b0341041260355401c0ba080c0800e070360482d00000601c4500414980100115000d001e08400900203441c20405c040000c4c01a0700c200203012860400f1000c800b0f0060100e00090308503401d00755030341d25007030a028008400c03c1c8621102c0401c0c0704000b1703452901c00300b2041d901550200c4509904da00c03181600380250809058116024400c00040381c10341072048820340385107298009840ea91511411a00750b8000e003c03401c1007070222040421001a602101c2c2c032054903020f062001d16926900c1d1024001d0081d2114950056041942040c40044d6407603035016441c80303240c0900586 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 882606456 1250 882605206 882605219
    0xb03010609140f1005060d0b0402031609120201020a0f020604030b13030914100c020a091a03070b16030804060b090906150f130e0109061803080106050702011205060111030d1401 78
    0x41040f541807808844c812000d01441c0b03071200003009124454031020400c81d08600c0080c0c12a882540e03040c03c070440424000d10300680210880c002040000080c445074421030300043e4448580c0700d030040900c01c20103801001c664851090701c02440c1c000300e001040b03150001b41010184049030703003500031a04024001a40090382c504000304031502a010404060342c1c40b1040e130381c1981c0c0f04401ca0340301c0d4100601180040341071003540c49504040102044e4589240240741c00d00040380c000b40320f0440104040030b40320b034003c0349003030a0643c5886c0a4541d5035032811f0000040c800c0141c044e5000700c0d20130900000ca000018424061006203000d00812040c02c0b08003c42c0b03805880040341c009000040d0800300550580c002d0342ca00b0100740010418200a81c1c3d03803000c90303100381c1808182c840040407420902d175110072224050101c9040061800c0440c0e00042c1240c40c4030a4084151611240042c1243e4450201800590030310380c200c0e0b0700e9103440d0220f02c0c0586149458032071035000341400014103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 882607706 1250 882606456 882606481
    0x6070504230a0618090507021b100e12071511010f060f05100e12010c0f030501030201080c0a030b030615030c030718020f0408030a0e040b0402091f02010b0301060914 73
    0xa41d0091100e0915403034968140ca00c03804e00060100461018800068050603c0c020b01d0711a0380c503035028000103007030403203544050854103500710300410400d030190550300e070091811204ca03002203c07000c110101038201245480c0c250703040f80d6070380c103903032030f548402035400540c04140054098001d1080c8040c81015400325240346c80341d40c00b100840042044a0b0806071034030b05a400541c540101d140f2840c001140f880c079040304182d41d00381e43d5520000e81c410350140c0d4480b00c1d1030701c500d42440154555000200b011030050624000301000141c9404030364000d9118400030740d07000e02075440d00d290000c003014003981d407100e290b40640120400880b1034a404981201036401015480310000c22024414009401c8505910030b50b100030000422081c0c400c0000e00103540380c958440c2c158450b09024881a00d580c0d1b452180a14010311a2500560324480400c3c10342410382c084107800c410642e422809488440c1c41c080d00b5510307041c8045643c1342e03103800503541c00c00215610303446c40d116500d51084 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 882608956 1250 882607706 882607769
    0x70305180c04110c0f03030105010810080615062505070f1d070c02060403080301030501060905070e04111b06150306041a0c04320a08280506070504 65
    0x6054100300707001c007114030b040c0c0e003c42410000304000600741400004450304c0d280520f2000342c4c081e071000c40100b100b582d0000035503910400000f151070205103003911310b59695502800450030284003a001e0324054460105032608555030464488a03e4986107581c1c440c0303034200e001510f003805010800324042d161001050200c42e04520506c0d109000ca16401c0c0700040c029011138200040a954103025944001c040c0c00514020714040e5980e51451800030b086134019400703070960a0402081292140d00703e24490f41451041d0340c0820301f8281121b800c6064802c608038840d410542a5100d46000c00001c2ca0074850000a407a010700d00e90080c0401d955440b04440c01031541520003407242640d03c0310384480b1b4110101d002c0c3d10381003c0d1070311403003128500c14283d90400d0442c40503061903015001510000e1468081e01c42506050511a01d01d440341004450301014041d4011140c001300394515000c1032b42a0000150740e541d00381241d0017451742c0c0c40f520072080129607140d104221003280c0c60440a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 882610206 1250 882608956 882609001
    0x151202040e0f120715051905100e060103020703020f100c1202130510050f0304081206010801031205160f29090604060902030a050a03020619021317070807090203070305 74
    0x1502c2c2e0b8850400c1541c4c01218200c503010501a0340c03286003081d500032103028100c60503ca200700150300c50140c08450008003803c5840c0e03510141081a032a5003102c1c00c0d00907000f031a01503520b05003800c081e8500308040c150070001d44100748400002034540d5000c142982c000d55540300f0120218140a0203078011003039000101c0d44180000c0015140c1040400e81000042c144542800040d501e851502d41040724141d036801800501c0c8503920f030000c2c44d01c5912030400d003000034055041d52524124000c882c942102131200001c1e00700e41003484100505a41544000403800340c0e5094507000307082c04035400c501c0c070214500040452182d484000d6451082c03401c64014282a85c1d144c40e20005084142010f980500400c41da40e000f0407420300080395054001d800401c164145800540c80103211040a00714151062100030703141700400311440101c840c14102000162051505603050002d2513018aa99101d5800c00044003201500510301c01c6129032010006079880c4078641e213040350060fa109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 882611456 1250 882610206 882610213
    0x82a091e09180703050102040f0e060d1110022e0c080103112b060c0210020906192006062b120e0409050601031101020a02100c0303151202040e0f 64
    0x14001d00c103512841c04580400742d044510030f650381e4544030300726032164000031500e2003991401d0140d20001d000d03058205c40300740c0d03805800755415110341c101210340c08101c80c0301c0d8003c1e95105000c1e5108202c4800c4800b10001c20300c24041d10b000c0303850000c030041400e00251908104001581e98056400d8038101c0340c01490703141c01c50124600f00b11650002c4200200d011820035001c0300b041d024150090b061320302c5000001240b480c10b140c044c0c5401c0c0d0b0044101081d500410415032907440d03c000f560350083e8100f05880c00b0291020040da84c11031710015000d04000d40c0c502100c0d03070800c000780042c010403040d45c0481c0e041032074170202c1c2d1171543c600020800c51101000000c1c002454026280700e82c0d4810b02d0308003101c0c501c0030001810341e07086910503100307980020018401c0c08107400202c080400300740004c000e20440b0381e000c41d402c0c01254140318144506180c1d01d00030703d80280c00c1103052070300d010822145151a00c1d110007221030590700590055251014201003047c0006804582640401c003c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 882612706 1250 882611456 882611461
    0x409090606050904170307090b071109090d09030b0901020c034003080a030f02040f090b0a0335070309030b1008030d0e0a0f0f02130c09030201082a091e09 68
    0x805e4a141c3c0050021400c10074903060026243c080040034142c003074840c0c030080c0540c505103820090003d1000d080e07240d094105020303403038020360801d0a800860b070340500c943c00980e440d050300c90b0080c010b00014082c240800980211140c00d40b414001651075072501031426010450301c107211501c1d81d010503c58200e000304061010840b6507010b01110003551501058603240340c0c4415060b40c106500441206002100521a403081c41c081d02c40c0c07002c815070364021114919180c0c40e0b0340031808079003194400e10403500b50f050b1410540b176102212081c41100c6541c0c0209240c010150304107403106650700b0186002007459401009581801c0f69040130085050413180c40700100180a00347e401d60742071090b00480c81c0044c0f07003400100c02d92805003018140100702030044c005130186001c80c00741074a02c0d12240c0190990440303203c6081e6a02840c004101d5650418481c1741c601d609245015040c0300500030b400800c0200c001848000c2080d1707900070b0349003800468615011610700c800360b40301107240c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 882613956 1250 882612706 882612743
    0x9060f0c0501090507061101180f02010509030a0b04050a1406040c0512100501180c020a0c0311220603030e0406240918062c040312020c030409090606050904 69
    0x200308585600520000a000d0310030740d6168507100440d403042c404070303d2410400320010070a20400b2004880c1885800f0308030107954807601000e0001d00000c0c180040800c070110030392000c110001c2850ba0100802d0541d0070a42405982e07030b14500b100302c1d50351a003c520a40b030010045401e80c001c651080803203007854146000c00485401c0d4214111061080d448050030107122030042c035000700b030080c00300941360400f189003105480c91007203080255440703d0400000100100102400c40ea000140c222060341c100d80000c4500c06241c205052440341304c500c0b44c00d0300143c1e41c000c81c00ca81c400c0c0c0f2000c1034051141c0600094035880d1103520600d9104c1b021504020010018205814109142507154144c40341546003990018807183c03801c0340c1d40d840c010301c4800302003030100c9101940708c50103e014044004564000d1035004200030104040700b0744040045401e0f4064500001d114000d076919942c8841081d40104002e82050380c1403801c084000402e07062901ca410702458000c4900c5c0c080c810303102c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 882615206 1250 882613956 882613967
    0x603020d0b0a11070b0603061e0705030c160b070801061b060e0a0507030f0512030115030e0f0102030c120c0f030105090712090305071b0b04050411090411040f0609060f 74
    0x701199000740d22015440c10a58004004004c000c2c0b2a81c8460301e2400e00c5c4c0281483d00d00000d0802c2c85005411034800c03068030384013040300c2c0d10000d02e00d003240d502c0c1c0d613518041c03005000b200002600041c400f00701c00d00b00001014800d100c3c040c581c0e503440551307903500c038212140c80b13040340300141c0440e21003950404641d950300071920502410302240c120b10300300c1ea9005d00c1c1c10016802035582240c4103602204002c028481c4a920450750002181154101504189032000d011402c0c1c0615648050300321401ca4148030031400102180c0c0219140d2400f0340c403168066000307803080d0364155070041c00902d41d88964000d5592080c1048040c0b41140e00340b6040c40410f60b800340066090119003418680c030707003500340100d61a0f02e1080c1c1d541c82d110101031a12582a0300c0d0f20701404c0e4a504600350a11401c0c06550030fa4044a2040b2001318845100400c5802a48075003c0e4070340e0420f06005680c00684000c1c002402164648030000b00c039248d80c6e540845110030700c0e0203003200041c09144031519251144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 882616456 1250 882615206 882615211
    0x30c12141c0902090a140903030405030a031e0c110d030603120507080c010f020a08061e060f0d060906050109080601060c060f1107030c060b1e10170c120a0603020d0b 73
    0x1080000b80c060501d40001d10848000c84030342d0003040c1c0710811807024110b8440d103990403840c030354015802c41c2820350f1001e13200d000d4691803804066803580b0114003258400e12320564030041120400c4951000c000050441141d141941164403524000040c1c2d035109114070740480b0f4021005080c455510a012500d40c0d11010050398404018022050b0041081c0b2441000310160100140d0f05d0842c00c00141030010018645c2c0e1048500581031020512020403400d84190f0465100d0303a1040798001c2403200f401000740c08000545000d20115401c02c0640c881006c0d1078003600c0c0c11400b00c0c1c0e0341c2e20240d543c102c24041d060008544101100c0020b0198200040a080000001c503401030001c2000b41c1c584c20144c003e5001443c403070703a0103007407182500c03404241c0401a2161000c41504400c0310894840c0a03200b10b004281a40a40b0017441c0318040100302c810301c00203040c881d4100300c4c0690105800103401107800c0321418010401d103801c0e80c4960011a64060103010221000f6110340001d42c400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 882617706 1250 882616456 882616507
    0x10219080306150a0309120509210f0106060c14241902030c030709050406270608071e0603020412110f0603181005041a0405120304030c1214 62
    0x80d4076020700f096542e9000d48100c540c01d45c0e000072007450b54100307151000a03041d075400911504001c00d181540b0b40114802195044203100d4404000915070b0030b14102078007118202c15403078088089003450b4080c02c00f8030842d0065110303007588a41c0303a841589a16107101d0290018190007031900043e2000c041e941e0b44004004442000030000d50b02d29401d13a48100c2d40300e5460704002040044481e0000740d440040d18090b60200415800c0644140034900d100e0a00c00c980311190300d583d400c40d1a160400c801410b5a68144e80d2025640d0400d80c4c44038a04803500c98603100e905a01040f568424420340d42154203d00407258a684540c4580000c4155558042c0c0c000c218428100165150f580044d8010000781818004000800c2400350400c0501724082c0441400c00080c0301c003061142c006107c1030091111040d00e95211887e1003450000c0c2c00d000004176401c0401004149a04a24640d4040340601e61465403441134a00c1100d006106001c500c2e541c0805100481c0c46203d0042c40440d00b098 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 882618956 1250 882617706 882617719
    0x1051f080705070f1a090f0d0302090f060c07170109020f131415030d08040c050f0d1208042109150e040f1d150613090b0a140105010219080306 63
    0x43d0380c840c9440c0300d529103402d407851100202d806010410080500741d02c030980f07801501d04810740e00000c94031602c1c001e01034002c054000c20354002d681c0e40c0e0300182c6054100142510b582d0000d8034019510784003188120450b000452001c0b403034101041c099941681d41c0100b1001400d8443c0040040e40410b10030104003080da20203d070018000b2280c103c80c090741c00c0159101c80c2501030000c262a00e030a80101000300020380040c400044c5e02a559001683d81c22a2020342155032640401c402e804020720192001d020181541541500320700000d01030350050106401e60010300a05194001080052100080341c508080100a03210b01185600032a50319003081c882c3d1070800040c0c15291060b031042e81035642c03443e540e0b410760701c812001206c00078040084c21a111102d2902441481f00801050003600705c4801c6d012410304c0c543c8410303805a4003007450546410300695100007420350040c043d0f80320044000202d0950300010301d11076080e0890364100610360b6596200d07021500b020f06425003201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 882620206 1250 882618956 882618967
    0x50c040f0207061d100c02100b01020f06040f030818250f0f1508160f0e150909010524090d1e2616050a150605030601051f080705 57
    0xc400e4000e1140d60074501640c030a640090260135400c0c00322076540c0301d203142e1600c40c40b9181d1030b402055004035202c0312903001411840d10801030341001c00701082d85400c0d0007130341c1c04c200411042107840802c2901070f60311103459a503451065130f01508003d01c68000d50303200310340d400b1519582c15020b89964840e81c9075082400d9607501078041540d903d0700400c040780140082400020320480450718140001d103403c0711070303040008087e61041102c001c0002044010840320b00c542c0e010320403034141d00201038960b10b46100701c040380d0045500109000f600c615543d20001a003481c110303d02d242e1400c8200c6404110b43c4c40e58803201c1c1150700250f00341d030700709606c29640300c080f070b41c00901c40142d10b03030204031402000e445180030ba2880c0315130310030342e41030712150160346050306030703c40a031031003c4074142c1d044110810300c0c00c3c0303d0f01e000c40c40807000305165414183e004401080d500b01404440f02078084428503625081006035400c40c58082c1000464101340440307520340702d501c156810a0140c1002ca2904 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 882621456 1250 882620206 882620213
    0x50301020d0c030b0301063b0a05070f021518010b0307080c010809151b09030f010606180e0606090112050c0304231f0605040f1b0507050c040f0207 65
    0x240c010000d0100740a07a00c15488540581502030f14285400482c000c114841c02c0184041c1c1c640a00303c001365001c2d084904168980503042d269900041078500312841e54604000944080d01003103460100140446003000c0c0c1c554000074280100c98100365041d01107513030314101049491102000c403110703076480e0b14800750310352018405500600f031500003a0003240c4044001410860f00074001c100c0c40da01221004100381800c41c51941c00c04810030f040029070040c40b02d9000c403030199403401903050003004100020040705611080c01c036095a11046602010929030501c10b5140384a0030120f00001c000181c402e1034100c004140030401410305420b8480d800041d5012100115012035500300004248424032488aa45801020b40c2d01400d44031043e06a00994a40c4030003d20810010350703228021a4400c0190001000740401410400000402c00c111801900000c0c0302c01044180508a009040348a2411200d61607000402003c1c1108100244001040140d03556188650b00b403010f803000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 882622706 1250 882621456 882621461
    0x114071e090608130c1206060f030804050105090a0e0f0123030307020402160b0a02032410123305010c12050d060302040f020702030106050603070c06110403050a0b01150f05090910050301 82
    0x1b8100b41e0340302101d482060b02e020012240284c01064061003a0365041002030094412181500d00a107806c51312201d028008c100c6110550b044244131080800400c901c140800c5600c0d81200c184d4072001092600c5c01d5030040305d1031a8a40b0190701070304100801c40c050b04207a0000e00c5c880d0540c20b803110282855891729505500c0948141c22059000802e1003e00740450b144900790050101480c0200d040f00340000d01c400241003043c3c0704ac428255640006d03400541e01c83c40c9188115604590002c141404901480305a11205618040b0003000412654030070509104966401042440343c9407244900750740a8103c00c0341608450345510010005807200d02441f00681041c1318090307142c140502c109402d48035160044c0307000d6441802040241588508040f41b00c81c0c205000094541c002c990440c0c081c411a00080c11070710400c1c4082e0100646003013058102c9041440320701070080c0c00c580c11986410070318410800540240b1088200cfd25092465503040000c044a040d0709664900c00f003402d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 882623956 1250 882622706 882622709
    0x60c0f06140106020c0a050a03140a0204020f0a200d0804050c030a140d0c02010503010b090a1505030f093013140a0b0c1e030c0114071e090608130c 65
    0xe501d00e040c00100240c680412480c1c07840c03d02100e041010500b8000407402080d498880684005021600c03044160340a0000c03034444c903000361003550b0300e11403a0b9070003103250721a12061000030b82078120701000e500c45008000c50b24540e0310240080072601641150580d001820a5640740a0011440101d90382007280540c95031044034844007a00071100350a0501110410b1902480000400000180e910500310b0b8107440080c41c10302d8035202d44001040004001d5000074159100c40c01001000700e401030003551040070122900403499944140060b1607003140550b24541c0034807070070088858140340b8030011400408100c0c03217041210368600941ca40340c06501112030070f1004000304066091004105000d009a14801458900314030f07031030382e61100440480b22a0500d26483c1c102c14a00038003c9480f8030014400903c02a6802021688140003c0d200307140460030b80001d80080746485054002c0c0131410391544401540384c001c0540e000c6400910007004004181401c400040090a42e8030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 882625206 1250 882623956 882623981
    0x1207031101080a02030601080601260a0209040b0604081b0411030f090106080c061e07020d0506010807060305070509090402060c07030506060901080c03030403110103060302040e01050702010b0a0807060c0f06 91
    0xa86100c6030005031503100064058a1103600400c10042c050b40c1000c4141c1e00504c0a1a2460204006070111500c1c1c4180705400c4c003150101c48140400004503401030420a48119800c11078800032108102c0c4e24072441c4100079407a04120f4022405007002c21003c018444003601c04215802c038020010b0300e903801224030046001c00b8409001c1032960910a8002a01070b12000b040e0501c0c514001400b18060b010a45000d0031050720b80000707110140c3d06540c551903014280c202482e07502d00d02240c44e0102402500308911801e840050180d220340603103070080743c0b1603d40c1450003248400340001040004c100707a82182040018500171002042100c0040d07000b18007425640c1170040c03c12040c800180d00c860283da000d000842880c2d54041f0440b821a80e0040c01142c81030b440c540142d01034005a80007035405450000d6040c03208038103401040c45100310b1307402044262071400070130072028200d015441c010b42c4209402d00c4400e0260003214000390040c0b0142290005035911035040c0e40310104200d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 882626456 1250 882625206 882625223
    0x70303032712030506040c0e0409061104030f031e08040b041a090a0b10030201020304170c0a06110c150405060c0a080d0c1e120203040f200a050f030a060902120703 72
    0x2002d41c0c43e4148522034004004980038030260801100003890205410350140c411030307507032000d1010084260b0010401d440d9800080d40c07a1a0780b0f041031a450300348503c094004c02c240241e90304004400c170303251032020354503a1a215081d45940d1100f1310440b40c000e01c101c0300003201c4a042c0c10007c0c00d20f02174034071401407070009000d02c15461a0103a0b145001401010100c0710440e410300040c2e13000300c1940c056540b116074002481d010f0444c0103180004104115800c00780080000c54081d90200703e4195041c172900448070384510900521504c0000368a2450400130140014421490241d00601900f03050030102d5151401d56110200668070400d0752800c1035550700108041150880c0c00c0000ca40c2021080e0090703441c03100009428250b000c03440e0400554008009010040c510015284441e00890041160b008003914011090071408dd035030720034003001030001550715203003400301b02c40e500203806460764040c642d45410107040c01606c120703449007089006020490041045200560107032610 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 882627706 1250 882626456 882626483
    0x60c0c020901290c0c04200f040905150a03080d020403080c07080705030d0c1128060801080d09120303060b030408031e010302100c230a0203160302030703030327 71
    0x7a0f440015000900d200c0354400b40000e1101d05400b19042450301c2e000c0c0d6011584417046101c1241c40d12800007403043c891400b29551141c0c619030006082a20b400c04010030503070301c13100c1d203207045e603044000d0326540030641c07010a2001070504409083c0681c0010005403c240d04d030b90710000c00741c2104001c40c2155005003002c011191040020b074000744000d034040d000314458124010721b09400c276140540b400306404101240340e150010412009140140500500e840c01540a644101c892240c0800190b42c4400402d1040700895400140182500c520714200e00d0b050003450000c500c540b0a40a15985080000300f40200200540c4118070420015580346019841e129007540e00016000000345200c00510060719640301c4081810064184200d0101e180e1522a44564090a10b911200360040303000302c1d251000105050064800c40540e8228400034540d00d045d004240300195040d401800c013080424000e42c0038013081d0340c1104040664802a100784090451402400c0394a403000404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 882628956 1250 882627706 882627749
    0x3030c060c050403080f03071e020d080f330a0612060b03040b13060e16050f240a1107140418030e040b120609150906090703060c0c020901 61
    0x1d81c0e03104007440d00346141018190b40b00d04105000342c41c4211321415000000c81c1c0114020804000c0d40501030300c9040045440b4040252190303004402d21010505000100704070382a081c0c00309100d40084006101c801c0d0b02081000d420a1100000841c80342d02c15241d0589074980034400401351031070741c80d0000e10106060000049900c82d0f07101c0882c10b10f090040c007000496801031141c09c001c1c1824801440072043c28550001d240424211446100c1c1454031400655103a010380203d131400c503502011142c10f8000d0041c003030300201d80c56500003080310b180d1a0180d9504041c25182603246000d030070340c1421542075440d0000319000030b200c907504490b0030207041c0340500410350545840840e840724042e056170080c00c00d00100300454450b60f1104c103100079644600003030b00c0c20700203088202c0d62681422440c036515000310b541c184040d808410002004d40f03030006000c03030064050134000d1082c1c80c07560301c0d4240104101a03803034040288010f404009030350b0382d50b11503001e44035440c0303643d0041c01000c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 882630206 1250 882628956 882628961
    0x11403010f1a0c0a0303020d0213080f0c030a0b06041512051e031e0a120f05010501020f0d0801030b060a150e04061d0a0513120c0b1005030309120304080703030c06 72
    0xd6000d071442c041042218815100824580c0000c0d505040250f258980420000301a0207118150300c010305400c070b00010824000203102e00c050990100b980c0c078000443c02419221802003001902c0d01c034003100071926034202a4410140d020b00c03007210001c1141c46034a20116000c00381130549075135100054080d00e001041015050028800c4011440c00025556000a40d03880c07e50740540000003180c3d44e0080c03402000f8000e40006226401c018808917100220014082801083d00500ca800d040c442c0c81c0000040000d01d0b001d5980324a18144c1c65540e44610580300186480d8105c0080c0700c0003d45105550300c03820940071291184812026410140000caa074680e0185a80105200100c14180c4680304956000409000045400d42d00c018032032008402903c070007042007480d01c8000082c00d520522002d0118424000e204e0140c031a500425914901c0c1d018040e89a001048050030350703e03000100a0100007908140e86c2415078502810b030074503500e544160041400f01c5000f404004961 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 882631456 1250 882630206 882630239
    0x40804030c0f051e01020f0d09090b0f0d0605060105091e090a150e04080c0d051e1201170a0b100302030709050c0a180b1803010506101409011403010f 66
    0x148402410346240200003050052065204d1070b5000240204012603407082c441c1010400070b9004640300c2405110000b002c0a03c24402c5e034600030329103a0100d245207080b00b950f0043c0c1a0003007941c0520764050701c03098002c1101414250500108001c075035400c1e2550b4008444043c200880480d4140940040c0800000000c01d0785e83d9051500245203880c01c0c0520150042c0e40016007443c4059a440c40c003d0f11a00c581c48104525200f018003101460341d1001c018490343c080c03154540412803041c50303403000c14000c0240308401414004018003040c03116400e0034801c0c903260821604035035450349860a0481c0c0a1751521013035510707550b003807040d401c00b009500000c0c81d03540340070031140c9132540101403180036000340c001c10481882d2031048602100c1c1e5140e030281c202c00001964441c000c003120280d01d0038001007140a0f500b00400583c00f407914015014400345a0f459504200d0001704c1d03401c1c0e42da40104840b42c1849215030710207042901d01c5000d14007a012500905030017074144024018083c0700d6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 882632706 1250 882631456 882631469
    0x50a0606080f0c031302010909020304080301050a0f1a0702010c0c0920070c03030f090305030d05071e0c0b0a0f050406020705010b03120a050703050405091312050909040b0402041103040804030c 85
    0x841400f0040b00d54000312948266001d000200e00d007010710040740c96801c503a10003620b09002006000501c0300c10b100075070481e4402c40700385000c156a00421342007640c25100c0d12440c400003440c0450243d004400421045205141441141c8081e513181500303100aa04900c0d00300c1d0f42c030280104154404c84204451b400300200040c100700340f990310741814035440d010040030000d8030100340c11254041c80002001c0d44d031120580c2c1d118980300b04400c0007000100c83e0300c1d001034020412400040184a45541d0072405541e5924800040e43c03074406514902a255605c2c00340d9504030749803281414410075003c0c5105000150340c03410607040840c259075124202901c40d4025100c081000c50341c541c12140d0084690a2140c2c40b803815040c2038845018581c85280c22115a40402c00d01d41e49900b0400a00e0f4803429a805031f08141c210119020b0151160150300030804038089400309229081d0954482d200420200b800402d00100200c0b030b4100307039000c9a03810004601442000790380003100024014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 882633956 1250 882632706 882632731
    0xa050a05162103060f0b0d022104050c0d110d170c030417060c03010303030b0a0f060203070201020f0d020307231f050604020a080a1a1002070e090319140d050a060608 73
    0x6208081c2e4040400d44104071070281e000804100710707c0f890301036075202c0b00f00748210302740b0064042602000740412141110b49000c4d184056401385000740d103081020342c1158424400541ca001400492401140c00751485100120410a0044104010b0400220302c50142d91103a213031070b641d800608070b820140baa050b081901000742040c810030560381165010303c1e011a1441c0707500049003c00031240c00001e0040426080860700680010080910a20030303030864100012048507240c0b41d018102e85000107820803c64500070039082442010781840600020840622500d4110702c0c000c1203086c5070f40859106200701a00882c1441410b5102c10305803015880c00c80110f20047c03c848004014901700741d9180422140100e000c9a4010401c40207803a052012110040c01380d0780d12058420789242091070000508414400701c151044d500da40a43da000910f0040d4041d03c18442d084100d1030101018861820b40a40d9030189501a08102070000740103400c1c11002002084010943c020300c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 882635206 1250 882633956 882633959
    0x172a0405090610210b0f01180513020c0d0305090d080106020a2d0b1504060b0d1e020a050d0b040b150901090503060a05160804080a050a0516210306 65
    0x403503918640741c0c40b0004403402002500160303419108940d07691600c03640c00d00c954001c0c00720145160f10082900340308840c110460000503004407403c4044544100701e1040c2c00108102030b0400f20f40d5880024074282005d03003021207510360303680342000c0000c450f8002a10f81c800d00000303410901140151520916003504103604001e00a95104d22504008004071424144071003200340c02001c0080200d4440300d0b820084a55003005044441d041c0c0f51440c1d08035800c0c00040103450103100f54012201c60314a401d0401c27504008120081060500e8401108040c06d150802032071207100074015940c00c0d40f0307000c3d02d803041c0c55805801ca4210300003890080380b0303000700c0e06c10903030b9080c1820b500c40d100d456001d03549070401c10040710000c040380c1c010740e018440c180901c04610916004039118140310494203c20b00e04480084a1a44060b9009032582c0010000e007201944514000e1a0707044040c10a10b01e414840d224013410000b00c2d4100f03948900c403c81c011075007400400348103050b110b401c2c0340912070329 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 882636456 1250 882635206 882635209
    0xf0501060905100e240c010506212503050d022104050616060b04140a0e030f120406180302030d110c070504180206030f01030519030e10172a0405 64
    0x4108a04d190f21507180c1107031004461030f107031407440c0b12000d0740003206480f4103001c0b001501820066802c20701c00c0000d84080140d0f01d4000300c4c081c281e0360034000101003181318010328030304000d542d07201c1c0c1c640000f03400c00c0403000c2942007111000c0c454056008101480c4000701000d103400003880d001400380010071041140340c0d41e4609035646012504500350740c0e402d0380c1c54a04014008881c10030307001030602c01c044c0315011602d02034074460501c5401c01d00c80b058580d92095241c0c45103108036019001c043c058200c0d03006070400104d03807080c804c50300003600240d01c2c400c82055149501c41200144e00c0021079060b42c0015000311042c2d120402049800c0800110200d42c8a4600e4004c0d18020359070350303010f152135004900044000c2500501455a00d007822244020079030320900080d00d803841512403040318400c403001122420f80d0941c3e1102c02050040041000f0075814124503000c1141009200010301c00710a081390249588c181c80021300542a4254905040c101d444d908001c1c5c024072003000903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 882637706 1250 882636456 882636467
    0xe0f060a0e0c100e0117100303170105061c02040e0a020a030c0c0b06101803391221050405031e0709110c120a0e040e0d1d040f050106090510 62
    0x2110421300303140103511070610049500c03403151107044030050a000e0038484403880c0c0c001040d00b036a01a84d100407140140c090b0000b00d40c1d000b031007810b8000ca000c0240107900058441d200600316603000000d403801356038098031070f1180b006075a6022001c4c2c1c006080c0c4c45c6c89806100d01c80e030300016070512700c1c80e800158845144203d0003c01482c0078141040070b0160b510b1250030054103603080c081c10ba4a45a44904102c840128914800d8084402c800158010a4101e6500404558400031415905800c2810038480500ca00030211064405104c40191440941d40c4014800b102a40c51030348491404080610384542161030000310602c407017411500d1100490102c0c01da07240c01d400800c40d42d030780c10302c0d04005200341010712915001311171900c0110011040282000c4125079a40d028594504c2c04010884d050700390102d20a034040c4c1b1594125034041c40303494401552581800f490054444003150039035901d8004a00740da981c0304018080070303030880c4200d030150a06440c540142d5001800103080b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 882638956 1250 882637706 882637729
    0x11010b09070f17360a11130f0b0a092703090b0412050c04020913271a07020a0b01060e2215051210050402040e0f060a0e0c 54
    0x100100e484014a04a01a4420b2108084180d1043c600d501d08400c919080c0315510032030484070340d1142d0050494600c480340195882d440741020f08441d41e841e0f80c50703142c1142500300c100d070031000045400100c4400c2e40b0603100f14025000c80820810b80100030420140281d4000c2000c0502d0407800d0640505510403a0f20381c900a40c44000b80079001d0b05003a0380c0360802e40d101e030004480c0000c1c08038080141c8041c06c007040748141c0c100c5002441c2d80d4100821ba00940d040b15410154001d5045c0000030103411151704181c030220580000c50428103110704c0c2c0c000c5081c2c2512048110032414400e90030300d1401940c80380951014000790519591103006540043c89248100300030b503c00c0d08010b60b41d54211040c1b10b48001c81c0c000a00310511042d80107054607203150424031411400000322410301d014280c07101e45010020b04141045595070340000c0102410980c1c102d569a041250005000c00c091001a80c5001c0207200c03a03d02040707440d043c1c0b0180188607403e50000c02c0c441c000da0712a0901c000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 882640206 1250 882638956 882638971
    0x310020f0d020903011d0f0d0e010c0209100812130f05092404050a0509010c140f1803031201080601060c1101210603121403090c09060a1a0a11010b09 66
    0x50f994080600041c0c05041086080351134200201c00307400401d0340015040250031000010b8400c40780131010305946c4c0c3c1105542241c040307242070501500500d40341500c2c640c049100000781c00d0091f21200d01e03e251201110344107444950015228204c082070012480c0201020038003001c0381410600800d00496014042c0516103d40c0d0039005071180040b2404030703d407a0040c0040141e803501005400207031606441d03c0440d54a8040c04050180c1700d242840c40d07102a0b0f80c4018644000703c0c0c40486c80c0d50100d20158104c41c143c040c5d0300210b981c144000c00780304000c9a00c24100b941000101d9080c0401030b4040d1080c084e030284d030300001800c501040c1d542e40c0c200342050840d41806a07501001d401003d816800801d251110100030451580100d2010080658034401d02c5a00e105007002c0d01d11083d513a030006130b880011161084c1c5071491050703030310803001b03000b1900041d903491140401c030814a42c0c11410032404120810000d80c009412220501080028051503480c04082a00b0200141404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 882641456 1250 882640206 882640211
    0xa172a030d0b06040b161a09060711151009050c130e070e1306230306010510050c060a0c1e0c020904020402130f090e0d02060c03070c0b0a02090310020f0d 68
    0x109035039030700d001c141e40003800549205946c0300040c040c0032411048600c0e0071541e8a00e4904540991018000300c681b055100c2d030004c001d9030b11000025108c0c5480c0a0600321544115020100b065052140c0c2e18050710060264949041c1040920307400e68900801c2e5202c85002880741e4100407404000030400c0319a006440260b0f919010f00c12541c0c5041a02e015400c034084c0003440b5402240d0f944810b0403500e030341c03210bda201075001121402d240800d40040e6816440400180003a08d0445070213040c0c44600c0c20094a8402c50300003c0703040c00b00c1202c1d40d501e8585d6522014080700c2d00640d03000f00340340200c0f510361000585e50b04040e260700e07421003004c0d0103021800000f900310b448990454014480600e010b244003541c6800c407800c409403030302545401d142400c644098600700040c055a00500faa005002d15603291203200c0b0550b000100500c1c1008030300c46540c0c02240b03480030003d001e40c0a02c080960b40d1100d403000e05181c80761a94400521910410241400d41e4980c1c054034034944042001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 882642706 1250 882641456 882641471
    0xe03010b010f12021c09140f03092202120c0705010509060415021e0c01090c09020f070816020a091a1207120201020a0203011404030809070b040b07050a172a030d 71
    0x83c018040b001707000304059107029082c01c00d220b220110f004002c1018800c44190240d08501c0f00d0312070040f002ca030f541004190280351038002d08100d24400141c0750040050501501c0d0140c410109404d0310202016030000402c2e0091203401e00429a02a4186008000500707066940209084011355600030155012646800c184091103420007a4032151400030703290502c0c141001e00a14020000b1210740785002d20001e89d11000b070098030440c00d440c400c0b0380e040040685032164a60b002c90350704003d1101c2c1c40d021200580e5600102c902420b03840381c00265000c95030112040c0c20301e00171090b41c0304034004203546901c820001000801d032940d00704501034182851005130b25040015100075415424281c100700e00318151400301d071265000c1d0352400040c0d1142c0b4485038450180e03005285511004202c01c2c05844150401451124820412a0035513000342d2500320700081c8000d02e050440d500007401d40010f96607101005042040c00b240300b51600301140007a5038a1243d043d100f071885446811 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 882643956 1250 882642706 882642727
    0x2031e03071107090c0e010c020607060e25050a05011b0201030b1c050c010e0d05061f0306020a02060118180f081e0a030c030204121b080a030e03010b010f1202 70
    0x342d8410240700c000840f02150f0b1514441c3c400307094408003000000301110424604c42d0b00c90b410520380d06d0340150916241c04184d444420180c0740c0e055141545100f5440014046250340c44071011801c0e5845000081c070382814200039940c4820341c0114100030b0b030a44115a07003584c031070444886650900b40024441c8100012036074003000d01100d150081d58182c0f108080c00320102d8405000003003683e40b20f03500003c103010081c41035842072001d0300951084000504005078281c0740d00c0716445011802d802182d07642c6d01e0409a0b03105412003030058001000401c44111a01030806004001c24000e01507000f0303410f41100062070302c035005000780e40890b44040034030200104443c060300c3e03140212002002019030000c295403200100c500002d2900300c1c5001d03500d1192085e20309503024800030a07105607142e15503501c142c00002d50701c0452196440d001070345480800c0315091043c4a510b43c0c0340302c0380b030744010982180d1241040c607043c000441000c016803135000c0c2001540307a501c070b540146c03641c8003040e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 882645206 1250 882643956 882643967
    0x10c0c0803060f0112020a09050906150d0e01090c031a18191502040f030b010504050c1b01240e060a030c120f170903061f0501030b030a12030e0d02031e0307 69
    0x106080e045d80700090581d88a41d1007a0000d040c1e50b82900d4040c11a143ca4060081d010ba1450385c03141081b006000c2c17003212180341c0d008504404100400440e02e410551641e1401d260302c0d034004c0302e0b1456006001c1e03c0044071f1007040f9a12a41c0780818085804040e40360381c1c0c440c2c4e1030402402011590b07140303a0003001003030400700d00b44034005801107440d01e032541c1880c05042075500080c3d07081400036000182604d802d0280a11039100300a80f60304000603031084000000322410504250354884c1210701c1c19071221102500c1c0c00c203014075901c20143c0351084100c20b03600702030200c5005c0e510000341400803450702031400c021a800202000600d4000d42800003409042441c0204002440c045001c0200e590001600c4008000c800366101615142d010399401502d14031420349105900303070104110f44c080d43c0321801003075024007591801c7d0465514a10910302c0c0410820201e9580c00c8800c0248104002200021005000462074818041000c0030b2a56641d507040480050000014807010320a030b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 882646456 1250 882645206 882645227
    0x609060f03060b03010e0402011706030316330c0c050705061c0504050a0b0612060c0d0e0f0a060c081b0d0204081e060610170a1e06030302010c0c0803060f01 69
    0x861510b132656190350b10141d1440c000c2d18140c0c001703008003010403100454900e60a0244200400562174030503201c264603518899403205441556141510360917a902455039100402d00e0109000182644401d00301c04540101080c24108400000704500041c2d000620304141c0308121415a140c120048480411145060014150310b060100344010094001216010144a2308460840340d85410502c40380301d42c07405c90300c1b049a00038404510002200c2000304130708000d2920108030106011042860609003401c100310580c40030307810a0600c006480744481000c080d240454050811040607260318000d041c40174124030300040c400502078a158111070081184605079100c400b5940f122054801064101c00a64001c07040090043d2401c0c0c00300d2039900c11907844144524a14000980d401040100780b900095901d16940b01c0c1c20380321502c2c3d03191200a2103008241702e41145002400c0d5901ca40c0814140300344114210700082c07403241966445001614501180010100100e4003207051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 882647706 1250 882646456 882646469
    0xd0b0c07120302030a23040210020f010e07050f0108010b0d050910050f06011107060c080c0f07030c060906020d0c06090f02060d06050a0f030308041b0f0902040611070609060f0306 79
    0x1c4804800059425030080c502c5080300407020000003800b64081711039100507103215031104001c1c9001500620740842d903280107651520485195840c0c1d0600719003140c60300e080e146900e5100400400a0f86020402c41c0520070003881d0115041d40b624a139903480340690000107142544800c000b40321140d08001e1072205401d0304105015034240001807078449a4180d07146800511100702d1031465803000030340007044401ea03640b02d40c0403c0c0d10fa106d0301200d401400840c0f400d800b0b86240c03c075a44108100c8000954081e08601a08030328040303001e06100352070783c40441503410280040c516185c0024102000d503400540c003082c1041726280c0070441c2c200981d40294401c4021075101c1090301c4c2940030ba000e03240c0650303403048542e44800321407554a00b24400240003d0300900014005515a40291500315a920302000300703d444030b0b00c01249401d00e40044180a41c040ba040198a80c8811805008d0780c081000d0003a1500b0600003c184003002d0040344117118402400701c10852013903200c0c40044c00c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 882648956 1250 882647706 882647723
    0xc1204110f0117010501051612110607170403080903070b01061d0d08030711030d09080304020a12030e060f0904021903240909060b10020601230d0b0c07 67
    0x10285811120a014803035414040c451054032015a54000e050700004002c01000448180c0e10309001107440d50b015a00640702d5140300c0080c100000c07000444445600e0064964401c0e14040fa03040600e40480200101e0421042c2c1102c1001d04980100c041c0d0810780603c0c00c0802552105041c520b0b500ca07500c00100381c00c80c68000091101d80c00300c5031074400720180d201902c4941c04002000081c00c1c00b910301906d03c04041000c125102e018114034140c0076103030b5050700e0070704460324600d80444241500c01c0d100914004200011460b00401581c0940380302005819028801c1c1c0f801892040079000b52400740e413001805601d55128a0300303807401e44070020420b40d0b466a42d0409041c0115130700000380046418034112004000d46241c60440340751312101060403d51030085542c0141035050303c01c0c0c59a50740c4042c3c04071607840d8802001040304264000f0501549401881d088042c080882403c03030400400c0011255500e10350703085030b9070f60031182400c040d07200d42d611100a03100f1711000620740903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 882650206 1250 882648956 882648961
    0x90d0303090f060501050a060207061403071110020d180b06040b010e040903110f031c240b03090f030a020c1e0d0c14090621100f1e090503070b0c12 65
    0x741a4120178142c1e01c00341c800c28200b507034a100130390b9181d80c14040c400110f5807000071203030110404005940d00c04c0d003518019441c101001c0c21541070220010b513000703080c0d2b00007602c1220300307045004107281200710000d18401160580c48100050310b0140c081445541c80d9401d0601c40d078821368138602c1030032005008008810f42403401a19201e0f00700c995036018003c0d4001071009000c0407059034229610030342d2b03000041c006030b41024010020823508848840000c840300f06840c40803a540c1c0060321500940c070741e4a0508a19051410816070310500c8558010421181710b00d40c00f10320203070f49c030b941901c400d0300340076081081107500e140005555802440d80700c0382c1418030918054a1044840c3c01c18440010442401400444e68044800d80e8015014004504120103015041c0b0a20300d0100203072108d440e0b055080c502034a510016020145880304010049400103000404001c072240800300080b59107656003e4480c012200041c08884958000480c010f90500c200c5508416601d0b408000e807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 882651456 1250 882650206 882650213
    0x1e0a020102090301150608061c05011b021618090206070f0515091903110c04110a090501020304031703060604120503040f120f110312132108090d0303090f 68
    0xc0d00120550b034031035070800f94040914001002c281c0c080e039400359111a1959a10401e00a02100300302c03141d40c80320082001100804c2081c07040040c20441c581c3e444208810460f0700034078200c810308244002e400101c0c1d08124030032001e100300054945101010500740098000141e8034016400040c00e00c84dd0603024204000d804198400c081080101c20380c0c0a803a0314000e699a104850344c4512006810701515000c00e0150f684002c03e1307502d4074101d03090031000c2804103003510324501d40c184d109030011030420802500004050b0140c4070a10041d4105403550301d4860342800360349249102c0c00f8001011505548444048802620462a40725614107607880c1441e500d50245c8690902c0060700c0801040b00d2080980f04403149810100c204100e002e00c0e11410b05594106941640c54802c1004016102c003000f0054165420301c0c05144600e80d16017045101e120340d102c1da17003860b482840184040001c00703800c180d440c00b0409441d60500300a16203001c5c2c0041088407405400451511040e0080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 882652706 1250 882651456 882651461
    0x906050f040b090a030e0405040204060522050a181b030803250e1f1115041505090304090e0106030209180714030d0e0a24020c1807051e0a0201 63
    0x1581c070503400b070165503940803110380c0c60325280e4200074009007101801340c0e0340e403a290b000745420500040002421340e40e11000504003840382c60640c40e603101e00300c00c40b122102c464411285d000e01511003e10203c10714450740403001d45004e4008141038985807200704151140d901b102c0265034003450481d544e052140d42c030340f078260800390389150140380c10089901d40ca200307000c66401c028020b4182e04034208070700e00414040001c4007c10302004103510030300801540400614180190551540c600c6040c1401d0140c202d003804085003035a607040005001e0790000c000f046504880384030344000345c07030814852600d016105070b40c80a075102c04030340203112099290301e145034141d030816800c40308801c0e81c46010050940c3d902580a81c190010000c01059034003036200d200c102c00d0020407401c1d0f56a117031f921181c0c0d103107003208242c140602d8500007004c0305074040000c0c0c4040003044507102480300c0c0d0054030750030044c2e000300141c0400002190042d60140c089846030044002c104101d601c0b80b00e4948020700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 882653956 1250 882652706 882652711
    0x1905010b031005010c020907051803010c030e01060909021f031103152805040f0e010c0201061a030405030a031a040603081c06080307030c050a050307050a030801060527040906050f 79
    0x24602e000e58000200341d8090115240c4040e4080d092503101e54134158141d4558110b90403040c00c4511208620b00c1c1c81c1ea0030b21400c0240c00003074800065110044805a003100c0103500402160340c40c0c8101d0f00c0260b0344640d0161444024100b600608428040084000c0c0000e002a460000b501000b4010180902c0c42802107038242541c0c03071038036000c1d86110784c1c400b85041e103040340465014400a101d94102504003101c030784001d07800482c040b120300a0090840305000181001071355142e10a00109100108084405040d10b4819055007420340310300c0e449218403da46028142d13200c0080440d01c090310000c611203c0000c00400c0303007582c0e904020301d590780304036207000344d200d41074820301064a25071040a094601c900300071410241295020345440d09100c9090314184609101d4400095040004281840c80351004d00700300442403070003802021060704104d0600c0340620106000c40000514441e014881810000d81c060308a4003280050041d41000303482181414104850105244681ca0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 882655206 1250 882653956 882653971
    0x5090f0d0f081e010317210117070e0a090303090f150509010e03071202070509011805060f0913080d060e0603060105191401090e071707020d171905010b03 68
    0x203030603696910421803c1c560f00211001c3d0302860034010300100c0d8200a0344282c1907400390540b4a0506610401500400da07600f0040000c1b11340790040c480c9203440070485490481ea02c008048580c14860030480003034008125509031555601c010050510903041120b800313402c04240034208a4904000301400c2c6128101615a0704100200d5005030301445210345840009020307500703152086d0b6030940030750400280c03c0114481c40c6000b282503590624500c2c004e00d000340e0316190301d00e03500d07800005849004005c079105500e5a90318031066203a011217258040700c030000e1001c00b10b460345041c40e841d0203844c2c84102e43c503182c20008199440c6240c80e060290104504503a4142c1c0d0b98420045d419002d040200c1d80310a03c0d4804200d40cc503031080d44003000340d05042c8503880540742c120418410100321045400201080c005603400c0307110b14822a007150080c40079203046074404101074040c40491082400303408041c0c000400b040b041c445420146440000c007442596510303036544590ba082529202c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 882656456 1250 882655206 882655217
    0x309010f021c1b0f0507060f02030702100b010216171005090a1719140c0313091d1209040213080106031401020a080a02210a0606180b040905090f0d0f 66
    0x500071110603000e04458040c0b5513940c000200544081120260081003080700ca19444213282840800d160001d140701e00ca0b698010407400300d0051ba070900342c40020440358195044a038181503141c2204081d4030680740c00c00b51070103030092850704492402036032601c5440d54500c4c1c00280a1245808140c0c500c090380207000c812140b0241d25540e40c04d03131051000b03c03000c191200000719100d0340903002e040345030b0301e8000b6940e0070810545d10013421580b020100d120002c000003000d00c81907070207204000100c03518414490b560b1040e1000c4a42e1400b601000c6402c0d55404a81080155110f4040b5200f1a8500c450ba4007038a5a428009018141c14041111005079441816101350f00503c00c1c2c41500740c0c1d130ba450f0b01440d01c5021100e802584918070242c88039140351100e03130904c4201c20740180a000c0c41003001502d54a8040c4c001d25441100894201c00001c54000f04950780c1d45805680a858141d000040c0603100e0007001441d1061141906005020b4191044000c075048558a03401003400c1e1160f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 882657706 1250 882656456 882656471
    0x307050411120f190b0603060d050a12091802030601021513020a0b040501090b030c090907141908090f0319110d03020730080405100204230a0b0a050309010f021c 71
    0x40130a03224001407850304550188001449850400681d000b403601600a9034995030351030b181d9200e15203d22401d01c0110b2103903035042051107005100d0f2907240690120450550802d000000c3d150303006004069203070f04280c40030642401210181c1d0303030a154001c00c003c21460340e54200346081d400c00c4c030a480c045110480001030004170b03003040368424440c80008a20307024001e000c0040b0030318003400c0b000030425281e0758000c95080c1c03580203020049508104c5a5800e144503402410030100405002041e009030303480540c007510000c16502c45150030a44089941c10f141001c58440c0341e80034429072184514007122449a40543c0100191070140c210311035101c8014403034990f009588446520b23001058414503e604d44110911a00036124105072001c8958880e200d03400c0c0c1e04207800104026504480160000d10103120b0390018480079101c4e5111185015049000f901031420003205210300000002e00000b820f5000c804110380e0440304544650854660f500e6949110070b0040c0c11a180246 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 882658956 1250 882657706 882657751
    0x5040509030406120911090703050402040b0604061403090f0a03050301061b02060405060c120c01060501020c0306220f2103150807121b0e10060504050307050411120f 73
    0x40301e05551040d21398502101a00030420010b007100b02c1c0503943c180c018000c1d40e855a0700d5040c8070340510314a58000c24075041c5401040102d50307580d1200c2d03110b81e0041208025960308881c00d088110102d25000780c8130350f6444000b40c00c0a10705000250140962404107041507040310241d8103803201c80da500c0d1800780714186131071683ca001180117588584180401c00c03581c07908a00030441c0d18000f00903140c01190884802601d0342110401c3d1060340d454820601c680e59041188013242c8408034000d1806040c600d0961800002460298000d5004d41c007049040c00b00b5172441054203944142d5185194107420a0400510741480801c0d00081c20140340e0366040742d10568450a41c1d900d04040c050542c6025240c64402415150484a903142204106804c490000100c801000c0441241c1c1c0646000d044c510f800e002aa084181480800d01c070031301c00e82c0c0340062120151141501c0010701c40e00131005c140054003a01262100c00c8215204000408405652140c0509201a00d00998042424 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 882660206 1250 882658956 882658963
    0x21e0f070f0305030d0b0103153b07030b0114030a02031b07050c0f1302130812041401120608010e010606020d03020f07080f0f0c28032708070f05040509 67
    0x8000b80a641c400d00861840c05c080790720004126105042c00503801186c40344d64174003561740750311004030368000e290442e0b9012025028142030813180010b08210b809441c688041d00d22002e05135008240d0380741401c2000380d02132024400b13885400d040300313502c03880c3c00b0070540080e5200300e61703545d500c850f090340e9082c07054105c8040c0c42196500801400c48888035100b4441030206500085070300c40611102c003800300c50988020b000c50b0403080c0f40341035024106001580390000321a01900b59560401080101060b001241c400100007440e013144444c0e410305406000d4071464004030403e52a01c44403040e00d0805501010884280ea000e8480400400030180c00324052043c3c002d03c8010300b013040300000b5102070b005100307402050340c125050003080300080a01ea049100014810784c0415900d2804071045810100c80b0069614042050301c4230b550014000000d00c0d03880d0425540c0c0c00b25050f102803035405114081d1580c02c0440325a5a511009004012041c0c17050a0146141402042c00b844022 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 882661456 1250 882660206 882660209
    0x120603070b09060a11160311090f040b040605060d080d0516140d0e0a0c0e1e060a0311010c06240f2108120703020315040504030806010c03021e0f070f 66
    0x811a904044208205030717064000044485d01c140540c100326156442004415405940958050800035040c0400e00c2042c1c8409000074042040802c00c20002030001c003000c5902581c04507020500751111000f203580d01c2008030005008503c08a041440c1b00619030009108440503200c1a008011842003a0f40d003150100607207014110030400708101821070707040300540700300b160100c440c19a084d444079a0071416940245218100380814002c810b0001034240070411410100328146042032000208001100e10005064a000f03400303400036603001d0080b5100d01500700000344032075100e10300c1980260030b804004e1400301c5441000030543c1d5016008200680c1c40d25140920748000070130000c5243d8043c103000302c1303140d4400c0210030301d403480401480d07000780841e88000d622824034089040e8040c0c0d058103080e014038503100410010030380c80f01c0307015044482820b081e40d0092042c00c049040c100100c9403d0118034103c511000c50300310014080520103070b40c8007a1a10141c8901c1c500c803485449 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 882662706 1250 882661456 882661459
    0xa14010e01080f16120218030610050102102a0203041a0c06010b160c0602030d0e011401090b0d0512070302071a040b0f040909050a03030b0105040b0301090b0402040308120603070b09 80
    0x3c040001d50300320b50000c8002d6900c5041c0c24001c1106a030301d4800b105903400883c4100c2490b080c00003185040c1010000d05401c42c0031360340390041c42410000002d580e030282303410206200e9102c13004200c803000c0440d030060381c901285605100326000b07c88044e60340d5000d44240ca03503500b00040e140801d21101da06a52407144c40e440030700440d920740207520b54a0341040074001c00280d100e0040000192409427000300800c115000b440d1104104086101120718070a4060361036410101d019402d2442c85611038156081c8480c0050541c00380b202146500540c001c004055126250b050000402c1c100003070300240340300354211400e4a440340c117036960481c01a03030040d036401c1c014403060001c203614030301800d501c00d42c000c1c0580c242581c0e45c0a80c0281d40c41d03184140c1c1d250b040050a002456414080c21000c084207090052610b8030740031040a0620052040942c0103645d0b0054030f4090381d4a40440c1c006507045803101c4e4130764130306d8401e50a03410401d0780c0701d9102c0e1040d1140015900c6140e010703142000d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 882663956 1250 882662706 882662731
    0x30c0106060e040b21010b060304050a03180305030319020d090b010f09060501120f0b1f0801140f01030f02040e040c0e010603052401021606030606030b03030c0703030516020a14010e0108 82
    0x10010485d60b119114103550000e075548812480c16a500c660018620880c003440040101507035500700588404101c0344000a0300d500d21000b400032030400001c99412030345c00c006010074492504400402405001050034109081148074000d11003081005030603030f01000241d441203940d81c10310324211409882682d011440e0750024940081440d480740c941d000702c0d000e020904400940c00a032800d1148402840003042c05410308002c82ea00550203400f502e501110034902c00e01540004000418102145042688a9145110092107030301910003d1015000c0b16001d41404d15295989a9450080b0179000802500000d1004d10900805d0f000e0454404884c1c4410303e030400303151039400700d54100b0b8194451311080300c007801100700000c0002c02850380c0002c0c000e410400300030291640d25014a02c40e60042c041d840044034041b071072004480c1d050402540d03404105619402050880002030b6002d030329240e0004074900300107c00304c1c16807030980e071300301900030000010364040506690600708001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 882665206 1250 882663956 882663979
    0x10c050d05100f2c13030f030603030206010b0c0a08040b09010f0c020a0b031324060e1b0a091a040f08010213030210090308032d011206150305030c0106060e040b 71
    0x38541d03200d411820300c2c003034041d903038500300b03241a089040541e40c0769111421004040c0a05134407e03c881601304140c6020322101740746840003503543d001030060141001e00003410b10040300c070400078a041c50b40d03c007100548036566903420961351381210513000d000c80c0018918500c0503101d00c9903407142907401031002c51541d060206030390383c0c1d400091288011341480300d0030b00c0114030316016001110800040700d0313440c10400d050440c1070f03d10a074070403d40c107041c01e020301600310000c4d40708095148105592545403220190115840581c50740030036240c040c500600e05c0c1e00b42400700108203443c00b0f4003000b01010382c5d0f81140f5080344100c0c8582c1c1c41b116100042400149080c0c0c0d040804a540c915001c42025100d4131200707083d85c002e503a900c0c05014071490014159610340340c500041e81c0b140845109542c54003000c4604a841070000900f1241d8030440305803808004108a0003039a044021284c0740c2c85400c5000380207042e01e018080100342d014804c103076135250900400b4002400a0851520304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 882666456 1250 882665206 882665219
    0xd090b0a080c0708041d151503010b0a03061d250f0c11040f0504050105070c051c032a03111306080a06051504030b0901020a0c0f02030f010c050d05100f 67
    0x58101c0f43d001ca526078020400040c400982c603c94400040d103807001581c841c14004404012120101915400f440440000300801c0c86044203580c112078980f03034015964405403104034010000c9170040c02c4100518409801c0c07820784441c13220b2040400303006910083c4c001603000c0b005600314103002b10008078864009846244184000600584150b1101b009103aa5500050a0301e1811084418895448040009104090003419003103081d60401010301c1e40341d9102c035a100c00c9450032082c00f500d19603400d803040c103109900a0628071444855202240f2600343e5002c140107050360f80100103410700b0490251280e03100c00316000400703180042a59140b9062043d03c103041e0080040c22242d036074150016054856500f0703241c40301800d00440d80d4941c1580340c40c805c1440e014052000701da106100d11b2181c0d0b0781180f2085042c85e0041440240c111107880000d1130541340726110145542050b051a40d8684c00a0250050486c8000c0c2130101e55038031342100c140c0074521700c18a44e03a4006820200301e103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 882667706 1250 882666456 882666481
    0x6030f0b070206040b1609150c03120b010215090a0506160e09061014120405030702130b0904061109030d031a010e100e0604090c0e312301080d090b0a08 67
    0x1c2c4546c50800ba01a81c1d40d92090303480d41c129200c0c1030000700e0a10000e000c1007550040101002003044001000b0304814100000d656441c4c1c03502e00c002d80030003003005ca03103200010895500c6480e40407007200d0302c1d45068110140744001c0f481e2103c010540001e600300b424500510121700c1040050181c5603030484c1d07102d040340e80d98030784d10305034101203010406c1040300d00d808040c0d54850b0b8000c8005680d500040e205220b94150101d41c080101803510b07019101c680d444d11240383d0015004400850519400d1031404924071030b414180b0343c14882c0a001c482d095030180c2000e40506c1701c0c0c0920441106685c030040d152000c8540c403540c2d104a161495202c598000c1c81490300940002c0d1080c0c2c1081e4031000400701722091240c41c40d02046038540600708c1880d107500d0717560300500412055a440d55542d40c1e412981060090741d01203190315800310031940003542114490180804502030f1003543e5480d030150316201c0000701400012110000444c40c00606c60031100c0301000c5558a02c01e03a900d41b4510542c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 882668956 1250 882667706 882667741
    0x308091f0e10090f0b041e0e13150524010c02060d02250506040c050a03031d01180b040305060711030a031a04020406110105150303041806050406030f0b070206040b 72
    0x14040e110f140401d400a40741d041c040641302c10440c0564560900d01c8660400c0f46202046501d80c4103a8418405207903070568180d00041000d54081400d041407600c0010740031042c0d2840f814500e410b040145030031014500201c03948143c1c0d08000c0502c0e0080046540841106019401030fa0801a6500e00b035500d0303009003554102505641c103224002142c095401c6041501910b41d540322000f480240000d15900900905d000c98148015501e075a9000d400386100d00b0010307103101600800d09000b41d0103658200d050b444021401481e41c1e0b1a204000d1194000c4d001c00c0c1d41d82d00ca00790000741c855014071526884880c00328000e605118110408501a0500e0b80010505400f408182d0943c1d450704d00241c4041c18203a02c2c2c09245440c032060060843c2c10041c140003000d0030071103580e1580e0310701108440076503080c4003e41c16507028407102c1074041c013007030ba103e26041880d14500006210301481c42c1c0070074610bc0d51441c1419210003404aaa0309400d44014000318a25008070302c030411040c030a0003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 882670206 1250 882668956 882668989
    0x5031501080c0f040605070b0a060e040b0a06050a180b041116030908011a010810150e0301060b04080307031d0906010806040b041a03071e090e03130308091f0e 70
    0x10f10f812103200c5140204e42041c0d102401040010420030708101c4001314096000848410130041607240030343e42c54980c1400340010b0210301d007010105001210355001100a0180507048c0c40c81c55680e038011540c541c00144106050f035241c80318200e0107190a006010304441c4690805040000210052000c1c1b2000c1000301c090089030031000030840428003138611a0000510000b40d103840003400900a60001040c9214285105c6010310414000c1040c0302000c00c020714040203c00c1c1d1820101c0d00529003034229001c03603000400c002070001c000000500a0520a544140c2d0040240c0d011401c0c1a01e280421944002c2d42c0300015200c0d44136003001c0340d120100910101781e0a030b840d00810200c8816107401c40020344a4054040c8905042210400410015258005102c118200301d81108080c1c05000c82003910384805041001041043d20414140905214030082d52442e2800c0258488400f203400358900c0038140d04000442e10465441e81103070384ac0da410a10b1008200415103800402a5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 882671456 1250 882670206 882670231
    0x7120e03070201050913090818040e060c0904060b07050307060c02070308040519031407050406060e0306060f0a1a03060405130302060a0c0909020d021803011503030e031005090309100503150108 85
    0xc1c6d81188890042c0b480643c040c0100a985150071511011540c2c1c564114034003543c2003400000d04020005085544207a0100c02140c8034283c001c00100602032917030052001810220307012050100120042c040940701d03003810010f030020706d030040c0e803a80a24440580030210503c020003503070404e07400103120041214a4440400c1d01c0f0340d150f41030300440042d00500c0380d110030804d21060130709104001c09011a820412840504003002a9440c10024809400b81d01124040e070807580b5010320b40c00180002032070a5103e480c1c0741008a00315003045a100344528240710100e051541241034031280150158050302e402d5680d41d0690000c0d00d40c8a0507501048014000080d00241c140301514240c11400b030b0144c2c0e42d038880140c4d0824034030013021140c807903403404100e03442c0403c04c44060740445c3c5e810305080b034890010400180c1000c54101da0b4080c0701d82080e08011082001000a01825404075041400c40c40801d104442c1ca000031102003079140c20000d00444250300551032940d00200d4084103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 882672706 1250 882671456 882671479
    0x706050a020904020d020a08060a210f210806100923040e07030c0b0c0319180e0117150c0c031b03070b0f0601050403021314040b07120e030702010509 66
    0x209040f0f0340251100d82d170159003c50b031045000c0d4440b489a82029003140e4034941a421b0140c201881c01194900b07841001291980500300b00c4001c000f1040c4507040036907021420f0b0200400c0d004c55118002e40e90010301e2450008019180443d0550120380041e075404060a04000c52621248455030070010b00c100d410350900d6080c1d6a6000f903d25404041000e01b050038a185410360010f102500844217400c018810740051001c004261010340c00000c00710192151510ba05480c0c20340c3c0d03d041d4448400304d110012400b644c0c210705040c12148052203d40d50014100d045c1c0d510707044124a001096100d944c04200c955101401805204020781c003960324110381440c4111204400c1e20103c22315800220302c400a0082e000c828580c403142d070b003007803020516144c00000d0442c410740c00300030302c43c56104101d0140c1c270301d035a80b09a0a018001a01304054101804c00c0c280304a021a100e00c00a07035089000d0000f46031501079030030100180d000a42c00c1508a50040d54030703412003007800d90441d040f0440c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 882673956 1250 882672706 882672709
    0xc09020a0f08091e0f010c051908041a0c0720010c12050405060415260a02030411040c0c02040b010e0f0d0201031b0e0a050612040308150d0503120109110706050a0209 73
    0x201113142c960180080820700741071000c007402e403440c0164280510009010300c0c14062070b0000700342d608045030f02d46602c0541d218500b5614030000c010088248454190410101d88421002404183e000c0c2100c26441d0040c0707005000d10340a2100403e0024401603800c00000320031032040b504079600381c1461410141c6880110307400390003075400700e000704429250641d2265001344030081c00c05c000d106610078411300c0b82185100d0715005403140d80b505500100060600c02d0444a0103810a4024002e2126610050700103005940010b800d0740b00c0c51421107000c1c4c00350b0240703100520070703031014001c003000206080812003580007402040c1e0616440c0d07400241c042c0c800c0a49220305102680b40e112284610f041404888850742d000f550280d2420450034084940701c01095502c10b034146440255580e5a00540004d00c9101804a401c0480c2e003015808000c0c010000c0d095400f404a0146e207940e2707a881c0140305458a01c18640300d2207500300856804120700383c116941c0501c070000b0252070013a04d0710 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 882675206 1250 882673956 882673993
    0x5010f0315112b05161d0307030606140307050a18020919030309060905033c0105010b12060d030807050c0102091e010807020f0d05071113090c09020a0f0809 69
    0x3140c514240403030755144545600303d031050036040384003078003c04116540b400000c0c10895000e502101c01d40c1858014404c01c2c4d07810085032010710b40c009801c0c014039a03104642c500d5100c1c11904a8803d0140c540e0201c0c487c2031048060081b9206038641003d400b0ba1001208004e42c01102c0340768000c400c42e00c3c800d145803090400080150304c60341e82d8010041c80d184006015006c0c40d0003a61003600700c0d2010300c10350100400034500005900a0085244d401b400e4540f4003c3c41d181c007020259401c0c0000010030001c41030107010280c6441140038056a502020803a240300381141c014045001070380410f03a074500c00c078007401c04800300c00300040c5004003010000b220320251401e031300e0031030403609010307000740d42e10002064020032980002e09243c40c01c400c2294503004020300b20401c10001180120a0184001801d03012010140600c8403032030a802a64028100ca100d0545d5116421200050480e035948226054804255501218840e07082c0c02140d000601074200c12252142c86900d071981c400c0907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 882676456 1250 882675206 882675247
    0xa180203100c1232131218030308160507050706050a0c0614011502060402030c090c120a06061b0b010303180b1207182103110a0501020c0105010f031511 67
    0x41881a6103090b810015568528101841d08811095074017400b00780c118002043c3d1000e5400b1001403061a54540212040d101c4103900800c0191170300302c00402d040e0031900240c0289900c0d51900034890010320195101c0c4640840101690b003d41c408004403846000600007818052402100783e1070141c40301000d40e00c02c0c085000301c1a800000401042d07188900f03030600d000b0540080d101628080d00001d0300c0310908240c490290b80d503100011030305042c140403201545180c8402c80c0c0c160401c184c03160000c1c041402180f01041507400400c1d100140d4106100d04298011080300c5c882e0f0079954219543e410b0000001e019000e00040403460080c04405000401801c2c02901180d20b0042401841081402004c440d2001d003c5010b000710320311010203007c880801038500e041054140b4040382c08040c0c104076903400c0e00406048408020064004100e62001e00b0000d028690300c032100080d4189052200a082d002d00c151a5000c40e0310b29000f02c8000c00500b040c0b1030400d8040300c241880480320 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 882677706 1250 882676456 882676481
    0x1050d110c1c03051b1603020f1504050705150f09040b090103050c0112020306031009020d0b07080412030213051e06220e04050309190f09050a180203100c12 69
    0x41a510b950756814030485503c40780e031741d402e2500341294003c1d01a46114a0208031140e5005041e83e00c02d1600030000c500910480074102c41c261090f41c4071046002205580440d03150145020010b803070b2800300c85000542d0542c2035104e240c00c00082c1042e980741c1c00102c10756001030311640e22290558601d0034540c001d40c0603601030300e1000100d0000608000c0e02001d072a440718418402d000d15514006a51440c4c030700c1031000012508000d00008918a4110000400080b404404c000005910500d40d90280b803088020000c81c0000a0054099018801c0800c2605029017020000f5203460300c40e00316044402c0051890171944100800c40c258809055459030f0310306c40d82c82140c0500d8030301c1c1c0e407000cc2c4506001c1c0152410a036039115280d11401c4a942e105040d9002c0c030404a03402690b418006041100e4000c1d1080c0ea18840e00e00039050441c0c152015511744005c024080c0c200c90050465660b0040107444914107104e40380c4e0080480c02c054204000e0783c80c0400002c0c03407151082d48403c0c0807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 882678956 1250 882677706 882677743
    0x50d0b01081e0c010c030504180c1d011d120607180506120423010203040302010504061b0806011d0a14030607020d0e1005160c09061401050d110c 64
    0x140340d00d01c0d182c51003010000c80d4100300c00e034040500e202e02094a2100038802d1070002084a01810100d40600954000d90f00312055100d43c803030400c0d0550701842c90702403640c503401d200203c040c5138074420b468040038441c0401c0010300324a02c25040340fa4450600c50000385021a1604d013600110329000d070484807500422108101e924800b00a00c2c2c0143c001c00341140d64034a8040b5848041ba8040c03c0075000501c1080101c80071070032040c00c50300751940c0c0d141c0d5100841d280d207881c1c20000d02911069078196111380c5000b06030f03002903d0310304001031002d02d943c88030700c55900d910004440f6018851a501a400400052502c442e52030240c00710041c20404201031103403240104041c10a10f0142500041d9486200c4c4070002c80c2d085009803000390400c41e640381051500e0b007401d4415100d11051846810b0920040200f00702640042c00e0665400800400c80c2684a0090b0408061452059070205005000490b56080c03103401500b101042118041d05040d00c82cec0c29940b8100c040e03900200500c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 882680206 1250 882678956 882678959
    0xf0d090f051603150507020a021e1306060c1106040504060611121c020a020309090a3e1e0f031f060e040c03061707060909052e050d0b01 60
    0x800841610540d140142103402c0d20350344d01d541c8020018821458100e40329400250054020306c01008256000f40205402c140605070082190000c0164907119403c400301e4908210b00030710030034083c0c5a460300c0d852071110702c58a50021142070280d1307156001c41b0411011425445074040c40300208115110b00c00300c0f040302c050303650418500000721408442d09101d103100f4000303055611241024076150050f40e034030340900b01301c0c254810703070040700e4000c01c20b8028013030320003201e6004090312040c0d6520b620500380065a24190030080000c20496600f00758448621040d8040c000c1003114510081041c0690101e8000140d40d08124011003025901000b00003801c04460400d80700c010000c040d8440060903c6009000281d00183c124000c5580c0d400201055000394000340c094a03c404060541c4000404403654444d10390103014001014810001131040240c05800d0280c001803501d0003505201c0e202c4120000006d4619039280a0102800202e0b92240343e64100f002c2c2c000c00c50900c0b1507 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 882681456 1250 882680206 882680213
    0x50702043c0e1905030c011515020604241b0e0108011a0403030309110d120201060e01210c03140616020a0510181704030302060601090f06050f0d090f 66
    0x107074181080040c5a50070041074158035000441c1c50b60074049a00c0c0d9640355a802824058554003841c100d0440c10343c40c141300c81c6170030ba0000384490210ba122000c1401500b280c00c1049072210b00655004040c0f5030802049007102460b1082c001164240c044001243d50004010038814100460b05c0b00100304c50483c2c60b0415640b1043c0c6601410148503181007400b00f15000c00e050340705070720001e4100356030741400504020700e049400005800c0200000a0004503061844031900c41c0c01101c0c000d1341c030b05240041c0f440024640c2c5170486a41042c415036003900b146a100e01c03442c42040841e860441c000011000551050006c40c85c8614507001f80348034030b091000040380074100f450031029907002250240014000086030004001a10b02c04105503102100346845500614401041c1020070401114207409410281044034001da08480310354441e00019a0289114001e010034101c510006000090294004000c14504090310350300d0984400350460440d04629412100d1501048148052 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 882682706 1250 882681456 882681551
    0x40e010509162a05161e083003010f0906060309080a120b06070602030f010b04120b040813080c01020f010c0210051509090303100801021905070204 65
    0xc04407200d000024a04070000150020030380c4480d6200f481c214030001a40e42004400780920a9406411541c11198824802a05080500846104140300d13031640030030b4140380c14550200d4044a010384000004c290706c01088c07090341c901c2203540c08840180d164001c103810700207500a11040c50035248582c20980300314280c40d9a070b40700341c04050601c2d60b0103020030102c03400c582070f00e8107906107400a25642120140078082d0100380c25480100800c00b142441916001548160071000c010b030990703038945003925614040d078090480c2c20f0584c0b00788100000c00d00740000c1d8006024084c810f00b0001540c1c5a915601032031b80000c0a40d0b00655031510b07a0396010040a03002d20700d5200240804000390a00079503500302490141c034440c0e21100400c00481e41410107420b2404c02912400e00c1d0315000fa00d150346c0e5403007501c3d03d42a0f11041400000d240c0d00c18401d580c065132036440c11500380300e07807424210703516040300300182da019644a502240c10341411489603203102010200c1c62408258280042c1d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 882683956 1250 882682706 882682711
    0x11205120a05160204060905180c0d0302070608180303010f05030f011118010c390803040611031603020c03100902091b1b010501140102010e06150103020708040e010509 74
    0x1001000e101032010160080250344801a1000c02407003003e1441c000a005014a54000c00c82c0c0c91801e1700740840c03075442c490400c60f0200814200c910580c00344041c0108202445030240050308403a10038020544a450000e820480038000001780c60035040c0203030b055900a80c002215200214070801c03142c03d0501440030410030740d40c02001800e0484052400c1445100d41c41c16908100060103201603005801004e0f1031038006586100f01032003581940000c8215103114030188176660100c80450410000c2c00043c1c0c1c40131f90241d814245841c01c19140041c11500300540343c0018032400058800020030040c0d4140640c1c010912803200800749400c1554921281103824204000e50015881780c03801c40d500b100c41300d07114031944006410b82d00310501658510000c40741050400b01110001508203074162540080241007206101005a00704c5034811042e421580003800040d210843c90b060006d030032481030401615203115136603107820723990054019050181d103050040c043c900340f9051055 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 882685206 1250 882683956 882683983
    0x41d060915070206091c050f0301140f03060c07080d0e0303130308070c0503040e0907171b12150403120e0f070501030e0307380f0f10140a030b011205 66
    0x1200e0700f0410f071200d8455945506418105411001b603900a6204204440c404000c224105481f940c4a84601c4000b101c4176000f28818450483e2004680c5004603800d80a0031140030040d03e01041c0c0e981308d0080360004c54110030b1030340c0e079440701c1c8996000034001944540700320407240164440340e00d0042e000050180040b000c109003101250000b8000008032010b4036410310f60484070b581c959540300e26004681c0c10141c510803403c0d01d003a11104000411500d06411034148040c1d281c140000d0101d1031505040091a07039120351510a0b0040c40d021145800902919110b15600703c6030000505840694207045616806218818120b030014010030010380720910702440000401c841065480c000d100e80513004d0040b0f24041810b80611311050300160203040da440aa0030001d00302022145000ca6400d5104c0610800249a0410541d03a061041c0003c007200340040341083c01c616101445d100e0100d403c070030411804401305851103682c034009d04250202c0da401d03203164038050742010010440c18 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 882686456 1250 882685206 882685213
    0x30e0a060e03090a1a09061b1e19210c02040c0203040812030c120718090b03100b03030a0f0c06052503062709060504050105070e030c0f041d0609150702 67
    0x942201d25030782c5c02c0791007000084076813030b441d908840c0c001c1d210003031200380007442485484050746410200382d50304500c041154064500144104d00383c5440030070300e004001c1842e6808000000140424585003070030f01c0081ca010441c112a55004c00c6c1150790000b11000035030301c01700d010400501c00704806015142c00b010070340d0560400300344001440c01405c081d42060786802000a05c00d620a0b410840d20600c401c1d1070b801413540e40c2c8001c5005080c0341e001c1742d00900442d45403a4030017040b80210342501d4070103801946001c04a1784200c800c42c003010890000c0156030349540b00420740300e0240b140614000c10080c461501c6209805040f40905c0c5208824542009000c01280d182540141203a2400240e900000c400007020200101100e000040c0054501014801440f90540c40305102d49450703110030026035400020140d40c0c1401c0880e03154060742802c140f0100d8100343e0070103502d031044070400d040d0301d20a0a9149040407411101e22503180c1c06041d41201882410b4101038001a060018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 882687706 1250 882686456 882686489
    0xa0609080d0c083415060605091e0109120602032508010603050601200606090907051318051203070216061d13150810021207030e0a060e03090a 63
    0x5a03c0c0e640980b146007241140d075042064800320001c1810000ba44200c00660a558150b00d82002c080c1070300b10000101e145825004607140707008408444521100400c1c410141c0c04440492980c0c1010604c0780d030410615441c0091064901800c100059218010168503440c0c200a40c0600d41c1c8024071407281004080300700c3c915150094107403415540c041c580440e40ea6608001640e10401040b960305c1c0303140340c08507112540700010400034050070089a80143c152601500203031b417130009000b500d920010505203842d440b08030b0b0b13028010201c90f02003c150603c3c00d41c2c80d51410704600303007039809810100104206840d50305008541c4d0310000360211405403410250001c040032100c1100640722811014074000c2c554440c0e920507485020000180f0060b0407002c046042450a4032030403103c2d101d4801e6514030b038040344c000d036004151603994602e40d503600c1c408200d02410f03100c48110090f0081203000320120341c1a00071101c0c400040d034015a070300d00403a0203012840035540d000c0003c283c0742244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 882688956 1250 882687706 882687713
    0x1509131b140f070809090903030702060603032b0e01020c03030709091406100e1c11030a11010f030b0409060204360e1009030c03110102030105030304060c060b0a0609080d0c 76
    0xb55994141a00d09036a1901c0c642d19103240d03144610f0034800c2d8000800d004010138050000001c40c464031041c0d0940320300362180400c0c1981c82c000e030f02c07106035001d1000080c14170900140d4001810301c400d081010510b400e500d411242264441d05660740c203500000104100345421240722001000519020080b42640d600781205520025240510900402c2c891070f01181c8100602001d001008001c2e01540c00700c50707031000210b5407000080390f00300740300e10701c0443c1450080703001c070030460f0030214140d4241e400b0401183c80511401038070b8203042d511108480e20361120f1003455080752042200694503400c0c40b840301c09a20780c401100640c03a240041090381d40101030304008007200362050115400c2c1e001145282000440003110050be40f800e8800301c1816030020800000c18040d031114100d0058280c00710303081c0c0c40240a902c0d015401003000b0880b0a204451600c0303128081c0d000001ca000d0114009140840c4690003400010000281807107000303800c0c0560400c42c803607800d00c0e00c8440c0c180d99 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 882690206 1250 882688956 882688997
    0x30c12020c031b04020d06090b01090611070306051305030d05060108060d150c030e0105040f06050f040c050d0606030b0a0b10030c080414011d0d080f0708061509131b 73
    0x50b0f00f4440700c049000316606031581d4056070501c801105007070001940f140c0120000300b550381d520070700203008800001040c1d409041030505064503100a841200d007140c460310081c04010700f03100e0185103d01c000d400810750600c041e1058283c8280c0101d0300d404c25000041049501030720345c030f11424410003500001219000700780704020740000041030402012406500400030441042c0c569401c01c82040304100800d1030400d0344500c81c031b60802903611020482c1c0758680007200c4c02400ba00e100d078400c2c82546020f030310a942c05807180c6800310f18103031240e865002c420000d54900d0121925489502103910f08a901c441c05500c40b448c0c100a80e070030b2104020800240980003800d2031903113280341140c0304429080020410211080500000ca588a01035519001641c2e00300000703505c2c0c00451400707070304e0864160181a05a591503410385030b980c200001c082ba00c1c00f220344c02460401042a051f1642e03104000782550b09100081c2000300310030b007001100c1044814100b0805800c07030f100e14441d400d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 882691456 1250 882690206 882690223
    0xe011e030f18050a0203070603020903070b07020d120c03020601080609120f160c0905060303030f01060f020a02100e03120910140c070e060f1203180a12030c12020c03 73
    0x1480c0c0460401200c030700440c010485255140c4608000c1000d4900340b01000410b0514a40b007507045500580e035a000807002ca00070816080d5064214000c1001a001c1e240090302207640010954008050070707030380f11003040300d84e041284045101d1b405060305240d018004103004090010141c102032400c81c984648888403140413485601020a16400d600e0045042e290344074400a483c09046050341800b036900304441c03040c070b003100d800c0c00d00044540c18007005483c014a07200740030718031a9003485c000340e500940481200046106840503e0091b0b5155407941e90310440c244c443d02072191181c000d260400f000300310700f81e50f105010004031285444920102041c003485142c000160130340d100707841e00588a180d0010b00e96204006000c0383c3e01541c00c042034040c4504842c0d00d503482006030300380800e02442485406850f04207019282c0ea4040d442078429150b075006110f941c1032522402c41e00301c148441641030b0002042140000d0400145a8142040c0c02940c001820084414030000355603a500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 882692706 1250 882691456 882691517
    0x1030b270c040908070204020a02061f0e1311150417010e15041a010f0f05040912030b0f0901090c02150c0a0c15020a17150d02060705120d0902010e01 66
    0xa075050701c0f00b40036040054484180c0c0c000c0c01559039070000e000080d0740d00001d40d000d21403030450b100140111502a01d2143c2100d090404003683c540c0c030100e4000002d00018025100d0206030340365000c091352880f0440340d00f06114491140c44034148020010254103e00b10410386a150500c96000e5500005402c503243c03944100c5030790255074030b10303001c0b0a00900700714000c400e6140800215200f5910030110094a2000c0b0345e40c100b50780d0310350403c0309407402c200003c1c01c402e45406030384800d5403081e00301100329803025180142030010030b0302181244c04243c1c4810300c21551076a100400c5981800800d074a03080f8400341d02d1040c10150f0b203075082032140d4126101403001400750303a0300308004035180348400d8101541c01c54540d024600054082c050448001082c805181c00043d410a0000b40d900801d030009485614030808a6080c020700b03038001c03c004d495602c2124684510408d4400c001c2c030a940886001250361802c0b4400540400c1140346440d050003090384015140000101c81e56104244 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 882693956 1250 882692706 882692711
    0xf0f03060b030f07030b04030f03020f090111031b0102092e050903151608010906150e030f07030f110108010302010e0f0d02030d0215130f0212070e01030b270c04 71
    0x50300024540f1042c04112601c03805010300010511001b1134101b8841ca000340c441603052500b180c021400ca1040395000c54510505001c120030315441901d0540000f0204070440f440c0c144c0d1200702413520100d84020017441e0f900007a00c400e003802c12644112403180c0c03200d03045800f1100c494016000c0010700c16000200310700411140300e16030b0200141e20322020170781c80c802da8500340f4254260000e11114401c07000700704c3d44000090011803d00c1914121020308014040c50702622500300c492030000c1da003550b41442800000a2004c5090141c01c000358404c007080c0c29509030034503140038240d045401c402d040c041540c00410150342c010b1943c000044003100c1c6100c800c200032000a0f40010358101c040d4040c0301700012510859000142e202c61028264015102e13941d82d44182404584070000040c03186410703103c100d0050422085e0351100500220a85040546500080c2c031594801d80c01039030421440c40620400c21004031101011880e818441182010f00c425120303510920340b9500c82c003a56 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 882695206 1250 882693956 882693971
    0x60106050a03020d090804150f090b0c010204180605010f020607020a0b130c060807030f09080f03100806070c03171005060901020f060405010e010605180406021b010f090605010f0f0306 81
    0x2c0c801e07811a071038628080030400440d03005040c161130682160003a00e80005513462203000850080e40000c01e40c004940d070750350542d420040d0140f01c80c1c2000740c1c0d2074015074082c03101080c00b120382000851100801400050040d01d000001848010048030034000d5410044c20b0100c03030360307001c03850500f15508169900310a4840502d00c00590390000d5018150040c10079020540039400300e442c5008111a5806100b10b60000e810701c2c04603a40326030000c00c4078804005003400c400b561005180d008212101e1980155500c80d0340608020048488c03800050001041808040c1c0011018039080c40c50b5030704854610b00a1114801c0c00c10302c0c01298860707070010071010b80c0f60f1f100700207404c0c8625424059035154280b51401901900034001c3c2c0310b45c42c0d4204980801c1900b095814054002c035800c0c422003442d122178890f50000d60242100641c440601751a518182e20309000760402c0084050340010308103103e0030640200e400c180c014a100c480c48034020060040000040390540e034000d00000390b500c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 882696456 1250 882695206 882695227
    0x638160f02130b0a0b04060207140a1502030304120807051b0111120f0f06011d030705122514120307140a060c05190e030f0609010f0b0604050306010605 67
    0x440d1644002584100b1404400160400d503801002c04281c0a0300c0e201c1000703880341c0011507107000324010079005034003441041020307510986101d0780021300500b02400369600e540100e0052411503100d42d01581c000028441000340401103c405200d41e40751440d0603050100c001040d0f40704500d0781500d0945e560008040300c810a510100d50300d513150700d52503035071500c03a01b540443c29401c886410441042500041405114004540c49030340141d45081d44c0e00701c940c21203225507513803200325501841202008180c0e84c40d0b110179540e00c02c000c1c0d40104100b44540120900ea00e44290841c49809c3c00c0f07217000c001e05162015040d11800301103d416080e40d04115050f0300d0350040d054003030403100d91882c60024100c00420080c1180d40100350502c50b80008500558aa100f4601c0c40442c401c801103802c00081d10500c04020044001410394801706000c140140c5400002c0d07038012042d035075034110f2950034501c520800410400a40d070300ca08007880c1400082d00c03800144204010700200041820a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 882697706 1250 882696456 882696473
    0x30308191e1505030604030807110709050a0b0907021209010c06020909010b0c07081917160606140307030b010303050f0c0a0b04111905041a04063816 66
    0x2901c000d040c11480300d01c15100c100c0c007426000382407180e09003a014000c20725041c0400c21038172035609074036486515101d840084814213030144210f8164050f045012664103640c0c02042d000d202c44e0000869070741d00e40802c0000300880581450b00359400310820507a040140400d54007418002d007050702464400b414604003034461142001d6001c1855800820320225040c040c052880011003200c44460f1140920790340c1d19a421800303e04031659020150028035402c42103c24841c500784010300741021002001082010407008540ba07540712070741403041145100d4094000b100172070090080301e14640365071680c800d040c003015040260000c0c4407102009900100d449a440003c11101c0104c4d0505009007018001d880480b4072075000c02d4010f0007843c204411408a10001c40f1010b44039103800c0800c03000700340100022003070760100c4407030000c2c43d580c2c2d110301002031664019282c9400582c060301d01003102003980c03d400302a140c058004510202c0d50a555140320160083c41c03c000e50f0381000c0700c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 882698956 1250 882697706 882697721
    0x90703060506041d250e01120201030f1a0306060102032a0a080703020f120a1e09180603020306010b0a0203120402010e0a0602010e060c04120f02040b0415080c060403030819 76
    0x2a10011000703181a03411000a02090301a4000c0c40f81101c0307154450302074aa4004d51059004240d86c5000601c020f414486802135040d205040002e40c8a00d5201180203540c9500340070300100150301e00000d41818180541548040c0034400380d80307005907415607000611140c8035084660a280400c1c81400d8008000c001c0d660f41c1c0281802e42c86210500d4000c0d91080303021819285401a10300c1c0110310449001510740c11050f6071682a4044465400da11044440480481c01c000d44040001030b040c00b52203c60655841051010076840c1c21401410701d0884103070711442c9126000c0284002c055404003d40d07203240c40a0310000c2094540b8001242c043d0303154001170b98030415541d4005840c035015401036a4042141d000d451955075161820400d90041e40f18035084110541e115000058590030050880c41c8000c200040c2540e40030081012030b0a1590302003e003092180702408240800c02540d03100101c03c40d00360385000d080d540c00a041d41d0000d40160032800d548000c2040d407444940160a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 882700206 1250 882698956 882698981
    0x209060301081c0207050a0e1e0702010b0f060403030801030f03170c0417120316200303100f1215091b1805090309061b03130906080609070306050604 66
    0x90316540c5400741c942d162220055492600300200911004141c00880d0013021120010030b00307803045190200c040700e803200040076030815020b00382854004030019100319000e41d4466000007100c6810b101880801400a001d01e0303c1801c041c8010800254032a110a05495105407e681c01d003245140035504440798804001101784c0703000401c01c0c0504030781c0c080e10032188031110856036029982451900c444085402e040b1400c030400015103e00a00c55550800c1800752408003510703100034129091409031900036152582000060107e0390183da000b010182c40b10f400c9072420240780001381d03c41c2151015004264000d1900c462141d940551300100045400c001c004200c00003000116074405100c0c010198019210f200d12000d0850f00c0c410f1903c03e4944000462618101d0010400642c10400c170680c1d00301400c3d400e10128003014005000414903145100c400e20f81000500c0060301c905800c0034003681d00160400010344c100080a10480750010300004442e142c1c0d50101d0045c00d09464400e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 882701456 1250 882700206 882700219
    0x1202061e040b120609040317060a0513020c071e0603090f02040e07051e131104031a0901050106031a040c03020c0114181504080f130905090705121b040209 68
    0x34507984580000c06884014961403c0d80380daa10b420040104000d5602030b00050341c00b50500030151420b0005508098010241a10300d03980b0302c0014014669015000c2049402194200260304100301c1300b00601135005c0786619081e6101174000034012030344108820580c13550103000501c50a002c854040036005001440604150412281d50749034620406000f40c000c0c1441600c5010000390400c8a090010042d0310443c2120f910798014007149000032a07110010040000069070050030305568890038040700760703d4a0901582401c450050f4003120602d8144003080006a011609080741140101c5000602d808100f001700c1c0240160101e0000643c600f4030b40d4503045909010302d5100e26102000340d00601506e062207500c0e5240086100d4006030a280410f002034501c002030702501220034400f500701f031200780080018003581d92206800700c2e40c0c0c200380b2011403414480e002c0645015200d0850f0541d4041c5602c1c0d945204c0510516a0740034002c840d5225a61501250703007192005001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 882702706 1250 882701456 882701459
    0xa0b190b091e01060f051608160c030c0f03080f0c0115080c0a0914010303050a030e0a0303050402091f051005091302040f09060f0e07050c06040506100806011202061e04 74
    0x2d00012003075010040300821903642c0002805449242c0c450038030030b007070b5072103d0405041620848407540c6581c801c030344c194400d1008040088000340d00d20f5015010340c01a13490a45507090500011004c0e42040c8403036600d4144c24004520b100d0100d5000e00f080b6660144d40d50000c0154500401c0b0201a80400c0c100d50040021000b0001500280d45c0104072180301481b03950305030040c200ca9811091440207449d2034010008207000b0030141c44005070b0303400c02003400c0390345010b1a800c1c00c4031401c00300d022aa44034140000d40c105048840d502019001450042000c00341e034140720845284540b0f44101100381c626540c06101e0700a945103a24050b10841c0c090b18400702c410040d4229018030414400c0c2c20000040121082c06088115007a41c10340c2e030f50403410112007080036400148803030117100342049444011141080401d00c03403070048014060780d0400600f124501540ca90018800e80d000c0030050100c202590b0049402c2d81e412103d4940c4e0704080050b581345a0b0003648030081c40c4002080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 882703956 1250 882702706 882702721
    0x142030501061805090d05030621010c0f02030a08180a05030735070b040309050603040b1501030b03062223122b0237020a0b190b09 58
    0x8810380300007034080034101078901d842c001107130303001c5a0403840b540c0084071668880d03000d80015600040047c24070706805480c08031104d403481e560034082d00d043e9940e280115003198000c0c450700c03261b101840654038028190500a110300000341160f40c4085401c000801c20071400c00c11581095442001c0e030382c6504480c2003440000b0210316258140c2d6101d00c00d801200c141c5482025403049604807810b040a0540d114568103501c024011030070300548881c04180da0341c41d140a580320340d10840412070300e80b4080c1521100e9030305114031141498180b03000c0d5800c503079000c43d08941c0034954120702c4001072001d5214661048038140060105c80341d41a0f102c0b41901c01f4203241d02a4407107081100d00b11103076031103941340d070344200030a00402c94182d588842541051000583d988400728001504040324042090410460191070058251106443d545094180c83c0c41c04001446030004c1c0025030300c580c0381d045c07010100509842c0321b00d00c940c9a803025496284d1180701740e40c10242510480741380a24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 882705206 1250 882703956 882703961
    0x11040b1905090f06030601230a0e0a141504110f0a0903050c03070e060103020703020c030601120303051006020639030703150b0a0513031205040509090142030501 71
    0x181c20300401c420800205400d440f04001c0e4094500500107203003130ba00c1c00c0000e80c1c400c0038044a81c5243d01d0092143c0000703964a415100140103280f1000c00e49040403403004003150fa1704440f07155402c0012081102d0901a03044100b800e04007a103000c949049843d0310650f0a01c100c89501d00000f40120303000d0301480e03001c003641043d02d20407002c8901645000301059a074468078490905d07856428000a590365100e6000b400e0254841c1c0121852201e105000a003840ca0907008100d1540d16209004181680342c0902d40c0c2050014560b00130f01400c0c054000d4880c06c0c001d11240c94030305402d02107942401c569820101030b40951035141441c100310b16018840b50300946210000908280210030346a07454035058040740c0b4055506460703c500b040c000d80382500844008507620381c090310004007180610075007188060340c50361002d17941c60501d0104641e00c03030301804d0701d09646c0c542054104072074001000b00c0540061a10381c4002200242400482da2a04264102c540b00302030200104206054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 882706456 1250 882705206 882705209
    0x20130111b1203181609020c0106050103110304020d0f12031e182402130302100203040e1b0c0d11010506010f080a020d0204050303070305070c09020a0c11040b19 71
    0x10a0301044180c1c8880415550040c03040b140c001d201040000c522103c602c4104c1d4200c1e081a9410313030380103501c5401da524001c0d031658004540d90b078000076034001e20142880b681014000c2400c040000c4a50712030301d42410f0000a00003070140d030140301d00b00c01303019071100314006144d0310440c1ca040c0c030020b03584000c01074441040c8100302d008580310900f61141c8107009e0444c401400200140d01103a41e0303140c40c01d6480c0040100b400843c1c0071025030110f4403050000b00340024105400070115440c5206002030780072500c842000b19041400284041100700e000b4540120f50200e61140078030b04400701c00a184100c0c0e10344000c0d880b55030482d0301401c0c0c0245a403501030798400000c004d590b031518019948114289120b40008004000103409100c0030b0303000d0140800d0290006081a85071401711745141d11451042c1c001c50804038640d0100891200c110740500007200c0150700308800014090100034000000419001c0440c03003412840d2281d600100025100604881450612100708044100103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 882707706 1250 882706456 882706477
    0x10603140703031823130617100e0d0806040f0504052d030f0d090506040305310902160203070b040812030103050d0c0303090b070f1101050402013011 66
    0x110340314204c0c2c1d84401d45800c444281d0f44082101d0700324035940b54107021030304c0410350000030300b80c4030405001d00e482003030041e05d204001070307210880700500c50345003801e442c0712a041c1a08151018100c094007207008042420b450400200549640e00010058400800003d14035454101008148000050340039510f1042106113290805a005075a4010000010b001190b900401c140c10005014000803c0280801500080c00103d0750382ca0314100a000e075000d40026a02060420072250207629440e04410140d03501d8207036194129081e0341c00c0c0c1e190b214802c06c565000c200b9440c820b00344010800c03002d038014299000c02d41c03295040d103a00d410500502d404d9114411262840e920990f085070b0603260003400610148aa0310011142e03d460208210308240c0c032841e03000d000030072038003480d03000d0205ca440c4d80c0a44c90b10818014205006185000c115078102014000540d81010300800502410f83c0712800e0004038400c24044c80151020031181d030340c074000c10101c035840080060400c0940 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 882708956 1250 882707706 882707717
    0x510021b010c050a0c060b0612090613020901030212030d14150405040f0204150b07080306011e1e0509091e06030304031a06041b0207030209280e01060314070303 71
    0x300381422800c850098018074041101000025a810302441a140e40705114800115903a134000000c00e40c0c94120300c2001806003040014801074100521843e80d001081c040388600788081a0002a0721907010b11000e401911304800d103040a1405100f1503500010403101884102e200844011210078100c40d540c0905c142410411024030b014040c050086411001c80c803090038050f02007100038104a0040327603655400c4000018801c000e24003030107026000b030382d226840740b0b04900054045105d031085038102e28001c2a01c003a0b0560040410323040840401146a01030340208010364661181c2e120303d9a21034800c0003004840c803c207604800c0320302c00300302e6001000e40310101031694038060303800018000001c28100e04e080c855181d110340e0f44003400500106103030001080308042609a03400800040e00002401d01c103509080d1046038112080d00340700301c1e074200c0c03102c0d26111950704124240462910307480d01c0e00f0603401c250001c802950b003007043c0500c0d007441542c2041e910606c0c0d10044000c144d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 882710206 1250 882708956 882708997
    0xd03021605041e020a05070c080c15040510030903030e01140a061409070f051917091209060c150112050606091009050a110301120201020601150c020913051002 70
    0x30980a00110000d80f02911106461081c407450040e410010440003008010b024010100c1e61043c6d98200500c801409000c58003001c10500c0100314000c0103529001c141008200490b4540c0c2e00d106a50031910302d000039103003406240480c050b0aa0741c0c0342d80d155600300940284811000c0703600500030200a00e00f0800d0380d0b90b400d6010580c1000d80c0300643d02c501042c001034845e5014401103000d803402441c001d464a8803201128140c018920f00803000034050309001199661900c1e0403d40040c07c41005100080c0c1c46090700843e48142800c00340500008540c40c0c04c42d503000c100e41e03030001002da4850040c568556100c42d40e07581c0c00301c0c0180d505200700c2020440c1810b190032902e00914002095002907130401c101309015000c06000c1035440b83c1e54008255254420700095070103040c0000c11003200d0405030000901e003580c10381251084100304040031004540150144012a03819101d40b4480d80c1c444000350754002000b04047e0050050000141655100d54007d0401c088030000c10142d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 882711456 1250 882710206 882710209
    0x3060c0302090f040e120a1e0c1a040803060d05070b0f09030d080c040905190c03150906140919050a0c0f0c0201021203060a0317130e150607110d03021605 68
    0xc6100000a407070761b030052840c440b0001c2c0c907507004140310161401e000a5000f50600719400712009040c0c00000103010003041c108001d09412218031044d40450020303001c0c101030300c40151903c809455548264100d405030b00c100101404240000c140c0e2500c01d0f42c40710400250b03021190b00a581c0544240143c10b82818260b001d1350800d8040c0d8003e407001d0341000d0806030240002c0c2805405188441005030f20180280c01c80e010b2445902c1c2503590100f900c48509881400612998003c101854200740042c0710b0b000300c1442c2d2901101c03080355808401e84603460200032040107212072700903060800701002584600c540000500e42c03595035500e460716086502c22180d016038072800900513000401001408131140700915001040244140c50255036543d031a210b01410007802860990081045018040d95a0414000341460480725401380b40030300309110009044141503100d110085404014003a0086011190120160141b10148403c1c04c002e56a0700c05085400a0241e2621b4041205d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 882712706 1250 882711456 882711461
    0x3031103040c03031404030210090f17030d02071b030c050f090f040f060e070e0f06030102040f0b0a0210021c0e0d052b06030b01060e10080106050306040603060c0302090f04 76
    0xa54010010b2012907096035030840d04030310315020a5100134010300010000d42d407000c89809007120140c40c0c07030301c406140141e002c0085045501c410840c03000c01844420214020007200c04641210200580c3c0c0c5106142000c0314409813280b00540125241d004402c02c00c00000b20800e0b96070450300c0001500d1000101314881d8000c031000112800d03c08041000504050941c203030407803041b240800c40318000c8c010585011080d80c40b07034000140c0901403042d0010100303034003500076500b0340095140504112600d0070080c003500c60041e1034540002c11405880c400c1c01200c201410070403081d941d070851b0490109610801c42220003e0901d44509040310b108c000071807000d11849500c0b0542818454170211000f440000703150800018441c0d00040044030610230840603510618007410503504190004050740f00c0110007070b00030300c840d0206007039654010001e20704646852411907601d5a80c80e0108004e010744e0b030301c014480c1c0c0c180a0384440c07803030309a0043c0400200a44600301199a0389040106 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 882713956 1250 882712706 882712711
    0x30b0112140a0201170a0e12070312090b0705032a09090921090301060e0901051012030504090e19060209011403041a09030c06131101080708010605160f0b0403031103 73
    0x100d003001c00741c880c1c5c848500e01041d80c4000f44070f50001c2d07a680740d4540a81000c1c4826a4240b04500003e04082010340100144100d1840380e1010400c030308103a40c0d448400c0c000607284100740000440080c2502c586010038001c01c003100c00c15a082d00102e9074450f500758203c004140c0c400c1e150040024521a00001d07000c04015180d821400500c04000751400190321502469400d9525010007040d0003203050801402600380348000a0185402c03020f03040c0d01c2038581c1118250001100d054400310384c1c802c0658060b42d079402c80005100c10b64082c520700d8450036038034520154240f0b140c90414420194043c0c0a142c0e0282c0301c81154a0b50b40c1c100340c8061004a034003d10102040302c5000c45030b411952120f074044903210440789010603c2e2429413400030210744842c0c980301c08007a10000c1203c105041c40c240300d4282085c03801c0307091281020701034500500500d410490085031225411a095401d400d0140d04684403240c02007180c203041c040610100d4003640404e050030392282b008100f2804480c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 882715206 1250 882713956 882713959
    0x10312081b0f070c0e09010e07030302030702040203131b08070501020118060e07051c060b0f0d06150b220b160f02010e1203030a050c1e07020406030b0112140a02 71
    0x78450030180c0c1c0a8070380c0c010300303031429400314240081400a0f40300441c6801400180e40c040d074091408510050035100782c920240c0d01904079a00810009400009450740315604450160300d958550752500b6034007015030405440010b84079808094280e42c80c52680598542d0015900c0554481e001a4241d4100004126102880c0001540030a92951103160951414801d45034a196208000b4502c01406c1030309064804001e105882040344501c510b45030076000f560349030800c1c583da00c00205035543c040809407401d80c0f42c41090005480d1035001c0c4001c0c3c209210250388aa580d90740303100803a1141800f00c00c0d0600d04103000300d5100090000d0b42d24942110a4410b98000150f4403c02504000d1700100e040c06042e040000065440e00010303640c5850f0000150b45910b03000c0a08007d0380c50141c40b219940b101000401c0c00c003060100744041c0318a1042a140e030710300031440850010085580041c12080c43c0743e00214180c0030310750010304040d001f03820b4070900000296003543c0310982048000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 882716456 1250 882715206 882715231
    0x50108010e19080f0418050112032001060911041e081f0b030a0605071b0203060105100509030f0109050f060c03011503150602010518030f0919081501031208 69
    0x1420382281240054480d610441409044c841c0d101300004c0d050300700d500407481105110207110f40d40075041c8915401070803002c0707800040c201c05880c050f02c000d00c01d0720058041c5001c02500018a003007504800010201c01000f0050140690498901d54120b409501e240180c01300e100110f151842c40c41c0f000b966400b030090442180c41005144041e40710071042412261501b030a000c071580c0074804004543d000d04808220381c0b4007000010301111056003900da14551a07682100580c400061030707415500700f503800003070b00822010305070b4441c0110400030b45e25101d03080006d0711049040d0840c00300107110710121040340b1300345099542c13160001c456a04002c2005c2c00104400140c580700b074058111141400075942038a41d0340c0007034510242e004003004d80c4d1502e0902000301e268045a0f000d24800b01c01660918040c1d0200c2d002034400c124489101e0000342a01e10410707031141ca21603000308140d2045600441c0c10302400b2082e00d0007407109445042c08900c01a8040c0d000300070b880d128014034803d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 882717706 1250 882716456 882716473
    0xc0d06170303062e0305070905041b0516020a0f0509010b0a05220306022b02040e040210171003200d03080405030f0a02030d0b04021c09081912050108010e 68
    0x14001d5604a454500304e00044c070390300c2000c0c0003801c04041141900c03541e07808182860400c0d4040c043c99199409180140d15260000c0780030248560860340d82445854025940c007000b000079030b00ca03418030310702035130003069224001455580d0907581411034009031210313602a0f903600c503880700d203010309051140400da042018107040c0c58100194000f0004814822000c07540741e4403004101d8200f543c2c007442041640ca00079900c2c0b0b4416070401c882022585043d494641044c114a02280740608028010040702d80742c80780281c041c01c0005d1180203d111001510b10b0140d076003884400051000740c03900007101c540380358282c408880800100c403000d0705001100e18950b4085407901402402941c00d03000c1400148503540b4900c0050183d00307031642c01180c803000106c88070360490320f00c0c034011440795204011401004ea402440301c1e40c1462036485c0000c0341c1c4824205528188100a0f1504807981683c8010a05c01e4008000150164001d10200b080d6030b2540340c62402c07180c0030b580300e01c50391384050107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 882718956 1250 882717706 882717709
    0x50a060605030408070221010e0c030d0f030b0310091a150d030e1201150303020c04050f1303021203010308040e151f0c05060103081905030601090b210c0d0617030306 73
    0x2000031710310140401c030101000300d01c01e04482d80380030b0034000165103036159801c40750307010051840d10b04c80840240c000f070410394030060800003d04045205050f04c41b41584904e41d020700244101201112060089100528042076204440e003290704130030341d10a002c2296180440701a0310b0000c400780880362048a0398400340d41c008031601620b0341c021422603107c08240f00c04c4c042e50308940245058010f106066141c041d00f884070f4400c0c807a014030702e040d0401c140464a1000a50000c80100000440d021903050403420300100701d0705090342ca240040000100450b01c8020400c0703503d441ea01d0b0115440f1005941c200343c0240040b554400d4000200b80c0064030341d0141e0007a2010141070101c0c500f41b1541d522402c4c03110982c426580740e04080f44a1000b80007100580030f04003950300d8041e03c2c40c03804000207481c000481c0a80845140c0114400510025100040b24401900c81e11481c040c0b504102d00e0205a1103092005d035141d0910304005401c582c414814243c006000c0099802d5594010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 882720206 1250 882718956 882718973
    0x3020301030c1404020702150d0c020c0315090703120f1209020d030e04060e011502011119141213030905100813050a0b0c0306030606090624040801020a0c06050a0606050304 76
    0x1d0350584c480c0e800c010550060b0b0b0b800110424030580000340c80d0319030001d080c014049a0341c02d1211070954202144000305950045601c50b440300c840500003d803902c54800e454500402030304010544501004100e4009070800b4981760340394007540e2902042c2078103002d140d003a5210003d00941040000000e080020301a80749002840d0000c1d00000d0340d07a03602c2c0d822624088003a400a581180c01e82c580c18109030707082c0200c4540f80020164a40382480391a28100e000780c00c10400410402e0500050010101800494001e010303054500e00300350820510251807440b2107102200482d4201e00b000440c0c0c02d25200080c141c14040c2c071144071559a1800b080a100c00303070081182d660046d460700600103008415054010080f2040450316464110107247c64000050000c500c16803648041140a5840301c819108042902c0491040c8916410444100740520342115450354004505c0381e41c5103600c01813103082c0a000340b0052185da110b6010001c11140d9a000303803000180e04000040c049010030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 882721456 1250 882720206 882720239
    0x12271212030f0603060506030d05040e0f13061a0307080d020312130803070c0314120a0e0f120703030f02040807051512070c050c04061404151503091203020301030c 72
    0x241000706041070035504041c200c0f0303990740003150403030760311b00a10049044c20030542c7d50291035403c11900c0c02c1d0034012540c0413410300500402c80f980d4614001118088201c0c1c42c0354505a10030003c0c40b03540040b1406440a00c0304d0901503010748990b6030001441900025046490b0b006600a1351911240100d0110080401002801c855000101d11400a0f21203001076105448568407a4101141403070018681c0039008013100f010341c004d20403500044d001c2000c0580146c03442c980051500c0310512050b00b440507030000302c8414056041c5103144606800d009000b0f80344280c1d420010308040300d10b11012802030b40030f01441607010060600441c01d182c400c0524140000090b03a08001692000070251031044a15500007580565204104201004003958811048800780072306410300c41c00d4455100000070980c03290303803500000b410313011311091100e003c3c007596801400c441d020810094041c11395240c0440e002034800b041100381c28468429207040c0e03580489a80f12a525005ca1030f144100031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 882722706 1250 882721456 882721493
    0x70e010504081c1101020a092c10090b03060f070528030606140903100203060411280f09090f020c0f1606091d090307122712 55
    0x100004581c0503010400740f1408a6016000d108010f545030000b00070142d8080700d44504c2c3e0061120300401034211842c00b00362040c00c003600700c000d00c03040e882500c0c08454007421100c004101c02804480210200c3e560301f550302011082c400c40e8251014180c4d6140101e0740c0d03040728002000892101441400140720800811002c0c000c5544000d0704040400c0301d00081a02007517a82404025484d041004603002090198407607003001d0403400800e8942c00030741e074101c00c544d500000140036a6956444501007418031851251100b040b5034084244a4a29080700700b40c203001128250824480c40c02c062105d441542c68402446c50104a640900003c0005071030b040c5d003c2c02540100c4004014000d08052408020204040800ca40403140c140a801490170032008400c00d0080b2410100070f00400c0c0040b2070b01c00e4542d03941c00003450440c0220200145004d0b031720002007081d039601c00501241c2e00c8804800e8005005810074000001000c1d21890f01c0100745902c520010400449000410415 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 882723956 1250 882722706 882722717
    0x61a160209060f1002070503060c07080910030e0f030706050f241c21020c060438070b0105060403030c03050a11060c04080105010b0403052a0a0b040905060f09070e01 73
    0x100c0c3d00004100c10360f2034a80c800144c5c03100e5801c204503c1c08002c0103070883c80c880c4e00d641c6050300c03540b10582d00e80310b003224490048526030fa0010b0700f18880c1e4001c2040300c0840007034908884010401e591203a00c07003a010f8030070608003030104080b240501403180c060b2045415041d03603522403c590f410f0058800310360319481010780c620b51289048440c90300c0c41491103042d055010124900340d4404000e2207074482e9003150302001c5140850b84852045a003a51103071b03427002c0070104840300408030008074014040c0c0c03480c40104030441c1d499030319000b8200144c802c640e5003603540e0b2240700307020050284c0e200250020b501c0f1010480440c3c01000103080982881c900100b0011029041c03900e445401e03246142d9040c0000b0303003005004400e120301c501416205020340e00c3c1c2441e680b01c040d920f900c0c05540c02c02ca03072002d0710752501002a60b09d0b580c10b140009000030700000d940700305022003a04188074585606082a0016103d45080f80d00d0341410007000304a11890340b2888000c403054130604481074103100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 882725206 1250 882723956 882723979
    0x80615040b070309050315010e0612120c0a031403040206040302041a090403080711010506030c0603090f0f0304050a050301050708280e0c0a050105040b0a0f140c01061a16020906 78
    0x1c4038000620856000342c0b15100321510341010705180000103204903000703400ca10f00510010401d0040030b41c110300100e8040100c0c40945c680242007006000302641504000501ea012805000c41d40c0f401990203038403401d01c20350744150144c80f54441280c0c001d52100b01000207000600d810360001c008050040307d0400a01e240001140e4003680076102540810981000c0141c0b81d944106c400e10399040c0e0400034011828003002090303554001c007480030312404011001402209007000041703032900910048900c114140b044803074696209015042c0203904443c0c001c14142414000d00c9d01030300c402d0752a6101c2d5030b42c40303048070492802484410740c8441000d603000708880079030003011030b0403404401410381d0501038810444080c40c2c0c1d40c03080e4144002440f04000c1c00ba40b010030348404c40201d003007824000e0b00202040b41c0302000c074007191822401c0815a4500103a056200009413525010107200e940600011244280200c1101c021010b41503100640182042e1704295001840078011a1811 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 882726456 1250 882725206 882725219
    0x141602040906050103020f03010b0f1e1005030907150804030324061e03060e13020a03170705010e0714460e04031b050709061e050f0108061504 63
    0x88184601c00e40b415500c4000502c290301d00f40003080c01e4804220000c0020b0703180310006c5220300300504503c52059a21040a200c46041030003444200b08000340740007a4010341800242c420303041981c0210a510608001280c00c1500ea940b02200d6032094842c0150303a900ca940c12005844000c0705061040689013150940f05445605071000d48100e03210707920b5400501b50503440406094510f10201170500b0b00400c500c2c1c441f1407000b41c00c1700e1381842074401380600d8004070743e060308d41d46d000508629040e008500d500c000c071400307008a54820030013400081c0054000d20741e41c11050043d0617540007151040400c51038070801c00e4400b030400740404850500c44e11210882c0c1880d5080c0c0d03ca04c807c000c42e50380e500c5000b0408080c050442030000d000c0504198400400b640001600340744480c440441c01800e0100807c503980c018a00d01d00c0c14417500781c5aa24032001214001d11103070100440880200f480e190100c04c8503001c0c84180c0d1303860402d903101c0c0100656041098103116441e81c0400021805 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 882727706 1250 882726456 882726461
    0x6100804080a1416060b0f30060a0506010e240a030e01020304060b0a2925030e0120030d330608130c050f0402130f0503160614160204 59
    0x124642c51301e65010803815082080640e1401000107104004420703c40e0100e980b03000404001d1030101681c2c082c1c801070031582070244d59420743c0c01011442041c0810000c0b00f000c0c0c0041c1c3c4030305c07403e985030214010b004080c0820440b05017131484240e21491481d50b85880e99901030b21403c2914900071a407440c01d08482422a0301c00d40301074a001c0e4851441c06d070607040141068006010990300041a40310034684101e42c2c5401004043c0c485000150003128001120043c084480c12244411052500c901c0c2c007400000d42c04160901103400c9918815038402001010849010f00e040039510b02260004440001c1102044043c407841103e12059001d004540d00036245007244c16410560358105100035000601c01829400700c00d428102c0c140018040c0c140c2e030300071204192200400b0340f80060014020f40108408052240f405000004a201c0203810030400c580c0242c042e5001d00c02c601180404da0f542e40e0107802e004c04c49802070505e40142d464002c08005080c0300701a52182d0003035001806 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 882728956 1250 882727706 882727717
    0x14132301030f0b0c19030c0c12030506040c020109051207020406080709090b0a0506030a0f0201091d150108040b1f09020c1f020412080f0408032106100804080a14 71
    0x64040c0c803420104104500c940d0f0a58118000400407420b0054200028120159040f0403008150316100c025080e1070040803d00c00d400c0d8415a514448041d40b2030007402003e084601c140304a003801c648a01050040c8200210250408050000c0e210704143e40b203483e61110b40200e2300326580e820001170002051003440d001c3e01c5807030b03030200380f201042c180340300034542c05440810041c0c544004d011280d0380005035030301c0e520b032b000c2c030202405800c44c001030798450b6213a44064140058117913070f50080031120b4051841150100c0041402e80400d1004480650081320010480729907040070604070b41543c900145400303015400c01c0c07030b4240c6900c0320311b081c0d0f00490b100d0300301503001c032080000d0240d20390403055800003800b900710700745071901180207030308034010102402c04800080d0f010784c001d960b82c003240d01600e041021a03580b4118187d20f132403021380c0d01c9203140700b10f001400410b20320320f4001d40b00b41500c51155241c4100e512103407100000c40d48500e80700c1c018020362040941c25401080060708 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 882730206 1250 882728956 882728963
    0xc08060103150e06061c03030e0105090723010503010e15130c02010c0f0206071116030506090d080c043003270f09150b03090102131413230103 63
    0x1060601104a41e00f030b106060200105a00808104101501d41540b1041d500c4d84802070482010002c0c10141c006080d0b60039001081d5003000c003003144075000095820100d542a02040213540e6140080c40210b500c60020380740001c00c10001003014111290b143d50f0442d01c8031303ca90080d41c0e0b02400140c2131000c40e8200b805099203e0210119607030f020f00c110400003460303007408a40306003244002910707810018039040602610801251552804200046a4801c2d441006c54a151a4105035035102c00480c2ca4242c01c2c8110022040c03180d2040c41e68501514462841c1e83c14103050191411942a020750a482c40111518040c0d040320040316240400a00035225140541c400d5072000d04130012050a90601d8409000f00f08070040b01c110b22001240d00000e000243c0310544441c4511080070755100e1040d003203021042c01062030066004201d00c1c206503041c490040d644180030b0801c04c0c4078001e1540c2c4540006c40c0102092403e070480841071000c00200c80d1312050819140030040c8081c0c0094 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 882731456 1250 882730206 882730223
    0x13051302040b031c03020c070b160b0601110309091b130801060501020307080d0e0304050d063c0b0a18050103020f01111b03150c03070207141c0c08060103 68
    0x3035090600c5440b08002098001d0420a01103400070700020040c1102001050b40c002480c00030000244020809048101401540c50403003810641103805000300940700d001c11702c000301d0020342c020b00742d64100307100c0080a9800c0000c00002c0020002c0c004020581c8040300402d203066102005004055400301444282c0d0304034280340c0d0003400c450369a00a42e065610070002440401d030f003181922000d080361180483e0100da629442c3c1d046005642c131190308041004040720400c5070540000400c3c0c1c0d180552541801d60449001008440d92341c0c413844e400c524910058054501e940000c06101406842113100960761717112079207190311200f04460245d039a42c0c0144114540111488817003803091908040e40d42040900c0c0d900c0300150760f126039881d103000d040200c032602c092201e0441c901c2c0418200d00f180c54842c02c400700340d9208807506401801508000305007410700301d0400f0100f003000303020290400303100d0000302a05050b540080c0c569180100b000140e40c00c0030010303e4061482504030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 882732706 1250 882731456 882731491
    0xa02030c16050a050c1c060203180303131b03021e030a0c06020c0102250e3111030a2409050601090902150a05030f0406020c072606190b1305 62
    0x2160600c00410000c40c030890200016020142d02035204d0f081b4940c0040c401a5a6201da0314898404c03a1010b8a4074454000401000264034001e04045c04990085032a0f4482c4902c54540d01c05940d51070100030340c00070002c0002c0d60082e5002d4483c1c001c0b0742c0d018049589a18040c1c1b03500d4041141a4070907001a4000f1210384055641030020f00c10000039104415094000c0380f1102c2c2211000380544c1007003118075400507a10818681105c1000300ca1403d1842011107021024041005440000d03100c450003e1039400e01070500003806080d844d080340415280741001d40c1c4e150780c200018003100d01825203401c1128040341090209600070150040b0000c0c207103055205000c3c1d4005100000c40a80303405201c031400168012040780c0c3d0000c003880d409040d9558914191000b401800010402c038450350740082900520700040b03005082c0d0513184107094078402d014007030766040c0882d0341d440c541045804034000c14980303804c54002154020001050800b410400320111001195408010b1146412 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 882733812 1106 882732706 882732713
    0x190f090902120403080606071109150406080d0207050604030b0a0902011b050a031404140603042d030f090e07110c0a060c020a06170a02030c16050a 65
    0x108644810004007400c071240802c80c3c0c110003283c100004940f0920b00001540d251952050b17120007025009018800d00313130b4020b8500d40c40b69a00c02c0087e2150f5072140900405010040003c0c003922180c0f840c02480c000e802d900280c041e04003000103001164113818140e0303002400300700200d500d062910040f96112243d1001c640080041c001c03c8042060116000d403455001c0e50b1441011490440c49040031b12440c458001d1004101841c12540d0502001456200740103e03a23070b00b030300d4070542c02320143c0041206a01842482014002c0101a00300d0b8000d4000301c002e1804410700e904003544050ac509020300701400340a5142400c4194240030802620301103009402600f81513516503003d0030b0405074900403403150b010300c8008144c0303521503408030b00448240310382d46c034036a01d032089003400075031026016880c0860100158228982a1081c8180681c031450040c207402e1510b00f03 = true := by decide +kernel

theorem cover : BRFrame.Cov 882553956 882733812 := by
  have h0 := BRFrame.cov_init 882553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 882553956 ≤ n) (h2 : n < 882733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
