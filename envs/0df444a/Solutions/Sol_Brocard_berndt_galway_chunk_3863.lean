-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3863
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:53:55.407255+00:00
-- url     : https://prove2.me/submissions/bb530732-72ea-4deb-886d-783af6b75957

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 694604316 ≤ n < 694784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 694605566 1250 694604316 694604357
    0xc0a020d080613150b0d0204030215030f0106030b03010f060f05030c220c3506010c0b0115120504390501031a1f0f0f0815030109050a03090e060103090201 68
    0x800c5131403464035031100060703031040c15018060300681c0c42c40060f6120700d58410404540082421350b65000000c1c410030031000d104c02d00060444039a401e02107111030320200040c0c010482043c3e00181a07140c410042148501304945030180c6900303030220303800244402c04209480100d24134006505039170380c68141659640703030414030602031103051044c805800c0c0784a220142c8515071800c010040400ca0040844c00030105075604180282403880001c0c10b551a06094004140116000d1030761082c0406803c0c0e00c105a1505080011101000b01d0304040c9000140740410b440300300500d034002c01c3d554000c00701036130321220007843c13016808002038a450015000340c010b40c10b103901e41c1030000c5041601d03174403842d000301e25050000340c00000303072500540c010f000300744000420410401c1c014508031801e900814102d411010380e000c550040b45501000a014151410b8020103a001d5034080000305a0440140c2c0c00f501c00494180d00241e8414004400311402840040d0008990035140c01100140c0b2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 694606816 1250 694605566 694605581
    0xc0a02120a0f12030c030203130f080415080a0f11030f0411040903120f020301050d0b090322080d020d080103030c0c0b0a02161409071d090c0a020d080613 68
    0x5094810340709031a01d5022007620464400d492030111503960140c610391600c901801c0741c920b401c0441c00d500f004c3c01d0a42009400d0b81c0d00500d42080f4441300700900080c10155401040e898000c1e40c02c0e152030000062684200356044040c10b4100751460001d00424024803402c07201d402e1104e0700b15580c80c4940306103804003400641355100d104060f6076450b1120300a200043d4002e855000044222461800844100101a07031602c2c1c070500c0140400e55a5800c03541003150400915102d9444c4d00a01d507040d403195451100c07200000301020400007001d000c0040440329810107440315401d03003036404c1e40c41e241840000400544200018800280184008041e1034003c0140d811800d88510104409501100241025070302603c8202c1020301c1c180381400141107001c1608440c891104d012491014026288100380a1b01004801c91050801028903421000902c03403516420305d40c100c0c2860384c0c01000c0c1e00300107001f1000300301002030051a41d0b41c052140503000b20702140000038417000810350b2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 694608066 1250 694606816 694606849
    0xb030304030512030a0e1b010f030902030d030908120406052a0f0a020a062c071d071b1203050c0c0a023105090f120a0309030309020904150609020c0a02 67
    0x36006c3c10295650108816844100303400c05101c0076414000000d446118540c1151080604101c8d074480140c502086110a0746081c0c06d000c111606907107030031400d82c0114001560300c1d0915070200000d100d05500a140185003440101d0043c041c00c50304080f18024071001e02181c48020814103a0202540009020f018042c1c41a10140079566803600141e403500c002c40703500e40c03002c6540c01c00300c00000c104546a4000040090910700d103407600140d00c0c112544000d889440c1c1140c0014140c034050344401100381160035004032003400a103050604c8000802c030500000b032800001498410029084900780c40710100200083c11669081003a070100400800d4400310790484661401c2ca412005074024001041c4045030614180004904d0410a0015040319030f00c10000c03045000c0c0b03104112800400d1038903000c904600c03642015400f402d0314000c003d4004104900f000103020f40000ba4401098501d1414001d4954501880050340034410b0314140c05c0d044507480c1001481d15031124900d4485 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 694609316 1250 694608066 694608071
    0xe06040305120c210a0509030a090b0306041e2003130f05030c07062006010e010314010216050d0806040509030921060c040e060d0b0c130314030c010b030304030512030a 74
    0x202031302e00b00c0d642c41036606541980b521450510041c0c401c10b000b250f9000110000542c00c020240c60003e15000d80351265404051000000c205c4c0da4855800030320089907190036107040030020288a4000300301c0d950f0040780c05044141060f00032820341046034040c010402c0040003141154480325040c00701310f0401c0b503480c03204102540c8111002d0000700010700715034995545484508280300395007010500c1100b19034010f203006025103c0303010302d0581580d40010301e0701049c00c400100140244a10191311001d40e508042e10410081d0008031010000b0341666081c00fa61541014441600e00c01c0d222070140c3d400c24882080c19092100d56807149030880306207440b4420031031030500d0400704143c616101000000809101141043e00c0d01904820140c40c21840c5c0c2586844035081040050112041c40300005401d5103443c010b0381951001d10342141400100303902035804030360fa81d0710001c002803440d403e100041204c1d02d4003000342c40c2141d40241c0900502e02d0307400c1c50030b00941e10003040381c1c1c8400d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 694610566 1250 694609316 694609327
    0x90609010f1106091609020f1909091a010e18130804030606120b09060f131103011109040b0a12060b0a08030a03021206040e37050a0201030e06040305120c 68
    0x80700300f00c1a40a010414041c184c2c3c1d99000c1d13010855111a50000079155004006071415902408100e80062003001c0284054128000d0304079541318081d801078040506111a150030005015400c12540c90b0980703900d01d1000440017131000914450882c10320300c4e0f00d039400064050402c2d10418144500c1100d00624143d280c2c0d95100c01c55005401050086000001040403c60307000e1b0165000f01c0d840c070042c40245401c04124a15601c01003040d112511003400c01410040940702c9108041c0c0010004e120380e40d08018007546a8200c40d00b402c0c803481c01d03c8810501400d041401e842030b1200440340034030109258a40300083e101200d07160350440d00c0d140e00042d03911000d1000d040d9031880c0b50b0300582d986c003540c00701d90040303800a003076144640d181c504445410000051940c7e0b08900d00940e04400748030551081d20000c0369192541940101400c001c01005004584284074074400d0f00e041041d81a66160183e90361070488005002c44d0041250b00340502c10003c100c0d13848900c1a040603e0071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 694611816 1250 694610566 694610597
    0x100209041b0c02040f09081b0d02070e0601181809120e010c080c0a050607080603012304060507020c0307030c0911131701110f0d0b1014090d0203120d060902090609010f 74
    0x245d100c0744242c4009000c100008c17018003411321501e402d0000c075100a20b4078606102d07110468500150185040c0b1007440100b0640590341c80914004040c01400202c40c0b01407040c150010b03201c0031104807a109402464514014040c0d40610f68500301a03448281460050f600c0c030242d548200c84061440c4a104001000a14100121407080400b581c0303038010750034140e00745400d50b0002090284090307005070503410449030004442e5842070700920003040544803c1026400e00c0c03a903800d0503425005a070008014018441841da0455030b0020041000b05030440342d0b94040e00620b0100010303044010020400305919001d55030960241c0c0c0000103a110042040d0700d400d511640c540c04910700e001c1801c103059002880f5901d09084243c815004c2030010060040591012298040395030303002160030b40706a207511944014a41c2d01400326001210300e01c41d4502117800c1302e40c03501c0310a0b00340480810984880d0017640e11200001c2c08080c10304134032070010b44241040c1d031110005c01526448a4864 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 694613066 1250 694611816 694611833
    0x10302130e0402030f190308060402090d062307110709020306012f1920010e0d06150f170304120b07020102070c0f06030f050f010603090f05100209041b0c02040f09 72
    0x241600408940346c8111901c2c001d05403040081c1403038480d601c18400784442e901c13685900421141c0c0000e002603160b40d0240b0b4a130080303103002d901002040c200350401c0700309131300119440c040074100b2080303802841c2e03150999010b03440f045403600e000032000384021815000291000101260b0b40c00340000c0304504c039a0842c5010500111a203118007024452001d00081a440700259000505c01c03003502d415180c00038001108020503980104210095a001e00c1815072054000c44400c00c44109215070714400c142805606009881e9440d2400d000e44910b40300000c111800c8640749003015410562644500081000c002c0249040d95020410100011306403540b500c090039002c1c00c010a10390510000408881180c51150038540c5000140402148401c5002d4111145480c0101d25501d251510b11540300700f89100812503c9a441a035005113541d0300580b540d9001603071b007000181e5032010907068091404003c580420051108600541015081007180100f07100c0003040109650740c0c3d8090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 694614316 1250 694613066 694613083
    0x3070917030a140c0d14040803031f050108040312051e0a060f0902040f030f02010203042c06010c15050a0e16050a0b04030b0c03150d050109030905010302130e0402030f 74
    0x140c030342001540b900c00c0d039042104521402618540541007550040c07209603a2406000c840090107000750340d00c0d1305010450704482c0580038940507a516400d10615481058a82c00090707440ca010001c1c000c1015480341c2e05c1c0a1090350117076034440781d803411080004000c0001406d0360f011281c0f5001d0f01d659001c0c5001d07500d8007d90408000003240d80c5800300410782c181ca10340001003054010401041403808050000d02960780216080d00102443d10040c0e02d1481950720100303241650842280801c210030f21007403d1040d800390301010a5842c000111203098034200300820704e00100d101203003040e4550f40810303072120b8119400140503907207103103da00d0012841e1032901d600c4071480081c01142801c0003804001c020740559a030419045a843c095090801000841c02c0080840000c07100c980d54845c414012101601801002c80541007640c0a048100020b80100766112400141944030384210307a000c951486980340c007141429918808207074042e205903850b01c201040c1512205041c8080d55 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 694615566 1250 694614316 694614359
    0x40302060c160b15100e01050406050c0709050112110109060f18350a02010c080706021204110f090f0703091401050a050105100905030606090703090b040b06180912030709 75
    0xb0029980700003048900c000c5c0d4522181013000f000300c9281c450b60401c0a0b101940c0d0305040c010b49840344140d00624100c1940d102e00c0394142070800001c0d60740030030304d2007420640c020300103080d00b1011070300155880d840034490600011030707101c2540c901d24418420826003015005000c3c0c081647c419403940c0d82001c080200440241c050141404d0342c190100180d582e0b0700300710180040c19140c0d00080c082c5e101d180c0c005040c007840043c10504001a5504541e18041102c01440c02c600f0301d8241450503c030004016405007010501d95501c500d08000401d110b038541c0b0403507da45039180e00c821006000303c0f840c00c032080600461800403c103020300400b84614411140003440703624010030000080c200c03801036410f0044040042c00b861b240401c4141d27100710141d0750300d01e05846a460031030081c00300550150440341c9584c00c0c841000140d106080c082c0000711410500c8101d46030b82101600b400f40e5440c8165130288602595941c1c00101455200d081c904004121907507400140c64204400185c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 694616816 1250 694615566 694615591
    0x209130e1507030e160e04031812060906060e102603160b10060504060315170601030c14030a0f05030f030a051012110f030c040905060a1103040302060c160b 69
    0x1c034806102046442e8401021051714501d0f04d00d012a46d50f101400580041c081004c50030200c00c4520300c2c0c892100040c1805000085510b880d07080110040010103030841e0901d040c0341000500420103110b0702e01038400e1443e5151980d2401004503070312501c052407075007c641d18400301068000b0030b1000e4400305d5007030100c284098496251001466000a0200d80040c440040600c00d66034000b05a5040c0c07000c134240020034400070004180c590915921140200c0e44649511501c8400401d520303040700e1068004c10074503522407820301b0381c00012104960300b45e40030324484404207d2040c41c90403298020b4007968070304009034400883c285e0048410039409038541051000f890345070096030008040c0c1030012008520345650b4110041030000c43d0310720425030050010815a400d01c100c44d510340000b4001c0080204070700d04243c80d47e408503006190356250040039040d0544600c2168030540d17159018142c44e0b40d40d01c0440300c841c1c01c030064441e0208414503800780012120941a03000c2c1c55a600316 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 694618066 1250 694616816 694616831
    0x403060906060504050103051b220e070807080d050d060914070206133519080109020703141b12030405010b0406080d11011407030c02070602010209130e150703 70
    0x50982d003075a4461401646000010004903c0201e141d20000e01c1c0e0582e20b9544411001c001000b42050004030700c0b003000810001149030146034481004c0c0c0340c0705800d41f24425070b00c15003140c0700c1d807181c410010650000a01c245c2098030038402807044114007600090015103d01044084580e01e41c01c07461b03004088418070403450340401105611080c072900f4a2140c561641d10003098600c0c8205c05045206006426500308a0302075807800003141890303444e911a0700408100b007445031860342c0b0360085014500003003440c41d614021110503942607114445018140c44401c0429800700d14042c02b02204103a59158402e4203003d5030066012140d00c0c035440b410a414820300b1940c110250702d109520b401002c2210340300100d0400444e2406003402025154881c2d40140544000c0e40c1507080601e000c0200a00c554040e4400003030f8182590031a4121519100e041c0e080703120f28140c1076401101402030301c0d0106640c1d0000302014105d1000d644605200f1101440094030580310303000880d441d040c0303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 694619316 1250 694618066 694618073
    0x136061217161403120708013308060a03060906050417091f0c0609060c0e100522080303131106040b040509040602040f080d180e160e0604030609 64
    0x11891440c00d06100145407502c010420346028180710002000c00301d58540b00c8020041c1802941e8040107482c141c500c40d403500c5a4014507004c400d0045c40949104906940100060864040c40e001c54440c0c2441440042c48000c3d50300e1000146601d40c04002100d0103c002141d80c0280010303244242c0c00460107040c03524010f000070482c0d09040c1650a424000c0110f9940c82001c0b80350614050b02e69120911940c00d012200c041c03203050090201c0d401d21349400100700e00c69010254919982c2e684003000340c01c8108208550f2043c0820400090042c0000722034100b8440080c90b00412450191041d01d656030714450454008444440004040d128804c040c402100c010321152001110303a5403800c0e08105840c007850203640501806a100c0d00c002504010f0b1550440300909551140000f00701da541291950ba540b40480c4c01001a507002e8040307000c5032100f8105020740b4080764680169640e038a5100e00165912211780d01000302150110740c1070f448040080000c0e5020300d1010509229505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 694620566 1250 694619316 694619333
    0x21201021201050909031804020f0c07260312070c12110d1119080d1e270201081b0a120e03040305060c0d1e050402120601360612 57
    0xa021600a440c4c100801640e65408400c03590030340c8032540d50050310140709011034000d00a580302c00d401c4039000680001d58030400180c240c00c65401a16010303803840301038840340c202e0380301000740d0000c1c1c7d1090149241e0300c00a594455841505031034013401000c1e83da1a00c0b01d2481803905182c001c00d5008d00c0c1c80348403413820303c103001d03071070355541051044020549040760b515104c01002e40c007140b41e5098030074100210300086071403505001c00d062104004d40040c00c10b81030084e03c2d00c81c0045140000c00d0f240030400d081c400c4c0842c800f4115950480c0440d8005440f80c5800411914441d5241a070b1100b9044585000d800107008594800035100c0761801c1540c110703880c1d40400c862541c4180400c00018500003071050740104400340581e1105802d04041d4003038101c0d400b01000000005000c0c07080c4400680c0403610560003280c0c003440450040b013141d80c43e0a8203000e00000c14100b40c072080f1100510006000002c158100c6500e03509030503c002008488403600401d8180300f410b06031205102018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 694621816 1250 694620566 694620569
    0x150503011b140c010e0a1a130f12030b0d05010b1801081c1205091605061e210108030d0e19031419030912020a02060702041503021201021201 62
    0x3104608002041d1600500000c10b80c0d85460710121000880318a082d100b03402c0301c0c8190548504894410301c4034602010700000254007010240107210024007020780c4038009400e00c540000d08442d40080c242c440140c0c400c5110180410305854140226007502d070201151009809480000384090f40c160812654589810309a1100101407006012020000c64108d4000060103070320700c4110050b520584880c415000c01120349890f081c1001942a00419000e071140445200c028501d034840d02009130034000d0000c0718146021a50315401d00d0119940101410203012403131488001c0c5440c10b0141040d8260400820350b000844c0001d960740c920700440c1c011201e00d101600740c88040302c10480c01c650480001a04000c01c04102039240c1c00124100c801c501c1d107080029103035040c0d038207000d0040c4c104000300701c40020404244079412171010414450a5900915175490030009408110180000a8602c440e06401210020060b0369a0b1b248205104c14040050703101e000d0074500c561a031405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 694623066 1250 694621816 694621841
    0x50103140c06030f1305030a0e0f1008070c0309090f0e010c0503090a0b04060213081b0411071104022a06010801060303300507050418020906070b04050f0115050301 72
    0x26034441056a5502c0094942c011010110180c8590358900380c4443d1010802028009000010f108100e45a100110b03041d1148295100c520301c030111802d01025040c0c4e0703040100003442c10808100d4142c4110340712240c41e8001e14211004039103c0d403404040b00e42200034103914998600c0d0407100b451003801190012203103030a0080c11071905104041d100e40401c10014410110030740001e0410100341e041c2c030381c0400351052054400c2d84810f41907039103207607801005c9104001d0003106000d500d4103009010b0790381d12029000703003040400c1d9643c03040b5140c203070740596015400788100c881451007030510404801d40c0e000c0d075a800c00f025108860070041c0c1a00603543d07a0f41441001d00100f900408101c00206040f0420544801449440311340d500750302e42d5a4900074104000c0c4144c0a5100000d003081d10000d00c2c841100c02c1a03901d4000403849401c00b0190041c07000e215000220704184815644240261f041c2e0310750048100cac08608584004130114940112007900f8000c0e81424820545012903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 694624316 1250 694623066 694623073
    0x7091412030c010606080a1104060f140a030c0e09091207140102160201080f0606190302070c0e012c13020102100213090608010207050a080a020123010305120403120c1a0a05010314 79
    0x7050708d8068410310503400b0301403d108001200e502c0061140100070800c29130180310030707180c6004000040c0501100340910b07001880d8070b120b80b030040c60404186030140c00078000814668500880745a5030f60804402592541c15004002110035000c2c001800d400c030800f103c0c4600d9600c14030000d00950400b600320350a8814442c01c001c2962203c504030303140c00b03042c00210480c500a07103501b24040e20030001d005040c046154000100801c802104605a40241e0141510101c040c0115071200461144c14040f002040d1702103480d2145050107515218010300c15914454401e50118050743c1c410464248804011841000820428421030020f010300c1c10082d0310b003d0594650582e02c08664a02420f81140091613407034940c001d40c81f5109220726410010350400e0001c0030b0040b144000d2209813858000d540e9041c6425000c00704850a13681c1c0200c5014942c1d03d8901e04070307010711452034111000c425100d2840c045011200c2010300c68103d042d40420298107526144014600074520b80c2d070705030f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 694625566 1250 694624316 694624331
    0x6050a060c0812044b050a080d0e07080a03090b0408060a050c16030e12060c0f070c09050c07140c1305100e0c04140907091412030c010606080a 63
    0x20603150031640d00b40c0d41c044000c0020b480703d0800c1007800c0680940000d000d5091007140903080a4440202042c00c0d15520032500f1750150300002400c0102008001d00f10381146141000162052000c0d18041200400000e80009103045003440c0150340d40084007140c1c041c60762071040562208980300a844520901030400b0702d00300c602507a49074050316600540b620f41c4001400490818196100320f210504055405020303414060714800748048114007800ca5115903520b51440050038600030100d01000c5840e14806003425600d80e0040c04c0100c441c42124000000d0b81c1d1464040c0a0240f2551180d0b540c0d120000c3c0b8001d21003401d103055800058100ea4040900c40c1d4541c0701e603624043c075101011030103507200e40700c404284180d60806c0c101d18551905015101107a900600142c5107076001750f42041c80720070201308068400f190f0007000500341080c1402003440201e0100e0700c1c000c01618803009030070b50340030171070440d04010141940360395140c0b802c00c00a68401030064102503940801c01004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 694626816 1250 694625566 694625573
    0x7080d090c030c0b130510030902030115030215070816080c010606050409050f0702030f070f1502190801030b06010e18010905190b03120a0903080f07020f0414011a0409060906050a060c 81
    0x517032510813a8822079011004240c1d490103600030480d065401002000b043e00c102209251071180750205038022000300703120580011000c42201e2100c0d4210081c6030421181100c0d0b0845c040320348204882c1c0000501000c800b6520074010100036115070307183c807900e440c1402c20310030450b800245902c00103d501c0042c41002500401262401a0307850180d5546140c181000201e43c0d420703850003066004001c000c1c90031a40d16901401080e40038040303100c8104404001100e201400f8007001e01103440c0d01000c0341996008030203482d45590094107900c05007044c581d050084440c240d220300c14990b260420000032841c83c40b00c60300000c0300c8200030007080c45810003003a5aa60f1050580061010009a0052141c040c002100c019070340310085503074400400166451a4000b00d034100c4c06030402d100e0034651860140518138240b070140e62000040ea28010600c01180145000d507451520202300c00700b40c9075654081c840180c050410301154370ba203894148038010419610a4040000b0109540e000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 694628066 1250 694626816 694626847
    0x312020105041113150b0309011506050a0305100e040f0204200f0a18090e120406230c0d080f06030307031e210f0c05030903040b07080d090c030c0b 65
    0x2d548064074072403c5424040c2110004000d08041510200d4102200203011b0310200c00552050707007880000c1c803d0000c901081c0188000c2402070a01203401848003a0440b071003640a41ea00c210141280418103945080b0080341c00010344040d102620246031050542c1403074025440d400c600f2641d1900d00f50060800e00d8038501071a0100303450106d0020760015920b101f42200d440ea101440f03070842e8444d0342c1d180b2000c01454103145003082d900500c12003840000c03100e001c1d5003c440380ca40398032030b4140b074a000451031170544400340090315074144059181c01104100d8407441c0c100c541c6464815050042202c180001d0081005110f07502c20440600000d40c00300403015000e0420049d11700700d801a8200307403500d614080c3c001c3c1d00d6200300a104144122960012108078966101c00c0213104144003086600b40f00c00c84202180380d1080000300501500400205102c6015076001414010301d010504113440c250030707041d01c509801010030f005021000086000a280030b8580c64500740c40e20751140c82 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 694629316 1250 694628066 694628093
    0x90a2d030c08070501140a06150f030b0d23070803040b07081e030c03041b03020f0d0f02040207110a0608040c17151906080f12072307031202010504 65
    0x400840c00103a50800142800b500c483d568000020301c881c950310003901c20650002c0320400c0d6810b04150b000101c410702d90001848449076541c52070030a9801d07501c142c1c06450700548503504030114030303004d9010581c61400300384680f0241d100c0e0f80d480350301c02400514010494006041d1034000300810021440040c01704d800c071550000c091501e490200c15a40c00748a141554043c0a14000003042102140580114415449a08580c66070009001140803074801404000e40090f0060642d01c00c510b040004401c0380f500c1001c0c0c0c1900490980d01040698000080443e28015016490f520500d40721200d40081c11a07843c002e2010f1074281c903042e040d65054031030100b0941c82000714100386102070000b00d290cc0b070783c10607100803070822030400010030280301d6007010f40d10314007c3c01140095010034040d0143c48000300804005401d1754205805501841c3c0c120340c070480c88605c1504600c042e1031580d81c0c5000d4500509590f51079800c0005408032180a101c0c11645010304001c00101da9120511 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 694630566 1250 694629316 694629323
    0x3010f05010c17030c07030807170105120309061908010b120406020f0405041b09080d170601090302030a060506010e0418141006081b03030a090905130b090a2d 70
    0x24407401141019040d0103520703c50260102070010800800030224801020031512980d181501d55948840403100c0f400d5a00d07000320749403601001084035183c81c80100c0b0020103040c0540c0c1c030341404000010541e40c0100d0020742011807900d0f030703003c03900d4011034410300602d0000d8020b441c103c00c0c24039018207640020230081c081c1c0ea001c60f0010301c620301202600d000c2c0002400030080c0300400c00690f07a4000045203c04001307001614040b40004002c14146017030b05054844196100706c1030261041c40e03034010f190368100190201d0000c05a602008411400e40c000c80d0005034030f080000005140d08030003406140924100b613015085c079441c410442c00d016802c200b60b10010000c0042a41c14240c285d03009464050a082c03002c9041c0070f000c0769aa01c000d0b00c44101c640001043c205043d200c0c01f80501c54000704000d68030401c039615981e04525030001410002207103d0582c0ea07281010020b040c1c5280c10b250f40f00491007401c0101c5810329511386409070481c058400e8005407984820034000c04000e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 694631816 1250 694630566 694630577
    0xc06030a0e03070c0b0711030102041202060d0b03190b010b0901090302100c1b081009020a17120a0504080606012c0d0803040b070215070e090403121401081203010f0501 74
    0x1254402c2c801d8a008650080140861943d2121240c48941240c02c081d00d1481072240a080c251905200f11811210580258032403100b0726000c02c00e1a81180f00d201404945402c6042c0e816034061200240601010307244210307541c202c1c10040c41100050700580d4403800100071103030142e0b8100785032104a0340d04441f05034075003154200c120f4811398250401007002c641c1412101284124600c00d006840301142200c40401001d140f4106440d2030000c0a904403070201c8051100141d00030700b010103070764410222448658a442020840d034071000a0314000b80e40840d06010f02c0c42c003445602e41001091804403403104000412290220240380d80c0c00405660000c1d00e049515501c0355000181d410100d007a48910f001e050194005104070f42c3c040041c0502c06440c00071200c04070041d402001d141d69204480812013060103800b1101510135401d001d5a50180360403095075010321040e0090020001d80c5551400d00702034138121481010016841040c8014022000c00320248003c9a4003480c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 694633066 1250 694631816 694631831
    0x110a020616090e0a0f09050325021c08070525170607030203060310110a02070e01030f1112030304030c0c05060a080a0513020a0f03020f0d02091602030405041a120c06030a 75
    0x4c5000801c40305003015055401c0c005240207020740400944a601a01813601c072286000800704070a103502c0c040c1c02540040c81c28001603200d4142101d02d01d00d144100c0d5890310302202070301c0d001d292404000c440c400040880346444122189008544018094001c0c074000c503a0328009199103540c070041280041560110010700c0a41d0200a6442a0f50b10a8402c014401052510068075804102d045000d4801d00c1c100060208859480318101c03500029190392440300c03907075603501000036400c00d560301c4502c08954146000091000314000d0b80329840740f8074211500d240c0302031030000d20350015100e40410b0001d488a50b80002e015a40300b041c010f4000b96554a600c1d0303916080002d52000f035000620f00202143c18011410760382d003900e000300d5060a50b050720342c0411000b102c0c005802500840400c8c04202c6440c84000d0a1140314454010f0701d00301910b5030041001c449407046600200c3e003c0b0440c44410b414840e07002c0b141c8014000140510450003c00301d00d05102c090320406a240d5544213 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 694634316 1250 694633066 694633081
    0x7180c050322060612060e0c0d020a061206050a1428060c150203010e01060e0a06050f09040b13140a05040b0c1c1401031202010621020301020706110a020616090e 71
    0x1042c80903017038403000c40e020b2074280e04102d0020710740c10701005003a210703c100c7c40b8010704c1e0508208010315401029540c1441c01c1071022503c25240152840c1103e407160070104640e5540401710001c0e00a40010070341d0b04401e001000300024003811072444e003980602c00380260503403043c41201a9601801c0642c950282c91410002c4903c001c018011158400f10000c1400805d0b099a0b5040351025520401012480010000340741090310803540440d00030000a040910050041c18240100800c0040c0c04020b0a010407103070071104c1c103500b00d403035030701d44549407121105c0010310f8000c480414100550714040d640d05080b0b190140508041000105590031000d41d6101c00300119245140140441c006650341209040004e00048410b25030001d00130301120710520400f01159402d00e103103034030700480359808a85401d0341304081c1d030155020484040800c03110b01400c9880c005203000241d1359804840024103109001c0c100001c90381403090300c071004543c4900700c403054482845000030251242c48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 694635566 1250 694634316 694634321
    0x10200c03010509060103020315010815070e03010603050105190501290c0d1e08150405060109080a050d03140c0306010f0903050109050c032e110c07180c05032206 71
    0x90019410742c01d040030400141004140c1d01e048920a400b20b8084d81030082e600315521009005003d442d5006124100703005c284200820380060440c2060507000c18014082400e40b9120b0300180c8490791140c1c288070284021000501c25440681c001b0005035050001c09a41558100315050340841e0000c541107008041c1c00880e0083c107608011107041c030a0640010b09648140020603028960310303088420750a004240c024841c00f0608056808800310700c0c1040000e08001d0695410030040802c04207456104000d2860124060b00080c42e507180b2100340203013035504008484410000400a00c0b036146d403e0001d6a401180900708000d15a6480d0401c85542c2400d900150080d0308180700082445004502141d200409a00707880045031824000c100c065070030054650440440b0411000040e16a40180400004848541d18101c030705101603241465580140c0350801c0307801c8002d85425410300c00d014050001d41810f6085261104049201d9040303004441920f00200c1004c104101c4140d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 694636816 1250 694635566 694635583
    0x4050603092508060a09030c140304091a030c03150a09060221040204050a020301080d0825020708010e01060b12040213110a2c101707050702010e1020 66
    0x408084500354000c0381d1082c03925101d201d003103401e0250f44086584080d46002c1da0140c6500740c0c807402c003200d00c203039641c80d158510f5101d1800d06000c14040800d0301c13005030003110038268001b40d103160f03003500303002c10981404071001c250380c465404408c0c020221a14000b0250340f03e107501c1000030310180c0c14103040c4042e104101b150f400d0b00c4031003541181e03a03000c1042180d010314002d03103041000d680ca602c03002d4100d200038062400164482e040048105114080e0903511840c0780c246007012200001302c0f00d01c0d00e8041c08480340542c00141c02444488030074450030096510010003070200b145054074000051042869091648484900080a43d01c9002c031240f4642c800391010040d4000c2a00c0388040c9411160120b030010740002641300350300c4100103540711400701d60b107401010b20080740e0400162217030744100d500910903064010565a8802409544140780c2c644690340c2e80d078100e1000410751130503072039520320465620512405065111184018100c0c03481d071a440d50350f01c0c2c01c445902e0320101c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 694638066 1250 694636816 694636843
    0x6050f15030907051c0302150c0301091a041401051504030804060c14150a061d070c0f0b15040608030307080103060e07120c0312050a020303060f0d0f050a050d090b0405060309 77
    0x102d2600c07030b05e40103030b0090241064026800c4c2c400010400b010766600341c0081d100c1c00390500e401c0c801404150030700c0d8441c1524210900d03440300c100d044500403800741e500e40c0b02038503440075801004000030706007402c000600d032041c95581c0f45814296070760030202c3e00482c09450104603031550071404025510031a5652050351004403001c5c2c00c6111079101c9000d504603188803455042681c0015a070303104918034007580c480401000155660814201d07080300d040321060b281910f54200c3c400c041644001c80e203000b0aa01c003104107014142000340410395010794007203505a0b004104010b90140d201207601d0642c0d030f00c40e03008624100e0581109290903c0303a0011034140070400b52603410801071320703080012a4841c901507000e18003041001d0f2158010200300601507001040098694a0105d101060581000b06400240651070711095203240d16460200c0344e0341d100520080a0080800004428401038504207000504000070340b07045000c0c0d48200c074042c001c00301c04125108014040580404007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 694639316 1250 694638066 694638079
    0x3040e0c0d0e010b13090804050402030423030309011a2211220b03010b0a0309050a140609100509102022081207020909100e0c030106050f1503090705 66
    0x1101e15030280200580d0044c2803054080d01d2094050740490300810519135000010303203042030f103407900f8040694801481261038040003003e00380c2c5868903400410300b0071505401035807a441c0041d41c0b1800c485072100c01500140c925455942250380c2c1c8070b032010580c119050542611003101d1315103c003401c2103060900419801186400041242548506140d0b1200b240c40c2039043c2d07640d203013001a110038099180c07031480411800300c1c0d143c002d4000e1445140f00e1011110000303a6522940030829202d01c807242143c101c00705000315414104010b03050482c00c80010000c1e81000100940e0301c0c51007040000025445280c40320b05000c48039000d039030307001150f41010380e40c100c0294907030b10402c080e00c442c02030a0b8204001052940c0e00140b900d030701c0070f92025683c2c9030407170031780810103a110010543c0d8141c0c4030310201000c0d090703101c1c010070900c504404010102204500101803e50b04103401043c00340c1c1c0c81c2ca0741c1c03820a94034005001c400250494205a0707039100c00e08820f00300a11134204940214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 694640566 1250 694639316 694639331
    0xd050714090a020c0c0919050c09120c03060106030f1b0f0f11100f230a140f0f07140708120108030304030e1903060513020301050609040503040e0c0d 66
    0x103400106012503002110101c4190380e4845068089009010111200340c0c412258400c99007810385100790041d600300074100405910114000a440044400e9071100c00d01040610050500b0310b1202600c203c07107005020340e11120804660b54501c148100c46c2010389540401c50064820f9200d40c00118060721311115075850702c1c5000d480e50610301e000034005140403903070728020b0384990703510036003100036102900ca1900221000d10140210b0540031000c00d59804480f0100b11103000c592400b807542c0c0e074400b03556207886101101114005079400c401400e8440411901c0c3d03821048156010520804051850304da01d50115086406d001c1040903d00c0005040c5043c40b1011000e001000c1c2d0340c0100301c01c0c80e031301c03008115124001520010040b500703004070700501d440e04091404d0b1b820500501000019a0380d190401a1030040ced64910651300309901c40302c05c1d41000c0c0102a403240081d2011861400c19a5405640e4851849506c3c1c403240789101080d0300c20240000c440480340641020b01581c1f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 694641816 1250 694640566 694640579
    0x90f0301050c1210080a0f02060c03120103060b04090c1a04030209010914180d030e2d0609030a1b030507020907030c0305010e060d200a0821040b040302040207020d0507 74
    0x181d1010f42141c0722000188005044002150801e005654608024000c151690b82d6644560030354404200da2140091090f0303140f200c000c0000d800d01e0400d0359209011035145042c002c0031211056182d0b802182030049100119400222400889480350800c501161030504015014050f9070402984403180c0b50000440100ca60017036124030360984101c0c0035541b0fa0304e0900000145107541106150400c150b02c80c0402c1c00b90303000c108040041d00035514919100794401c8032000381c0074100e400c1003161116205900c1c0c0c0c10000715600c80c5400d4002d40c544612104c0180c10054140305a0741460507044003002014490000d0380c0b0902d80c0a00170310f0580c01e164001801401007500b0041c0064a0318000203014071803000401d0003100050b1901904404646038494616410000c440b01e2801d11a41c071212601d40c01c007404010a6050043e080310080c40107041554403101030f1001c2400c02c1071000388106500402210110380d4100c87c010b80c1d85035a0710200700d40039462800546140030701d2500141c40d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 694643066 1250 694641816 694641841
    0x2d09040f0c060c0b01050f091611010c0504180b150a0207030f0b0103050d0e0603271617030301051e0f0a080313080303090d0804031403041209080c090705090f030105 73
    0x242e8070601c20b079102e0fa84c1b070b84103210109500711805503001c9000c0c4c0c00305801c86200710403105803110070302c1c0041040c403850300c090b425030b40000492030010703000060400804040e0707045815001c00a003428000e60780010002556482c40042e28080d0078000600340e50128020000c0400031076005000c3d905000441c10000e11101c0244002d035003900810080001c40c1d403040040905c0410014446400d41d242c0d5081c074910004800d5a0484a170030200686103103840800103a44103030024040001198200b0000115540b1119035211082d4020300052006039035142032120304c4010188440c3d07200203038038001114041c3c0c0407146a0084a0b0034008162144088001c1c89803803800c1e004108125510160076503684421103124145400a80d50400102d2055203913541260003490440040b0341ca008401c82c060b801520202d0300381c0341c96100288001d4100001c54020110003002d81500c8800001080400000504000403c0300010318545155200b540c4400d0352480036008120b2850400e801810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 694644316 1250 694643066 694643087
    0x24070c12150216031b0b09010e010e1b040f1d07090515061803030f0d090308010510170901020c01110301050f040b031b0f0409112d09040f0c06 63
    0xc40c41d07494200120540700074021580205865480080c0d052a2501e044841640120510703030031040400341d2501041c014030505000c1c6017510000240306100003045801c681e902152525150424402c59030b030315880003644040110241c40100e11302c0c0b1103803c043c008100e0b04060301a0207002c0a00c40b10700510014803142610f10a12080085443d102c0081381c25486400086038800c0080003420820425080800d06841c4007070b08803802c102148a006c1d106030000030880c030716a60388014503414994407400702401081c05540504030400c0c0c5c050010130040800000600030941007001c203680c07020950449500c46602c00c0200600c040c1041c011031998420300c41e1074810041103422103914075140c402d05070554070003002016084c2c8d419541011041160780300b2070340048403045101c965102c5009006125203d030400e81000c4520704108280300c00c42ea040b00f45015090316410950b0600c1c11100520860304981c18051036030f40b450316180f0003d082000038413103601030300b00069042d0030618154 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 694645566 1250 694644316 694644323
    0x605150703020706020609280237060f0c0203071809030914030c090a0b09010306020306010219150b030709060905070801082a06090409030504090e010204030224070c12 74
    0xb03c5083c0c1d5050100e030303241001e58803007c8540007800b41280311310350445e81c108002101500d41c40210421b0700098034580c5158411426101601042440c0280b06240308031015246181c05110350304181004000d040140e995009214030201c0090640d074007008210001c000b040d02c41c542d18154244048040c4c40c2c0c00000706c000c80c03407020340492030b94284903840c2d4899001a00402002104500300506e00304043c08001c40290340320910806034590758582d901071805085c0c00b5035130b8103008000918100880b900c036550840c0c105041c04c0003805110f0b00007020304403003d000c1203841174a00002d0401c030b4680e000f0b0804a00d841c200041c01c0f41e99820043c49460b00d41c55661542c0e0740c450361a902c48a103160f00c2e141d500e104002d003007082e040004448510300c0c0080c00c011705042c00709000c20211000720350184c021440114003001203108a000d10008044080000d600706891035020440c2c9813080ea005850b81904408020504600c0030207481c0010740080c442d0713110980e24034040044011030281030b07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 694646816 1250 694645566 694645573
    0xb090c040603030509101d06032701201c02090604120506090c0607080316030b060714010501121106090f0a290a020d030c020c03070602150a0e0a030c0501060515070302 74
    0xd04601d40640d8036860999201c1c047c0b8045281e80c0c1b400c0199030f910043c201424600d1010086100c2e41c000364840000caa40131000246078280c1a07410041c003803c035152420811010888106482420786542d0026050b80e04096100c0768000c0000701907005036041107c82904000300c120500c0301c000307041800341030300348265220106240180150f5107d440000b5214100800c0072605a0400103100042d189040c035000a5210b0003800095040d8084c05040d038000300c82d4060340c09201c4082c49943c7c010000c90401540b1000c4e1361741c450240c200d246041078415900854094820748034003680c10441c40000700700c00c01c50303030300c41c4142c0da010307000e41003c0d20b01c20565040c031040d0721010100300d8100144c150000c00e002ca0449000310003500304002c07441d0460060380c1d00c4012540b01000010080c05154001c0c0060f0f5804494090344a00000e103003048a50521400182d980004248469525094500780d060049103040481c0986102d07031120b41c00001403080d0400743e5801101a0441503c43e5094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 694648066 1250 694646816 694646839
    0x20c0d1106161103031603050c1c081501031e180c080a0b07030c08040b270f0c03031603051303080315030c010305070206160309150e0d0801060c0b090c040603030509 73
    0x10305540340101c0300e040803600a20346c403d90100340144050b00e55488100116134083c0d50441d6100404406020742401044008c8180644500e6440042d455a9000c0c40d0070881400c040164a10314825807a8038125242d884401c00d026111007007500c0400c80e0071400c0c03d841295100c180f20f603159502141074400945103000314a019210780202c1e8005c0415030386041c400e88498549544204001d0304000ca20764102c81510408102028121240c80c1100301134641034543d840d2003401c1002c800482c912036042080503203030140c4800001a031139501464499114660313400e14102c02c1280743c01c00f824017030003c000c00080d90b070900ea060803004026415a540e140d5240c0054060320000da4070200980c201000040b403003034006030f105503540030519011a004082e41c865200003c0100b2452480c6900c84500722145542000403031320031103003072508400035803407c03500500c0014180d0000700700b2080c603000f05001c0f0500b0009d0000741100100704001c030b255240b0300030f0700c02c0e0b1199007181d010b8a04070701c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 694649316 1250 694648066 694648069
    0xc05070b0306010e1309050f031917070305070504030f111305061e06120103050a02010801230105030414031306030b0f06070b06180f010905010e07020c0d11061611 72
    0x140e900651040c0c44803020010311008200d2152540910001143e036154a01b10100b042081000000d0342c00741d0140d070b0b54070041d12090095900301c00c4030409002800b01d800550a41c8020000d5012010749000500c940b1054000c03201c80c490780d8009005418001c0640040c060103000d1120b505030203c0b4941c0e45608000c0c0001c0945200b00c0711581c4c40450400b0f14003035000010b6010200364001043c8500d4541c801c12802c405c02005c0c0c2003510a940f20303654080071941c0011800e4054103200208000503072010602c04196041c0e201130504001c804000320f8208001010800500e843c000252600e800b66481a00c2c800c80c424400c0e02d00103802c0c48c0b00740c115411301d103000d20704011014000c60710700201c87e201c2c9425410040c00032074014032a01d404804440c4490390450040058140c00005545041001800e0b03805c1038200c603840003080070074480002c1e00084d64150301c140c10f03107100b00d03811450b0030185600301d2031010302600b1250004582c02c69480710312000c0300c6144511651102e9020440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 694650566 1250 694649316 694649339
    0x31203160e011d01090902070507050306072a0c120302010b0108010f0f0504180203010606050c0d090501170403020a06020a0c140c031f0b220c08090304090207030e0406060c0507 78
    0xc200502080c0f0680369264401d003800b00c8142000410f04040160542e50002c90040b40d0002e242030321540c000c1700044c409443d0038000c030390b0008424500070365010203c0800e1843c2e1100915201e0300348805031246020000942c030b0007401842208400c105040c0e103428042c1c0a0044900264000b504403000803400510700d000d000b0aa81040401030100b605090512004245110040e06159a00d10804e00103030703402d0003014090042603840c0b54443d0300789001720f8501455404150140300c0c0c141c0c820b0000740d0384400c4660310f14224910043c0551145d040c2a800c4c01c8a4803c06480b041c00044c9403030841d40c2101440030110303c901d41c0000d156a000054030340f5940c24200c503030380c035030401d00390b005200300800d074a40444103003240e0004600441c10b001819a01d10342c1000b25000604842c107084225882c4600b620030541401c2c100c45501c2d20395031240c5c03280f01d14054828a9a408101402454816484007010090160041080c2030f2107042c01f8010380200c007012611803240036008075807428100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 694651816 1250 694650566 694650587
    0x230301050703051e01240c020a0b0405011206033906030e0f03042303031b070617090619140108210406020a11040207060f0b0a0501020708060a0b0a0503120316 70
    0x403c4507003001906e286244501e040d41012400308a0204d41802c0540c0c0c0c0d40c1c1107000200040350000b0f40d1365241c0300000d008070400e6045106128902201000428907520354904e211400034407218039120b04401d10100200820568101035007010302c0400c00b540c166100190025a013001c94001141524800f50340744030342d0052950100810380c9940040e901e11500810991008060780c1c100790b003030403a003402c014045c3c849044640c02070008210594208400d03100e0050380044090203450843c402a076642d90107824445401c4100030041d20502280e4802952040040300646265070b48005055450540c05014401d80d000724502030030043d00c8604450441e00507402030a60a001034130740c50800140d22882607000341d000c01c1002d0005000344a030340344036442c0e02c20002c0e1902d503601c18082c520810340c00140c1554002a03046c05000f200042d00b40d40540e1409000ca07140100f00085524030b48546d124a0b0117101d014a08100564000c001d5489129031000410040036004000c036480f1414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 694653066 1250 694651816 694651829
    0xb04020a120b0303090315150609240c12030105030d05120f04081315030e070b18030307050a12170f0106081e010906060813020a230301050703051e01 66
    0x420440203800015030300503060341c00000f03003564107103405000441d05007c1c4880346121f02d0788030b41c020094055040e03a01d403c2d2025003617a41c5030030b0800400115804c001801c1c1020200b0304003a4034401900d140c502204d2050070301320203840c140410700780c0300e48040d0000c3c09054400d00510740c050860a00c00d0f0261896101300e041d600c1e82c10780b1181908818100c0103082a540f49004110910310070440b13510b104000c05401c080c1590045c0c00c820001d040700e02c00000e459003070b0841c08d002c000b414842e505841e4400d04000c2a00b40944c3c50b40000b80c82c622414000425030301407966604107010f090b504a940781c004603103804840c500408002c0031200400c039800380c1c01210324001801703034501c240c1240742d2043c458242080d00300b101000410074000241e0004070a51b8079040305000c8241c0c04264640c12810891038550880c0c0b956002500c03c0c072075409086100321003000c2d2585c0100c0d001c0203918402d80050003c008905003004010041d01c000c0300e950b00e094940840c080310281003841100e0407a0360 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 694654316 1250 694653066 694653077
    0x9130809090a0b18090c0d03020d0513030c030605100e01050102060403110a140d030f0b0307030206130f061823040c0c08040e01080106080d0c02010f0516060504060b04020a 76
    0x5100c0402a031800c018011144060390303410000300030b444030900018418841200720010b440c0c5106001c0c0740c40c140e0000076001c1c0000742840c00009400180050782400c690070500d840748581074100300855840d43c8080c290007450b0400006000182d84a2401020040190750032983c4030704900484040a05c10280107034030510000307011070b01c140031040450000c10240c5510078803e46506c031514000101402450b0400c40c081d464807a0144200c440e403120606080c4880860700300003e03154046072001a00803080016001860340051440b171000e028100102c075800c90704c80d140100030a441206041701c034107100c24081290180c0281440300040207614050119014a0501000c1c0815681540500c150b01108400050303102c070140001d4403428074021000c1d031400e84258203440a0354440d00c1c0c01d40100300c601d10680d80c40b1030f42100d426020300b0030500d5171586050031039683c17142080c07031180c0384181e003c0c500c20490540c01650043d80910400d21050140508000c202d120305c050b018040394 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 694655566 1250 694654316 694654327
    0x9062202010c030521240a05091b160312020f16060e0703050604050606011b0605090715020a02010324090e0106120506070f0e011d0307090c02070302091308 69
    0x10b109404910a0724401d29100342031844109125100c0e00d42c030b0a400001c3c5421008020502003117a00044600d41c41c0161450380c1c151000201d04250694010240550040400940e2010004014409100ea00032101b55900030460501c003c03410512400c6000489800401541043c40c1c000c0c2e0315007000404106150034031180211540780c0070000d088401b551107081d0303015500340602041e4011400f64010340503624240c0303020740c1400401001c050520546440e4103c00707208000181d0303002c6078410000601d82d10b84140151601180fa801285540105094101415404540c80c1d07203452003a2070500005082022070400c4108503648450b00c0030518004220b050b84681000041110300c00000599a8642c1c4500c8078015013042d055529600c10428001c469034401c00e841090030179071900076034284a1400081501003009510503040340c00407940c1605a5042c003983c801000e44400400c603041d402e107000381d203404032884207901c0303003440d900010981542c171207014044079070140d452443c20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 694656816 1250 694655566 694655569
    0x2011b030506030c03060a0b0f040203040c03230607090305160509060f150f030412030612021e2808120703080403021e1e010c080412120f0509062202 66
    0x3400c1c0288881e500d031207081100405600c081c00640e0080b46000d82c003040242010060180c600200304119004520400400010030441540103003070f03941c458503407a2800c6c140c13000415190140d0b81c0390b03025402a0300a120100d074006440000b00c1c3d1184041c0e442400d1030544d6130344202d020388034580e0850039840014400345801c0d00700f41e225040c010125400c020340001d00000c940c100070151401140004144401d025540c59003c1c2444c04616007440114145014030500219010f0000e010f10000100c3d140d10400e401d2498051510192401074101901c0d445005402e19008410912103a4014085941030000c5101c50007040001480f5181900031760342101c00207001003040e001c5014900102801180360035405040a00c1da000400740281c00d0546240403040410004039241e1401c802010f07031642102203550302a400074680f02e154545064107843e04000000c14014040c608100c2a480c0c008541c4940c1c041c080510880318696201c0031000c0208202d20a40ba0151004090000c0103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 694658066 1250 694656816 694656821
    0x901030308130b1f080a0302030a03020306150d0f061a0415030b0d03050c07090504031b061b0c1a010302180a0f090501020a030b19060c1a18070602011b03 68
    0x2405120b00c45150709500d4540043e1818296442c43c81494001080d50030040e0340116400a030900340c01070511211595006540e0b403088281080c285070b008070002d0281da44100e00c0c006a0000c40c00100e50701c0703003207506034401072000c804902586880d0110200f0300b030540c90140c000f014590b44490b85803e0030f060389240d1103048040d0035403c140d1074101c205d0603603c4500d000080f440c0700b40c98044d16084c031000f00341d0502950f9001242d0941c540700030080130a900211005071485002c08030040342d00d85003803840c060b010384075280c800005c1c1c40c0d0710505601d601091002c030150180107021000401d518012071048401e00c406503100010302c0c2000c030a0040c01d1051904100340810001c3d45810346010b1030140d8691078800e07203e595001c00c01c000d80030341500442e407107002d00b10b0302810365005440b15402030b640781e4042e140400c1a41c007101001c000f00d00a00c0c6d01c06800c552041c1015113480c0c1ca814881c105a01d00b1138106d80111040041c00c6030050184001e212003241e0310020090452404900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 694659316 1250 694658066 694658071
    0x5090a0803100323010c1407140c09071d0d030f12150b071a0115050a031e051b030c0d0e10060e09010b01090506091c15020406080601020c0901030308 66
    0x100c0b0a0030800000a40e200080104402c104203c22020030801d812480c2110900140d450900c20241980480c4450301421124507962200401d80d408094045452409820302942600203841200348030780c0c035400950042401d10311034540038402101806100707003800100c0c07006020071440c04020385054007460006030b2807040500005444d0258014100c0d015080383d0064465001c00124401801681d12501e20010a410048001940341000080c25601c00707401400402c040840c4804000d44650000c01c070f200309001420198906c082280c1c07009107001c2d545600d498500e01c0140c10314111400036240308a540303840c0700741046211406403014240c00d80e00c0c044240580758442003940543d1241c040544600c0c2e180030040c1c600001024210b0f0702c4201c005051201e818420002560f44404444481c02c09a0340c1c503840103850405011000d10b1000010424030301c0090b21110f5610701e6015104135580c0395604011510f9800069888219190f0310310340003110741d0018404030740288035954 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 694660566 1250 694659316 694659331
    0x303061e0f220615091203120c03021c020409050702060c0d1104030209070306030501050606070f1731060c080304030f051b0a0c08010c1709120307021f05090a0803 72
    0x50501c82d0440803604843d1240c10890032076440340d0030602e01681c400c0d03010014189040132091706180b0780d10082e1144c0702210b0007142141c1c5030325008c1080ca00c01d4042c0c0f800f500e0010720100742c441c0059245801394019019448003c0d14181c001000b480c400200c03107002d10402c541d0706141c08000d15000c006401c2c081103404400c1010400040182c0b11300c2d41191040907140d5002540c079003585811070030f4039800303402c8a100e980700384080004101801e01142a0942c03000e0f050802c0828400b1034500fa0050401390031050180045c3da060329a010820070f100309101c2ea0010440a85070001520030031280e4070050003400041c00010b00003030180207020700c0a4640c1c244541082178100d1026805400740344802190f4100e12505801c2041145a10700906a800000c1c00207030b40d804c80090040003001140000000b920300454140d00080c2303c40741c0032040d40e05000d5502d250845010359a120785d000072040d4041450070706580c14916216807405450200094850011a500c5407042600058081c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 694661816 1250 694660566 694660609
    0xc20011107031d0604030b09120c032a060103030504030b070f0c1101030f05090a0605160c0f03051e041e06090b07110301050127050f061519020303061e0f 68
    0x2d5295684d42d002030002107100e04500b00d02894100038950800d501e0300002640000c0510844100800200948902110300045a1550420980131503805d00480441c00d40c0c1b0f0298034000700925038000d00034000c0c2d03400341e0040c0e40a13807505001100d21049400d00783e0009009548498005003e400108082d0701051501060a420b0111407400320b94007a02c9100141e80a03001120070172866009050b4080604200b0f0b0303003d42912040508482039484000b070278160340551200c2058000c609030f440c00042d41d87c00c1001c959100040301d4075035000303008041103880300e889241c8400f94042c0c4140151813a0359030340034102e45040203c03011364000b1102214400030074104020b46031004d101c2c0c14020205460b084140c1c4040040e0403a03142c00e120712456101d402c7c48100160f86c1e1070703407910503040b0310141c1d050f0b00484201c507420300d11406610010f0f030554001e4070324201c169500101441c0580c4080790040202c0e01149024820030030f10030707059a0010800341d10b0600900e08400000c0c6009143c1412 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 694663066 1250 694661816 694661867
    0xb1609031502281b0b0103080a0c050604110f0306090d05030709170a060c110a1113090507080705060711060d0e2e02181905040c2001110703 62
    0x380440a0400c883c80811040d20b25107080356682c00b100e80ca1400c00721040102d440111900c8402c82d42e00140400b90050400107090140c7d18403d201188640d5049001c0c0d170f480e42010316220b2284c000c401105031203111074072180b0341daa1501007007140c000c0b1a03100084c007144000703600940301038000810030f00601074802000102c0d10000b1b000428421a40d10190000c800369140940c126191504180104503000d120b0491450780050000c40717440d04600f00c00c0a403101e1030b00007200c40c6e9220492019943c2010505406c202d00010080d041d140620165613006407a24240701c80d03405001d4003e401c00003000403001c51030170041c00030101034031188404108401c050091601c1c0c404002c60b00001403d08449217185148154100036012190704025480c1c111124484001940e81d180700c1d51140620400180385440540760210080101400c2884250650040985080d4002603001c00c2c1c401030a5403125554018400d829155503000c030310a0600020f9241110440701007501d00f401c4581c440c19 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 694664316 1250 694663066 694663087
    0x3242e06032405011b0201030b030312040c060e0102030f030c07020a03080909010503010e031b15011508090a0f03030209010c0c080a06110403030207031202071a031501022a0a0b03010306090b1609031502 89
    0x81001c43c0c0133024280b4642402d00d8024011500c980c4054104150829855810fa9022003164803841c6440c4400703441e6100c0b062050303001d2040c418001c3d405031076400008104613505003e000401e00c01c4660345a075a07614030505003a54030b1180c402d0400d4104010386411000c1c1000d0a4140c0300e800700850350b10059007501403440340f60a030020042c0b0340e81c55a80c0c400d1164009011036010010801400c030b000c400781e5a20341d210501900003014940c0204640059902c20f00001401d030760410402c56005d59102449916400051030940305281084051001c11b00ca900446003125403590040c00d4652660b00d4103031403050030429800c218010a900020001008911408145182c5c8403c0d5624100030201502a64003005c00f54159000400311000780d202d40c01d48903244d440c46810740b1403103600714000034207060791603045000d0065001c000442403048039441091440d100312008410f580301d0001da850803444c040100400141400801c0c40065a0480740055980392041e015060a0400c00d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 694665566 1250 694664316 694664323
    0x203040e07030605120f0a030806420f04060f02030c030310060f0c120f17130b1308040603090c090c080603242e06032405011b0201030b03 61
    0x44071100001d481e410700b44418075008401c04032820101004044144000c0075031a207590702408040c040c400711500042c2661142c000d001c1d04040c2080349114442400140044154a030000209819280d91781c0c0daa0114290800c507122500040b41c03460900b4603002041b6040381c5032410341d500710b01042c030070403840d510708201643c043c0c00d0011302011103505200c00101174265a489003020000050300410210fa8030740180013422032985800918a608064183c0d400b81e041c24421a090740540100003c0a4280d1518584a80f203440b011300f841e02c2e11407071a11819851080640200c81c100020003100e80643d204440c014800d08595030050780d81d20000e003c03641100741300b00102e0654010040b4030f140500c000700d1008111514600c0d45078144000721103000008203400c100540d0300d1a6404900251481c030004400b6072141c0004882d11008000e0141108200402441d00405110216521146d90100540e4010307541d00c0ca4865006100d046150076401099042c180e9564a0b0082170b101030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 694666816 1250 694665566 694665571
    0x10603080d09064710020f0105060103020a0f031e050c09040b01050c1209040f021c0c0206070e0103020732070e010b0f0304030e030a0c080c030a030905060a0203040e 73
    0xc180092600e055007850710594550744c8139001480748005580e40c11a441080c000001403962a0003031100d1003445421000c10742401906521000d01e1070010004c0380c2c0010b214580c486140001e201799241c05d801501607008009489011501c0c08030001d681074883c0c1d1141c402ea41031116810908080d0640810443d10250b03070b080b4036100c0c001402001c0b41083c0c022400c40b200d00b0b1034428640704244c880c454171101c231903200910314940050100102d941301d03001038a083c1c400c1c0d02d0466481c40510603c00c1f407403821136898a460350618007000805400899864401c3e41581c840944001e11200114000d620000040301e5514080b03a010020704000100c2221341400400c4410b075108006003501d2904040d5840080c0703c001100050041001c544261545071a5a60300f0540f00e484a10b829500703441d00b151003a0b0148210502c036028445022071000480b0014026284900d403040b060503202c481c0c041e0090003081d0752000030002ca003081c00040444405030304c152030074140c40d01e0440a102409 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 694668066 1250 694666816 694666837
    0x80304060f0f18030305091009050f130902040222080a050606060708160309050a05090c070212100911090c03061e01140d0504171c05040c030834020d0605070201060308 74
    0x11640d0b01f00d9052808940d41c1c2c241960070030b101c000d4a0240016043c11410714018003501080a81c1c0c5e410f54000e400664005600174015502c400107141c1c503a605103040480c01c0341c07640103924002003000002c200380c01404d8119011780541c1e134665041c4001075004840440d00d04004100d011050394941040500c028440da5131086500d10308400c20031465802e0300b005210b0300e002030a0114a1054100700d0b07150650540e220030394403406027490f0b030900303a1950450403568100302c150010482c0c080600d08643c94210b5110303a103615600031800310340c003040702d009810076610b507103601c000e482e6810f25000ca080145869102c14007008000069134000b203095490707007512403052204201302c40104a1004000085a43c00c00064070f170b242c2003140c0c0c414161f03940030750b549010400f400031980215000d940c00c0411283d03200300001c07440690140c00002403161001d9007640e6951b580c20098881c40f62a0000c0104902ca042030304c401000f804081c05c1801903641e038410010000d90541d02410b40d0100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 694669316 1250 694668066 694668077
    0x518040b19140f180a1106070f060e010f020c1b0307180518030922180b06090108060105030c0112200c01060e10031511180a080304060f0f180303 64
    0x5003200c1c150300443d0042d1510007080241d81d005400600000b0b0400d2086411041007054030344c8107008a44244120200900083c0402d486003041c000950030403910401e140c402044081203e0b0702d10001ca0103440c2d0180312070b400c181542002c0021034075010003016802070a40b03610710340d03030030540300f440c91683c01102003075840307800300701c60b24901002000c1c94405940180d894180b090300010070005e5201043c2c0d03041c0d0b27901c01142c0304542c0301d940642c06100d40b0300d0030003408450504100c03030f001c041119a1885403030124004122108082081070403100090002e0403011500b00054440a91900c01d050300d040d41d42405c100240c0226401c81d01c1001310118103940c0d0743c14840e002d0b003560303255040300240e041d9920500c20f005814888060480f600f249030707808138120280250010f0301c913801007034440c56004140441c08102d443c400b5100181d0880e0200c035016500e032441034881c0520b2003840e011516600c85108071601400290b507038521545098406c0506c01407542c2c0407103803540c00560020702d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 694670566 1250 694669316 694669321
    0x10b04050111011e0c12091e060f060f0311030c060301090b042405030f030313080702011707050306031902060d200304150b1c0201051c060b0a090518040b1914 70
    0xd03004405a441c3c2c806d210f00a10201c1c400740c49001882e074024030f8444900070482500400d200701039002c135400341e001440a019003075443c901c14801104601003640e8128400b170440c2c17010b280004581440c0362000d02582e08580c038080304c504c001c21009101079001911800c0802c06070002d41140c103d4003802c0e0702d823500036038101814036251003c0b030000c00b4002c0d401042405142d40f10305c40041e044d0380d80000400d030f940c1004d10048811180010440e20042148c809200115030881c010b1340c400d8006400303c4001c9507661b000051014264900a900040e082220880302c1056070043d807030041c1d0100c4c1c0d001d40319a0701c0d180b400e001d5008441c19510b800c03001035000c10343d0b0f05034041c03000d82802c1259940440250800422541201071800906106d0000340316000c0820068100f50101c4000108001165030740221040d59131100c0800380001c2c56a400216052170410071280510700480c01c80031072903a40c0c0d507400d0120040940300c2d0a8030200521003622804940c061055084060103881031302d030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 694671816 1250 694670566 694670591
    0x605030f15090d0c110d080c0a02010e150f070c050d0305090f010801030218072f0d020105130f02060922060812271203030103050d0503010b04050111011e 68
    0x16000503280742e64a40215a680322425800008030850f036420528014042140b140056400b07080803071b006040d8107020030811707d0110b0108002c041203000b0780304c0c0c0c901d04112804125170300b0f14610105003440014810842d038040d075103020305516442010b54180c04ea032a600000ca054401c2c0303104800040740000d1301e04e07882c00c0100210001c42c3c2c083c00c00071415411940029244801490f41c695814050000a49118861b03c02004bc02038092a40c3d1154000e82c0b4800146607180488146140300c0d0345013184003a4070520aa070f00c1401d80c028141108100d0742d1780c0782c24085484030241e91040c0180009201035454030100d0582c4142d500d0200b80307003125040e48034180c5031641e11118003504581540c10f0752112000840d40c1107582c4151140300302204140000510544060684d0010b4142d0325404100348004000d6043c3ea01a8007101d080b03085400040314148024000d40b000202c05000410565018604065210400900104da81202081100c00150040010003507554440c041c00014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 694673066 1250 694671816 694671853
    0x403080403030306081513030c0c060512100b0702010507050c1305090d020604020120070b04081e0109020a17030d050a0c0906020c0a05150724110c06040303050a0605030f 75
    0x5d0845034082c0060b40100b80560312030040040ca0f00750103107807990000b0b040501c504080030030717980d00415400001c0c0e143e08008010740c122174155007107d82440d0105d0030710000c80320180e0445055418917817800340f59900445090300f00b01030495151080000c5080c19036260681c8403d50561306500007041c1c17401400041c0762208091940c81950802d60501003d41d90050840f0130964110140b0b086071040b80f50054940301c0700d60303c042c12032600810042510360011480c0da0f0841950345590341c64500c0541c6050807101451402544004800d008100c10f000c0080d005511081c80b0b4103503414050402d005400340c54044610b074148a80e68200900c001c0c8e04140e20304050581c0b48001d00d007411034200460744803182400303210320a04610905541c4014000f00301d032649a8416900780c6817012107205100720403400d04800c0c0c6843c1c05d001c981110075205200f5191110703c684028002a180e9480680c0244800742039004044e46807240800e42d40c030104543c1607142131800013495502401c4051450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 694674316 1250 694673066 694673069
    0x1180309060503070806190902120a05060a1d07051c0e06070201020f03130507120b04020102011a0306041106130f080c0609131109040912082d06060c030403080403030306 75
    0x41c00002d1041c003075260341c17198000358803901c20b85200148140d014102d5601c1b0b1150381c000c283d407a00005903461031030400c640c5e43e030007203241d0354041c00035495000400ca440c0751540a108181c140c03009059802007084080590401d04900b4007074640f05030b50030640c1c0049e41c0248124041500c0d1404005259020000682c0c425200e200840c101106404800d8542c4800740c002c4002c0c0b602007009005110081c00200e00520252241041005803482c0c0049818030403142640035505c1d007181c0c040d040a04402d184040c6070020081d05450344c89640340911040c1c00e91003e40c0000003400b0740002c052580c0c1e0751201070f241080540590510b07280c1c180340740c224185e80140c010380701448840c1c403580310151030407000d440036079001c0341036810008004058082c003400c4a0b030050034540302c0d070300384040c0c42c041002003225076480754a150b40d915078a07107104802c180190084c0c4040c0c855041e01c1c0c4405130f207031a0401c030020301d45e61030044010710345072860b04103070026515520009004c00815070540305050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 694675566 1250 694674316 694674329
    0x60c05070c0915120c05030105010f09060b0702180a0e030a1d0301090816110411030103050d022d0a050601060207050a060219020108070c060e01061e0503070501110f01180309 77
    0x410340e0400c40f0400c1000f2240b180010001e141a050010410381502040107004040d000b0030080d0303540d022505000040388600069645419004210003511004895010f80c000d000102c1422014550040b007401c000c19040c010b6036038180c0c41c01d01240510060845904036036985c1013290028058803100070164440074401c1c0e16000031180040c801c0b5060300c0c81a00ca00381c404103030360000d08002d10b100c9000400980d1251a008103107000c40803c40141d8181c902510407203c0c106d40c100826070f542c0d0001c04403102c0c80c00d0003810568035030908841d0010040703501c0d0103486c504126641e902d442d040080c8c0204e00548c02213042440203051a0407104018102d62006140c1216964042c1c50800100ca0010707040003448800944500c1c01691700c0b54480760b000c0004c200781484000c0c5107000300b00e140130301c1c01901c1d0408110304038950991039000580f1002406003c1c110b282400540b80d82004040786a82401003031409a40501c1c284243c000121000b1390007141d90003185001402a141a00b020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 694676816 1250 694675566 694675571
    0x60809240a091401020d0212010905040b0103110406030203100b090f010617060120010f11071109130b0f010e10030b0f0c0f0a0e090105101d0d060c05070c09 69
    0x80058800315a0300c0d80110303031076038002542106428071011010106044440560000810301014074044d801000c1002504440110710390b00e5003c801d007035500130355029000b0000880103101040400c2c40702c0071303007060040001903055078a90210f0b050075110809035040c280e417001180d0084c20401040707580b120020700018100c0d0b04000000d0130521520140a003000c24176030010301664003e00d210381107500c1101104061040c42510311b0701924060340f44001e401e041605d0072040541c070105856600d613120f521000416440c10034000c1d0404001c001d00454403c000c48400440c1d44568064011482d46000560075811b050038041c003c000501100011080b84100b000450050000c80d80c00c141c5d8a051881c15440302c100c071400c0c6003d0024802d07000c550004500000542100e0301980c455805d942269042c1c0c0c0c1c80c0c08000346030496008100c00f1424921031024840582e50420b01080c2006140d00b01909050312000c0440d0318100c541130100720000380031007d102540d10000010301c580c02c0300703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 694678066 1250 694676816 694676863
    0x1015081f06270c0905060316120513030e06040302040e06100509150d0302070e0108030c0c0414070f0c0f0b0108250611030705010f0c12020423030c0a060809 69
    0x700c1c00c10541e8100811035040d0780f2400a20300912604400000303040007045291241410840c800c13100039009a590301080c0c05000303400c644a0180206441001540c1c107071070364840740744c0b42a2422650b00b50581e52000b000c010100050f501c62144c414540c0c4214008c250340e00e0040642041c400080d0030951150180004000240f413285210204541041d98108604c0001d4982039103402666048411103060a00004c11040c20000140c200d0080c400c4c12a0710300d8100b0000c0c40200c2d0300c280b45140030800c3c40800549114000c1c0141c2da0b07a00a28902101e0500a40c0c40e181c401700340c0e040d001c41d07003c80341100401000500b08004041c104150890290022000104080c104024440c2000b801020007030291401014800c1d150981d80000080c00266015070342c08008100303081064000c10f50000100d59000064030079a130a6070507007a0082c40e1441121035203070000c456501c4c6c40b41c5c1031003018811810754071404003135002040c6a4a440d641414401106814817494920515420101e10403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 694679316 1250 694678066 694678109
    0x6220311122109130504060b0f180114031609022a0a0209060f060301140109060206151c0210030c09091e020a0201061a03040302100501081015081f06 66
    0x1e6220b500d440442c8003599400012001c9040303038543c400900081c900d0801000203022183d00100c008841c11500350303d190401808012002001c42a01c40b42c01d666440144051116414012820301004080304c0580300c21500c1d0300c1c040340d80d0307800c001185600803420758845003121155100b403620721180c1c015100c00c45d421955407510a01006885407850402003255078444a14094000c01c6c0501429503960311120741070105110808880d00041c80824001380240c4049602c50044010101458510000d101000301c1040741f00c13030320469804096030200050744d1f280342d11040003106850114501e4901a030141c401c070100d600501c101c1e82000200b00703c5907214800300d8502d40700c46c1c4005032901c2404100f01e00400d042d4000100c414545000399900207103803805075101d94842d90031500e650000d00700035400e6400030700c2019029808120a0562940c09410800b800b1102102c4219565038400c00c0c079241c8520751044079a20180950b20060000d032a001d600054000d01c100000226401f02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 694680566 1250 694679316 694679353
    0x203010b0d11090409060e070b0901090621090605070e03160b13081e0c041b08040f06110408100e030f130b03041a070315050622031112 60
    0xc94812420350300c02c50300d030120116000707079550000301610402200e07000345022401008810341408407440b40b50710028040d910101151400c0906035a0468a10716240041d9694140c0c5410310311002c030301c0c04c6440d80050241c41a000b00b1f031b00503040482d403814809000380440040f021940c0c0240c200d0131381070201140114144045403140501e080c0d5500c2d031284507144020305900605da2500800c5d0507500310ba01e10041c200490380b082c0041d1780640b0203503410001207a5081da0600d040304100d00b0b082c11404c2c002e50103582e1081c042c0403006081d103140c1c2d89681c00c5134102d4002c90a40c900100c0c0c1031110780c1c0104040030031010407610811160a0000503940c0c1d90049980c0350216030b40009000b1050203280d2101401050602c2d81382d600e03424249402044c50380000c10015160741d0220000398124468041c80c800d03200305035040d046550400c1c0a100e82c1d50700228a010b418482d011500720008180c229100080d03002d008410040c0d82990104a111115400f564005505c14160300c1d88442201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 694681816 1250 694680566 694680577
    0x103020303030c090102071205010501031b0e01050d0615080d020c0301090803130317040510050919060209012c210d0327030e030105091209060703030b0d120e040203010b 75
    0x800d036413180c0c0c0c0100100d161000b182c100303092500c2e0350041d480401c4415000503050720700c02d40040e0007002ea100d0400562040d07501c00c0f80c40071810503004200c1410241e08011042d0b0103a40040b424a40302d034030b070205400d0380d5800004190300013800f880c10b240e4140540d800320350080f0000c0c49495501c0e25440c00300c0c08050105d4100840b411805030415016104061700003a0b6400312420512b81410901e440d098801c50100c00c4504000000f8803800020600651304140318811014050b81c40e280d03d00203401540c440c50602903000501e442c250340c2017450199440402502c242d502503143c05200c000c680400149200081100400700c0c11407020540003038000042c600024800c504407000b80c80d003a0003100c1c61207800c0240c3c601406240c1d1011000c41042c034150001d102c26110b48030840e645d110300042c07000d0784d80000c1c0300080c0c075440c7c000014880382d402494041081224240020140415030100721410120300003000c00060b044070100084400c100c03000c609661501071005201c1c880e8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 694683066 1250 694681816 694681831
    0x1107080403230d1107060c0519020103020904020c0a1217070c060921090b03010f0608040c0806070c1412090918010e07050103062c040609080315090609010302030303 73
    0x2441c86402c103116024060840b10380c2e180e040f1806000390322405003110003145088111402010008910701d4041d400011011740e0060007000750740d8103204551000d86040204904254007007058040907a07560010302400740301c02c8003425808a4a14020084100361081241030025002c01030007114444003115910150321300706800c80800d41d00e0000004c02190500410300707005002c2d48a072000782c5c0c800020500341c07161269a00c054030b032202078500380006d02c42c1e407030940030402051214502c5901001e411611418101c80b215807a04002800c0c404101c5071400010f405240035001d00450024020803c0d501c0b0018001c003c15401610302c0c18451021420b00600b02203000c200c40c80d19514a40c055200050004c0000801141c00282c8400446c4a260300090030700b807020441c4990780d4160f402e0384d06100d840211450503440030807610b04000f0000e684440c0e44400040c08031320000015407103240144540a60308c0100d000b003040c0c00c01c02500340d42c0035031405801400141c50010890b03030031164 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 694684316 1250 694683066 694683083
    0x801051e1b0706060303090501080609090316080405100c0c0b090f09190c02030c1513030c0203250504062c06030703021320070c09150302060c101107080403 69
    0x30007080c0c1c80c40621541c0c500070300740e44c50302d0000018550322000801c1650002d9803881019282c0004201f01e0a10544503900641c0081000982e4580581c1d4050a41841541c1e400d08043da030724001030014101a441e040824030800c030600412283c1117603d00a010882442d40c1401c4003580072600c0710b001095182c6c010014040407540c03d25141c84a210030b014101003d1281c05100d01d00251a40c01201d10a000d0348107180b100c0d4008030885016500c2007092010507101c10f00701e0b031011101110f00002c181e80500422007505922000092181c0345101401c403e104610315150500c8111a05584064072150919030116412441d9651b512100d09010600c0803681d10b031440003908010107580300940c8001c0e00094219240c0058101c1a040c107202c0e0b1004c503c2d091111a550007600c50007030003c1c0000f403c0351081c42400d420790300c1241c1d60a101244088003035185d034081152039100030402c0100350b01c42070380a04c0c0c2d8030040c024070780742e1441e05480300d040154660b2003c1c0280981d000040c000c02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 694685566 1250 694684316 694684351
    0x90510230d0c170a1707020f1314010e1f0605090d111c0c0504150e0901020d05040615080304140906040e06100314030f030c0c07050303040603060801051e 68
    0x20403002070b0002d0902d5005548016050240c0c9941c1c81c0d180a8040303488414140e846450f0003401c030241c3c2c034400c1d0060100001013103030208128420342d1122407415404d0b5a02c1400b41050181d2403120301908500041e40c41d5410100c10b2100340d8001da000f400d00044261406000481d40082030310b03002e901c1920741a406071603e24090603507000400c1c0660700036103c0a520f10a000070101100b500d01d00903c040c3d070196449030180026500c40c1c020721303e0031041000d004c001101250311900d0340540d00c0d200060070500885101c1c402d4400c199029540d081d200c959200316907001020543c020131047c4000d500d42860315910a20200380241c0440c81503030000d0004065417a02c1d0089000c4204880c103452151402c503121800118680c001075070b0004254036030b00c000200020440c4c0040000820480c11f40d0743d042070b04049a071083d52010300307600a02c0000209038038100040c00c003070940c40d24082909410109250708440c00144640b011211a03100c086998080c44961f5812024000e07000f00d000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 694686816 1250 694685566 694685573
    0xa0308073515221505060406050d06083315010309060204080a08191106060d030201090c03051c023715020304020406060507020a0905060d050601090510230d 69
    0x4076064002c99003007030400031240322014006500c003d02c15104442001010180041880c2d000d40600400e50800d404000601881e0b0281e000f60140d51b10011020400b00d03141c4924908188900900941340f1071089001441001c0380f15591418000e0000c119a40385868000881c520400840250602d940ca4080c10705000c120b0f011035004d8903114040741d20141c171900d400d403510b034400e14005241c00044000340311300d244111216940e00c085480204035546070760b170420080200f203230812005c4d50b40e502250400140d61100c050000c5003c0c0c00030b403004860308040300080d849602048400c54000010800c070b40304040d048011140e071045140603409075456081603489403460300141141d5694000e0840344901600150f1045c6e10a54040c0b1a403561071505a880d40103511001350702c103160400a000342e02d00741e88681e81c040c60082c14402d06c02400d4650509040d400e030000703002c454035001081070000ca44030340300004000c2140080c11700600d519011841d4050714070320521621000407480c061 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 694688066 1250 694686816 694686841
    0x2306010804080f0705030310060f0206091b18070f0f03060b1e090603010305030702180421120c030e0120070809040902120606010311041202120307050a03080735 71
    0x191707a0100841e9528100355004100360260b600c200350005140c00f8040c07403107a10104100e07009082c40c500500c40301c00960100d00c1c030828120300943c2c004111812001d8099a01081c0750f002e1462074455a450400c0c0304402062540e2142c244001d01d0306101c420001d511405007214210ba0800b11052000000c40306860b10324070800d00710a60204010001005100e008401807050f00d200302c3c1c040780d20601219403a48408000c90b005000d04012480e02e501c00b01c44200c1a0f042908ac0d4540003d01e05626401c010803038010b00e08000000742d50384900c1104034403d20890582241c0d098140101c40070a20346052144900c1100815601c404034208030340d501c1c2e076040100170540c0242050300b046401c014483e59040122a000d0001c0d0900004890303101c1c2c110215019240012001000a40b054003440302580e000a2210075034070041090502250b401c0c04040c060b00d01c241d86290039810614001404910040d1440702b2086e01c28000300101c3c070409038503a44480413000c3c441740554509100c10b10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 694689316 1250 694688066 694688077
    0x608010504050f010606030c080a0914060c130512030a050a0908481210051608010b120703110c0d020f010606020111070f080d0204092306010804080f 66
    0x10a609210500040000201c0c031692800c46050081180c0e40c1d0340c2808400317903042c031642800420200c20201d0100302140e003200a04500415420425150300340343c0074a40035007140c07021003000f00401d00880030750442d01c01c80b00501c0100c449810b045807668210351240701d0140700700305000d800281142d00318000c40c100310042040700d00b581e0317410040b47c60301c82141c5040180c0300305803501c0c4d41c10004082445030000708032030800c0c0c0c104180c21440c0424480030100c02c21035040d881c819400441001c04041c011144a480f900c0c0e09014000c40840001e0729022049e08404480d840030701800709141007410342c20b6800400d40c600400c2c4401550984051b034841c0844011071801000580c00023203030002011101d001c52072000304449540d4000480c200c440b0305c9018480302000300b219101242588400f641c542e4016404079103000311050354807040b68840da01c603c920540380d00c4100152024041e034842211980c3c081c091203480d1900009020341d00081005201c0000460b904100301601ca06840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 694690566 1250 694689316 694689329
    0x60e0a030b090606100f210f05090703030e0105120a110d0f0c110c01270f031b060305040f0b220317090a030518040f020d0203040b160c020d020406 65
    0x10740a00b0800051902d42c2c41c00c031000c50240010b05450725a0911820702642c100c03000b9600c90f41c6050100442490103001581800890380c0c486c50801e011b083e0b148143c5011b082d00f50001e0007943c1c5146000351111002c1c052560600c00301b0b02803400e03400000f81820b50700c129041400100130000c001c0000207405042c0d138107418585041c40902050b05580e000004a103103548648085031200c0e06022350b00c0e043d04014600207507180c5021040801e079141c070415030504400b0000807194a40344004110905680280d038010102c00d855515140701d45018406070519107000d02c1980b805071a4034445142e50b03c2e00500c030300b00150018844640440d41803034950402000e0342181311a030b0030000d004c243d6013a031504481103400c000c6900c44c500010500c80031949038035640c2c10f08080d03d2a142c240c1c4100c101e01030b04992102070310010265103100925004620b00001a183d0501d410300002c0d42c0c000410400b150304400729284d40c6d294028844043c400e0781151880791003142c40c80403a001c0d02d85e43e4080d8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 694691816 1250 694690566 694690583
    0xc0302040b0a110c10021009050a24110f070210032c01240e07020c032d070509131515080f150f04081e040807050316060e0a03 56
    0x100451580202c403e15500000011240304411040030480d00c60018005000580d00141c892104400160041825103020341e06880004805880d442d01c10441050b42e2003032054280851000815588170b000d003001e01002449007081ca04007000c600754819402c010740705080c0708c084c0a40d1203110360481d40301414800c03489128903a01340b0b49100c03614403c5040900950034141d8401c0845108410300490482c66110000d42c0ea1610302e52080111025100c00e045018401e05440544c030200030001c80092002d00101c0c0301e08003020000c5407441030207a40c407442c0d04580303820007055450348003142d000340c500c05e1f01003500a110b00d07003800b003080c2285075007070113a0901400b48c004c00c01d000018012603040303d003a1144586a10903241d20342517804c1400c5042d10024000c200c10700424440154494803c0d8407e601c2c20800d1000c5007040d0030b0b0300c19400b0070301100203410702c40740314244148030042205030b00414541c0603078410b2113000030b6280903c004000c10f911108a069032001090f400458020624 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 694693066 1250 694691816 694691827
    0x3031d0d120f0203070206122d041106070b0f0702030c19030905010504080604081803060a0b01090b0a0203090d051c0201050411060702060a0f05250b09060603100c0302040b 76
    0x480c070140544264100810180c0440d00c0c01940084200d5100d00d40c0142814645242c036800b0140d070b0940941100744819040d901c0e5002613105601d00c0c41c1450400c3c1c000c01252525160000325100d402071058020f080a2011030001a180041150485084621200f203590340740300032403840c06032014004040c415005920b1014880034800b142890082e695880e0141d20b0b600191500d2081344500c612a41c0b1040000300482d2403200685201c2042c00302c403441c08101c90000074540741d029200c0b02c04050307640203144050f40c6c0103000c1600070081c6c0310b407e50030074601510107500e03401172241080c05001140030035020048240090395400b0940f0300d41910015658400900808044904a0305500c41a543ca1301034503000090307032081e43d4000c06071450221842c101300d8100c98000144c0742400fa00b4044000200c0307500414070310441696a0030f200c2c1c1112410207002403507000e00302c00000e400000902000da103001c00d18800d0104240d80c0400d62610b0040202c0007485681e1100c001c0840202c3c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 694694316 1250 694693066 694693073
    0x708060423040c0e10150e040e0f0d031a0411070c0312030f20130b030a090308130c03120207080706030b1008060f010c140a03050307110c030703031d0d 67
    0x40c000d0269003c1d480c0340c2003032912040300c07400b10b00f001e5486400854640c1004c0159034425501c44c1e0464040d498000d59805104001c101514188925100207400003040e2031040c5070200070084441c1030500d4203000d0345010b002604c03039000c0107008035070281e42c580d10300c0b03100307190b50804a41c0340c1d6511441d084c61842e41c0341020790100d080988101d000030b0900c000d28090211074000c904903d20240d000d880307024200c141c8142180e2011800b41104000c00100041440c0481e0181d44150441c420100d90001c20f841c009200081c0180190040c00c61112150046074101c685c01e0240d0340d008005080c00c1e640c1d000280e1401c4821707808200a8801c201e40820303200c0d03154001024071780f0140d8040101c203010440546140504648250b080b150f405082a4035612a00c05250340c240540f1401c403552408003802e504004070950190080f4100105012590727621141800c400c0080d08040d10307020310548006a155803036803001404002e841000382c1d1640c0a0310f00241210100100b0149030b4036458607 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 694695566 1250 694694316 694694381
    0xb030c04030512040f0b09120a050102041a16170c060109060e0a020c1f0204030204140f18070302010c03120c0e040c0908061303030b03030f040f0b070b07080604 71
    0xc45060140c004801e040e15030920559095540d4003085034406806c101408046800c0b1080056003c0810700c141c0725203400a00030024424014400940d995003016110244400c0200c0107250100e003c00004400c0380340c0c40403180070326510500c1d840c025140940b507008a40100c03100d102c3c00307002e010300010f60840306a0100301203032400400e1900300d94410f481c40c0102c1c040c1c280503201d01d40145000804000701c21040c900913803480100141429125000302e02110b244001481881c136500c4280203c000700050b50603032101888000411201d00c1e04c0146480740340e2480003d0510481c03651020415006082500445905407002c0045a5544c2c0c4001c142c480204201401170746001c10b42c0289604c541100402c0d64114401080305448610150f100c0300e4842c0001e804040c0d03504070840716603a0030300050421540c0e0a00481d121400d01d60081d042c80030660290541200c1000100001820070603503642c004458203021103c0e0703907900b002c1800b030240d005c0d880803003e81c0f042d0300340a07840d20030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 694696816 1250 694695566 694695569
    0x60314030927060d0201090b0c030c0f07060c1506090c0c120305060109051210060f150302030610110a081603122c0102040803160614070806040b0a0b030c04 69
    0x4441140c2c0c40c6854842c0c580342c0703408a03100c240b070820814001581c0ea040c90402201c0552062501d14003169490034540c00b690000d10766411103420005007402506010449a0780d4144003030060618180b9100001e480c0005460004128000a40082084461550001c0010b009494052000f070007501801480d04115180c1100c69800404c00d5030340441c840c0c03040724400c440607159002810300b0441003105110800301d03004201c0c820603080a008072003a004200090541601c440c1000d401d10500032901142a0b000500701441442080010340c0e0b00c801d034040e19015410014210b507400c6000318284045048054000342c2e0000d00e401e4150f41e10044445a58029074908070704039810741120080d903416640b5541c1d2481066013a104440ca41c0d681080c04c0749010000514082c0c4c1c4401641c1582c001c2c0c502510503c4040e0a104180881805201c040021750079030301ca22461b213a1006461010050466802196104d0b904613140d00e0340d0301580040c0220186650b1240340004030820107a015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 694698066 1250 694696816 694696819
    0x3032d13090b011206230d0602040e06030d02010c080c031f0b0d0b03010608072c040f020901090c120c0c08040902042c0703021e0706060f0f08100b040603140309 71
    0x84015061403c003180c0300d118107844003d030000c031b040130700040403298400200c450150300c60500c1020b540040c080e44020401001c0302c4010305503c0c9410810141802d802d9400d010039641084440d606240e4407400450b171108000e03d0017038903612a2089810a000525600d02110500035804140340d503031013002d0680086100b101f07219440310b650a240c2640e0040c8200e928540c0540c10a0040324407400038030304004403d250078049003504114101c2001c00a540c01d444004009a8400c15410009800360160021403c14171040c109410000c00501c0781d1900c564181e40d8620321034035401c0c0b0035605218041e0308007100740d03190f030f458040e164020351240c45170724414440e03403240b00603104004403102c0c0d8071080d89580011a41d5450b205802a42c000c4000700400e10705680d80014a80060010380701560087ca0009031081c1802540d1000305115002942d0342030726241d04000355100004ca505e00100b00c4100031a15102d002c0101d1f028050f541c000910340761104141600d1a000080640000f00e030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 694699316 1250 694698066 694698077
    0x2040e011e06060210050a24030b0a0b031b040204090204080708010b030c030d0c0c0b04120302012a0302071103060408120a180809011101051f0503032d13090b01 71
    0x781caa040c00031624503100700d0002d6000451018045175003076110b103911800940003c541c14501c40710300b000c803c0e07488ca40b9080d2a0341d01001802840022503100d607001411150401c51041c107000000c3da03d04d14500303000b044648001c158a002e45450701603070000c29000c8803d54503607494620603621040c040c003e00245600c0c1101d030b00b0f2580790002e0402916040940071300340c0d20070749000c1110580d4582720300303403000040c9000c00119a080360009100414401078400300c141c0051034024250341103000b449814440811040d0703418502154401b4441585040040c1d884540d45001c2d00080c03c40003086078180a0402000b044c00010701c02802403194000250a8035947d0006100480b0358509880305800800400c920000300080024504080141090003440103984051401c4d5207048402c0d0b9040c1c41e03000700012000074922541d001829045014500707200e28100741034210707050b038242c880040c00c9003052960b226242000f1034443c00c04421074544496250070754900030b04404022a400201c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 694700566 1250 694699316 694699361
    0x3011a0f09010609050613030210030204060809060c03160c0b04030c0c0b1e07060b0d140706020c06030610090816061b1a070210090b01090c0f092102040e01 69
    0xa082038400c0d042c3d5107281c803581a034500704410700000d5000000060310400359000048056600d41401c00103041250341c0c0540d9981c1800380080402c40c0180c0150020b92000040c4003190078008203481d0700034041001d07a01038154201e0f0459030035480d40c10241403161181c2c240024140d00c40c0214107400d000d0b69280400b20390741c40300401d40340705500480d44450080d5807810782c0403079a80c008011560040f80040345085294001030241556040b080310340040b6840f003206100d005118a1004040d140050700051045001007846480700030a42c5102d281111001402c0c4d90240800602821b044000c81d6400024441004601e20701400707607c001c80c1c0364032103003015624035065a40a16134030101045402c1c600581c150035519001e0a002c003980601d50300600c07079107082e102c0c008030300d030050402259a524001c20001202d02036580300d030800041480e4410b8003900300304480211200e00c03000a01c0421080d8401c540c0f24030070403000b54850f0510b0100b004440b03054000c440046020340c014083c48 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 694701816 1250 694700566 694700569
    0x1020609030403120c03050c060a0605031c0909020c031606020c100e0a0f0311010f0f05070207030b0103080d0902040207050307030e06090a0e0a09060c05070b1b190c0203011a0f 78
    0x2c1c022407000030850300c481552140c8180c45044498260b40c03280c02d0030b60601200d4500d242c200360081711142411969040304104a140411520650140f90075180c407502007961802402505680500000031344c00080c0d6440d40b800c00c10803180903407842d6125100c0c0c1c0281c1d20300000a540840300c044500e00c80c0d03004958900c16944511003414181400070400c58106966880140a90000540030701c00c5030015048240c0080c003030340c00c1400700b07044000b51001030036010320304441e40905140c0455001080520000e503017028146d040d61b40140ca01610b0b11009242180500b07039191000350001d00120341402000400805003039040d2007030300d0b8100388100c250140036540c0582c00303941c0d602590398542005040c04981516410018107040440e03d62025141c5600759120703425000d0016030b001501d101400305c0100d0341e94114107404554007141c004c8a81c54001030040d918034a8001d0b0700b400307010000724014a80c200100d64060004d00c403a0903075403002c440b16001a446a801041c0307111014903903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 694703066 1250 694701816 694701823
    0xa110603060609010c0218090307170a0219050703050a030309050c01111002090406120503040608100807060302090303161203060504110726070b0106030f0b0d150b060d090201020609 80
    0x1e5403020300b0040c20300f140d0030011244100208400d0340c01000c0d01e21441c3c0111020b5003054810003829008580e28805c51400c40c1d8409a000d2441c0070306a000e00520070f02c2070f0702144403020b40740d550442c2103603440725041c5103003010b1182d80020080c1c40388030100742c00c264140c3c000002850049041d5240c03000b0800040d20b140c031200102c0c03d1507070401890301500d02c4141c1d002e400f01b00c0740500300007030094980090b1818581404400d80786135202080820019030301c070f1405030384011030850200f0585d14140c21166036004601960b0305041e000319210000d91001c10035140b20040c46914148207440c0340c141424004c040c441c800000a0038500701041d00e080c079001b41e201007140c804040346448101d4652074541c9400403104010113000f03030341d441c95045e40a0060050b035800b504203540e03d549424006803c0b0f83d4004e0514111078142001400507503100c2c1d21918210390400201c1c5824618841c03108002e20061943d181d20000225844000303030415803010300154400e800b01d50300c640320002030715607 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 694704316 1250 694703066 694703071
    0x4170a0201110a03020a1e061a0405280903110a14010608030405060f0901110d050a0305060a0602031e0d0609020c0106060309120c030c02060a2106062a140a110603 72
    0x2d80c6c000c400500002d0486483d010304004080084e40d80344049507110000e403105040030350800d0300100040718003480d00b44602c81e040240d6001604041c1401c0c07507c0a8503d01078800083c0041e40d42170440b040c107004a001669400181c0241c0303400601c1c034034059681a10000c8060019843d140c0c0100d030f004c0c40002194180ca4000f4001420524038501c290320560012180c541044640c0301c240300303010020091102ea0012580301d0348d44a046a040050445e40014441d41c8285141a020090320360040111003041c075818180a034406080c40c4d4198542c403c1700692107910340740a10006421045034090a01d18404070003d10049680387c800301c0607a8800b0300081e04184403911032810150003141142300041c883e06002c0038014854000134001d030070036807901001c5240c0c0c9695140460001034000a0007031501d000304445401e1138001484a4101c052201e0f40441c000081800200702104040105034410f0461941c507004401054543c40c08140840d122074001002840030b1074407009891 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 694705566 1250 694704316 694704323
    0xd060e130602070c05100809010b06070f03080601030905030408010e1203271204090e01050a0911010c080c0601060525020d0308061309110f01050c06040b090304170a0201110a 77
    0x485412aa40307030351000b50301046007120b2002449600248549a03050310000222050710790075010716080184138207454840d10b88511407481040b075440040ca040b00042407064051602c100e10341c0d0703000e005030700500400e10041d140340f00120700060f00a60540041c8840342c488402c2d504d440204104084140c00143c42115029101c0d00114156044000546190f205180f048945410f200c1900030802d9120b50440c1ca0f14a8503541000e80ba80401d004481e00000b00c1d0703800700403c0c6c491f61135a000c03100c1394030f600504004008400009002c003004c03c0c2d0709282461410380e505541d6446002c1c10540c008501403c01180c1200451202001640b440201c1034000c3c00e62a404201580d00705c0300180d008280c1e50348904103078028204e034502e07440341c1031800b8800d596040c0e54400c601308001c100640b510501d810410f0400460282400200d151900950700c400500380c1c9881d0440e090382580103a401441300300c6500c60240b680e44074001502240300307000fa00c1c2c401d0202101d0f140503880d4510245c015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 694706816 1250 694705566 694705591
    0x20d080a110a21021203010f150512061c02060c0d08010501050f0301030b131b030303180c0e25020106050f100f2304030b0f0108010e280c06050d060e 66
    0x529015203c1001c800c2c12403c0d82c4143da074aa6080f03010038070a90003e8009a000d402502c80c2813200ca401d034007600c1a1001c81d42481410945040c40c28801808000c049038059040e501c1e503004181006443d50300442d5000305902c1c0c850901030b00c00c95545002c0091040000c1d040e00000665500480880300d4140700b0200d00391440c0c0c2940c682200481c0080c11400701680c1301100072010420b081413040d81401c1e5011a201014550305000f03040c0c030034480d9946603d07941202130900041d40d0401100454400405444d00d030b66519000b9070004081b20040d0b0302c0000c806151040065041d80300308241c0e003003220242401d01944040c40400345542c014a004201c448229007a46401981d190600e0140b8081450000e039081c00c181c030154109a1003281c03041101410300141081c0078441c5070140c0100c4008110119030042d00c140e41c2c49584c41c103004100701058540368400c5118244a14807900401811041903968100801315440140c003141014580741021030b06c114010000703070243c100e12800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 694708066 1250 694706816 694706843
    0x20a0309020a1a0d02160b010305010903230a0311220305100524360c16020108180a08031501020604032313060e10020102090303120a09020d080a110a 66
    0x1a500a6000302c0f10075405e02c031035910340400100c0d140c01c4123018511410010910810500e0054800810740c84070314070680360a41c0e88041c010f6000e007980d611040303d141c08036552501c01d0352007400e445506001250f0b10380030050304150070b40e05800b200440f4450001c0307e6004c0302d00c50480003140c07019500026101c0028860030301c40000403c15450140d001092091000074110800100c030011390703110b90360b00425401c80c02588400840b074941c050068000c0624154502c6040c810241c100c880007810b01040402103040d00041031299886120110111001e0360360508000440f5007085a00c0c940b52643d02c240c80c1c1040d4404100715004a0340340d180e0300c4d08022840c80e402810222522561901201449840d5030406641c008100070f000c01d40340e414040c407070201880b060144103031700e200541e80100000407443c0c400004486184c0101d50070855581c0ba8044404090080000080e5014017500040d8051000c000010030030402c094a9489400110611003501c4d40e4148401911129044a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 694709316 1250 694708066 694708087
    0x10b090109020318010906060f14130e1009050c0901050609030d030e032503110d0f03090c051e1c0c03020d110a1503051b07060e030d020a0309020a1a 66
    0x207150000046481084c64070300860f59642150300810003900c2c1307151201001c001e0301e0021a1940080d29003000303000c210301e03c4000030030078001c1c81e5601044c0031640c849138600f503400300344020020f4445003c0103114000c10390800f955100c5090300858882c161400001805142c18000c40f804410050007402081095800071380080000c2c0c045940030f8002005040c005a4510020001c0d008800700c2c1d40b003d841141c200100300c080f81d10003003840c0e6030100c0342102540c1c1d0000d010802082da180340100d44151180f91086421902d6888150021003a072305943c02c0c5440640641e625141c02d030348c20b429000c10700324040c83d40c05154501030034520341c0f1102400541095005201c8850003440383c1c0941c001d0810105403081d485a11441d0003c10120010700d11a81c94000e854200c51548040b05c0d052005030541601c901c50a20010800756454500401d100d03000c0c820303a4640e407070400341191161545040a8003914120800701d105014040020414540d581d01c1025907903054141c0b9800c0400500c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 694710566 1250 694709316 694709321
    0x6011701110a020d0810050d08070c05101205040507030c030b0a0b01020d090302150f040b1b0705010e010806031f020711061303031d040507030c08060a050303030c0f300702010b090109 81
    0x404a0080038001080840c81d038230781e1014241001e111380e40d040c1e0340d4900c070304103003034240040c0e0042c0e0f1041e0b0b4881c0303007c0900ca41c4a401ca900022a0010000b91a00d0302d02c0e229207460000ea000034550001e00c18000b05010382c4401c1c2502c1048000710902c80d98001000490310380d8801d68800010580008050001d402c201008030004040e42e00140d00e1f021242446500c03a80291740182100580019000241c0b2a1000349070850980e8070300500503142448000307081c2c07040e002c654504001e507040020b0f807580d03410040304100005801141000c00030701402d402c0654410901526985900d00e41c6100f1400c1010444c0c850310540007828584608640d4200c0d002249180d00624428008816000030384e110322805004821341c2d2070000d43c030060701401a00703000006001e0b910541d0703410310811079600c012044079441201d410286948441c00500368860307024880c81e19140c240945c10007654840c200103400101c1d01444800003059403203040c128240c84120312126003010300c1c40300400006076580c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 694711816 1250 694710566 694710571
    0x509121813020d240308090402030c120403080115090b030c09030f10050105041118090c0d09151508190f0503071b050d05060c07020d0506011701110a020d08 69
    0x5002403045600030030160142e0700715000f19600c0590300d000105081c00403541483d0071145262034084494650b407034140e102c1c0144500c0c140500d0700040055a000d0000d400c50b14100220402441c03541400e0a0042022000340144200d40681c1d0a64942076400303605000119155203212918560f210348154100350019480c41d905403044100c404a0030800340a5030184888542c0006020341c5080208000c1d00c000381c031035003903401e01007241079084513400501000310141507032454281c0e201d50142c80c610b44240031030100f040345414400b00c100008240e00401f641c022030300520142c1204085071006002c04d00c20070800354070100a00c0440c00580100f00c151074041e4100c140c15081c40d8440d141150b010510071034198032020001c080082905c1002005041e003520181c541c1041591000d03941d01c2d0107411a03040c4500482d1100c21583d4448030103014503880b00030740d00f40f0359444260400c5640c05c84182c80d100d508160070142050f00341c10581d5407420a5034010440c5200c0c5040a40386480702 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 694713066 1250 694711816 694711819
    0xb1c1d0601120309231f17072c04050a0c0c14070e01170d0f090306050408091c0507050d0201080604090615140a080a0f02060310080d09030201020105091218 69
    0x25001c3c00110a914a007440c800d242e4117000c1080f00d4400b000c200b040603580d1003083d440412480445040181e881281162042d01e56420a14580c4030b03564261040907104010041c0062010b004044240f000305014080d20b100340d6040c0712513150b200000c42a40c40000700c082c000f8050340b03400c2000c6050604c2d42c0b260030f056181034881c17454940907000b0107600240c028030305064440107034050f20700c8100442c07840c03d4203601d0b20440b01c0764000d000400158142c031014241c00d4640700031030107010515080700d9802c080203003116001044c101c0c40c41d44c0a00006005d5074103001c0c9190000d243e0a00c44280c030180c1c2d074160f4419001f952240b08010060842c8134040c0c0e48281d680106014244031003040e00c1c00303400e0503d041180300401c1c0040203019541e541000c0d0507174010682040003e42c01e18504a5103690480d60703a6140c1d60f80c00c00d401d50a402a81c8246940d1107210380c0c7d841000d0704008100103590007a8001d20143d81c40513085607031002c002ea2081d0f200c40082000703002070001c414031402c80a00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 694714316 1250 694713066 694713077
    0x90103261603110c01020d0806060d020c03070b0106120204080a06051302030a0c0f090209060703050703050f040b1201091406011d030f060f09120d11040b1c1d06011203 74
    0x51414260031104400a084011542c21100440d0701e403003c1100a110a00034801420750f1f00c110301c0e00030141d8401a0085009103008603600413003c0c0c03a9010f80360010843d800310390300c640071070800081c1c2c6a028400ca1001c034410508034819402c090003107e0a442c4450700510ba565001c1d41d03210018140181314242e11003801040d4401030350103001c1c2c1d494280c05811002c0c1c12034244201d540e2a405190b210b519518810880202030ba241c6c1c000381e80b00c10b9054144181c4540403824142c40d1486100c80007a0b101c0000900413449204041c064601c107003201e10454007682c0c031200b203c4100c904150040421041c6400051072a620507030702c906144403d8284024000d03d0200420720300100c3c56105280f94100c0c00402c1081410b049102c3d500c141d4120050040d06150009070031144a551309030850a83c440c022604400c291000712001030144210581c0d584608182e40f0344080a00a0b140c80041e0615160360040401d120680300003550420180105900e41038001035080000308003101480f1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 694715566 1250 694714316 694714327
    0x1704050d030c020f0a03030206060d06140f100f03030509120f0a0308040210140f0a0302040e0103050a200f061803030a181a0304030e01090312020d030b09010326 71
    0x8450104406280d84252203a4003240d05030f104210741808410a01405443c1d2a00200003091340028155001b28054942503c502e102c3c3c10f0a00c060300c10a076003110410b0190060203910039240c2e031038900c60007a207500101d03125107880c40700d0700c0803482d032001a00040050150b0496403410b940710902544000741201d0a0002c031190302030610368055003e8010904550410007542090490325004400c50710309001040300403d443c0e0414090070041c00d03000c0b90080f0389150040e0280c0e048401402c620b091110b42c0f503075646089a40c0d139403030321700440e28904031640070401e0200c01410550a80c000401c1540d65452a005200346604425050040030000c400d01884c6518180018103109800e139444401d001804a172008015500c0c3d4400105a0303225205008648074107001e803074104d5170601c1c01080007402840120342120403038201900f900e0645503505002c5800003440c441150040d101072003607002a00030045800803d11001d000c540b59803041100c412900c410006003041c0071000c172403c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 694716816 1250 694715566 694715569
    0x8070c23070e01090c090801060501170a180b01051806131a0a0303110f190b0702160603020d1505030a0b070c0f060203061503160807020c03010f0605101b170405 71
    0x100c084e445250069a03401d03440e8409079100b03c1240241201e00c00a1043c54a040002000034002c0d01c8100d0018040402240300c400c440c1d0844645141400c41100720500542071070000f1030428031655200b4110441c403840d0001030480040e00c070b4003004040100100c00101088041c3c41101c0f0200500520002100900d681d0404650091402a0b95880183c480d60013141e01c0c1588d82c0740c405582e60301c509203203030390761000324200c1201175884515000d076611004816858104060505a40301e580030502240f21549503010700f001e1000b0310418406400c04a04001c240d003914014550035030081400c0c0300218898000c2c031a0051024a041d006041e4143c5422202300140482103c00d503030000213108061802c01d130040514014520030b0b501c0d5081400c0003680300c10041c2d190401b4001e040300010704aa000384920f40e211280030b0000c1c454800e100070364000505480c064540314950001c00c0c1a80c10f44940c070710001c81c3d4002022082070081c0c64440080d038400d800c5849610640400c00440c40d07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 694718066 1250 694716816 694716839
    0x2306040603080c03030939040b03010207150c090e0c07031b0804030302010b150904090804080a050604020a080604170906040b0f07121b03110a0204090b010608070c2307 74
    0x2041d80c3c800145849041a49070141400188843c100c00d03080c4050a882c0d6000b000491800d04000c2c810390f03a40f1902440d0003140c060101d050007070351305500c0401c00009001e4203942101c0c08101c41c810402c2004000b05084d10204258018100c20881c24030004003030601d4a402015010301034106841081c80206003c4001d0200b00380c2210700181c0418100201a02402814410401110f40307214010000001520074000c5e00d04051255884168400a010340360045801901184054aa4a68a90600680e520800c4d84d080340201c1940c2000104090017280c140c3c040c56100d40111210701c2a40c042c8512500594902c981c801c1c4200310006d040181d5100800c9644240f04650f51103451038180400118240401001884096144906c0c803000388940080d000743d1505040700007030590b0f419146002800b1708001e411602e40740c1c00a0510000030001c1c0c5c101c808a9540c001c050b61a0f28049424601c4000000c100144416400402a07255044a114614290215040c0d10380d5240710326074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 694719316 1250 694718066 694718077
    0xe16240518100504090c050f0a05092808120a020c190509130501050603070f0b0c03070b0901020301030c150816020c030a0312060f05240c151603230604060308 70
    0x2064000400b000b0105c020b0103402d1031100e203424101c0c14241410074070001d92090840035000c0040c00102c0c1800340c0e1350a47c2d51111160111800302210f40c4400b0400d0b000c15032030090607250707c1090f0201c010400050201e4a04084540c050061123683c9401d101c0340010701c0c1070709031001c0141c10380402c641c0c8455403040c0c824898a0000c101e020420b081660840d8009000b0f64040d40094030300b400300d17102c4074009104855407041038aa90f081a089281e04601804200924800c0300100380300c140741c0c0c150044c605a0380641110a460341c0e5922182071440c038050300020100c1e01050000702100078400100313a050040d801130391910500240060304040d05d102044011035881d2420300300c0042d0b01e00c1003401404903808410201801e001c00600c00140e0401c1311114410084440b0b052100000103a4010340080c0c02101c0c1001280e100d0b4450484d0304070f40345110074000450b0160354520134000c41000800f20b4564044032015100001c8035110014116a001a2035010000014144000418 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 694720566 1250 694719316 694719349
    0x60403120c0c091518020408060405070911250201030e06040b07030606020a081c0b06120412090b160201020c03100501050907081b18040e16240518 65
    0x790985558034110302400c4a580141080034601280c4e80e000c1203c8200c0042501c5955a4421405241c1c0e034044000c1c0c851034100340814041c00c0306010410900140c441c05540300f084090210ba0b240d100c00d41820700620440c0000086102c245905054104a0900c0c1e0f880c01031401007101c400c007080c00307490423406070b60803540c01c0d0b900c0f020803404507414032444025101030710203003c2c10f4071a070301c0c1e100c100d01510042e80c0d00d242004800032406030f10744d840140020720140903e51240c0e00c00310b17822481c0c1c4080700c6c2034505103d501808011f1f24499400c0100790764610104600300305554084404103000c10200320b0652140e05c441101580d010091450075800c0720078007003101c1d8180b03810302c0400300300034000c0d00600c07002506001c280310b404251003c20414000180b41c4419607892040e03480c41035000d545800034500400c0010280000c105140031040301c4013000300792650340314424000700790285a00c0003a40e41950001039640b00d040200901c8030b1101c40704600304840e4000516207901810070b203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 694721816 1250 694720566 694720577
    0x115031e0e330a0507050f0c070806040b0703060902040320180a0606030b030109030203040509100510050a02061308031513050f041203060302100e060c0d020f010f02070f02010e06040312 82
    0x920806141042103a0300c040a800c05005a00741010086c000d0f004810f00520001000300c2d254002c1c0784100300340401000a40300701c6140341054146401c0d000b00c1604d41800090410f000811551550300807102100d5101041202480820383c60554020f481c6036016403020880e03050f100d82e641240c401d1401752000030320010305540703400c1014007240d0003c400c4501070303410860142c01027900442503408680040d1030810795656400c404062060a641145500c0b2440c480b405404c503900001411041001ea001ca03101c40d1100c54a2166100c0c1e14000244182c00800010340c011008803041c3c0280e00000d03211480400112000c0d80644174112682d9080540000400040c8070301c10242d41d00450b001d00381007140c142140c001c00d00341c2180e4400481807103070780b424000558880c44203c80213062510241c83c0fc00d0f480e00802500c8121004e0741010641c2051050301c4010646c1c0b08680095600200c111b4422180e0b50040d5114a4548031640d0300c0b80e42400000b000c81c4040c04000100710403642c48 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 694723066 1250 694721816 694721893
    0x20c150103031d0a03080904020a020f011b0e1207170a060e010506031501080a081e0313030f0908061906030c1d0114061605031905030115031e0e 64
    0x280e2481d880f002e280300e20031100840b040000c10202002c84480c1e16040c0c44c0542e5910513440705901e41800d1840304c1c06150720340a0070f600701182000c0c2000700240250b81e1010079a45100422104840c0c0d4204004d003900821020807681880d510282e134400c007414144c0d481044152960401c03507040902204143c1d46400812006d890300f4803100401e00f4211030010000d5061503a813a50701c07105010014a01c0b00c0c0010501c034004610200c0c00c100d2108006a03a55130714110b00408030300140250201c007c111910600ca1159006110880a861581d030061604d076031800301e80d81c0c4075012829250011581c444022000c68960303201840034145403070381510100e103000229107400d0f0050303011b5210001a003c00303060780c2da504000c4500c1d4000c1d0940404210b0030354104075081d0b21902380b40003056800d4541482209800c44080d44c1200e6030f0404418a07465100000d030180d4190052980d03511a20508418461849600100c2081f02110844490900780402080042e0301c48000b580350008416a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 694724316 1250 694723066 694723097
    0x905160b071a091506040209040504060c080604021c110c07080d02160b040312140c0d030e06090d050715021303110109150507080d24080f07050103020c15010303 71
    0xc00d80c1400b5496400c2480c1c41c080d6081621450440002a040500c68010800c0381d555034059484001c00107008200300c2c00c00e0b15081c1c0090104401e14404120010001000f03442d01e8030030354406858401e07000c08d030005854152001040b80140c0701450020501042c022802c0400c803042c0a060542d0041402e94013072480649024410a42c44840d245003500034002c4040c02410750302241d9001905c00130100c0707891000d0341e5034404443e078120700c88008919684403541c000b50309000004161000c01469884c2c00b0006c0e2181000c450503407003940000b80b4205200d22840c011306405018600c54001c0143c13000c0c0803416030740705407881078071401d40000c280b0520141c0c030a080c1a10700700742419030703d081c68606080e1501d030040da20350742401b1000ca180700a00c0041c0c0100c40900c05044c004008010803040c0108100188000900e0301c1300d0003880c08180000001551b641d003228410003050050301d04801140a075201918203c03080c05100060790802611300c0c0818080d51080c5c44d904c60010007002c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 694725566 1250 694724316 694724333
    0x5010503070b0301050a0b0f1b0c040c0503060904080702010c050a05010b090708070206010b0a210614060703050d0f1d0d08070518040b010c0506010b1306140a030905160b07 76
    0xc10140402e001000104141c1c0d03203102a40c0d08884100b036203a44c860b0b40c4c00106014a001d40030301d100c8000380051000841110114100400388000c4500300520120603a0443c0c00e80404c440d2a900300304001c010401280f004005001c00520514180f000d500007591003a0420b540c0010450f00f44c0e443c2c1c01655441c1c6003009100f80e00107a82d02e0603200900c1c2280009540c0c0c2010721030080022800600454000d10890484030403444180159462040c8001d030140240079502c5042c0f0b10740c2c1a007a42c40380c140392002c00c441a0a8165660341d0500401e0071400004000802c0340c000210b54030381c5000303402d0501030092600120402c02810414400050142034488014940c40810070100245032101d035020340454841c003020703280001c3c6100030b0f50042c0c0d510117075a00003600601c5044000500741c51080010706500b1400c044d00104641c2d00d010075a240c2200b0036414400315020721803421420310a40c000b039a0320780075100700c56481140002004004142d9080800c0120b40015210148082301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 694726816 1250 694725566 694725569
    0x19030804150518010809032b0f11180f10020c040f0e0a232d07030201090e13140d080105030a170f0409061d0f060a090209011704060501050307 63
    0x241012072803e24001d6800e11100c0742d4045650610841c1070114000301030030410f0364009401200d07003103507194900c80545030314070464000035032041c03d00c01d603a007440c000b0740140604a040c1d44ca06c2400d0410080070714484010034200b113070700017860b072050340e411313696203103045421078100c2c1c0160040c1c2d020001803100343e580c00c1d40b030010540e0500041c001407030300025086c880e194000061000008240c800203020303441c000302542c0507200f4941401008482502901011443c01c6400b17240004d421030307420703214900c07480080d003c0340d60240100604403202c13100d030798024860109030144502c5561005250081d030803ca00182c6e020020b422507084d0484c0e2001e01600c030445c000d21600707c2d2952040c5e0400102410300380501004100204400c0d040001c1e00c2c094291403105024490f1070b00c0811001d4900040b503441c3c1a1050b101065a01030781d41d420501921f000f070035299441d03090150400195100c6441d042c10040308103d480b55400b202107065020328071500380802d003945440101460318586 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 694728066 1250 694726816 694726859
    0x91002070b0618010f0501120e0f0114070206040510050406020909070201022d03060f0315011e0b031b0912030d0b100518010e040e06040f050f030a0c06090219030804 73
    0x400f80103000d9000c5005005049030340919040042103901d01001001d444609004800d600c60750301c030349050000641000c104801c42e103181014994414800b2a40c07118140c0d000340454010034001c1c40c00c2c1d0601d0304102d034002c0c0508001f43c81d041050000c20442d18044903044010303540840c20514a0041c1440600b8112180107034071140d031200d00610500d4070001c0c0200303106280d8903d0f0b8030a40e0b2420b000d1903014a20b0054490003540e0348510140365500b1121501580d45662480418185d10040c144c1c0c1c00b912483c0d00c0600d407a00d096100d107007142e001e0800310f540501010607140c0240720800040c41010740400020541c105a01c0078000e46d40341150014084c030400780855a5070441200c4207800303106092821078464240b04010400070b003140e1403002054040e4070300304070500c070140c10310070100b42c411003c0f030b1051040c000c1c2c150340b01c3c001c001391540000d40403001c0c0c8010030110342006000a000400036180302c0e0290000b101540030f19402255412004201040507003c04944984000070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 694729316 1250 694728066 694728109
    0x43e040b031512151314060a1e020301080a031101111b0f0102040503062404060608070e100c0f141c02120a051b01140c070209010f0e0f091002070b06 66
    0xa09880d0000480002400c2c00d06409244805e0b20511040c22410020aaa004151605070a0000b107000c0540600b0080f101c0014110000ea0716040b05442102d0407987c000c806804040324075642142d401c0d0900350b6015841d900c0c0c000241e843c0d070340d00d0000c091200c84e03000800415020b1035070b82803d01d918403082c2d6000d0391060200300213540b000315449034450709e114920b150415250b1003090a2003d00c0b001640c2040c90140c010070140c0d00300521501685241c2c841400900d50340040180400d40d5000c10b2002403170b540406c0f80094002c0e101503012900c9105403040d030606031500140707821408460808000c00c48013503079842c5501445155994103000c2041031a14228000141681c850001e4010300301c01d80d40c00c480d40b000001e41c441006922000e20100190074200e03105c80d61a0040380c010b078401c100302400054242d02c561480400c4a404e080700c0078141e941d03031070003c19484005112040c80d0043c02010b5211030490302c018022584540d20056590402105100f5000d461340a000c120f0721 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 694730566 1250 694729316 694729333
    0x19080c030625121b083403270218070503010b09010201090c06091409040f110307081c1b02150306190306050105043e040b031512 57
    0x114429075402011100300e400316004058440100c0303212075500c0030b500e10383d032030301c4100305140d40c448030300300100c180c0d41c0e584840d251290419100391080101d400a103c0403860401c01d2a600010189500e01e4000d06001554021202c03415011100b40103121a0754a4034a202008501d880301451074502d07a51886440945402900038100744418001c15590100100301000d0981c0300350000b155042c1c1c40000d03055047da070f480001c2c1110806020761907000b42c254070b20018600b04205007510032904200c0048560b4000c0c0c0307408e030802160f60a942d4050080501c007254855040041000815214000ca030407000c0c070160090054170680c0800c0f038503101c0484a03c02607980c0500c0c0a0280d801c4032500d40e900c0c3c0b9000c00040000d040502c0c080c249000d080030000602445034007680c100c5005580600440300703a0000f030ba50000c1c500100d007000c000280c0c00302100e40c3c8441891600704003030311002c3e031429885004000707440e0011500081026084000420542429440e80fa40031040c00c1c000d0840c403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 694731816 1250 694730566 694730581
    0x6030f18061b03041415010501030f0b1c0501061706090118030807110705130b1206010f090e03070f06200313081602060406090914040209150d0219080c0306 69
    0x920000c1042c00058000c004102402a500d4480081d80042400c80300d103840100c03402020151309100d000d020a24280411444086070301035940454402040b007a800106444030b02801ca005034420344103990703076200125040300c07a802c2c044502051f420050030340f890086196402d66141c601c3c0507540203200810040040e170000100d94020304c03642801001e1040c4041024a082c1c107981c071161384000c0d100003c0691072010350250050071405d03034200c1003891195094a40c3c54900780b05001c0040d00c419030400000c130055000754501c01c514020340303292003001e440d43c005a588001c021381d0000d03075554804c1c904016040141314915000820b141c00c528103140b100000081c00140500040c4000038200c3d0355094041821200350381c000c1265031919100c1000810005550080405403407800216101d000e00c4180c0e41c51107183c0c001c0009034955102d4115021140b422901650441c06e5112080010307501c160520a05410b4442c81c10300440c0f4008850303140c01a81505a03000781c00c01c0c070502250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 694733066 1250 694731816 694731841
    0x6110f041707031101030203090a1b03020a150503240301111c060501080c1303020a09060e181207060b0a150e0603040c030b07050705010c2c0f13020906030f1806 71
    0x130709034242001600d0b0384c3d64040c0a400c200c6031100080404000720906c0c14001c031202c4005003a030b0b0081d10500549520382100412a0400ca20000c01081091001420b20303103500700c800001d8041101d60505640c240d40100342501c0c4121103003114840d000c40c400c0e9911700f80094501010010b000c09004152070800060803014000d000001320560018072000c0d80140f84403078a0082d64041c1c048a0101ea40d0130244000701900d0140d08000cc40c00c101281800ca80d40c3c0307a103040780e4412009454034603604224003141d5070198104984952315000c160034155114240c180040c2b0404007052240c08103000d00401c0e441a115402d0310a81c010b0051001245141e041141503d9101c0c200d48405c3d1202807050700d96000c1c00d003000300990301b0000b0030407025038000e40d906849c00008540c8680d0700321484030844c0d095039840c0c00c1a04450403a250b1b21240c03908048800412410203001442d1072220004242113901c202c412a402070032801c180039600584002c0c1c04010b00210000c1c007928185605032450 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 694734316 1250 694733066 694733093
    0x10519080c0c1905010c1103090603040606050d0606050406060c030e150f0f040f05100c031805030703031713050616120501030f0201020606090705040501030906110f04170703 77
    0x40100600004004081c404220740c80540a0012a80589502c020b1168061034180c8210340c65401c09500d01d45a81c01180901c9040c06003001550a15101009004050308014410b036410f58481c00d00044a845401e65580d00c0c902070040401c11500304400c4c00180c40d0140d000000304071807007003090042903212400034408442200d2044003000703824101101030050804800c0101e0000603602c044541c4d210043c011a0702044010350310f15501d50400261251045503c408181110750034000240301714144880401000c40115034283c41d02c003c2494100a0b030811008250300c00aa08a000e5034a0801307540140031b420894101e498650b2400e4540501502510505003c90130022036680900010401014080781c1044650b030350381009a07002001030001ea025020340300120b101402d12103c000d20031641130720390515061400004600400e0700c0801503c02a03510b221030490a52100010004010b160304850344950801c0712214050151200000d10b50b03208003070400c001000140d8151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 694735566 1250 694734316 694734367
    0x3140132030309010507060221090d021c080a060e10090f1a060c010605040f0906051803090d0203070503030a05030702060907030c0302060304081c020c0d0305011d070215091b0105 79
    0x1910fa0b0300c1803911102074049c1405444889080040c05015130b10890704041c420f480f00b00890f0a90f5802800c103980318140c240017941c1902d09800013900d08d074000c0b4210742e0083c0300d01c08000f031420b80d44c01d4130f1079004c24280c503021844601c102041225810074011401a5002140704210807200008628280320301c1e08001c0c0e000d12404038001d8407008003035202c8401814003400030300081c0d0200900038014601054112000781ca050302084015080c82480580000c40344021403504a01c90b0401c02c03031144c040300480c2e040c0b044800100d083c2e02d0500141c8000a4243c0351541c076410300050290510600a01d030601a5010181c02c0000c9641c040d0b0b82800c981d010303107405030703242c0b80c50030034400d50301c507040401107040c41d040342c10920000c1c1c0c1c3d40108081c005582c1a00d0500000c00802c606540c420300ca40f24803c422541c101844010762031500d03400004500484001a0781121910800e1504698981098111000c80e0494032103209c07003e44600703401d00e041454200d06130340c4200302d11007268449 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 694736816 1250 694735566 694735577
    0x91e1b080910110d0612020a0b03060402043516140d060c0c0203010f0b130c030b0307080123070206130606080f01021309180f030314013203030901 65
    0x1e03a2000c000e200e1010048040c0405000760360803032500701e405500000020200303c0c90f0040000c0da0b101080314400d085607000344001d01300f5107001109003040c2c101a001d107901c19420000010311520000004d50240d041d542d1440030704d0f002c281c04d042d40076056041445aa00841d8041c13441c00e8961001605075144800303040446498800840d01620507140010255445c047c00541c042d80c1010b0744c0400a07200301c00a0080320941e140310b805a440541a09400485850b042c1130003448541014002d62000d1800180180200700040c3c0b905c0581d078450040c41c5d540c1c0c1d100c50307188012401006d0781038a6081d00c0c02031500f007100c00295543c10042200c2103c07140350000d2000c1080c1908004018001d4400701c90032078000440c00c9000358418403c0030256103907600b001504801502600d09820002002e090064070f4607120840f081e0000082202059541e0341c01038200004180440d000c0d00141d81703070b409280843c9441c2c040f07103444440d155080e40541c0141000d159000403c5031030092003031801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 694738066 1250 694736816 694736821
    0x60504061805012a021b030c1c05010501240c15060602010c1805092802030c0304030e030610060c02060d0606210905030d0203060d0b01091e1b08 64
    0x100200300180741e09104500040044003800415000030250002e41c0d40c1030210340c840400da01804501c40c4e08a5405a085482440303a50300d04828404822000501a44c5084421800187c0c00d01c0a509800048a014042c28010300000740b15484c050141c0700140e02d01100e15407951103030300034013a41410401100705942800c101c01901401c2c040503813240144152900da00000c1c0c068000107070103400140c2c801c07064a00490410b49480201c460281c0954002d4440001c0311040400f00e6800201ca0401362854890bc1c03004e620045200d800310381e110a849090518000307003442500c80c0d09600c030340e00c510240300341c1046000c3c00608541450401903001000b41c8081005409100d8400d84850310b040e400160300c9801c44070001d00108a030714820440d00185980300304031030b80070201510b1540148010062010031754000c42e00214010714094036181503544004040009070070084015031243c4400b00080391032541ca80716010381e803005201007400d51304020f940c46240014181004000c074003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 694739316 1250 694738066 694738073
    0x30609150504031b0f14070515090a090e0a050708060403140c0c010302030a1805010c0e060309061605070204021903061409040b15090f16050909311b0b0313060504 72
    0xd581a050b612070040903c001b4801c501c0341d1603c0d15481400d020780201032055013810091021515401c8000340b03003010705402d1182510041007234403001c60051140c0c030380c0200810810840390780100066002015586014500103101050b0068070740d070080c03c01d0084500c3d80c44007194843e017840702860700585a42d10613901001600c60008929000380344ca6804030140601034101c9501020b05498441c1c50744d003017806114540c0320031070b104600c58108501081c3c401550404205020940f1f140585c2060718070b0300054103da1045151030a2010304200b20f82110340c03d4001c0c400141411030655004462005c041600c14800601c0209081c1409001601480c90035030981d83d181c50151880c40549400405150b86507800c0e07a12070607600d114001c840020344140708881d4181d50107407a00322141ca40045011215041c0c40c0581401d0f903042c83e00d1076064921002d50001d481c010540001c4420050a00519002d0513070030506101c4070400c10045050241200c000030154803001c001820340c2c41c3d08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 694740566 1250 694739316 694739333
    0xc0418020d0c0f032003060601121e050108031e040602030913201819030221100614090915090319030203160c03020c10030f0204030609150504031b 65
    0x3041540c1284000f4408814042940a10040e084031000f11120642d04d100c10907a0b036440450f40030307000514092011507084455042083c0807080303004e5600100d440d82c0041c2059880c01d82104802c1d03440400c1c11407031034010001c01002e6104103150b603443d041c2007150081d164031550008500603128507110b2003c403561940420a031070881d0525444c56498400c00100039031068400c0f01000400d4442e20600346401d010b504003da000c0101e0729151071a56007400045010a1001c00340d01c41c01c0c1d03400441105c000c0c0494514201d000c400003c1042c1000c2000c1c0403404041d514034040c401c040200070412400040c009421400e628540060382d0388c0c41c0c0381910b548601c46542d50b4440d40740310341d0014181c1540145004122326a104e442c7c01501c2c14045890030485c0102800603070011154517058100908009600c1c05d07141740109116409408a81c08e9a210782d0085a40d603a5071682c41d0b051052003c0c4032050400c0400061001d4242610010720107400503002070350140390704008504101558 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 694741816 1250 694740566 694740569
    0xc0c010c020312090a050301092a050607140c1002010c14120c13090606091a0a141308191209150509040b09100503060a09080f03040c080a0f050c0418020d0c 69
    0xc00070f00c046559480c7c90b11881070002640e00111000c843d0215544040804ac0c01c1540c402401c11400d0516135200e1140104446071048881d0244000442c8641c41b0385071990700302090b40d000401c0408515000425044044514103e0281c00b403206040300100da104540e0004a0000d06036140c919510300314801e03000a0740070410301c3c0d14002d400a40d40340c20003c440d0032140303000e00e0b2500c50b4010300d41c103c10074496950240000b5800718081d031100c841000c0503100d0100e441144912280d01c903144503181c01c10840c540e1301c861111603e000200f00090a50f03032154850342c540f41401d2442c0ca0200381e00e0016800b400c0c0e080c40004030b0702000c181c072a64071000e14108020101a06414001381c9010315280901440d030103406000001554264240204400c3c00c1e4072903400c914040503454034000c80c1e000500122011481c02e800000c40800400004d00c00718042c241301c115842c602c0c944940790003075901c180f901076810101c0820802d940070760021056038069810000c4c41c126403070600c0c0e26000c035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 694743066 1250 694741816 694741819
    0x90705060a0f02010f0207030806151303150b031618020d1d010c0302030106051206040f0905030d05011a04150215011e080102070b04140709020703050c0c010c020312090a05 76
    0x401c410310001d41c01150071442e81c406400030098940c030f00840e103090348070708000540442d5103400412800d04110b10190890101b5120722400c140244441030b0b40d240e4641c1c000e5460036220b00c200400314000b841200314200341100145000f00c00a0211414441203120b00302100b0481c4048445c101005e4045030a00110b24408000030780882400f0fa400c1d020300351454616601c0e0088030a000360180c802c50781a200291a05810701203415038100074003100420781030704641c4500440340135404a01609000300c4c4640051502c4d030103110809001c6810581c0003e8640c072200e40c1c5030340c0c08800745040f030702590014584a40780790b0801398140d20307105040b005418400741e031200000385003003000108000c2a403659010315546545000140c00e0b80a0740c00003a01c0103c2d03c001040c0000c020ad105510070030040400d95014079a0759041d00b003280c00c00d12050700811030000f200441c1d040c044c000107003562003d0a001d80c44800d140c021940c2da40210182d0a0103c074000340d681d10301e54a480c1e0300c8008110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 694744316 1250 694743066 694743079
    0x30813050d1106070305070504091d060112170301030f080d150e06190b0a1803120504050a05040c020c040506041d0a05010621080a0c02090906181212090705 69
    0x4564000a11804800848030b4490082d2004107034854401c2c0101402015581e441e6424030b41890054801050072844d210201701031100401601141400341030f0081c01072002e1044514210708241d0070b0744500c40010283c842003003005000240200180321902c0d904071050b183c5403c08800c4880c000c0c8411141c0280c0d1008074407000030500209482d02e44135500030350b90304451014851140829400c14010b109050009008000c113680c4145915040c075240741c4a82d81105540303460740000c41310309002c81c00005070001810b019a0409030b03d118004c04094404000700d81d40301c4802900d07016000080c6124584840c00310700d15694a40104e20403944400854241c1543d1030b0a443d0b5904405404032031950070290005002c0c0000c1601040d00d05200000141400c015038826400398010200041407100e200759140250b01d030882003910421080d0000c0032142032507400440c500d151809007003920390188406e24000601c0c01d05450080c070140404511a4940c60001800d0034107640069402c401d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 694745566 1250 694744316 694744333
    0xf0f0909050628060e0303070209060d170c01020408013c2c060a1b11280507050301020405130e010e0a080703030b09011214100c0c03090902040f0303081305 69
    0x34083d4104800c5072030f181c4580c500303107400d00b0506450b0300070344601035404841b50340020b9850509603200d5101501c80c4044010400c1a4500c0c00c3d0a500305000880182e980031800f4412150244181004608039005e40010821040402a040c1d900502690a41400b61801900354400d54221803409028110b01d84001110a280d9820030141c4280d154050b2085601141900c1c480344501140b240c0f404038904014a0301c60020744184c2c0030548070b1401071240c3c010300341c55139154407030f80744220b03007400c152980c9070310942026850a09140c00c014840e0344104000c01203603031169a0908030002007103001c0707a29518016003030300418001c84501e0b01406030420940030490303803000400030b05110751010000700300c0c80d41c180200c000d024001c445400018842c402c0c041060390071079881c88405901250031100242e503500c41590140898800440c008031407030810560003d402c203015101e24501181410719013440301c3c000215503c000707030501030840003244000c169110f86505030740d005400c442c03052 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 694746816 1250 694745566 694745629
    0x90b0f1605070920040503070b0714011404120e090604090c0e042919020c1c050a11010902060906220b090418020a03140703050105160f0f09090506 65
    0x1c100441504440c000502d1420404d440110140c03030903290f0180c0240085070410324000c41641c09180103032040c00300d943c841d07050400c0c01d01401c07045058180c0160311500f003518041001f4144290b440c424410b685509401540f01e42c051558403010884010540c4901401c01d0f55940020781c0200104860210804c001d200140c58107000350150f010010141c258032118815030303441d081d0380900035010340c0d00ca0010010030b0354010b42010420b00e0f060301d80c010700851100f420582d03101d181e80082800464800740751038024010482140d6048000d11107204550300041062051008581c40b4580106400f4a85000c0c01c600c0100f00c4411032080c00c1d03054803511209002e800910710b09200ea41002e0039401c0d4a4040c1035001c645a0b4080d1610400d9411036039420354103070195411210b144600940000450024003404c1e0203028049804c408510780204000c01500c540038214041c03020381e42462103d690b00c0741c00c02d4100d80c0c44910000740e075202c0400250751441d068018100c481c841c980c040007070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 694748066 1250 694746816 694746821
    0x5031204020111030304080301060c24140612210909010b1801031a0d05010f020a0e040b011107150519030e070918031d0409050703050d090b0f16050709 67
    0x994000d0301c40d0f04034400c9181c0c00d41d0380c904c412100241741c400144010482075000340d408880321442211410104a01c000c007481b2000300751544140c019490f02400c03103040040302d4545401003810794850283c20281e4480c01d59401500714a02c41c4d00480401074100314288400359141c0d41c40080040142d560350305005540354112004446c15546685000c02040d80a40b0920074940d22209501c1740c1c00b02c000b4100413600143c2e240070364055403209419110120744d44014040c5940310b8a405126003040c600748421940b91500182c103209440d80e02081c04840011903500702ca0308004591441403803030300111003038001d005803118060750308080911119055003050600100c0c040444100b190740340c05181c1a90310721f994070000c0d403100500c00000300303110310340810103e0304224080c0104001c00b0080b03002c840c0c8000303003655580c11018061040147c1886100d00055103854901e2589050001c507000600c00c800540c102d103540001d009140c0100b0245100c1e0181c0c0020694040036030321031170b80c0003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 694749316 1250 694748066 694748071
    0x1d0a0f0905071d010c0c090c05040306060905060904080d2007030f0e0a1a0412050607020f01090b01060309021309231609092a0e150108071407050312 66
    0x49a03080c000040c2c0300c2441660b0350083c2c41e20045100d02012500c070015030305442151020f0342da0703490090000c1340c500c80718050540054000c0e03490940c0c5504e1400d081c41181e0042d0480a13140342003d040c0012541e0300000c09400903041489255208001e0a103800104038000c1c02c2015079821071034010780039014078042d1615a0194844a58400740301504581c41c01440141607446480940244060071444141a4030080b440801e02d1030310b80c96509080400440c00340c00c454a50100c07003000b50b005e5050103042003410001000b8024043c455a443c5c100c0072050041104150351856480b05558410074442c5200803080410001e40328942030884959a2682c0204074400003000c00344400300c000141d01340b094441d00e04030062142841c807084044c01e0480e070207480c401e5056141c12913103032003011402100742d281e503070005100c0d00d0440e1320141a007008040400c0051650100c000c9a6001004d5075804141454400011042140008054021914090801d00c0007140352018811017003030460 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 694750566 1250 694749316 694749329
    0x6070201020d0614030a03030c09081002040f06090b0702060306040906140403140f1206040b030708010c0306140906092e14040501080d0813081603090506130302011d0a0f 75
    0x10016891350503040310040100803c54040c1e00020002c408203100c1d501008004006152144001e5543d0810b1072070003600203621070000d41e0010b0100b020314041490301d0000d0040f81014000ca0385003004010080c002e005019000d9400000014000c1e5035a920070318000358094000c0043c1400005040c0f5284812034080300407580c0070040810781202c90040d1840c80f106030900030314068040406c08443d41025000c1500315890b51002d2905642c00e100100c0900a44000015003801e0303030900605a4800b43d02c844026242d944081c88640c542030340c2d1a91002c8140c0d490200c945070000c0c190601d100b81c1c0712003081074040c1000700c0314610320079900c01d040340c20703011070000d08080050400048403000e01c9017a425500003420346150a0041c03001c66030106030b5401c446145107454403a09100d0340140c4074540100c03800403256042582009404014280c1510030608200c50741e604c19110602c5408064140481a12614520103140c00c0106541c0e0010303000d00065545d031020703145800440c3c068030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 694751816 1250 694750566 694750571
    0x906180f021e030d03090f020a08060f0a05041205130b0c0a020307080d02150c09030a030822020f040f0b180103050616020606010e0d0501060605041d06100e06040806070201020d 78
    0x1801290782542e110600c0d40020080c20700c2c80000308013a002801c05407422103445034400002000f684d16810345100400042d400303490b85207010b604040c20a0b60081170581168500014000400c844500c00c00c030110716410110b9981c2c11000b0b079045040800e41c028205000c0011f010404802c000c981c03001694030980440e903d113501e0784050394540e0110a49a00140e100c030207240000d44054400a07001001e1002003440e0100c42c00c0480d06041c844030054002c95881c0d0140944480d814031104201100c4040b00010042c85074002007084034080c20091042e0b844000c1f80c20803074203075441103c4400f0700506500c50b1a02c0403428500b40741007448180c8180c040c2400062044986d118180403035007042d4080c02c03460750f40000660b081101c00b8555500085c102030018001071091188001414407905e40649641c9080a541e4031981413503508803100020409103c1903031210507a8403401c0ca183c1c141920600200d401240c0c0c28001d90344540ca03036103d0001446034041e01075008206010b0000000e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 694753066 1250 694751816 694751839
    0x1b01060308090a0b040b091005070503210106020309031b040221040c0f15050307030b030f010626070918020a0f090605040903020a1713030309090507020f030d0906180f02 75
    0x207401c00707030041c0d00c505400100c0c2041107d4680c03620300c1101c2044086030030715074205012615a9895074205588007200031f0354440001e80050b0286406600400451000b546408120f101003929140c1807130b00905a943d84c0d4903200c406a80da07070155120203000c11950b84051400c14806d00d52210255016141c49030580408940300441c00c910304155a88450b900300d001c82104c204480300c0d031009040b581016511030907c03603a41c0d028054511040180301c00403511608050100c99004e855014800c1d254503000d02c440300c82c0e035011680508640010000060010064800d0302d4001c3c100040254031940111021480e0891210800f01380ca198400c00c0100380c0e100d609204c00c03500500c04c040c0150303000301c1070080011018201d00050041c5002c40c9410800e4000b40b12007984800e81048002c0380c512034007030100c1070307851044a51000e66440101407610209484039100e10803605004001078480c5680c5040c00020b401c81121811041440c20b030a05550421400c1101500303400ca124103202c405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 694754316 1250 694753066 694753079
    0x80a0812011707030308092107120329030f011d1902011e030b040501090c12051e0408040f090b03010b0a050102070512100e030c0609011e021b01060308090a 69
    0x110b644984040e040200081400c544094544d90f038001d041c2c1c50035100b103085902d1501c80d201c0000c035070451075240054171140d042c41d1008802240c10030900825250600c1e03090000a00c141d0911301c4d80a551144271211903070f501107410184454040121742d800d1130300c00c40800c0a0210300c1d403080c403250340590f048a00d20b0f1009000e09090020081e001038541000c0e07208490148035020000011800d00040340e4403541d000c107050303130807da02070100140d840420b071480710707005001e200518622007010450351034032088003050318002040c0c010390013019100040400100c1f0f41118040c01c0343e085000c0966594459082c050f00005109070701075420103284840e0340c02d00401c0d5106441d4160050400d0034145402d0007a0700000c0d4201d40b0f0071340320ba100100702d11750191060303100c0c00742c0c0ca401035540c6100d00c0b4016843d00344050030540d010382c03401e2009c2503915030f00058040240602000565145a14408082c0c0d0704c100303074030048195282c130b41f0020821480c1c5008104501003a42c1034102160b41d081c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 694755566 1250 694754316 694754339
    0xf031006020a0807060218130b280605070203030d0203090a17070c0902090402090618090c0304051009030c020913030f020c0a030f080708070f0c1428080a081201 71
    0xc014003c9209202c14800135080c1c2e0041d140301e42205100d000b03020340c80400900c2e1081440340240c00c4c10703038500b07610752142003801145000798106030340b18540c4181420800d02d041030302d01c40c1340704108000c10688110b5405000f12148420039401c1551613007801492a07494603d800c10448221aa00407401e034003069050a0703030320054006402130030403860204e003034000c0c1d1b00840c1e00540c85582001121440e41d50140a8070040d4400f80d12100e400b01c011050054102c1d02400d1458030b00010300070040000c00c0002c1d944a08a5190b0000c20111820b00d4180c03916500814000c3d48444000100507250000c0701c1c991880d14080d80c0d030b250000007500c00698071103c90400c0729402800c038903c240007141c0c10486107008030340300d001d0f4545045060703201c5010030380101d0401c03908128402c02001c1880825501d10004e008516a40f41c25007018100264459020418000304032101040d440c210790342d070000c054000d0550600380c03190206c40340b500c0c995075840704065010ba01d8825001040301000310 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 694756816 1250 694755566 694755583
    0x7030b360c0103090201120911131401060c0611160b0f06180c040e16030c0810090b031615091d040f11030304090605040c02060606030a0209010903080f03100602 71
    0x300080c0c001c94004400440c06003c80b050700340e05110b1103a0542e00541d0061050104a81c0944101d078590040002049040302070908540d46442c200054420362743c80241e602c40c111400d5080c40c0300103c00c02c1ca001c0b001380254510110b1885000320b13500641c0c4802c2c0c4201540b5030b00c1803d06003101d9445c280003c40e11107098884075004542820100d14210b101b42d141a0040c004414403828a90b44a05c0b481c1c03001004c403036080203000c41e184200101d40e00342c0120361030203c0c20709108141d442d01c0489111100510301c0b940903159100c200901041e14240308060400c03140101d0f803550241c4418410150301c6001360070b080055085c03040040c030b070300390b00c0601f064240340c201a804040c0c88980701c1d0b40d9040c81e800025288003054403080c40d22990200014001405000e102080d00ea01d44000c00086407280440f840c19900600100711040c1e0700c10007200d0b0300c2512441e005031221440c0c80122401a01074000074901e450008210380b4940350394001c1c5100f40501c01442c4052030b12140100d0321707010304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 694758066 1250 694756816 694756921
    0x4090b040e031c0207050307050705090709030b06041a1e0a090e1902120d1701090213170118080306040b0117061c0b040f03180b120907030b 62
    0x1849049001d141c00c81c80800f00403400400581019659281c107420365012000c03c507400c0d4411001007100d8244103030400d40c002410b0401c0100c451035a19009000c41c0001c204510440c0e0314110f54144a2091072071740c29468014281c2001e01c014640000c542030585440144100c1d424040001e00350480d006030710b0104800d40181c04c60f20748a440c005c405c0c2c54001c008070390002c5040404080490300700052440030030300e80d4030002c0c1540c40200f80c500000c010381154030060b004003c0149808090880e05048419600750310300011981055240108542c0e140c40812a51285917441449032203809540519001c481c1080305200407001502c004007201001003101d8240c01c0010764500c0d00c04407075401c01525000c00d07402500295a807040c0d2540480381110120150b0340c03000d091581c0102145d1901d64800307010a40b8a00301011a2074a0054403010015131940c50700040d400d16050014000541d0711056001c0b032814100404800d0a0400e01340703120314040400162203d620314040090002c02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 694759316 1250 694758066 694758073
    0x210207030507150222090b010503060f0108100f0906031703010810020c0109120f08090c0f04020d060f0f1505030c070605100305120c0c0a030b071206120804090b040e 73
    0x116550b803001c1d078185100c4040455900340450016464104404002c1c05e0b00300e03800201c880d0500006004456000d0105410000c0034070401c00300b0f0f00e80d48000052000c090030650440c1e55056034408600307409402601c1c1000d0f5198000840400c1900002c0c143d82c0300300c035100e200c0c900908507000640400d114001496101040304448008245e00400e0200301c890008070303401c8000d80b281114850304005040001d21700c0e454248000f0380c060401900142d600d009803034450a8540010070401e8118411840740b60b0004003080d03c424182e00100040c0318032008005403030313610050300d024424280305c2c01203504a07a1030b40c02c21f110700c6034044074401d074444688d181c10032a03180c803a0f4008240060402c01800c03151300c000320105504000c500408058503411550300c44101300000d06090310300c03d00c14055482c10000b400050b0035420301603400306a500d000758400c5810140e1802604059100c03800022882d02e041040c001600010310a5800300138040c45115800300070300007207074984050b04d000741c0c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 694760566 1250 694759316 694759327
    0xa150b0d020d1512111f080c0f070b060906030d02030a030e01020912070303141215040b09010e1009050405060711120a0206100b07020307180f02031306050106020d120c0507080304032102070305 85
    0x1030240211f103170132218040946080c20b070003500e40d140c2da50200105079418158982041380302c1c030740b07450540d90194003030b030107043d1b031405240e0301955074010305400034141500e03481c3c01d21100034254155400d1302e400034a03031404442d030407002c3c0e41c8500c0355000950010301400f0280803071201860071511682800c014811096488240758042c03220f1100d40c19510070703140c002020702583c0e08400103019054131203800c404d074108244038240340300450340301292407404c1c8002c01001c02c2c0082286139001703815060511a424600c01400c0c02c050f20500610030060f000b05040d0440c550000d201d6201c1e1041503e80a920b0b40c503150650460301031000d00950540c40140b0600001c411251402c0000755001008980300205811010070380c0c01c00c81d440b8a020188c002038a052001d82e0190314010800c900140c030041c401400010200e0b5035108031410350b1a12103801d015698426012101d441e904240c0e0f07140c8905051400910202c1c40b1100303125502000002c0f940380c83c2c094400c6800300342d8981c0320300f490b01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 694761816 1250 694760566 694760629
    0x30207170a17161506260604030513090518190b042d08070218040f030c060b03070611060f0606040b0f0706050a0e0105090f0706350a150b0d020d151211 67
    0x15800300c9a510bd100da4040c0c000504000c00b030086502640d01000f0299a000761001007a190000c0ca91600141200030781900c0c010030001d940081c1c205801016540e0a00c00e00c0e80d008165502820003086c40d113800c2d501c103405000b89040980706451003103c012500b0300b0b500245420401090314040c054179000c4480c803001a0040000400c1980b258034003150200c0d001d070003e0304201a42d4441c1004c03c0c001700300100548018404a903200385002c40b412a5800d003180800c5c1c060007940503600d844807000903040d1800b00d90600343d40300386078000710034002d920b40305400102500d06000300c1515503090201140b42000c02040319181e04502c10020b14512780340810031078281031f000601038071403020345c0c02c26134000c42e24034001c25015109021601190400f441c490301115140c032001c0440e10511103041c401c00e0100d204172004640311a034003580b24105184010001c2125551404030503501c0880055214460303c4003020090180b510320801c01e10960134002da42881c1c20320301910041030300500e86070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 694763066 1250 694761816 694761827
    0x1915060614090a0f14040f050c090d0302120406090e16050a200616020f0d0905040903021509070501030f0b0609010305071209030207170a1716150626060403 69
    0x40030001000d03400260b90f00c644011100084d81c1090f07196001002000b45c1c2d6003000d02880000c1000c0d10b43c10881480e2a40f4041058003400e0700561103094984200800c2c1482040a084203080c0c9020a0340d0301d40d9107940140c4820454861110f0301034030640000c2100c00092050300c0c4200c1261101031070720070b1140b0112084281f1044001618040036507480c550101003200c544141104424031071030204815000e8a0411417650112031940405084484103511550403421618207460100e00d09c4294502a410016200f00c020b032401c4c0554100b000c40540000c8080803550b083e201006698900c03081c020541303400b40402ca4010404000100d5907510941c400c4e54802e0300c03440d150340d944e444c0e4850380c416078009020540c016070007a0001d026940c00d00b450320340350450060041a4002c040e550740c41010102ca80350f0543c0f1040032450380c10a00111410788611548250544c940c2e804607039908000b0714043c01000000c0144400b400e1a4407003190f0013004014a1100406541d03645a408540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 694764316 1250 694763066 694763077
    0x30a02090f0c040b03010306021315020c130b0306070c020907030b1c05030405030a0b06091e16050c07080102031e01030b0a0902010e040504030e01020d090b1e0702031915060614 78
    0xb80107204000004525030f009020b035019502c902005a0b0325200c0d011080d0110100e030704010125885005010034188d00010900e843c01025204100350113a842c00920080a8035400d464140c01007104101c034a69000083c0162588210b900102c00d4440c103400f10700f101c40c40210f8681285d4030841e000c0c2590700c07500c0b200c0f40c00d40c030031000c4924158803070000c81e05190112100f1101c0039070b0340f018407186240c0810141d80c005030843c00c050303124583c0c00094541985c0680348000c1c030510900c0d2200340b40c0c820811103510050000447c0e411315542d0369003034003e602c103c0740190342c3c2c850804240280d02d10283d5441c100d030740140700400c3d541c8070005410700030000008124140507160402c11081e480301d0099034071480c0240c40e02d1640348000710000e410454044000e40400410b00c606111541102c801d9807002c9020300e8164403c0361805a000125100b6035034069414820741c2e20364903d041801e00d035500000c0c0b01d070400e50410310060025509650075401000d01159181440d040344100407000307080b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 694765566 1250 694764316 694764331
    0x100906021216050d120f0902010c0f02030c22050604180206031e040c2103020601090924020405030d090605031513050a0506120a0c050d05100e0303070905030a02090f 73
    0x110504a1a501c162410404d126400049210100481e503e10300c81d10035a400400d00c1e600502031210b240d07000812030070400c0d1008001400c080d9001080d901c1c104803845940c40080c01ca00049141d5034001c1d41d1466800885401d1141002d00003070300d5081500800d004980408000141c0084541c01c01c10aa0401001d882e580c443c0401c000828800d4039034145d00540c000c0381c0c0d014501e81003103007070018103821020f6404100200c006100010354009040c504488020314005400c0081d46441c2d013139a090600400960300b490005403102c04580d40c010412181d00f10201c800c0c0804040095441684c0362003100b01091052000840008001c0c101d104034510040501c0c807010041c1031104201c510a403400000c80b540c90080280e6801c00d0003284d0f0003010303200020f0400d11020f507902440e218150003054080c14200100c00c0c200201000404044240140240052600e0880f0703030750f9942046458400098501c00d0001d0982808550105201c1d006032104545590f41e4101e031030032540240c01d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 694766816 1250 694765566 694765597
    0x14150312070b18011b031103071409010c0f05010510061404090507090803130302040606050f3001080d090e1e0601020c060d023f0a02070215091009060212 68
    0x4400315800e1190400e03084460f26110185d028580340181222000841200c3d400d8040080c4003070340f5000000d80008040000400c0e82d264000e5004941400603000024000504945c2d400c04004040d00018403400f071050030003010b243d680c041200c840102c0196400b64000411050200c800580c01c0030340e000080e0b00700042d10f15a00c1d15030b107186a00c900c3d03144401c0d031841d50040c000c620303090140d1001040b00d0324103107042c82085082c440384c2e885100300c01c0526601f241c44907503c11010481d00400f10615190342c0d422036070f403100794030f44480b10601c1e00e20005401103030201d04018080140d6008030003400390306d403421354101c01940440201400603415032207101a4095540d41e00002400c00d05c003a00000341e15401b00704000b82100d91640480014a51081c1030001080d40d2030365000d03045003403009208466154070101100910540f007000c0e4020350b02f40642e072510808400100195401590004260941c28000b02e03181e0445025480c0180c01c281e5a42c0091401c0c5006010200d1071091031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 694768066 1250 694766816 694766851
    0x9070806010212040915080303070215131707120203031009090c0302060a09090b120303130303061a0307080a0e0705130f0609060f060e030307021201090614150312070b 74
    0x1094913001903204004003904c4440c0f10580c40707580c0107003100800d0034074000d50031818503840294a590003243e0815001e02142d000420000002c410042c4441d080498800c040850001c2501103a00801007035403400c0007900c07501c605610000449208480c4e2802c449820303402d01405201804644a043c1d41d09180d01c1000b00143c0d03142030041c540e01c00c941e1100c00360603140261130000d850184040030310805a01d6412042200003004907507102c1034184016a860380d1341d10307043e4000e01c0e070303908584a64001892003080d003040e0540118020f82150b03e0708050b0340c1e1481400d03015504000360260f0980c006c92000c1009040c40c5441841004202c11702084582c21400c0b6081250000e03170181d450203445840401c06007160f00e80d154003900b130a144c07000005401c00c0100356a072056003002070180f50350001d0034554036429403158500d40c0c2c1c0481c0602000007c401400c80c008015210426004040390f0b040030141780c0001c81110103100d806c900d506105194840280c3c444004001040c00055001c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 694769316 1250 694768066 694768093
    0x80a0903030e100203011502430e010303080a1b030b0d0204090c030b0105010c050601060f0c060e0109020109140d29010308190503010503030d0b030316110301110306090708060102 79
    0x195115000c00145c480d89000040d100c4030301490240425500191440e540110440410000c1915507030342d200941020351700d00030180c00051042c201021080c146c003064040c180b4510f181200e000f0b036035100c016143d0760300b1141103070544031400803d0300900c8400d142050007030f0000419002d0042c2540050030842d0082000d498500f04100c40c42d0360f00350010320400c07242c88000340c0035000a00c1c0603105120303940c0d1025658201030207040d05218811810035504c1e480b40c114100c66a501c164140314140001013400d000e00391461040340401d40b0740e0004a411000c14804107801c641c01081c1c281c00a03440c2d1a407241c108141303042441070040305441d14840c00c00320403465000318820070203965a1a03c0309050711507802018001b1003006002c1004010035070b400000e60b0b807031501034500051584400b03030000340f8510a101100e1151104400d82d007081c4002d0b60504070b0310320000d400a00600d20b072442c2da0141c030710089610310307407001c2c120002c103070014825040d1a9110506004a406c07c201944 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 694770566 1250 694769316 694769323
    0x50106050d05070503071a0a0318120210062c040606030c12030f1d092503150503030a0903030c0c0509010e0411030d082d0403020a05120406080a0903030e 68
    0x92042d40c01e640b06120400460404120f42c8000f801c51080c0b02402045140c441e80891203624003850405440389198030b400340204c9202400c0e00c0d070119019105520400020351a061111b40c0e410300d0364176000c000a04403a10f07512052407100e0f19501c00b894404100e0005082c04070191040d114103545100110000700f001c2030144c0904204038800e07801d90707407500c0c004019280385c0c0c0040d01000440010300700d40801481c4810602c0c0c03021134540c4203030794800c21074995140401100c4900704682021700c411694251380036501540030341c10303040340f41c6407540305140e560301c9028120703800292909d0041010921404030354456034841d00040e95419034420015800720070a822940c1d04908100030301c020812403003c28800c070032040d0007800c40d050a43c000a030140c44d000b015002008a04507940150100407042c0740300c048180d045024040c280743c01e0082d59012482021101845008400e542960308401030b542280c0b03040c1e0350501d9035603620042c1000b0703040b843d6086062644492940c2c18407081030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 694771816 1250 694770566 694770589
    0x8060c0a020129130204080a02010f261f0803030609071b06020a120e070e07110a1a1803071b0e04060b100f0c0602090d120207030501050c090d0303050405010605 71
    0x180c0d07070f64864603841004c00c00100503200500450510410041090f43d802141c500c0d407182e02400c0c5041c00e805161815a03400c00c6120310041030400f041003100b01350800328401c6004105044088210000c8880103000142d1103003d0a0010307402800003580310310341102c0c1180d004200f80303840d64800b00703a80300603801c50024070b40c22201c090300450309405640d4010582c514290035060244012150101c503140c0711185405a00200408240021101c1c0c0c010320103407414420010845002030740340c0c1458032440c2c134427941d420309005465011039001250750852180001c008000755140c14400e598410101205010402542d001c0c0200001c1d41907401d20854845d50090340b001c42c49181c00820040070100c590041014001030861750003901d94030100b045606640b08000582d80c2440e007000419000720f5040c01400d1a040c80600b203a0030342d0100306001202d1141e0001c2c00315841c1c6401c0c0d2002800352821a680210582c904d010109100381c10a80d0818001c50000036142e403160b001c01c8103010706 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 694773066 1250 694771816 694771871
    0x6010521070c0c031406100b0304030c08041805150d0507060c020d0c062102040f14040902090c1b0109030f2d0f02060f0705030613180b01150908060c0a0201 69
    0x10718001703400121003408007560001c01d1107000c42009081c03410034029400054000740411601d020700c1c904110105045030080d0a521070110409001e13401480040c0008540d494038041e804101035099040080c00b00f91920b0780240a0700256040001c12200c3e40401c44090380c1c841003817102c002c0400c0c80001803202506d0030380c0e14902d0b000414034000901040c1102034030400c0748100800c0001c0401025510140c410a01002e440d90440304006400f4211003180a5800204c010502c80f80d940cc5100800341c0c0316414684400440315004080c1c2203c800d10400350104040c400c107a14003030b10030310826240c0f924a00003d2012009003400340c4000c81d0300c0030001c001c5011f500074032070f403150100862940140c030000d42100380e2400701401440d40c00082c20f850b01030305c000c1e404080a803440c0e410800e1100c00c2c003956800c000109090590804c0000c0c8128400c83d841403c2030f4280e98801d00d055025200600c006014070389981c003050115501104808085550f282030341280403c1c0f803959070303044416 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 694774316 1250 694773066 694773083
    0x60d1b090303020c01080f150307081c080a11040b1b120903070e2a0705060703091e0f1e0203030d0930030f020d0203160806010521070c0c03 62
    0x4520b8060301d400d000074009030600141104000360304034882c00d1a80c1c00b0000d42a4401d0925095000c0707481d0520503080b18034a40a01c66243d4030802848a003021003040541d1091310036101c030f49280301100e0301d05070000b10315001044140180c2241d40c0c0100408105801070711035a0078000d82036424002d02d440d281001d45000104900b1a280422850f005005840c1d444809420701400c0082c0c206c48607070b90440140300d01d0350704680800030b1000741e0f005650801c0c29904580303024080117005007810304e02114440c451185081c0c00c1501201c3c0e8029003580003c034110000c039242c460580401001c071440101180131142c07000107807402e001403d0304010341203004c10769038280e151883e240301d1a00e20500c10020480104420000740c2001e80d0240d107500c4c14005a0903003489a4180a481001800740c003e6000105100c55401404425600c044072641c40e80c402e922007a00440c0c0521440e90600300b850920305015810a850715070b01500300c4c07000d0400d818081c1182d507904c20182070b16070007035400301c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 694775566 1250 694774316 694774319
    0x711030a081f21030207150522030b150a08100504050f0c130c030b0901140f0f0f1c0b0906010e060a05210a15020a120b030606060d1b09 60
    0x81240d007036410400103071111010100d003032035081401d2208407000c0c0210982080140c1e000c1c10700034040d000140c4044032030b8542d61075407e4009002a40305050045104c2c032200300c00100c40361404000c800307507580280551030986902d80c0c0c0303920300340c800d0080650100407014002014802009000140d40c1c0c0d80303c01140915050030007508168440c0f0180c009034220303a10748100c2d55203004540c500c10318070303070700024410f02801ca00301c1c010318803885243d404c21510310002c508113205501c3ca503681c100844006d1350303016442042c002c01c03111120001d50805071040c3d20043c145407448450101007030803125800940c44548070000e00d032105540300340d1642c0001c2d006018102e00303050700c240e01540c00d85602d22424a03010200b004c8104c1a0544008d980c440461640512003c0c0050440540c0001041d01d140b2a120003034002584083d07001c8002c5052015841180411030042001049006015007015030750481880503036800b848102c41c8042c2c0d04c0d200350780110000c3c1c5480003640708541d119020503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 694776816 1250 694775566 694775581
    0x11104080705091005010f1b05190b090721050c100519020604172a010e0c0103090203030d0506190801050f0105030c0922080f0c0705010c0c0303080711030a08 70
    0x40d0b01c0501a0320303001d01809070a105e1646c10241d8641c60b2120f524003d400b100681441021074200410020709038040c001e15400e003907511652441003640501340d828025100d852549680e04240e02c100e205051050341c4518801040c1c5500141c4640a981503812844602c00050900c401d04480c081c0480d6000c03540d028980c0710480c05000c03244060006180f03a081a48951400d120721005282d220f00000442820520f02c400580d100442c422100c0e403507460415003502e000e0b1a04040c0940c1c00d101c0d0030100c0d2030075842801112003440e005805149850340002c0c11502810005000a80080c08800245c1040660082d5000203201d8000000782e5400e2915000ca4580410381c0702510235070118070002c0c60f594416409541000d0007210110010421401da1140740070541005401660040740c04828016100001d060b604120800d843d0000c0d155001550300188500c4090840e0340c203900240f000a000700500e0313401c490030b030520440f120310b21028289150b11070301d8280b00060490060110b203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 694778066 1250 694776816 694776829
    0x30708041806050d0c0317070501021c0c020c09130501020c030d0b0109050a0e181231061d0a0b041203020c0405060d0609140109300e09040302011104080705 69
    0x24203000c440101410130b86071a03000018106003c085c10480450001d82c210044010440350500d603c4002591210304195070701054045089a2801050170302c2d2041d5002c81c800f24255209120003051080d690701e40c0071544400145402c001c8440d0341d400c001048030005c0030000f8000701c03401d0800c0451002c4000c000140510425032006006050300b11050100e8090030f031310b495111144908108441910700c0300c051504259a0041894500c006501c044c0d202c40440e1100c5003541c02054a0026a94502540c0141c83c15108410004140e10031014121015103250a000c44000345110f1100307490b0780905416610550000302d144085044e843c00b019010300810505040440c2d0800062030b00302c010482d85c840d0785d08018a40d0b80c1d110341c040200925420760005402e86a00200310400c42440c1001611034120201c440f840145000c0d210403402c00c0d601082007815650300d0300e11035040042072150782240a4011001d554892a0300341000c10500302a1004103c544000d2002900d0041402075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 694779316 1250 694778066 694778069
    0x260405031c060b031609210506060a1212090803041805131e02190b120f04082b05090102091203040f0b1c0e1b0d0f080903030708041806 60
    0x1a86092030000c0008050020940c0d60041400a10300190301170840300b01c4d5560398030707040b40e4a61200c26510b4800e154400c078000c0071044c841c2c070841c0e0b4240c560740200700c039440251240380781d0654507196400005a22560368a0310404905041001d5901c0c2e201150864100d0b4010b0f420200076003142074002c100a004480d0000b209515000b001e0000391920b140302100c102030806040b1600f8410340031034584001c5500703002c45102d02103c01300d0303d81000c510075174408460342d0003d1003a403021418101c0311580c01802158004941441c01d011171508100480c64022255003c00c010518480c0c040c1440c0181c911400c900c400050742c80c2d80b940300f042007510882801044541c018007051100c6c041264584098440c0154010744400061803605502e44c0c1540b03a1060780ca0606182004402000544800400d04210105d04184951003800400c00030610042e0501c0d00c13681c0356501080b072450003040d440382e02a00303507854481140c1380d50407180c0c0300e03900c117020262036144c0c892074a44c0a44030b07020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 694780566 1250 694779316 694779367
    0xf0b01080718061103040503030f0a11060127020702030a050d08010f050d0b060f030d0e040605011103030402090705091e0f031212060a090e1b150a26040503 69
    0x240c2d030740d0940c40035000025290007218280480c1480c10144e01c074080003030f03400800c07005003165660303490703150544580e070000d00c0140003003036100c00908072042e80400c1c00350581c0d5920040e0b01c500c580109086561a41441c0041c810607401c11842e03000da20280180b5100a01900042505050115004245031816403103031011813071f0354809012666901d40c1e0404c502d900520700c103486480e40800200d0307100c81180f051b40d041c442e031840c054489400c45203804c15204c1c11a003c104040d560b8006540800c80e0b03e14070000c5800400020340186010111035400109900e0414203150f00440481c25803c0c002d000c1030b111110392495405646445800d214501c00254050007100c4141d0340401500d00588411060001021000800302e0b228a55420010201c0300401c2c420054054007142d101d00740d0241d071070201c6121b51241c4a45091801e0201e98a00340c0d041154a04075001c0e0040340c0e85002c0c41182070224050305c1703080090300700c0c00917001c0c040c1e0301038409141d9443c04124164500804128000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 694781816 1250 694780566 694780577
    0x80706090b0907060219060504020406051906030c0e2d04020c010204090f0c0509150906070605062d010302070303021b0c120607080f04020d0c081c0518010c050a05010f0b010807 78
    0x40c0361244100c4950102654024030204058495200040180007160845a0000b00d5201054114ec4102811900b140c1c0141c4040000494201040f144948590780c1c55070444803011910401c6440707004890004041da1403103070341e07007140b01c0000390590303000180d58482603401140074814ad55071441141c2007a00404800c118141240f18043d00ca40603c40c029442038502e04425044032140c241121900d440060016a83d03008602c0e0403402000240d5800c0c0c01514880c8885400040b140d032080d4902c0d291144a9540014100c01180a580020012020507400344054040500320f40c40d10311110301d1200c00350510203010300c103016442d030b100b100f24060781c1e1148007840800c9070401942c0703800c84803190303046010384d8450000c1842d2055040c0c0c0104210f09000b03000031012070109101405410910200c0c41c10506a981242c4030701900559031500e0b2100054aa0158050114120382620031019154003c0b50307070700e5040c2100d0341d40d4140100980c96803030b042020760b803100c0465813004050524 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 694783066 1250 694781816 694781833
    0xc180605090d081605060703050708070e030a080a050903070b030915010b0f0a03020f030a0519020f090d021f08070806121c18260c01120207080706090b09070602 71
    0x500d04102d4a035010785182c00000b00320034500d000d20000340c1d1490700503044500d242001d180003070042030107c58480024032860007260300c40744980c10704c120019004000b0160300b138032a01c400ca0103900115500c8103004007080450b40944051005800601d0080c0381c0310780301c1c40c2003460076040c01c0700790410401d00d0b46e444005100340b020640a5a0102c1224120746440704e2400509074003d21900c00c0d000100480442044040112a00501e204080003a28203802c6141d804d0038105134013941c1019842903034140f082001d5800e100c0031195507035000600c00c4025060023100d0b1038403107081c071070041c2c00a413407d01044041074100000e0354004805440361004602111316035a25134407052640394090790a9201c03842018481d403511603922103c2c2450303651103030b92003800c1c607082d80c641c0281d1010f20b803000800403041000442c0ca00541d800603144c101306d003a82c04c4c0d0501c0080d0302421046070211400d10100380030664910400000502c14082c0409504208141c540b0b0402698090011544128034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 694784172 1106 694783066 694783069
    0x30304030b0615040b1309180611090909030406080903130303050307141801020c04140f0406060b0d09030320180a0306050c120906040b0606030a0f0c18060509 70
    0x720b440e143c2d647d05c039202c00b81d443c84207941d08040c5084030010041045038200440b80da103129241c5140c50081400a060b001094030110703525440402c0a000035074024031000c1e00802e64000560610001e001c1d000c00310311003400004e041100100c08a40041c0c042c4040080c5100c55142d07050b2280d00600c00d0202c1d405100300c4c00e5006100302c004e44001410144502e220783c400004000640765a005100703516440b0241088900a9842400103099541100600100e9000000104480195080050556800d215140c42c01901d00800786400051042124030811041c00358560041503200020301203074007a4405400241010104517041d40c82400a01228100c8880c0d01c0040c0c8940386040ea407002c089034010011003000001c100140303010740c003550303105000d25000b144a45040340341c030301511428543c9502080680c03079611480130070f14130b5800180106140039820884c4100 = true := by decide +kernel

theorem cover : BRFrame.Cov 694604316 694784172 := by
  have h0 := BRFrame.cov_init 694604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 694604316 ≤ n) (h2 : n < 694784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
