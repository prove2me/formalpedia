-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1851
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:54:18.80933+00:00
-- url     : https://prove2.me/submissions/fb77f3bc-25cc-45e7-97cc-9b537afa3fc0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 332733812 ≤ n < 332913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 332735062 1250 332733812 332733823
    0x3010303080a150b0c061e1302130c08040203151303050a030b0d030206090712120503070c080301090b120c0d06050c0d050406020309010b06120a18020d0c180608 71
    0x940c1440d0841d980c1d107450007104098140c520320030881e000d98803000101200071034010050071142e002501e205550303030071682020030340882c0c2c11050306a4120005030301502c1c500c20101d1a0344000d020048295054078690211079026000c800462940d2040c0015460204615a01282a0941d8000c04e19182d09446c062580195009040c40000702c2c042281d14000c7d0025901034002500c1504541d030142402590780400751200050b90041500100c2c00032071a201c28400540c2015103001d0340c02c1450800c41d0380e40e0008204408000007118480d0004100070001e500070325400c180172540c44480b0b000c100d02c07140103001e00075542d030180c0041200c9448000c03031904095009040081c00e0b07610b81d44a0212842080540c4500f2450103082104200f50350b800703503004200c840000c20081000b80c06000b098801e5424103989400c4040000d25418882e0f007000b181150f46c0c00b0440d91404003507011032092440f884048400b00005d00f0103004540c110031108040d0f41c881c06080c0949841c14007038a4580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 332736312 1250 332735062 332735069
    0xb0c0a2a03080d02090306041b060306080c09040c0e07021006060509210f010906020318070303050403150f06080a020f06250503130e19091a040512040f050109050a0b0301 75
    0x740003c50144008260350b41603d00c46000a0141c0300b5614140c60850060058030340c9400c0d07900d0303644c039003c509a8400d2240300161011107000700782282103c000c000150f00002c0044952000060000c03504126014415000b0007040c2c00070f1000002031410f180a642e03841d040002002030134482d503405070b62444400c0c00341c51001040a4020b9061201050801c00301060b0324590703600307101c00081000034960041d803060318080c4846a6000440c041a51030710100c0c88003900240061006102040e03001c00c42d41040c80c243d040003e800c82c51241c901d01a142e0552180322a03410980c8072005500305903582500036001140ca440c54100a005001c42d60040000b10a00003416500d0300000c21204000b2514805003540095000590702c41c84460002001c5031000005440c48031403100114090254510840d440380422001c4030900081105010008205952a00c00c0380302c40d4142105040090014103000e081100c207190418002400c9904c0c80d5000c10300510402200b0800c1400041c20350303054 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 332737562 1250 332736312 332736323
    0xa090c020106030503031005090604140f10080a1a251b08030c0307110105040c1527090b030307050d050f0f0a02070501030b03010e06040b060105040b0c0a2a03 70
    0x9824400124010a00d81c0c00c010003030701c030010a024202c0312503a5054110707901140c2c4008a03550b000180010742d188410502449149170010541722110310503496441482e120a292180d9070740c406640c545100e0703a2041d03030604085040b00c2400e05041c4000b56101c041007401010744e124001c0c9c010300304060401118208807006c418100544440208207102c42d402042c82c03a202d05000064614641c8180e4150b0081192106450034100c01070184d60722868100c2004c078000b51800b4145004503619034012801c21440c407500e40148001c0a032240c0c6032854104869034010706100c4290122480c042038075120f03a009100043c00034900207017191000f52a8600b00b81c0342c10310544100c2450190f42810107140b4000300e44d011255030300040350022030b03009903000d03c00c80948405043c201d456000c211311143e00010300050100d990704175802d4002c00185030892600c0c0d5107011085007900305504880841c0c00513440c00c0144030316030305010340410720880814a4038a035520810410308051000614 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 332738812 1250 332737562 332737571
    0x904020402130e010b311e09050403090509090f0a110102010b120105041509050c010c03021c17070503090303070e0a031202010207031106060109140f0d0308240a09 72
    0xd02460888044020042050f140d01956140c08841c980f41c0c00c034682104404e103550400c11008411802d6440960300e0038007110203010305100b15626201c148403000b070f03551002103100207801c00880c400c8601c107d00940c0d400440038106010045281c4000e08141c41c640c0c01411545c11910780803d801c0320080d07004025031020f101d8000183d01500388100000d512004038000401d4441064010f5407099208070305003101c868036601620700b150300c400c50141140e440241c00b00c44a500070b422484446000780100c43c50214203140903408842800d0711040000c03001c2240320318524030341d14080d410410900f0820704524020122650320301000b031a403010880c03816080348943d20f07681040c2c00607517007150200075100b081e010013038080d5000d9581180040c3c01e2402c88004c0140202d14103026980c16520b0003502403501d0312059000c403164100560000307510880d540c03950b440c4420440c01c58480d4803851201c1c50511034880660540300c00c51042a40f5441d108941030740e0f640101415289400000103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 332740062 1250 332738812 332738827
    0x30a020711240d18051507030213030803150604090902090604020f09090c120103030314060d0302060105010e01050c0a050607080a0c0903020909031b0c030708011503030c02030a06050c070b090c0904020402 90
    0x181c000c5000304480c1c01d5800004400307110000c0b41d811070110180030241400e03261511f00710101d110345500074000702d445040900008462000864000740d0b400c40d05441503501000180040d840395220b10481940c81d0009001c5080071460540d01c0030003203d08500700181141c07000101c0c03142c2c07410a8411054200069801d0a0403401c0e01e100050700510030a0942e1285009130041c4600e40c0485c0c0f2540d80315002a6582c0b0b0003444040c2096410b50281045910b80001500d6806040d90b020781800006e00603020000303010441210914014801413820741400480a01041c50151120010340c0c10040700e5a1101d030028010021244e06907081e190f5951085405070543c01a01d1080b0041002d0350603407000c21000284107010b031441242581e03c00b56a9840545c00c99007a501c80e8000002c5810b4101b01103405250416040360000d820354090a1142e40d070102204d00c1100c0e04180010081200340900005003030344c0d640600688000d10300346400e0400958524402003000744540d80025050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 332741312 1250 332740062 332740087
    0x100c170f0c120307091707060318050a0819090e070516050a051f150b090109150807030f0b011707051e03061905130b030a08030a02071124 61
    0x19209222410103a03002c0420000060b0788660040d03c0590004000a401090718110590100e00706900354004000e02c40c6050b0054000c2c00300c280c4d150440d0920308560f01701040040c069903c2041c81039000940d6510f101c4d118a50120480d0810070800030001c50a000c1c4107041500d0603086041410718541b03c2d5494160b00054465508c4020b207980070b500c0301e26081150028269004030391004c08501410b070701d0008074084503108015100313203081070b0004010080642c03006041580040c5450030400341c54018890803902e80800c400300003105413042200307055051154138007110164605101d502c4209c40020b0206180120030b4102e000c01e0703400300d440b46000310126007084400402c0a03522180f2400c2d07180031904200d5506002d11070a00303001d40d4031310004a0102c2507841c0200701c00002a0525488030082180c149603075010301c00c8030040d6011030031600c080e5100d42942c8402503958415840c1c4404050081c4041500036071340c040d24804003a0014040d58076600d00124290b072a12800c6220 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 332742562 1250 332741312 332741317
    0x906200313090e060903130504110906211e0402040f060801050c04031a01060804152705010c090602070b070203070b03070f0914010c0807151a100c170f 67
    0x50700ca80c0c0e2040c000240201550002c0d003070315aa620a031031465440d99007150300c0c1e10418030081110704a414042c02075141507030102003c4440c050101703041508075000b103000341e03108c0c508544024461100d070140442d0707900486503102d02145411b00e00500b12411101468401400c001c0c49a51509035400811520b40d00c200700502e0900024001405c150503031100c594040d0009840c1c03ca44190008011401c01d02c0140c1243c10940d1039000c650703541c0d15645001c010010052140c2a2aa5030408441440400d8450390380c41d00b15090044c00c4440c030300242118072101c8048180b1600e60f40070031040c1d8001c501d020480d0340c001415a611026403000a0070800590001c09a4140100510540680c080c404001c0400d0580390900005c1e01c455540c0c912042d59800c580c001011141145c0000718024040c10710745101d40c1a4202c50500548060192a000e02d802062080d0700901041a40b500500d030390100a01814020003124858889e0000c1d0a904900301c0c01289002896100240c3c1c2c0c1d004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 332743812 1250 332742562 332742577
    0x302030a1b111203090d0c050f1c0e03060405100c120623090103050304030f03090512060a0c1b06020901110709020705010b0f06090d02010201061502060109050709062003 75
    0x180101141c5528016041a4541c2c91000c5584030304a6020b40c2c1280b044122401200c002d0024429084200000c486607410148111154021401100b0503443c0030007a50004107410b40c1101189440d454009104603d07001c6040d210360302550a20012980204108001001d9100d0109101040640030f980001d88545040d81c90340c601100001c5114bc210540e0304c1680101110307405505128042101d41c00081c040903201d90400c0000f0000505664040c0c103c1c144203040420b40ca0350384900003468088410000759240d080801040000012481a40b00601003400c3c0710710051820030b4807200d03800c441030004040b107038001000782d1180c4c051302ba2032006201c442c00722080c85458658400c060b4000e010211425804c10034616124500324140c8090000c01414050903c1c900307000b0008042d22a51040e4155560351001003410400c4d0f2200c11036880c1550010310320341d454071244004403030b0014803030400c1045840e0103000d40c0e41d2140c4110035602d1441c000342e00020403000c0ca03c3c02e41c400c052 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 332745062 1250 332743812 332743841
    0x20306100c110d21081501050a05160f06020304050615030f0d111213090e0a0213020310030b01080307150603020a03020d111306090b1005090d060b0301091406010b040b03070302030a 80
    0x60f131412007282d0082c02540f18079111140081d148214038015038142c000c829010340861000d110041402d032241c403c91680b9406000030704640d80d00340c7c6542d422030f44142c405441c513030040800c200b0039480384114070030302450580c000c5c80001180d006a544030034011140b0380c1004203003015407681000411034a00c01c0f2040300c407065980e424020a800c50000c0e1440356403682c03400d000143d000c1d40004241000d401c0e4024128280c1d55402c20790103002035100171b000004182d45100084007060007a44400d01a10410004503035802d802e040024280304110070691406003002c20500058454455010449905a51030a41000d1505e000500450401013031030704181c1294541030040e0190708140c00b1500c0d2608104007403030002c400c0c444201a5005144046581000780d84160f06100c040d00d81614040c02c0c002498dc8505070009095541c488801d81c3d040700c200b0303090081c80c40d003030040d0381c0148a01d8403075525003880d120464055001c008d0801050607800302c0041c220364030503000054410b0804 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 332746312 1250 332745062 332745113
    0x1603020912100605101d090c07060504030f030b0a03050a0201050f070f030203030a060b13171002030a15051e01080402010c081216030209010207120f080d020306100c110d 75
    0x101400401003d0740c0c0704c2c55101e024240b046400c02e50090700b40c04d900a8220f0700c001d507580001400c0c080240e201609003203003900100700e280701281442c440c05000e18480c0c0e45a000d00b86803400002c042d114010122803045c0f400d403008000003600020010016682820040c3c6c81e031081e403120118038000c500c80601038450101d001c07010554040b0086204161a20040007865100c001e2490b040c000c2000901135051a018240a03115401120403407a01c01c0504540f0040740c1080002d00782d03001510011815516001e4603510214900780b40000f40c9415074055440e500513191101c15124100700050601c103140e4040f4041d644501c4120440ca500900625a41d82d03052a0900384408122885641900300c4864101c0c010700c68021610704120503170052428500340102c1051003044858115807a140c003003180390000300000003500448080240c0181c50b46081030901081a41e107031040300800400942c0131300003926981100e04c0b008021746a101d00c0d04124901230740c2100c2400852400c94005d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 332747562 1250 332746312 332746333
    0x30c1e0d03030221090c12011104080309040608011112091504050c03063d051c0506010602010b0612101a0a0e030f070b0d320f1603020912 61
    0x150020300c4c903c00100700c030a42103c4800483d400a04c0c056581302440c0d009035030b920809142c251110794010031348000020f0700200c1c0030300f054041e0703006620422440c2c0000c40c010105140c584540001440080f000b03002c82d5504036003c281c10b100e0f601444512014690204900c1c0c5002c0262005004034854500340c9820f00b801d0142e40c945036081005d2080c400d400000d800101c103110800e40b8070000030a50f808104120302c1442e8a4420032441c034040c1e4803248000202030342e4008400c4c00000441800d880c0c05100381c02d1107818802d0581024080d68185018907020b515200f003120b58000f950040c1480d1920340032000801c5000c2035210005007080580079092101554005044000f156291002c1da05e80c210709050315032080d128140c0281e04400800c00000d2441c0000309043c89500d08001001581c148002a40b01707a1070360342c050f02650219200e1f0f100041081c0c4250080c96003004040c1524003541d00441e00a5860100c8042680110b224071042d00c6200c0408581280e05007900d0512a6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 332748812 1250 332747562 332747567
    0xf020c040203070302091e1c031107060f08010b1e16050718061208030c1b0f0601090b010c12110106170a0308130f0201030b010c022106090705030c1e0d03 68
    0x1541c0010300ca41054041f40e444a11002210005000c0c0503040c2c88203004040310700c80a03291405c1c41501403015008042d401d132402401144050085a1198105070890103401401c1c00d2050300030006040c01000242e02c100100c1e0764502c00c000c01d01041c0313640d41c910f00c01c40070b905c07061150740201540700c1d594001c03c204000808458800c0d10950041091075500c80003550440001040036009541c20030100307490030381c200014100701c1810a080e4402828045401e46800041700802103d500000010301a540542c016010018003d02c0d007095050910345a0707103002c10500002906201a51103c0042d007402074014038002d20010710b003428460164440c6545424001d4403ca00140980d03000030150711004001d0106aa003000a02c5003034034507a0f005400605249094a050040d240c11050045e40c1d406003c224040b071400b241da50801115a12070700d481c4e0044c0140c0240e81089205110710707240020071401c0d084084968030401d00d115101865015030380402a034016088100360713000d054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 332750062 1250 332748812 332748817
    0xc070f0501150618030b061201020c0307050105060a090c02061f17010603120302040303230f030405030a140406021b0d14070602070509011a18030613110a150f020c040203070302 78
    0x181030784c880e1000c51001401a105041507400000c1034040c81c0d5020589a0514109030400d00c030505000500d080c1464a07580d1039600702c079400300c5203a0b46402c200300312400e20344c802c50001e21038a8001d0140924240d00a911000700420810100005003484800141000b860720014a11540888210543c0c224010302900d05800152051400442d640a0305071203442290112505070343c0d26582052543c0c502d210400401035901d82100d818007440350941c4101c0010b500445c1b00e00b0045958803917500300035100c5045603a80f040101c07414402042102c0d00801c02d201a010300c0c200d0240340c0d465410000310b104036441006800c80340040034a21311400001044002c0e50f40a800302d41a00d960b600030040340c1c0d0b40074040d010107408004248854890080301910a00002c2c1c45a64051000307000031030310341001154a81c0c0e90a56a404d08030512545c0600b1b0180490252500319025040c650b426100d10f00090702d042c1001108418030b0803071882408040906403005000790740e2030400680040294 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 332751312 1250 332750062 332750069
    0x30c040507022103011415070506070309050d020a081b1f0207030815031c020a02120607120e03160302030409060609090e0a0c030204050a020c1923060c070f050115 72
    0x540180c541082100800e4038103da011b003400004000500c010320000504014550012080c00d1004038002881440302510511203568000f90040c21801c040e8030f4900801031039000e64001303c081c100411689021614101d030303824000e085900752341d61554038101c2080b440004061480508424820240e001824007500980d2043d9080d10fc01ca41e40d6001c070141040c3e9541076102881c20001400050309042500082d401a605c1000c80342e0041012418580c00400c0745e50000401c100200f90030091886003e82c4c142c6081201c100900b00459484c811002030311900d44d011078181c01018420021540540044041071003110340e206409800c104d10740c0242c0705005d04100900400d81000111011550340028412841610715020320004080191800c60200d07000c0010150701c1008000351036854440340180c0c0003560b01d500700304825030311003690310301800655405500f0003440001c0240d00a001501202e5035000b180c5000e40500940000041c40703942000c40106071200350b2081001107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 332752562 1250 332751312 332751343
    0x4050303120a1d060403080a0b0301020304030207061101020a05040302060313051b0a140102031909170f070b040b1b0a0b01030f050705040c1202030a060503010203090d0e0a1211030c04050702 84
    0x60071000d02858004968940f680005036015600240209118900058210b044268000f443e2101c01002c242660302c22601a00581d0203600200500daa102e1800d04071441080300071810b00c9400c0b9001041841240b0010384200303404004514400d0301d41a0b16282154400201c5981c028486211210005048092881042130640004003000990940c1100307510580c0070718548210603503680742107004d504000c0108141c40b0300c08100d031801ea4a10240c004042401000103a210402583c544000e642105040d1300d0144800c010400c3c00109503008254544500300c9080c907c83c42051902139071410241002d1114400042445204480d0600e800d01070780996406039114401e2005840a01c43d1850004000e040702e09a039807110303806036801904020307012980650350b00c0080d080e41c201f56001100b07078124411151009802c6440d007003041d40240d96103daa01d03c0d100311208110b40501000e0701c0c0510806840303103669800d20141104002c003c00030030240c20002002542d0380d986a00d41c508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 332753812 1250 332752562 332752571
    0xc08070b03060d1e021009030501050c07110904030201021e040e0702060f01050f0111010903050415090303140f2205040c05070c031b15020307030e18040602090604050303120a 77
    0x11005000e808070380c440e08000d40440c41c1e003101c0c1d0b5a56220f4a600500040105107004010b0006070740da86941c00d031413842a0344503141981541001d50845101800344403914404024000004200c4501c003014484104c8403030540e607680b414113034064466520021050072480101e80b180500800151045d121240c040c2071003652260300c203a07607405080c0d401401035403010740104220f21300304508043e691010700d45400888926502d8074203585452030200c001c1032011030244042c0a0310551142c0080c1c003490001d414074070310748000e892040e21007490802c020000940c00341013402c401c212268480e091a2a81c5c900c1e905030114021501a0f0040900c00c034144807100d0781c094850b006a400f85a001200340c40240d165503104a02440c1c5405001e015850303100d40000c1240000480c1d80a0301d40c0c64014589d42c41c03840ca00100103041c0e100b00385100c2e00c6062194002c1580104c00d442d03116910400c0140d940c0c1110b8001141805294852170b0b243c0710004400880301b03200f20a150252151103001e00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 332755062 1250 332753812 332753819
    0x904170c06040602042c06041d060c0325120c0507120815190e06040b06040306061a03271207030306051e0105030406020f07020a060c03091a2704090c0807 68
    0x528448807481000c40600855000c00d21f07928007944482d007010011150402e01800031401241400c600722002d1680b00400300412985907510920f80c1e807041401010340210318450100948206408060314641d070fa42d400b04441064014011502c0503904000e410150050170f1000400506080b514103140c145295010310481c100001c010924500b11002100c41c103080c10b006400c0010020030455029841c0c80400d1a1a01e501c802403000c0e41c0240b07000718049081010b460003c060040154600107400c0040040007180044542c4039501900c50030120024a03100007450014181110810f691000520b0740c101034040d488242140e900356a1000983d07a011078201410008150041c0450304c01c000050000c0c01d03640c01441300c0101880c3e041d091030104e80100f18524466004240494402d035030350f80601d41c1204030b80000301940a0704640015000c4c100006034010520201419200c1c0e2025003681085c00704260709038840507100b04001a03442c1000c0222044034410b603241c5000b10b54021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 332756312 1250 332755062 332755109
    0xf0a0f08010513020304020303040521011a010906030b01090e07030b0307081605013203071b170702120607050a09090218090c0903150a0c0207050904170c0604060204 73
    0xca04031840240301071000b0f0a2100110043e6000030001c80e0b05020421012a640d42c0351504a14000f00ca050743c42c20507403a8070000c41c02c6540000942c1752908020000641517a07010b4141c5050720280c3c0340202c1d80f103c01d00d0060310082269080440268010030070880074070b91561010440040032030844040ea03a858071240e49920b8850189402c02341041014445075000e103894100300e10004109010040e921407000030680000005110209000424880040d500c00301c40300d00010202c60341550041c02d036655001440409142c030074a2030022a2400c29580e0715020100083c4240b002d44100385068038008003107900803a503002c042061003902207080050f502c262024800240000c04c1b5070310030542044085000100401c0740d00f0807c00c11a02c0545007444070b459070403940c0c03e80102c1820000c51aa06071050891110110361201c2070802c860307500c0300b050030f400c240c2000d100e90304007190841641491241e00c0000740b442c0704510a000c00c00c81a9070051003222000c0a4040039101291080c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 332757562 1250 332756312 332756327
    0x90f090a0f15030807030f02030d060b090a21060b152d042d0b13090b1903110105130b0301091401060c020f1906030203010806071704060c03110f0a0f 66
    0x80d01000050040d480081d01447e1090380404071401142e0402c0010070310301003a070341c040d000800b9103007000c2100c0440b820400c00041c0600701802d000307100c600040e10480c3c1e101101440c090141c0c2e8540302c3d903038500d48940741035003944082c00040030341c2d400070f0b11600103000d0160101010314000d0341880341d2051004a00b610180d0f0710b070164840c00c0c00880410306da031107440703e06450000141c80314005141c40062000701340c454170500300041c0261030310310910210b41c501c90324903000d4980901000340c00055007240400b030301d0788003208210f00d40c1d030071004a4150040040903004402000c90200782d2194400145041b141050b40501c9046048030722117403070403420701c54500072500a010b50801450300d4000000c1685000c1c004001d0f0710f52241c107410122005138007000100741e0000052040c15024004680c1c482064202900c1035040c0100d403003402071000b0030182000342ea841448200034425001025030f054a0013110761504030041910400360710421100340821001200202c180d0700800c030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 332758812 1250 332757562 332757569
    0xb04180b06040b01021902010905090a0c12200d0902040e1b03010204060c0b06030f010f06031401020301030c060c08040b1c0e120318010e0f010903021b06040b090f090a0f15 76
    0x103082100f204862a00c10100c09400c07c905100d040740010031107032640b00e0107078850782c2e50718004641e01d40114000352900407011055075605082c85100190220701d042a0f003448007003080c3c400d0707546102d0740840700109807a0038020b601ca801e05000c0c1d03900080025804443c1c0d02c25004000c16018844105801c13440342c5e20407480490002d107003030008142503414403036000c80080c0c103440607a0f0b0080500360846500c01807008099554000600030b000218060043d1150100003c514550450300d0312002050244140001c00050203000010441e0a40964008110440050ba02d6554040b01c860700345070ba200c003014520f0b240660b10707801003100248580181c005140e0076490360f2a80d00c1d02d040d0750b6041c07080007003440d900c520502d0002c04080040d079401c1801c0d0b0000240010151034002d00340f006007401100980c00c00c822410003079803050212011140600382c441e03510840800031a0580a0f40c046c1103610040c100200b02224449030007a03d24401146400c00c00b03081b001603801c4000a9500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 332760062 1250 332758812 332758817
    0x204050a0b12010f0302150a02011401090e070609030c09050912161502160212010b031b03010e0f0705010c11031b040608070b120a0605030d030e0c0f0609130b04180b06040b01 77
    0x624000c0f51f4520780082150240f24400803540803d030501d4104d094100b80d20200249a8035800f01c0750400c410311000001d0111450280c0d406803443c1c41d1100d0360b01041c01600030403580c4a001c65401401008007101002c0040504c41d16a4528000d112a031070b900301c5e040d83d9503201040850700d41d428500c00c40b612400c0b942600b23902c00403107809011040c5083c50104240d0346da542d01280140d6030401003d0b885070001419503038440d82145c281400d5407000214194258000c0b244100d00c40c10100e503000a0300d0080c070300089200c040b8201b03040000486c0b07002c01e401d0f0041404256641c040c8130100f1006080507501401504d80d0703151001d558080500c2544a4920b080c0955030400c4184074001d5081071006402117952619000002e050007004210311340881d03640e8104502c025011b000c02041d15000f00c490001021051010035090320425450b036103d50100c203c189030200c41540b009a26600192042000b042001c915030816200c0203020303030b5075540b450b000138140d11300750058600720748069 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 332761312 1250 332760062 332760079
    0x2060615030a0b0a05031e010e010203070f0507021305010605070606050a15030e0a0b010e10080a020105090607140f03040609080a030c0b0c041a0a0f020f070b0d0204050a0b12010f0302 81
    0x2d41c07140d401414299200da034841c0e408000001c440c0d604000c40e801c020083c042800050f08407800c0c850071a0840300e414039031640107001b0800520b0308485181482522410b2141c1d07034203182d200041f1214030540311802410301e400c00210700c080d40701026000c04c038410881000600d03261400c0045402d028801e10b00465801e09401002c94829049003242c0c0c44048201c1d46201000d584034580407034240c0294100707502d03080410804115030684d62004203c040042c001148407a00001d066100d00050a03004900014008040042c4100360120005950050740c0d040e413402c03e0110b48a50151048400048820901040020002c02d14110542e8562100403100d0b9469403503d0750070100404008101c1d40610000506c0380e01511204c2c040504c10281665425045402034640790305030207081c04550044c440d00903900e81c001400025105400310f140d481d40c2851020b88041d1042d9008a6084030170303610300144540b40316020f001c0505007400d00418607a22018031805040c0c483c4406135104076003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 332762562 1250 332761312 332761321
    0x2001021506131805160b0405010e040509030c07082113050d050f0106060305040c0b0c0c0f04090f0609030e0102030c0a03030c09030b1608010603140f06010216060206070206061503 79
    0x2081d0b10581c08201004034144400f02080c0540444802d0180c40300e0704a2010050122046502003001e0400e2a00c0c56003050b0038400020240008405210700469503007020401000c4100240c0302c008001038100c610305a1254041c40d16444203003030400c002403501e10030004c000c9100302954000003001c02000c4034103113040c013003083d040c0590809075481c0c007504941a140d80b03004c2c051500039185945011910341010b142c4007091030440d91103003814070018004076249140118048112082c12140c60800d44440400a802080c0c0c1304001052010382031090020007455030030013280f050081e12a42071040401005a84900c2201c01d0410070340c1095408900082c0a80c1c04032203802d41e01c2ca0403054003916940e540400e110b0a903100d078403003081080d10100066110001d140541100d20b014400e50307500e004da03060301500103003d20701104088000900c090f4402c2003003084844946061030b1085555880c0030f521481700752000001405514001113203070500c0700e5090320f5020b4840d48180745944 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 332763812 1250 332762562 332762569
    0x20907030c030c0e1c0f080d0209010e0a03020d140f0706020f10050405030a1103091c020415050f0904060912200328030906020408030d0510030f0f1a01032001021506 73
    0xa05d1802120000421580400800c844a028100d0b06a00300801680d030b02d03031500090300c10000041081c0c41070701400d1062006807114880c05a103542d0000e000003062072910020b44c2404c0030941c4045c2c0c2c92284d141d0009810340c0c00a0b4020f5141c00c410b054803003444203540079806560742201c000d0308981c001c0001d03091051040c4c040380b065400303000549080881800029801100c100c0204030a5070320910020154034092140d108041d900e102d44048613031034a00400c2c000850303050494030500f4420000340510516400080500c0d501c00210301080d241d82c04054a008000c449240d036408003d2208822800004221008859030b14450509130788130b151403050701140c14008604241e1515440320001d81c0c240080c102500307541300696114200e4000980880340014221502e1040c4080c007040440c020381e11011001d608106401c1224916041001c4500895a90790400401c20b00001052043d48102828217605028110040e42a482c00480e5126603401c0d00104540d9442c3c007040d11840c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 332765062 1250 332763812 332763859
    0xf01030b0703020c07060c0201030e0c0102100207051204060801170a033504150b0904020d060c140c0c13020720031905010606030b010c050c04051003020907030c030c0e 74
    0x7aa15003d894140c070704800508201140c1e100a000c10140b0144604641c1c140c060b00200380d100c000203042c4c0c5020b210000b0b64810050401d5401d0540c0051600c2c180002400070020520141c50420780c0d465a9440091840c5802d00c50041c01c041c1c810001d007903c040c0414842440c40e010380e42d001c1154165005012048180b6100940c01c107410a0542080c02403038800728440d03401050b4440c103c2c601008003005460799001ea00b849021040304010040e9504503c0b154400d8002200182c1c040d450764064514400060840720703543c501050701105620006000c000c29201a2002c50b10b14030720a2a9005034000d03040700910041c1840440e0480703030a010f0620355113440007011030b81020460108100319072070003441500d0a0b5111001031003056018001c05211500030328141a07a40190707281e09858000a41c0b40d40d00c10ba45800100d81000380b540b4201000c4d40d00149104298100940d0141c018103207648100082414243c48286c0240190030900222901600c6500c0d0800c01d80c050f9401c11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 332766312 1250 332765062 332765071
    0x51311060a090519150f031b08010909030e060324060f1b01061d01030c0f0b0315030a06020a030f1d0a0b090a0501020a0215060409111905030f0106050a0e0f01030b 72
    0x41d20442c00519202c114403007549045c229140c50515481c824001000d840d2032a051980e91422040e07500419548151030b00d045490040e00020801214982115103080304030200d42d03c00c402006000410b10b05036840800e00e050100c603000080041d109101c0a802035459180e1125400d0182c1c10482c080f01c000c078007088442c8000020000c0d141c0400d1100885420140d5585400f03507070051003001000468000582a00300115180030b00c1c0511008480c480240700c041c07030050110299849031000c100c55910503522540039910740302c2004004000301036014000b4000e504040a0310b00c83c5111ba000450754000100150111094548030a0000100a4030b0040350344100240100821020f00c05000400074560141c81d06c0100128900b8440d0405401144698682000580090803800d02110072500c103589029003640d110350b041504840980c0215014001d139500718107202c10640c012815120101d802c0d505050700c90004503d401da04451114211030110300600c08100000051a0300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 332767562 1250 332766312 332766349
    0x11508010611101d060901050c2709040602030411010c030e01032c070312030b060702010309020f090702030c2406090c1b06010612051501120f051311060a0905 70
    0x103001d2111000e000b202c50390400528135001250445031031030014032000342c0010a04000b40440d0a00002c034040307512404544068120f007907907120f0b43c0000743c00c4540210200003415140146000e04280700654070031642250b00e200c40901184140d80207030f455a03072140c0c143c0d03038007584d946080740158014103500e181455558511100450280d0400c18024845080030014107165450b5140c400000140356200805160510303603140120740703502044da00070036024600031880490a0020a030202c0400c0c0c23500703400600e964100700145030000000c01e5079414034421038174040010181c0c41d900f042c000c1544100701c02c900c5c010944a20307040d0641c030f030081e03d8000c0051920800481c89211100042d40745d01c65078020f00d0040160940005c40251480c0d2021424407075071070160b140d624082c01d440221418017929050038489624113030700c440340070000c15008200a042c1070901c80b015021900e0122042442e4081a4006041003000e5480301c3c0c0d110f481c1ca4001500b01802c0140d10071810503650300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 332768812 1250 332767562 332767573
    0x3f0504090207060c02010506220c0302090d03021b191a040f090b01090e0103080912031b0a0203060c0a020718150e0403030b031f0504020402040302190e011508010611 73
    0x40c0c682452004064030707445440c0005800c49202000780c29224010529403041c7d064041107003030350b01c5c2c1d489120810001240c00203600c001c01c840a030002d015200180d070700005032004000406400088003900d80072110040d070f2130300000904118100c15021003c000308d0301141c7e8100405e105800c25105507140781c19205061a48500304106c00c7e03446507200c10000d644030b00d0308405658201806102904138540f6101c03032503042d615510b416114044840b070141003044041200090f0900603102c88008cc07890030203c5845804280d5902d00c1031420a030b00c6130240c01c000c42c03040420a0121781e00441c00d5005005164682240c0110b006818144901000d84030491814101c0010070194050110b442b002406400c00c1d0400030201c0d902d0454540c066804503480340c2445000c0364000d14480045000480c40d50344074070110b400303400f40d584002c3d080040011044144403010518405841c408201485a0f83c1d070b0700c0100300500301030208940858a0746005020840c4507540011000c0c80207001c603038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 332770062 1250 332768812 332768819
    0x150304170307020a03030b0603060a0506090d0816060e0114060904320d0c2111010212041401050403140a050717040f060810060e0a09090b043f0504 65
    0x5000d41d00450720040141c020a803003104142d05071054048401d400e072807442c210300c1e00d000400d0b404842ca02850f441041c000c150b9071140c2d40c51810610305560304c1074044c2e48503440e42855000d03401c68420201c8556040840c001d00080b0148680d1004421000b00d50003117840b404180141c14101800c240c0b50034000310b10020411821001110011400340301d0003451001407800c05040c161a102d40d401086070ba229800003084901503100f800300e24000d80c00300c40c1c49181000303490007a00d400c0d48c0925540081540c0020414082510341b0480c026400204031b00c0c00740c83c4e0b01d07080b0b0f103045800a012444401c0c81340d001c9010741010f04000d240a00740300d882c00b2000d480e000b541000100b644051203000140034800728200c5041600100110300f80449541400c040000030402103004040802500701007201d0340d40c1e42e00d10780400400c4001c3d0100f085821500740701446406c121419900c071442040c011191883c0c9242605510590b801d0074518281c19101001c1d00d040a05d5140007049002d00010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 332771312 1250 332770062 332770103
    0x904030c05010c0c0605060d0c09020f090d0506010504050c070b04030e130203090c010f02010e120a0c200a0e01030f0312060f141e031e0703060606031415150304 71
    0x64440d500b42c131050008181c0b0310704030b01522401400c684c01203005021200015412406040c00c0e50b28140d03001da21424154503c0042f0300800540980c85070002000e203060146c0840c850381a41e6040d5001d05c4141d941154102080c4142500181410f000100241c0420710400780a603c070303400140b040000f9a017540d800c000703980003600c80c41104c0e0885880e00119681081184901000b140002c7c40f00310060145030382c0310b20401404040c0d0150008040c032080d481051111500340d0302000c00c01c844039506180030314040740c0103100c9008056248010600f10404120799048a50000303d140c0f0b5503140c0d40d412900304014849102c00c042d00d1b00e90214109103062464000352404400300c0700f0038031a080030045403040c084082200c1041e40032418001d0b03200428410b074035000141028074a0310036881c00030315203c12580080e00c0d60349800c201060392a4183c01c00b00302c0d0204100c1a4056440c1c0800030340039000c0209400e58024454102c2211024500010b0340d4002d01a0003410b283c9811400103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 332772562 1250 332771312 332771321
    0x2030d09080d090605060901050f030a03032a09090609060e150f2112070309060f1707030209030f01111614030a0c120e09040f1b0b0a090b07020607020904030c0501 72
    0x104c03055038a840c02c011140c208841c455004003401c88088030144041000700351104122a4050f08054545003441c4500c900d200030184600098003101c0c1414110201c01405100d09020700d0481e103040c810b00084246da039004170400e80e4101d10300c0681684078003e100d00b0143c0001030058000050300c021203520b40d00d0b2041b82142e1030b0100c80004000840c862001c0c1403181e00b160750003070301c402800000080781d8000d108506a50325802c1c001680e210943d826550244509180c4640c400001d04000c0b21940c10f4000e8011400d05404980c03c414500ca6894243d902a40d90403000d86000d01c1149688004a01849885070042d90340d162004104115681180d02010303241001c0740a0104481c1001802c0e413031119035029600d0040482410100040c8018001a002916619441200f08107100001002e03003013403c072401d044005160307608415040ea812410b000804101741520007d4103285010491302c500b5130081040d464803d15600704a94800b0240085c0c003000102040d41001500900c20f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 332773812 1250 332772562 332772581
    0xf010903090810050c03040b0612030712090506120a110403050316140601060203030a020a032301050909150414010213031110052811030d0212100602030d09080d 71
    0x765507060038180400716280c240322902d400e440b030f07160000b0040040c05207400c0d039030001e40c045460a41c0380c80b40400280c0800b107070825004070740400960301c01002a448410858482c0300c2d00c80d483c81580e00c03010402a40906030040984200000000c9c00d01030041d84007035800041c0c41181d50400ea101d4a569143d500b0402e00358989054191602c414490701c8824031010301ca020b8000c08096051500007522408080c080b20a880d8000c10320f101003e02a0f0041c0c41105283c0b100910014503401041c002c5030320a10a07240280156404103136070880c00b04902c50780d8603e40d004103082d515a5990040d070342031494175443d41e82d54240035584200006101250007107000d81c0140b00e000f0310700d40400c1101d0803880e6800084c0b100c01c00c041c00d090680d8480406603644002c0d440c51201c2c1003d2003e0b504211041c814004074000060b81074140f41c45035001d02400441300044160582ea2210321405140080c002c5501584c010302c00750b15621300c1c07504106605807156213142d04081c1070752106000c0d20b01c14003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 332775062 1250 332773812 332773817
    0x31b09131113090204090e011b030906020d0c030c0305180c010c0224190203041202060c0703120309050c030a0203070b0a051324031515020a17040806010f0e0703020c0f010903 77
    0x408001b12800e900802411440401c000c000c402508a5032203009100401e001041c10f8465800790706014071541601e0040d0741440e014049803240b0300c4006c00904048000c00c0101e0b20700800b0034500b6400700054026032a100c17004011100c580c20056894001d24001281e019403926010443e00c00344101441e00e83d007000d03140603281c40c0a0310355410340c1e440072844801150f01c2408200f15441c422201e20701c1c00c40d019200582d880322514a01c5092490a40001e400303041070030350000741640c0c158800d45101d80a5025140007003600700c00c00d0740b07400d5003500181d40356014400500045e03d83c2c02c0140031807441410305900d803100b03201c00103140032036a0780017a02c080c00240002801485013060f0301041d00540c6010041140d40780100f08000310240540590401080c01807000e05000700b01c80500c55070030014171040e280101d064030a02c0d0f80203008095190107030f40c000190041c3c56071408410703510400307141200d9a44410048000f50011a59034841e0301c291405c9542e0311400707100305d010150207079 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 332776312 1250 332775062 332775067
    0x1413090c120e21070b0c03010f080a050d051b0613060f0c09060e01030b03070f0f0602030304030206131a071d01090b1602010203120903031b091311130902 68
    0xa210203040360829400024045040204a0090840210f04082810712610b5010301d84240014003801501a10a004003e40b0190301441401050703e405581280c00400300c0e0f06c0c0b02c58480f49016100c8803c104014019403048180d850304038090300c0580710070611800c03804540c003219040b8500d403041c1580d040070400354150a038414821540540b25601c080150280600ca0300348100130b000b11038030700c41e402c01c1003409100454030360b01c00d40250996107002012140450b4a6207201701061070a4031400c1104800f442001a90034000300580788036030b4058002d0880703556072002811070f1001c2d2680450351424046d070001641198002894080c040654802c0750030300c40c2203c86688011140907007410f100204000700705a000754001c8815410741c011854240c41c1451005030701d0344c01043c0d4600750151100003086800380e000005148101c5054100203014403802011864034406c20003403e030401f9400713000502201458100605078000001250300c0c200342d40101181d1698140c0295603281d400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 332777562 1250 332776312 332776331
    0xc02150405041d060411191701060905060315060f15030f060306131b09022206170a020304051e160b03010e041410021309200406141309 60
    0x2446400c03052100081107121200c82000f4182da6803d000b03000030160b40401d41440032039180c210218003071180c030f04d0410300e0517501c0b100d514a03103605000c1c01e100b056290420000b50b0003000c0c01803500400c0090080c00207944032210b150103440000300081c0d000380041c1207000c01d0361150b6215020402c2520361903501e030705283c0e49101c40501e0243c03d2a10941c0208103111405801444150b603041d404213001c41d4007200342e00a0030650450741e00281c4528408941c172900704503100301400c0b08951480000030420b03243c2c1070645007035184c0c6c100f1414401d076000000d520b01d80d241e40150b42050041084441c1488400750041414000c3ca03504035060b0400c000c290120358002c01564040c2c05100d011608644c1404695010302000800160265801c07990b003c0c0181da09000c29140c050b45460155a14011052031150891083c8a40e1078683e00d41140b06c1d00a0384c41032240740710800b500c1159842c2615210302101c0296a0070500100850200180000c041d00200b2043c010115000085030b600b08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 332778812 1250 332777562 332777569
    0x1140112030809060708070c1a15150a0806060705030d24080a0f030525050109030f0c020f06030a02091201090c08030703090501030c11060708060f01020d020703060b010c02150405 79
    0x1020b0310f1000d455000b01c007072221903500001c00c83d910011034034061030451110708000e801d510040d040d810385021503034103116081284200c2a200460b055030f03800030011140d50043c04070b1244c0d6008100083c1040c0105140d49040070040c82d5450040741200e082c0712020900c48101d6021400070712030a071990814100801a1349032400091980f44060034000019444e01040d005401100400300724000a03040201260500300001400d08411080e410010901d0600e000b00842c40d1f0540101d813001048a4040b44a450402011540541302e0f030151103880090024a4001508007140141c0900030751210b6190050010155000000040f03024502814a03a01241311908a6110390304200440d1001c6504010711b03030101e403c04e1a00044060400e102110102d4036840c0b110801d008181c144808254050412801180b00701d4540e43d0560765800103981d2841ca001c1c8542c0983c100e0074041011944503848451010010f050001080b60a5400030350368003500380e030766802c1c0342000c00c00340a6800d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 332780062 1250 332778812 332778827
    0x80d06081c031107051b24180913060905030d09030c0b010e0618090c10050a080601210513080c070e01091416021c0c02030c03061005010804050114011203 68
    0x20603082d28a03d404004c1d00d030301d9210b44001c00014846c0540c285481900d4035400d07402140403140180c0285903019000e1210b40315880b15000c0450f000d100c0105804910700700307a0f01d078000c103410044004c0340707a000d0b59241c0107840e1513502601c01d40400d004280c800703035031405405000c0d842507440400302219481d203105101c1040e04004e9041144804004540d00d03222803001e10701080d40e58035445540c5001c22b891810441c8011903030010101d540141290760840090f000119058840903c1d964600d00110341400324902044074805040041400f000141e6100c5030b0880c0c141a03079407030034403034540f91102039620004a4140c140e0100404010325040303040c100d4058000c0c484284100348080f0416007804501401c480104400000000c182034001c10040044420110030030112200e164405800e054810a05a0217401a43c00415691401080786440340b060140c6000c0c51034103020044600500040040381d80c0d65895400010b0980091080c4c0c0c020300c91509000c01c049642d240040206 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 332781312 1250 332780062 332780081
    0x70806011202011112040b0d020c070311090721020c0a05032b050c0a1b0209150a050d020a1e08010f151d0105010807050702060309070302010314040b04080d06081c03 73
    0x80c0c000b1021480380090034170888040fa560042c034161031740643d46002c2c00901c92a42004054842c0c00000402c006500e80f10410003242219510016a18094141c1e42c0782c5d40300c011645d102100390720060342800d895014050200f0494101c0740e43c201d40d07a030340c9413640d400f0800080c0041040d500c15007501211300c002020001803510144194100a900c071140341c0034035650801808241900c0c10881900d6000183c0c10a80007002450035041030620101441c810b10f140c80d0144c0c60461001c02c0f1814500c10804000c2d9002d060302100c82e00d010340116100001c0304902c548a880d841c000030f103c0d042405203100b00310015800050101c0903807804650000242d20003005524002ca204250261001000341103c00a0a04020a42d1000300c112400d1140440082d840b10740030042c0821080d0000c1c1c1030003582e100381c0b420068680f82c004880351318802210020071304459880080d0014120328013a101d508400d58022900b40e0310746400d1400c081c41240074080740d44a5000007030281ea1306000700941f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 332782562 1250 332781312 332781347
    0x1031419050d0f21060f290c011d011410030b0f0a0b06070501020309120f0703030c0c06060603050915091005060f0d030503010f09060e160207080601120201 69
    0x505506030369071520740c048601c1680900c0369101248500c41c0c01800600c100c000c4100d004000c299030f00142a006040354028031009120b65003000c41c2422011580c51503140c40000c28030a505801e030503d04040e8030460022400d5521501e0020700c1d80340c1c2212040011681c2000454908405508002c803c0002050f040412070900b02c1003000c43c2c5524900d540280a89000c0b0100d81c0d50100c0f25400703050a610340c15003010b40002d60405104040d400f442c01075950f1800d40b101d09068050f503004ea8014040410349400302080104002400f170752200140c1103160905840601c000c7d1240340460310b03250300000100c4c0c0c81d001084902042480580420006800110b5060910a4001c0c2d900d0009440400d01e460f07607040844c040d40d031414500404501e00070181c1541247c02d10b03004050b0b0700288203010940c1d0200b030307000c15442490b01402090b107282172401101507075966040780d8001c80d015509010350044c5000495030701e0b000c0c480d01d80641b040e148005980c140c2840010111084500108070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 332783812 1250 332782562 332782603
    0x7020a18050c0313020904020301090c0801150e1b0c0705090c0408010e0610090b0105090306040302070e01080102090303070303020a2106080f010204050d0f02060c161d04030806090c0909010314 85
    0x15413100c900e4451074034a0301a543c0500940d92803012070b006001445025208512a590010303002074150848031a4100002c0046880d03591011040301d00740056030f200ca099803030a8802401520146c0240c00701342400401c4450f5070741e40b007001c80d1002c007042c0c80fa0303800c0d82c0c0001010300252009008036410f0b0b1040100400c5036150400c510584030394580200c072099078850412450607885801990040203004082d0f522508082ca40a13684040c40d100790082d1a405a00000f804441031003030710152200a00076515081d507603036085000f540321011540901c082d41050450200e005041034800550307a280005001c2c0c10207d0b81c1b0300d00880b51162800310b81c0100400c4c081a191040c1c080811a8050706000b182540c0b031000130114090307126000c040d44500617002c40b800c01300c0514442140c1c081c1c20803a40720102500501007102e412500a404200b4140214069003401d84210303900055240146060800344400100746600070780c004c0d1042c1540740b1901d080c088003032000700d080340e0b030182c0e101c40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 332785062 1250 332783812 332783821
    0x504050f27060121020a08010806070804060c12020c01090b060d080910020c03030c15161704020a0f090906061401080c090406030c0315112a0307020a18050c03 70
    0x40c100c1500c0c107034081104198011440d0399004104507002e462945101007900e0358203040000080d0451641180014409400010031007800305038140200c00e140d0704c101c2182d54a07283c0760301803c42850300c0710030403850400c2e60b54607580f04d20241003180fc40c9030000c0b071402c400e4206120b4404000d031509200701400c1c2c0c00b4100141c20f503011108920300a903200981c080901409904003601640342c070780c15000c0001c40d00030048000c0352501d043d110500b1034007220b1b194509504070311103086a80c10042120b000c003006080a0300c444a0380d01038070062410400c16202c900c3c902d002580d83d800f549405890700344250803c1014010000030704001e2a000d51010100306c002040990068443d003000d02c80043ca500c03c645076600100c000d960400008401b5958a20740407403094601c100001c105031402c2030b50000c1c070340550f00f150355001c86041c141028201c00000454100d000341d58918052000b08030500c0140c61f1550b04000400700c08028443c0c4016500b29601912801095001809002c00800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 332786312 1250 332785062 332785099
    0x2010c0203220902030f0103140604030e0d02130c090807050d03080408180d030c15051006050a031b090f06090b0f03041a190b09040b060d0c12030504050f 68
    0xb0b40d0711200029216110388580e018090008001d500441821800041041466495041c00c40d0490b4810741090075541d40e00c6413050303142c40d0306480c0200015070210300705004e85002c205000506000800c20340998158104843c11100c4880c804800b1410001c004c01c44000c06021540080100b5200c0140741c1000b558000c1019100400040a0b04004901442c0d10035101100e007804d0400944521194032641c2400f515800310031408079600f60112022101f8500140601da00a910031403800d009942040e501755119040508202c042640d50004002d00002400c0e440020f02c00507150110060304040540350302e208550008800d00505010410002c00080b0440d10081d0403460655100d490301e15042c40c8100359603c0140081d500c01042c008030341d0420007010800b2862003001c1000c2c0444000344072032104100c401602d80f42d103420005200341415151100024400d29a01d8071081c0c480000c00100d444010090700010800310302840681407100d0f100c01c0900044866011109454405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 332787562 1250 332786312 332786317
    0x5010203030f2701020a0c06060605090d030e040b090a0516020d140703030207050609060f09010b1e0303120f0402040f1404110406091a0f0429010e0a080a0c050102010c0203 76
    0x1c81c642c281e60900d10303800c4070003e02072462107011410001d56071100f40c0c640c000c100c41c3c08402c042d54040c0c43d101001031503900030340450f00d071404007a001c800a0040ca4400380e42c0c08402003241030b0080d07160003e21003990341d8028a01c1c45404944000956405d0090303d0082c007003020040340c000e40d4043d203400c4411036003140e03c080182c0c20210000303507284038601d0120007170b00480400900c07910400c004c0c003048100c0440d8052160040080c8400b02d50b036100c2070182600c0d8074000e80c82d00100307000c83c091807690150504502094000e0110b030715040003401170500d0080101c0700502404000e40c00d11046152500510500e041168000c2c0300301c071210a081c80f500e41000e0802048541c0c0404003507201d480d10b401000040202010030010400880451802880f074250183d1040100d0400719a082c94244162881c24190f00010201e00341604d101c0080b40f4407446100d81809800030000c2c0c2d9a541c5ca40280015041e220007500c40e040061038202c803030400070b4000c1c9041d641415a2408416400400d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 332788812 1250 332787562 332787571
    0x5010b040c090e130803090c19050f010e0a120b0106020d0201090b010509130606080f10020a0905190b040902191d060d0608010f02090306070f05030a0902120d0f0905010203030f 78
    0xc0038030442e04d80740548080d80310701110091441102004120001d500400c03810143c2000743d0f48056504500c2905995070300762401400e41c040582c44c60200594410300030301c40d20303901c050000c2c5980d5448680303040c86090f800d802200c0d51000c010040c4204e55062220b11380700313002c41c0028000550942c2e103844500b0014041e117030145200f80d00003400c2124088402000681121081100b2034039400c600d074880a0006072820720703100300040320700b81074100c4c0308840d01c916060360b45060003814441005100d404c4190b5125014040600104412140c0c030f0080000780080100140d80d854458107a90500a4009107103081c0114442900b044070301c0700700c0c91622404200d0f611583c40180021902c0100400d4101410940c1386c100c0035400c90f01c5a50082c28440343c2101240d060380d0711802c1c2210b007000c42060290014006201081010640c4c0e08290342291000304016803082600070301d64501700c02a501100081c100704070007030125400a0000000d0082070ac003861071442c099013035014183c000741 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 332790062 1250 332788812 332788829
    0x160b07080309030909070201270b1302010513060e0f0f0109140a09180501050115090b0913020a1709010c050f090f190e060603090a03080405031606060305010b040c09 73
    0x3442c1144144101c841025000701081a1800c1040e0020f00900582c072000344403142800c03000c00400e410081c1d03560419400301c0c44500719594443d00d4400044805022410b114003030045c024000d10010b4288044c007415034070000c02c01e140b003040050000d81c020b01280540100049004544d0b4040d11031000d4840080044035110440d4000c1030100103543d000f400c181d440c005280e007041750600d802500c40c0c2c2c0154000c1c0300913600d030098584409400c6990401181c1d000004024024402c000380c103070203070010f04801c4041c0b00c13018800c2c217980c0502c00c2032001480c000007107001d0481c5800031783d410400a038000c100360106258090315910841c2400c400682000c10b85a03800e81c0c3d04800f1002e6201c1c003030044c00c0920145a0003001c07084c880d0045a9070300e503a01000a50303c2c10401d00b900c3c802d820441c000c110501050300d050742c0d100d50140040d00d45000030041c041160f8007210088904030300c58030000602d649142006800c44016030419403003541404c03140303503c16a214410b01d05480e902c9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 332791312 1250 332790062 332790067
    0x403150504080f0403062a08010612200d0c05090609041121100501081302010315210302060c04060503011e080105100905090703150f1d0708160b0708 66
    0x78100340c2e10501844400b00604200000e001c810451541c1080e200c440b803801d820798910944005c42042c0c208a80c084d80300141d8500010420644140c4500031404c140090000e040c0e11035540c070304c48a60341c8900141e541b030800150801550f100c1e128407400403140307180282c1801d204000140091103141416442a0740f2071643c5440005540203c0708070a903600e00c40c0ca4581c041001809481d00101d8142c801110b1080c00015294004e0740c00d030b8404c96041c0401c0d403034444698019001446402c009401000c0800b80118007006104041d6460010310b0000768829001c0303140091412500828002c000241031104100164000c0700380c0741580c40c2d080c01c81a00c000c00c4103040081380d20039445180c0942c20201801000c20802082c041641c0c0d282009201b603070b8660241d2aa11942031000601c20140804000c0001c0100e41c030095a2540608003c00c583c6c50030031a500714011441d8004649800074103040005500801c03c44c00c080300140301c0101e0b150328040c41400507010b000c1d406401d44800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 332792562 1250 332791312 332791321
    0x10911010e030c0a030f1a090c010516020901080f070902040e07050c030f0f070b0a0c171e041a07090b09010806131a210604020f0a030b0103030f080c04031505 70
    0x140810800c10303d0252401054555a060215090711880070550310091111a1001442006194244100d005034020f09022203150011034580d80514451303c0c0a01c4064150300069031861445402030081c800107065801c0101c07641130800d0400e034042048030f41704000801c00038031000c1c16030b6444a11810529115039494000e941580709003407070401d0041c0c0028014002d80100d0303020f88030640c00380b90b01040c44d40d5074041a108882d44100a08080340d00b504118000014190070642d10448003a40c4820200440010306150341c001d5408603449107041207944e054184d50854158801d40314903240e8040d1380f42c40920343c2c0502c5003215103030400003074100152a9440d00c122606100f003500f00100504030126041200d8180301c2c00b01244221400079541b20504016101000c0d1194000094101501c860b820402030100b0070001903080a61854000041810000403d0003540070791115110800078070310060540000401d811a000401c7c0b100740040f485000445042d12804040020075894 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 332793812 1250 332792562 332792569
    0x6030318060903070e10060e01050c0a151d0105060f0910030b0702210903010506012c040608030a05030703060e04030f270605040911090904031b021305040311010911010e 75
    0xd01e40006180001910a104200c1542246d100440703d00e5520f00003d0b410441c01150325101d0320a83d104198010900400420800607401c0e90388003203103000081082071085a0090b40b01400810341d81c0341d40d02c00800a035403e1030410010000c5003203c044c130440c60031130b298400c01c40706c900000d08047c07600e10010319020f008029a034994510007582040340e0811080703400080e03011084640c040d5003010042078043d4010480401c0032503004411114442e6030043c2031010940d60700e038181e400f5480d91000200031000744001c002c1d42105580741c9650b4504608007a041c0c840c43e60011154007849010007000c40d62103007007803840209905c3c1c840389460307514141c03140e03841c50000a107251314001040061180d0304a03005108840102105101d6250281c04075980e90040080d100d403c2480800020700203031107a083c90152a100396045d071289080307500071a844046100010174400e40d00d005210500d40c00854030046400032400901200310079650345248600792a10b200d051044000101d03006030f5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 332795062 1250 332793812 332793823
    0x6030712031b1103102d0906150f060e01021c1e0206090d02010e030708030403021005010b09041d0d0f110123060604060507030f09030b04060f0506030318060903 71
    0x80b8035000e40580e050700b840b00000e1140840a03120380f042d400f4000c110303c92030107a4200f015408940101307401e641400307900b9400e084650200300030359400b03034840040c0f450f20640b08070f011488402c410460602110600d00b50042d00710000744a280340c204059680e001031041d4048100220400142c8001038041d9100354041145500b400d010902d5503203015400913105100d115908112141c1070a9810281c0c200c8034241c6203980c06820400c0143e020540c2c010023160094440d1040b14005040070002008440c0c0070b802c041d8542a00060001403481c1ca801410340542e265144008403580d4140030950350f98900ba542024030480707215215146015084410207a41001c00900040340083e084801110140001d4941598050041565400c017542070700c05445180d1215480c1400700d0710241c071070720038106d03c260402031b2254010000480d10003005014600c180030105022500900e0300054901c020f0200e40294824460055407440f0030044084600302075850660314203032200402e0404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 332796312 1250 332795062 332795087
    0x1815040216021305061009030c03080f090a08010c030f06051806130c2c010801060e040f1b020c041b051b0102070f1a27010b0a0f0501030e060603071203 67
    0x43e0b81d00b60300c20388109090300031510440040756440500c3e1040380e400d846401e540d01000e0428088250280009400074000303060380f4005c61b1045051003a0800003070504030460f003020007030b03944492504d82c089030103003c0c0d0195a4403400b0203010b00b6040402040002e100341040044200720341c000300d01c813070b2288503134107150b0084090103001d1083c0e9401c000c3c04154fd004080201da44c13040ca00b42d062004041030003019240143c1d20018264a4a0400c541b14064403802c1c5034010782d2100f120010300600c1c452041c9420785641117007034803000010003a00b80a41503410b14000c606007400781c4000c2c0d6102176450f0042001c8d061a5441d401202e180d010444646803540c07126601c0040c102e03007440054101012014071515000f10a010299605800b042cac042d42d400c1c880482c01550503450407606490714211042030400003c10305840400960b001c5541c0c1d0040b801d040c5c900d8002d0140d543d00d4002e0440c03401d0807a000b801282441c502081d0b64200301d115070351241c0810718007441018440c59a04050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 332797562 1250 332796312 332796319
    0x618031202072c0a200d020c060a0204030816060e0304030c031b0b0d02160f3002060109090827011d060d0914011a010305060d030e010e01110304080c181504021602 72
    0x21030506c114614020361010217180034600c10b400000320b03090090700848041d240e0003421a4104041008414010019000200c48007601c84048440205003000900001c1d0b0054032644005491414000808103208022646a01c0444d006004800c18031040368031400b0088401a66006030625126554500000052881011501c1001408950903500802c0c0c86030014a06084a40021485450382e150101501503080500108030a01041d070188964a010301250307464007411410400740803502d0700245801100d0403d80c030282d0350307101d1078007160042c18188a14840c00d42000149081c0139100b6410402500c802c100303400c020030441d4038044050240005c2c000c91040c94209141c9904503040580081d28100001e642803626107400001d01e07400da110034020320107810044550780c2e8002c0c82d96060182c43c5540040f54801040100002c1c403581b005071550140400c1001091407600b004242585101000d2113000405407003440d00f805000c882c01640e40c00315410041180c054400083e51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 332798812 1250 332797562 332797567
    0xe0918010e1b01020105070206220609120c05060601020d0801300507031b0315050a1b09051c12081005090406020d0501050907090618031202072c0a20 66
    0x3910b0342442d5010704105000d800070300155848071012aa28036044031440741203404038441c00328682d541641180400c4c094900465045990785510b0a200ca2100e030030701c0010603018410b006c2c07120500006401400c244040c1000c2054468000c1c1012018002c1c6101446001d143d00711028110743e100300d11403105d8407000c2760b200d032600380030f91640c0c280c0c4001d03a00140d07550004120344031400d1402090f81d42c4000e4070101c008580d005640202002008988500d80d00e00034089502560b031074035162300070903543c3c800c1030605040074000440e2000481801c049501641e90300000d80f40c0c0b00b00719903c03e091810003840d40d81d801d0041072b036074425030019802c440300c0d50510090000c2900280311540c60074605100c02d903642c2c0180100000111000d0300090b000120900602d80305052752170691110310304003503141d82c807521070b0100055882620030142c2d21400c420441d00aa1210000710001c20302e929000540d0351002c140120540102400f03110381d0f0f690450700c0c1d220300401500061804c4c0c07022464 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 332800062 1250 332798812 332798833
    0x40212070602370f060b0d03050a08090705040609020a23041a07060609290105090d0807060f0207020114130e0601050c070b0414030f120705031b010203160e0918010e 73
    0x2c51340282c00a5890380d08080d0010707600d061881d06400301c1a0b1641d202c0e03192583c00c00d001c41c0c40760f00c00340c4858030030700581c000081d8560784e0340205170143c5020301c401a60307101049805000c0d07103005c0c0b90710000c4400d68042103403641041c405071001c49104040c8143c5490540036030344424411030b000200681c1c60500003040070704141e03001611000e949840b1400b001a140c10615904220841d401d0015a0410034000725040605000d0501841001a00c0c1004116520607003990014204e100d1200d5000c640001990b920200420000400080300c5180c9844081022710b207844c98055200800000c41c0030032000d0744110100c503580030092044e10700254946646803200e07070182c41072200c000c09a03211101245404078009008409900041c51090411701d020550780d0000003080d81c0600040c0040c4c0380b900846001420580e14000005940340340c0414004140b000790312142003048164001c800050700d80b1a043d0303401c400c0800120080c660351400c0c583c00361208008020081c001c4081c0740c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 332801312 1250 332800062 332800073
    0xf2919020d0f020624030f1024080c04050606070f1101022103010e04020303040e15040f02090d0f050115030305030f0901050601120906020d0c050304021207060237 72
    0x1100c0c441000c1c0d0325040e00d1500c0500c2280e981900381e178207204608000c1190350869002c0362040d00c079031001406a80c03000c214801d2070f50034040309915100d0f9454880c00281d83c80380c03c42c0c4480704040004140c4035016803d04d19025510480d82d4001806641d0f03580104460f40e80d400181e427500d5520401460903002c052422205482540d00402c0c0507120383c1319a124072960802c0c0c0c4c422404102c52510341140e2802c0c42000c1104000340051342c040c0030410000c82c003c11414241d901c9035030404c059503043c801800a1004030751705214000c0341c403407041c0004d1040c0c0d81c0701818078103010703003001101e01041c056003007040c01010b0b580040b00c0382a40c4614004201038000300030f540701e070000c00c50702040c0c0c0c3d5030b8007250750aa41d82241c4c000d002604143d4a4140c001403507010329007041c029140181410a400320000860719428090004a04044104002c40c6000c103040e01640105030068902686070501c06940e42d205a042003008204032005900485000c0e41c0114140b211204586c0b500003207801e00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 332802562 1250 332801312 332801323
    0x1504080109170a0e0f0a050a0f1a070c050f040608011b080f0103110d03050d0f1a0d0209131a010b03061009051003020a120e07050a0f291902 62
    0x111000a00c2d038915041e41c0c01103030140e03465031940c0d40721a94203071140000c10082c041c4150895600c03403095080071429440e042c2c3e20202070990b640219a00d5400e220b58503d005416188000340d0b44020041500090028024072089a030141c550802d100c81440000c0c018103440d8200040720362900b040c44d0228420649009603030350080d11074404c00c1c1c580d40806050320f0004d00002e000356001c02c0300f501c890705050144c2540b480c0039103400b5060411100700c28007915184503807000d0142e115151190340c20841c12642541040846150b046044180c1c0482c024a200034424400d1060444a0405101c1c402e404481208200010443e1030b40c1c40e010701c40ca094000f590300350b001c0c0c0e81c0c040b41051054010700030340c01941c2006040c90a100d1b02c583e42200694008426081006605403c0e45800449801410070315100e031000341840d01c0c1450103000110300c841c0c0c401540c035841c2601c00c129140082c0e410400c0800b0340c082d411114245140c0c000c1c8648101000683c03102d00000084000a038041030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 332803812 1250 332802562 332802581
    0x2120f0c0f061b040e060f1c200919050604060911180306010b0403020906060909042102030a050d020d0b090a020409110906190221190201060815040215040801 70
    0x4183e80d001051070600e200d107000d03074000d0080012103000441c10900c0c0030000f00d01e90202c0100441001c41d2220070840340001213804c1192440d481c902180000d002143c03088041480988403145a80b83c2040942056099240301030031881e030318000304040303450b82c1d0040c4001d0919403a0034090a002440702e2442c5900c900a01c400c0201d04003100c40e00c920b40428114100c41c00200c5450405040d03030200308581c1005001340781d000404004000031501c40749803152040c4d01130071442e0008071680000c681c000360b02401c420119082086100c9159400a09541280f104050016101e0424003100d80083c0400910250b202200b01c042012001060b00100182c4980e18010300401c7c0320711600311914000c01240e00e50142d014400f0100c0d0b4400c4021000d16404c0303a104884c20714240b403105900891404038140319800340020303580803100700c0c3c64504068a03042e00c001c100302460051100e4891004204035000d6a1500e004101552344011410184c1c502c0c91076a80d86e9103545000c014024214801d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 332805062 1250 332803812 332803831
    0x5060f0414060910030f141303180602071e08010203090f0c0411030114190b0d0501080f0a0b180d0c020103050a090305090d060e0102030412090b04030302120f0c0f06 73
    0x144801c686090680565a11140141c00d649540031003190135005400ca0001e0014080c2c0d8545030700701950280300342c0600915840141445514060400911442d07507103213044454207800e8410403860b0b5002820300300301d4a26500d8503002d1400401c00800f1310080742e2140c11303e50b001005100170a40c0c00300c1e00355208541c490860715420019800d020070b0f90602d20150310710100500c0104135440300da900408030080c0007050b0011818401d609000803e20300d07003000400c0400402e1008a0300d0440c841c0034050315040006040e08000c2811444e41c4002030400100341643e0070740070075000c240c403e1003119000d0124050b0740501407850340084c004a41030009900107403d003000b00310082c1c1a0710801d400305800d0356400d8036203a2580700780420a91161011200176940b108911940750081c40518001c900c151031300000900000b030010804070a80e0000d50200d030081004100091b000600c00202d5000020901d4a4440041d02c0d20541d005207041e0301c04600039111201440300c07010405900c50b03011032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 332806312 1250 332805062 332805089
    0xc0604242316141e1c03020a020a1401050a0f0b030d0f0504030606060f0305010e0601090312020709051f15020a0209070e060307020f1c05040506070521030402011b020f04090c05060f04 81
    0x4c0460351010a01040044040c1150a0505c414031a80003400c15420300e00407107207e082569241e0805556198982c0007596403201441441c8807980a400c1d5030a52001c400e116441a20300003984072515501602c00380852224851241405601030b1002940c2003501041201d90f6103d0161007002c10300c5103c0f001a107084000b241c03c40c42c81c60002e01420060703584501c1d01c4d003956990715000a1901d168030640c443c02e40c1c000707aa146540507161080c2002c82d011000224000e0280a51390119041000c429070a10030f5442440d40c0061712443e219011246402d4a880e02e401c00e8420010021146400c858000208440c2980000e141103003503161070100c0300d03074294605030703820300d500c086e0b803441c002a1040004001ca45441406402d14501136800d40303140703203580d081d221648410003041203101c2c0000310030442550b030004690f046c8000783c6c0311500d05880403035002070602c00200c0c0c52720307114640d80d0407244244041001100301134000541015a241e94403c039000050300700d48035000010740d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 332807562 1250 332806312 332806363
    0x303030606020610031a0a201911210d0f0506010e100e0405100510020a060b010201050112020915041a040b0d05060f090c060424231614 60
    0xb071010113040300e8118114200b2483c20503c281015030300a051514100c1d01d504a0307000303400c21402003807014204613a01c56070328041b08080c42504240d1034410004c3c010000c0044023030400200302d503000c581000382460445418042d5a401c1030280c0c01c46045003d1521960401d02240782d0300041c081c0d502600c810310780c1131003030b01040300c1e288841385520009000002000b0440c1002c0d0403142c0c11004e4510f84060158841000c21091148a0342550040c0e005001e8001800114807503942720200a00c028080d0b581802450300d4a6004680b00074001d448001c0041e0740344216182c3c252422200030070600492003045030740410f00f0082c0034450f115070b141c00c50450303880c5411064500c040798080041c0c07656549040062180c408020941000c1c2c0c0150b466262690381d0b9140200007522807400b031040d88240380703240d141f18450907000d92414008910b00381502415000e0880040c04aa25029036482e0807404a0315080341104000030807440c045944e4403c08140450b9000e8480c2c40c4201c2e515841e500c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 332808812 1250 332807562 332807581
    0x3070b070e0a0b1605210301170609120a050c010501290c060609040c0e071211070f1104090c0b090301050c12070f110604050607080105030a170a03060f03030306060206 74
    0x558410071424082c01c108554245080c1c00d6001310f03060150742503560101c0302208100c0c10900c1103900303506940f40040103000702c041e0500c02044000755000100241d00d00032606079694000500302c05030020010442010b050710400485504001e080c0081c071080d607690b041c1e008841ca130750302081030916224440380008903200065030480508840200b0301502e23031609000d0403280180c010f440103600100007040b1004100c103400d00480482c2d88030981c0a6000c024042161000142e04180d01c1041200d8000318100d00307030b05c17540c4c41d1300121900d4105503040c00050042c50f50309001000030041640001d8032112800c081d00c104601500240010303910b07140d1103c0f20303200d0317a40c040c21030801d07207004140a507201e0398030303843c0601440c24a036002c100780002080c41c00108403001c4039a940103c0c02c03ca1800ea00508141c011b050550080070700e155075607030390820303840c0c54a40c0103d56040410515050383c4070360001001050702c4403050f050141c0702e0900401038200d80c09a80e004d40300314404104400c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 332810062 1250 332808812 332808829
    0xc020a230c040b06041205030a02060609060f2b14010f02040506030a0e0118290106140306040f020415080c07020d121e090f0b19050d060803070b070e 66
    0x80d401000d0107541a9000420005100b10682250404d000f03000205002d0002608642c01c94000e000440d1111034650000b031401e1002000709014001500c01e000f002c0d241ea18500c0304d6008200d4000400c0da0f00c8c4250680c1c00e5284080c403035030760541070441409000e4840094400040103c0003407100309103a9038840143e01c1140b14040c0c20440400002d81118a13a41c000543c11401380000305800d040c0300720411103516440e90554024400e2528100300e1004100e03822030044880156a41c1d039854100d0241c400e00e100380c08840c012100100044640d503482e0300612444103024021500d4070303101d00c100d00b40d8541e1a410361021944540c0811000341a59003981c0e1480d6000384946003606041c1e441580080c090054203082c4101d0000e2035154521102c04046c10706101d9507042001860b200010300010010f43c4890702881041200b884a003005000d110804c2d081814100d0340c40140802d0f1000920099104280c00d0001040c0d490812001d001c1050290605e40c0d11902c150682000f00001c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 332811312 1250 332810062 332810123
    0x211302011205090c120c0603040c180b010e06070c0e070801081510090c030902040e010b010e15090d050a0c090b09160f1803060504050a050114011d0c04090c020a 71
    0x591081c5503103420f900d0031001780e480c1441c425080e5854140000c1c003080303c1e0b41042d2011200149000303024410076843d03200d241e06881003004c050180d44691000a00161007030440f060240500089510030b001204241030010f15200180e0900e5150845000f040b11400f80a0f02c141800781c4007200129183c21007903d80100000c6007200740491074090014010414846800e060507101c03101c01c03003d43d40703c0c4a4078902c0c4c9070410000c6910151180010321418000b000140326010306540000283d040310f041d19441c51042e0b80000383d143c807600349545400403000c0b0081001c00011004120038080b604803840014003507414009a440c2c030404c070381d50303441c13039540000c000b0300004507540d0814410745000e18900401141c00500d1074583c1c07101016203a048078156450b5121450450401209120b61403605440034a49400c55042c80074441040c0ea460b00000d00c641c411002051240f8220030848000b040c0c0b0307980c00c2213000c019010103503c94041d140240c0e10b2210f40700420b11880725614002804 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 332812562 1250 332811312 332811331
    0xb0a030302031c2c0609150a021308030c010204030b0f01080d14040f09050f13050303130303180308090c01020106211a07170a0c14211302011205 64
    0x403d0740303058010007010b106518000c001d41d252044c0c4c05408083c0c0355004d004504146142800c040b080c03004524201c405080e00c081c0d50b01c0b060812035982c00b000704080c1c110400c0b42001d03a076004030400c0c121803840c0c02d4000d20b610b4003000414101c1c07200154003e20449101d1a01691310b5a2655400364401d0000d10801c14150401a003900c041b0344250170288a01c00f420b1005820302d52100305002c041e50302c039040030804a680b01c00780142c400803003a0582d4465101c1140802d110020340d1941d0700da000140c100c1108650007446041018044d800a10380110346500c4d0304110307152401d00030004801503c04d43c4c494000e00c031a01d61154418001c2c40240d0b1450103501041d2100e00d0f24500c1944103000c0299103548446004504c0c40746520350702c50003001c1c1969140804250700410300c1071104054a60b940041c50841001d85640e00000c1ca600141c1002808503141d8096035042803140c020030150f00c809170710304010002003280407aa941c2005000ba80d624082d008040c0c607040c1110f809945c0c0188 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 332813812 1250 332812562 332812567
    0x30a030c0602030406140702010e12130303050319020315011709030901200f0c13020405090c03070c15050a0f0603020a0e040201120f0903031a0a1a090a0b09040b0a03030203 76
    0x810002c0d0010350b009440b031400014205180001c01034090400c0c0ca0002c0144d45555829a14100c01c02c4898403031051182c00910b010810f40801d000450b6903c4020b05015020000801701207042030a4400070311000320541d036a2404081518400a0380d284c5980800c114000340c603201c00084890074400c101c0180103518102c9140010f4540303408013080200d440c07021440d25080540c05014400c003801000d0003c210310400c3d84208029005445042064140705101c01c00c00d550756041c105402c02140d490095503921081c40441e03001c0100f1401415000740c81841d10440452a80514842d105d910810010800000c4048047e5501032001a41c00b10020800344103031280d40301c01e0754009205042104c1010360340c400805c196800100003d038075a03590000603061640500412449846240c10030002000540000c0d541413018001d60101101c1d00c814586c89542e0f101c1292030504d001004410860354548a8200d0303580240c02d82c500890400c001051b0300c1c2440107924080d02d030f05401850 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 332815062 1250 332813812 332813837
    0x20a0903061107050307060603020114031009020a0306050316060f0c050a02041116030c020f0105120f040302031e03040204140103031d0102032803290f03070e0c07060b030a03 77
    0x100070340200c552690810404003c0d4400160080000b03015541c80b40307030302103841440e50002401900c01c0d4014201d00120420030450070b90921004017055503464000180c4036651030108a0051000b40c000a806114841d542404104245a6031086841d26900c007084d0751840c08003203070801040000101254403051010005142c250404908094062270060803c01c401d07104140f0106a040250302080c5203003941d00070742c18654004482c087e02800c140745080c10000d191011020010703c4140e880c07140c0340106040601c28000ca850a2a0b40f08030f0000c20028010190450b600c2502e003284200d282c02c41105414003a01d844504994058503540190301140301c0c0c100c2e80c401000280c07411030104016802c40700642c02c0007404042110000e010104561140140484120080c41d1000200c4644000c0c410140060141110003050b0790341111407815001082ca004a140c200c000500240c404018075040c140c806003016500811003400201e2807041496118a503003131f40a000144041c40c0d50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 332816312 1250 332815062 332815073
    0x70204020d090602040f091a0a0e090c0306010803040e090106030b0c0307030603150504151a011b0606080a03090b03040308040f1509120f1103041203110601060e13020a0903 76
    0x2803081140141c00450224030319503c0c44202d034040e42044c18412040182440803102500c5001e40c02c0d0000811030040034018000248080a00e1090014602c8868000350892000340007480c4410700150885a25503143d00a4a0f2650840d01405d60320b02c140000080380b8071014064441280d4011038004d280d41c540310046c541c40d40c0018107110a0580f2071900100050107000f460011101060b400101828203203041a45c108070b07000f40210280c24400c524078030b9180141c21403004802401e14003e81c882c0e03821100c03400b0207105c4015210324649003000400c0407002c10a60f045231311070703529a071003070b911203070018001d0100303a0b00030f400581d020000500140c40007102010b0a03004165040204c50701c001c001d419141c4101d0f044030003518800045071095040a00103c560302c85050483c90b802440c14582d58900403481400c41c0440d96a94003410b2500840c103002c1800281c0081c0c5e401580c6a61018160005c0411114000d500d48022035510250a100382c8503c91200e58032054542e103180c444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 332817562 1250 332816312 332816317
    0xc070305090d0f03120c180b0313082106060703081b0d02340302060f0414160321080a0c050c0a140610050d1412040b0c070605090607020402 62
    0x15041051062001d0100c3c00d4100415600e030b21a03560040d0800b1075000d40c0b001d17600c1c962090018809000d50000404040c1d25940d004c0d1103024410303036225030701c100c0041605407c03410003418071440050300b0ba991301c00e031480f1001039078000f4140400e20b443d103c1c24060940308000019000425490108540c00314202d409264030a00c425401d04010010704550101da0220342080100700c40142096408041c50103a499843ea100a000440420944001e0f449200040400080c2c03c410740008040003070f55002c5491a2415100319000030882c290039a00c41c5555020030346205240c2100308103090000d1540c02000707031540e502c00202c1d465400c200e5010b05608903850303007408010b00443c00598410400c3c070000c6806005014040c402203040716003070038005880114901035484050015840f4030781c0b042c6c2e1060703000304044d00b402400081642481c00003004150300100000700043c50590b500043d180d0060281e05698045503154410b640500c100c1000c3d9820100600905015141c141e01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 332818812 1250 332817562 332817577
    0x9011a04050a090c0801080c0d080f130e2e060e010309120903020a0b07020102073f02120601050108061002010e01230f010e0a05151002030903010b06030c070305 71
    0x28504040d01e40340080d200c10020341240c00e003565120f031080c54185e80700079a5070045c064440509a8079100d4004500048a80000645000000100c040f0440c44581c110391507038641c0c21505814a45500c84084009805d83d02203a0420315000b09421107030070300c0401d405001c4500002501300d46000c07801c1d0761410044d12040d0501d540c030351810000c5032700011441e12142044d0b445901c418194810001410f00c0381d01b210305820024020200140d80001e80c51007138070965642c8042c000c240e0f46200c200f40d00d00b9400940843e48040502c03182829100312491524421201c00071400c00c1422010354a64007403044a0010b46180c01242003070425036001c2d60400c01c1803001082c951319401a00b400d5400700042d084400c10040c81c0d00003240e10b0515400d4200440c03aa200080b9490405880c039000406081404416521800300d61291250810310464242c060803a0465500250020352660002180a4025400c18241d2400782c500502241c1c440e030700022142c0e0038445251811100c0b83c102c0d08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 332820062 1250 332818812 332818859
    0x30c0907021501080c1201090b15060c07080d0306050301050610030f0204030515060102150129070f06150812030406090f051504030306150c0b09070b07110901050303090901 76
    0x4050381c440c07111110045004e0300706240146600410001404000300f4480140c0c0035507454010707600d0000b501414540d410034030311451445190020070005e000d40c403803a0306010f464490355034005103101c400725136240125410b0701c0c104440380c0d0701d5042c94240c40040343c01aa105d03000ca110300e030b6410f010b5403040b481045e000c9401030415490765640d03490141803105d00044100005e040110541c3d040040c00516030690341c1d440c1d400e5140c16940121070254241180001425034842260360030400b0a0740c1ca00d0390441e440f00140d1a840c100140205041028146070700368600c1c011900c40d40005407003254031740c1030300558510340d6191070313040041804040c2128a200d0065136030000c520308000d400c0720202d20181c0400d4a040a103405400c9444030781c031800b948180044001d030802d4000344030342c2149410400c1c64815669000b0707080d040000315008428540404140c02d01484059160080b80744010344102001e0398850b4200741d40c1c5d0145104943e070000c40c1c0401031100606002c0009500143c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 332821312 1250 332820062 332820073
    0x10b07020d0f0c08070303050315040204031a131a16051e0915040b1206030705060406050309100609061409010b0304080f0903030a0809010b0d0302121803100c09090b030c090702 78
    0x1504c089041c0301c0700398010340000f200032090000e5140b004e1016900300700c2c12102107280a18640e90b0090480403003803004041d502000000740c18107804001d81e4a143ea1000b44c4e80b409640b440342c00701500c01c00382d0780688400c502c0c14060440b10b005800f2207602c0f0748034401c00c2c1100303844810340320710603400410031a800c1070042c080c48082c200d100002e0409800454035980e1a10b151440240002d03c004100c0ca10907800f0110403c0300303495920450301a2039007841c5c015920b5840210040c900028851818040391400740e00065247d5950b00290070368240f90390301e03108240c4100411031004020700032a0310300304041020800250351f400042860441100b04181401d80400000382103070064445800415512820848400703001c0c880e07001707500021103000d070302042162402980c6461352444a044000006582e8260b00e1082d90003024401008040f1948003e002201801800c28103a642010400d010340108500c40c0c6070058400104014005015001074002003012520020306900c00354000ca = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 332822562 1250 332821312 332821319
    0x30a23010617070303080c041a0306030c09101706010503070b130f060806040b0105030f04020909010e10090b0c040303050d0c0311070606080d18090507021213050108010b07020d0f0c 80
    0xba100c404503110359280240610524600300503206620042c0301007202d8004210902c45100500b1228180501d400c000d19185c0d40d0ba4808281b03012000c1896507801400002045044e8500c00f490310151040110301340e0060392040703001075075080b013030140c2ca0341074010b04401d10490000a0141c2242c2c40b9401003401540c0d9526407007949a00b85422000014404008129807420980940e40f104a000e1074501e1440c07825010201004101410003886500300001043c0b0005094002c982d41340349070000d40b414103520020f0200200400c050480d400740100c400129455180e40507201260f40503200c003854015840000e200801d03105e00f41e40c05055a44812031340070002040640000c2c0d02c20040000c9950801000c1e80c90041c030140d003101080a0b10400c02405800d045d0554110703141c060000c901c036140c00c10103a040605543d00b419000501103502c543c1ca80010680904451082e240c91469036202e00e034100061042400180d0054000d6031600001509000b0009584c4e009003120329000d0746 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 332823812 1250 332822562 332822579
    0x606130f080d1b030c03120b03122109030d02030a02040e090307020a0503160e0c0705030a02070306060f03080a080a0e1002090103050105040b0a062601091a030a230106 74
    0x506810281e4950310026410541c0c40d0404500d00d04406080058601181c46a40c0240032039201000141000030500f4204451002900540072640e0000c050741c5105030b08460780c8a10340c00008880494180b1180400b0340d11019009950241c0f0030f820156180040355842000603600103030003000c0320780e030030400003610b8034800071030b24010309005015564a00907401040305c182e00310f40205100e40c01180043c4284104142031000b10b0306030032841c05a0360b5440145640d6801083d0010b8140d0000244144200c0e50209003507060f030340714220811107180c503010b080700070700e001e80002480c41c6020440c2c0d10495015030411540b10381c2c5c0800100d02d050003000c0f030074188820b141060400303a802240c1c8812a603018059540944400e440402c41d030901d0500050540138284501014000c42050301051007050120f440b1400704003a915160b40c0d41d450303400c040188001c501d401c0207008844582c1013a45404100c90008030b40282c10740d604000c0802c559040768000780d035480b04079136844200154010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 332825062 1250 332823812 332823839
    0x31909030801051206152e0503061309050604060e0a020d060c0e190314030d1a010f0f0f080618010308190f021506060d02070f050c0a0e060613 63
    0xe10070307612010254580028403107040d005a140e070006400c03603010881d45021050541c4600c5800b12807410303000780520385900d401d029842d9050349900548844c2c3e90340c11b400000943c0208000d40d100f002c0340601c500100d08541300800c1c01481078000c0c0d0080342c085010f40d001440800a044107032102c1240070760029580446119084a000340c84801801e01213030071141c405100c14060342c810036912115041400c82d245503000c002c2034203800500c0b45048035020001d85001000400303003000680031000c4002111032031292014001403c0c2d4074000455441620751484141954861403614040c080007500c0e44840140490303000405200301000e04400b03220345c24000d40c01396032156a101d08040c90400301c00f051074024030511800402c052041a4005400f040855198043c40c08580712500015080d11440001400141c0007081403010b008613412240c1c5498880e008807201000d0b0300050003e40c00b541d208103410b14403140300080007824118024004000c3c42e103032035544a500c915112070b030701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 332826312 1250 332825062 332825081
    0x40b0306150f0309010e010506030c130e150405010603060b0a031a04030e0301110c010e0c010210150b0c011b14090405060d02030102030403091406180f04060f060c0303050f090c060319 81
    0x5a440d14000406c5580070b2051039008101640030304580100000030420000204440780100eaa80350100d984203001070002c1410030f0b110302200c40b241d080c542003942c040c18890105031080d0b032803d2401851032400b0207501045a80c001c0c1e078048141d0010300d0700044890018800c0d814488034010452280d50280f00700c0300c40340412500c0640300c050202040b0708507103c83c07002c64030b1580880c0e240d0141c0c2c2c0e00010544012503032030f280460a2400e2145010351040c035680040c00c11500401d407005152019084400c5070441c115074107a281015803002c49058a142c100c2802e4580100216405d504154108507030000016002c40041c0c40b85d079000c2801ca0f4001c44090300018151035040c491012000814184020f0480d6405e01302a00308481442409940c1240b40c800c84240b51750322400e48558014100030300441040346501d99a421010784182c56803034084000a00d8100083d8884140d80c285500410500e0028050720414205103c0c42d58005091701c080390050304070380042c0740c12078003440da00d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 332827562 1250 332826312 332826331
    0x605070309031b0e1503030313050c060706020d0c0e0a120501110c06070f0809030405100e0a03080d060f031101081317090f04050708040230011a0303040b0306150f03 73
    0x100e91826602c04490240504504681a00b45012042986d40042581d40210781c0000c81d002043d81c525149290580b101056600b1010102d422010b010165024004110541d802130080300c0303070341d48120f88010749000c3c181e610003c5100280000401c044514003640e00c5030000040320568912074404c9608501103500842c1e12032010040383c5540071175401b0005841e418181d8079800e00d261020b490b4051380c000c2c10300410b901021591a640f0807245491003403c06007803205005d40780c2c10203000f01d41c0322540b6062028105100000d400c48d44111460490750800280c0c0b08890066004591103070020300780c02e030143c551064040c0481d04204407041044100200765941d0300014090020360504042801d101d2481e000c100816141c00115035540540d040322800c0c82034491601081407100700c682c2407031440943c100604585c0405511440e0319000340c101900341a14810105030f40c0b485207015003002210140003040c41030520520f002d46000381700b01c04906084241040c0880c43e001210b64485 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 332828812 1250 332827562 332827613
    0x2717160f02010f0c03171306020c0c030c0a0b0f0c07150914060c0318130e0718051b07110d05010c0e03120405011101060e1806011e060507030903 64
    0x715a003003004038248030050709100005503120b4401a0801510700c50032000d00250800140c4041000814001125030000017152103485600e1000c0d40c03002c105250502a1046c08800419450006c00740c0089984440c89245003503c5c0501144958014502655162244980125110a031601074604c8021507036149c81040b850302c107981004030f005540d440d000d03890800040340d0004002c02154044516000b034400303844406408a61000204204940202d15104222103146070200c0e050301100c0c072020b5016001012040b42c001120030685601d680858403811152442183c2400303818001c1c09a07060180d03410b808000305400020307840045072965920a0039451150b00141c84008041c8107900814103207413000da80b51410b20880c000c6605011030088180b002800940109001d00302c5c40180d40400e08002090415524030103484e0382990081c1000811420010340c041c0c0342910100090101c0b243c5059415100365010000c107408124400c20040080784c112a00b030070340c14030302c0b1806c8036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 332830062 1250 332828812 332828843
    0x150c0712050d030b041e240f170606060a0c03090506030c030126030301180608030d2901021905010e06010618080303241903060f271716 60
    0x9044803900131329584106d203000c915110074030140c85000c1d800032540c5000034210540341c1e0701036020280180482e034124210003002c0340200c80c0d81454412610750000100d22000e207034000c01d885040844030290840300c00c1c402e1401d2a0b2061190013205402410018411350f11800499513541c0200c80200258000100400400c2c10b4440565079401070000c6049490b40642d0455860784018842d01c24881008500c4460320f2000380e01c500c0082284030f00300d0340c0e200c82051031000500401c6c0c99480d0310380408120030025003084404180150300581c080c00e14030007654540305681040c4201903c19650f5030910782010041040360310b01805141e00c401d00103c90b450166200c0041c2500301466903002070080c4400001006001c2c2c1c0c2100c5521484115108007401085111685511921103030071200400024400700d940200d0010810090500c40e02002c05109104000f10402a684a4500d6032480e0040b9070201c0310b042e403102d1103100c00d6107404d2209170685070300c1150440a540d200c5d0414081c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 332831312 1250 332830062 332830067
    0xc15021c020d09031b0506011526010e0705040803030103030c030509030a05060108060c0705030906091207181503050a17130605130e07080112030c0602160605090606150c0712050d 79
    0x403014104038006405c072595503099251a81886409403c0c1c002100412680b401002e01c181d0181c10200c01a26850300300004010f01da00a11032840c4174101c000129007924402c104450540c0d20b140700943c5541d285540498102218030740a0f400c0080c2441070f041981e0341031000c0e000490150780100119418095103d0401da80602a10203076001041000001840401583e0625208031207140e1183d0801000c160103c1c0001c413030710101d008214000ca0301c800c4445c1d42790480b9030350b00d01c200507000c1a000f1041e40302c90070f0300002e080f50b40600070450004042f0041c02c034508000d282000c0c180100b0b003207440e203036088640003000402c2e008030b550340c203000b51144000018200309038002401d04200002500400c010f00821098100c0c5502d040c050501860071203d8450303102c07000710364031800311180c40303a40c0304e052108540d0b050904d40858a142d4000076118005c0d01300a05c00f45001040220700185540b08031040c941034004d0180004200b8452844130100c40d00400191400c0c09081d40300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 332832562 1250 332831312 332831327
    0xa0213050405060a1205030c0106080d0201050112110609010e090a02040801110403030e24041226030703020c1603061e05041203050a020d1104080705010c15021c020d0903 75
    0x200340074500d060200107265483c814103404480c810407182154000300c0c00c0a40c11407084280c20051380d0300b0b106001422000014145207020000d0740200882e03600d85806516080003d40090804c0c40b103110207289501e01072009000421050400780c00e0400d0200100f010154222015503145502080411240d4428060081c00010446425140908590b4003400c81781c501e48a0309d001c0d0032420855070301d100b120310b1041301e0385065000c81d40d201c69441500c03441c0d50100a03021540f51285100c1c0e44864401d4040c507a9a502c0e04207d494116550344004a0080d04081041c4100380714100841490414044420024500810300400d01c0e116096088412840054040040038904000c1101048030074842c95941c181c14036000c00c032601d4504c8844068080c070350788070140d01e180000590046103c1801841250034540a403000c140d6503600540b10800d90600107400307244002e4402c2404075460f40100f810b0310b1000d80d0450341000c075020b00c0e004c84c4c012554402c038080d6100e111009040e0025407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 332833812 1250 332832562 332832569
    0xc03150702070e041208041a040501150815070f02151006080c0301080303010e0402010306031a0403020f0102040b04120c080a26030601120c02011b03330326030a0213 73
    0x1914403d0404e95207030000c01d00d903030500500700215800840d04001c1000310b903006225180c00c00070001d003800e04001d8000e1480d150290b0011210f2223000030074030b4006c10b0240c80342d0601c0c24440d840b640c038400f0a4580180a017003c10071801608004900b8040018a031805040c0c200c401d0220603042c0fa00260036810080e1101100c10710a1004000d054800412241034132001c0d1180c050503142c510047c1e01411054200501145d401204003941c040d050050300e100b05d02035402c0f034000e8016008468202d00c200c0c040c0c01c082400070002030010b0403a14484260103441441100c03a02e030fa44260a42c14005800402c0301e10400c85950036840c021001a80c07003621440300790043c6142080b00010302202103000032904507545404003d11814003c0d40901e510a8a00c182c44802c0030300800010000c2c818010044a000721241c0240a18510305021144010342c100e5108405415600d86038046c2415910b12118203d54500340c4401c0407654015601800040e0400b585600c1c0c00064010494010342 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 332835062 1250 332833812 332833829
    0x10090b180a0b0a0f0204030f05030903151b0309030c070605041401080c07201f02060a060b0a1107081009060507031a0402090607051606020d0504060215090c0315070207 74
    0x4000c0085820010781039080f0003032090000e21600107800030710113400349034805046c081c0c40452150900402000605940404405a421305d060010007040006425903010034124007031101007845005003402113801c41180801c41b0b041c59820b0103c1e07441c1c10b6003500090001200442d04000900303440140382c607120400d00b01490301c5c1c0340108090f40d00e40030300c1034003600d4200030200b0000005040d49048002c03c0e00a40b011000043c00345c00100410211140f400051041c00009400f00345e4910410050704e101010040c6020480e060845284424126011140c0150381d000a640841000f00401501d01840045102c00f014140201100c000511940c189414800b01849000000200c00e038101411200140c032900e00e10042041805010700c000c00302e00c6903000c01c0011090350602c00084840035821164005000b0300111030f40e005501c500405a8400c0c15190132400d012110031352700c980c4d040220741500111300300207440c0c00340180b8070b81308450070502400700550341804160050998036 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 332836312 1250 332835062 332835073
    0x40c0314030a021209010c0f0b061504050a090e160806010e1501090924030f1110050702011d10031d0307110d050a020a031101030f0b2110090b18 64
    0x61006900e40c10b0410700e5072900300300040e0410301c41e07001c1e1081f00a03035500b011b0784038800f200910341041c03030000a03940355104030034540344800c07079240c20004c45040d684003410701e202c181d290000a2018150420351407220740198a81d40320200010300c0070500a001100040c855945040c1109641c0e14002c0d10700c10b01c400c0307528018841030760400080c404481d0b00700710005403100100c2da5420700080f9500310301c0ca05424034400000b444500040000c050340500100001e6000c180d04201246a07580c1c044808500b0134401d02016601800117081284201840c0b080104422800100d14130201030301d010200f5907031070114140002c14154030743c4c80714a031401036182c001036841c0c005030140c144000a20500048400340c04200040c0180800d095020741484081a10307407400740200500302a032207000a180041da00310550312402a0b040c4044090849034414a1340f0007070f18581d022400e80035001d8821081c2659840601e403052088040c080c2c280306d005800c0000c3c0c0c03405c0441644441d0003803548103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 332837562 1250 332836312 332836327
    0x10603060f05152e09050a050a030302120904021b03191803080f0f0c0706030b0405040308060906040b150a02070b1e030709050d06020405131506030b01021203040c031403 75
    0x1c505030118514404c484184480c910945100c6201c010382080300302030642c8100003060a500711032010f0944404880e008805c60701c1d10140601da00c1c040c070015006902185a1705c20080150005000d0200064005850803541078141102d06440c440042c680d68400241c0316121940904030410032000c0b03140481e0010f41c0c0c1030410300712149a01004e001610001884140070345100101ca5a0301d0000f003a070740e1503004000b090ba071126242c0c8580300c04a410f100305042a0714242c4161840307294583c40700d61664641a040c410102e8000384480c2d04030303075601e40e120401c1c0e56001d01503120200e0252080e0350b8100448000b820040e440e80412150a024010103003802d1400002c51840400c0490450b180e035116072045a48040c2a84542e40003400c1ca6003010034000c55400600646109a4800345444680700c00301d070807251003440b040c0100100c50801e02c002071082e00f001d6000101407045030002600314030008442d07442034504035442100700c60100300b00140052080100c0542d0302c040c5003090306 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 332838812 1250 332837562 332837581
    0x40c0e060d050d050c070302100804150c051803100908180102011103071b0b09070e0105090403020a031b0605010801060509180a1101110102031603150305030706020f07020303030702010603060f05 86
    0x8885843c805021012491064070901041508011a00108191b041400341c2c40041c062840541d019200c44490307004110001d0410300403e0800e0416540e6945071818000607208c4c00441e01c61150350501402110340d070150b4442c001c4c048094003808185980780481368011100324200c055007815a4104040c800c450016581a654841c40600b8440403102e0044082c0303140b598400e0740240050344401c2403048041e000586c04c410345e001c0c029054441d980b503400304040c102c02100c0040059000030001070010b07200d02060b40c030070a2132544000a0310501c1e0798000940e0000d8010061581d5100010030003440d000300210f40041c50100d145640d091122030098841451500151101032180c0c803040140e445101000c0c0510300705c03c000c64482c107000034501e01c0c03903020341000c0000038281480c40e040310001c00103000c00c0300e90200c011031a000203982d0301006908448405072082c401840b100c2c000d41c5040c801103100342150303800050860306506d000c104a609245450341901c0c98042000219079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 332840062 1250 332838812 332838823
    0x6180f0c09300b0a0c08011a030612010204050a180c050a170624090a0509010f03060b04090206211e070813020a090c0801080303040c170312040c0e060d05 68
    0x1600c00060b800d11858141550021111500400303500210013089500ca040303a21818003001140c0e01c0400e280d82e43e9072041110348000081405144080010031024070700b1a020008141010001508040e981c00c0043c003041383e140e11102c2e422a40852440310680d95201d0070300551400d0820703604002414800a150070184880300f51220500004101d0b29030718a19010001c80b8a0114414203102040d01c500198100030950b90040780d800401142515060114034181da800d82c0d540d016a40c6161102c0e40600a911143c81d00304c0e40c0c919485003d80c4030307600200112040c44040703208042500580240b040b000500c020704600d01c00c2821071008026196054100b5854607046000f601c0700342c000c07040f290141c14025886010742c0c1d800103480c099030304107502c00d12450322480a141c0e07070303a8400d80c0c9030301c0100c60082403107101040601c81b000340000e2121080c0a40401c03a410301465615150140e0015070f025503101015603020460701440c0006190b1044090314184080c0718140c0c4c80c0c69942 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 332841312 1250 332840062 332840099
    0x30d050c0a022104081204150206070203030c1e070c06091202010c030f051611180405061b04080f031305040213050f04020c0a080405030d080f0f070306180f0c09 71
    0x60200d0a03c121403400800395405072550390141e030a680701d0801000d0f0554820702c201d4200e00c00a682c0ea00e038007400071402ea48171351099009903241da9030703450100001390301c01115000d140f84040c400e249202c006a02a18500d03102d11403100c441d82c1090405000b02840c2d82c00308502440c0d03200d2900050b43d00c50307841b5100300e07814284088104950f6800f03681501a4686c0001000090f07040d95061244011005a00e66416210704c2d0100310344c648100208a0110380c05010b03036000c5000304030b1442101417041e4150b441e090701c01d401e240d1078040319030416001408490f499440811002c15000e078540b0b5070310040c00e045a08500e00012400380040441c5a41314641c41014400c0c001e0721140c6943d012650308105460039200e04800c5840d00d154150030900625000b8880d0b80b102c00d10550281c40341d01e00031081003251058035524000c641c641e52000400840400d034031514001540d44441545c00800c0710611004900c1211b03540c80d20b02220341d682a80000c025100d2401c00c20810300d0803003403511 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 332842562 1250 332841312 332841343
    0x10f030515040305090d031d04060f030b0901021603020102030411011e030b01050c07080109120903020a0311030a02040f14060901060f0e060903030a08190c081302120f030d050c0a02 80
    0xa40d840c2c0c10b003682c007070040c0005ca903004510100c00008044e4042800381c81c84182c40e8a00c900c081c591800e000464009000746d60350040400400d101291072031741c11640c03080800e00050f1400c41c9140346a000888142d00c11800350303401106101c00c22603007642e00b0041c80020b2810f09194071410312402c0b5202c183c0c01c0c450301410b94a0541c844140d115808842d00d041c0840115041a56038076101802008111800d5031011807031079500c003650b4807035407201d8212074000340350b5040c442c1275841d0040e100d10209000c541c584034100201005841e6400703210400c02103100d0000700b4110900410450050040025106200e41c5006105e0340b600300600c040d807416581f404c0c0c4200e1030a1000b26040d40300794200c2d50b078184004608200a6540301100b140310340c401c4403402c1a03880030b4402400607100102c0d1401c1c00714402c4170000344c1002c1000204004c841c0001c1182078010041c0c0d50850400035209801c0d0501e40000450f100f40282c64000e031030700201d0301c164003450101e940e05c0003521400344500e00008c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 332843812 1250 332842562 332842603
    0xb031c030b03070806161d1f0924020609060603030301120c1a0408071a04030f060209040c021e07030b06090714030c0706060902180f04060b0c030c06010f0305 70
    0x1803035242048890050000f2904542d445c6c20b250950f080e10300300c0e114040000500810a03c100d00c4800119040da1460241c03185441c40500f0100f100c800c1c41c111101020045890000110622220780c002c1030444003c00c40082210025002030900c0f100400c1c5001551000b0140441901d00004072411a5500c40304881c02e0841031500075410f60242c0c2c80101c2c0d8031418240b40040c803000038001c208990240c000c680e0300a6599202890080300344d441d0030341c02c540c10701040011501213005600058807444005142056040000d030031180d030580d900340140e200e107005207201c0828940c0e031003100105400400340c00f860b542d0fa00c040300b031005045030700614000740407551150054004916500ca00c40b58540c0324a844180d00c142c6801200d030a40300d0307a007000000507a015440c400c0700c00e540301024622000c0d40204051001c030000c0000d5080d000341e65108000b64219480700038000e40c19440300955684c80050710040d02e0400c06800c0040f03414404442000020300000351740395401d940c1c128914 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 332845062 1250 332843812 332843831
    0x20d02130902060f121602070b0d0609020a030b01090f030203031b0a140d0e0604080c0f2403041103030903030403060b010309210314060109060c14011d010b031c03 72
    0x201910754898000d40010000c03503900c00185014001e0820303407202030801c4c82d1a55a25442103818020180560f026800610052016a8000c0f00401c4020700340003010422a0383c60000741c0072644108031400001c0e695504042240da8040391080045c058020005010740c110f80001e606ca00c50000d0216a03a0508240081031a8003448090100c5400101300030444042c0702c0c071075440c2c111540c0d40301d0014242400301425854400251070a0b2240000284407014414041c0300180000800250b44460801c0e204a8543c42950810950220400721681ca90510380344c2010000c403460746940c4240c2050008410b10f84002040c1c0d000c8980164010030110341c9140181c0c001d009441c400707084c25560711400100005020104180c40a4564041040e02d0000104041494041da1814002030007944104910740c86200913001c0c550054151031854140d116804d400c54100c0b0091310030f400c41e0880709002c100f40a10440202c601c00340c000d80303e030030428034550707440c2e1120f90368480c180b5680342080c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 332846312 1250 332845062 332845099
    0x50a1206030c0807090b150a030506030a0b01080114131101050d140a0c18080601180f050f040507140f012f03030a060603140106030c02120a0513060507020d02 70
    0x40021a000001c80c2c1c00552583c200c140ca40e0104c2c055588000d0401420700410304040e00b19182c426001e11510b401d06401041c100d01400014015940c18402c110162011070512800745000f44045000011741403404d2030032080c40400100482031134103c006904d40840c4c072032080009060000d00c5c0c402c0e9142da65828407030007041240040d90210640c1c2e0100055183c030ba40c8404140020740d20bc20352081e0011030421b0607100d60740146107450700540c1c01000f800400503a41e040310102c03507102292044001e050f0b1011120115031141d90084084140310904c176050060303001400e0a94141180a02404040b801150780303203010034104101012042441040502c0480c409070382c890b041601e0707401c20780f0215030782d800030341d640d821f1180b60660000f60300340640b094a545403000d51403803c0a0b846c01070b05034010144514800254040d010031040081c0d80d0b58010280801e843e2902521010351008072044440f00d81c001205207c000c102000259403031440441882d40d040300c1c000114140c0c5000e8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 332847562 1250 332846312 332846321
    0xa060b070b0703200f03010e01050d1104021b0a050d083103030209060706090c080a0203070504020304050102040f0f0801050a060b160302100204090e0607090302150307140d050702150106050a12 85
    0x50700010391301080c3d241054003040001c5040313a05101085c0030a9803240c04100c445100500c00a0021280400001513800e052700600b04416004aa010440308510511424070428100c11585a001045486003003904820303515003001d030401c80710000c1025124804c0303480b180440c49500c10140345084904151003030301140c00d00c1d44060700c1036441e5903561410b0030140460060455400b840e455001c18184000030f00f40842d550003e008040c020302d803d082c04000c9d840640b040d034095400b04004991030503205140d00c000c0022200d00c400580c5044403841c00c40e1005068004042c3c203003030080150000183c01c0d40c09000c200401c050040b04603203003c0e4600220f2800111074980046400101144a540100180f051400c01c2d1481c0f170b03842c0d0004550316401400002e501291840d40c81d00499039a00107507038000703942d007040c40c5002c00741c001700c9115802280303070224196115001c006016505001d414105844181440034650420300c014090307015922040080201c14015204031240c950031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 332848812 1250 332847562 332847611
    0x31b0d060614030105010b0c07030b180106030b0a11120613140901061701020903070605030a02120f0603010f1a0d06062102091b0405100c050d03050a060b070b0703 72
    0x5041007030595070306100500d80301d41d0303021500c03d500c0c2400006624011104480c4403000110241024a05664503000142d00240001c0c50f00c2498007210000740800344107150155004140405203071500001400030360340012300f00d28800005000200001800034109a000041100c08605140c0100890801080304942500d8600442002c1c49090107065201109035502d0f1610550041078103030380c0318281d02c182404250582d00c606030401100340700b600a1f5820848039540545001c20b075168212002405845101d054600d01e818001c0034a424803410031100c240284c10300210704001c250000a070a04602c0d54004c3c0c012011807020000300f6400200a0f12665485200c3c000c40e0709011203118030031740000c9010380c4043c400300c3c0501c800c050170942c54103440e1202a1801d42003d05000100c0e103408502030611900f1440403000560074030592100c055a6600081e0f5454007c000d2801d64840743d01c010184103007000054049009070240660026039424081503c0700e110400021001b000e56 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 332850062 1250 332848812 332848823
    0x522050d210f05012d171e07060306080d0806040b061308070521030901120603121106060d020612100b070c15090b0922060b0c010515031b0d 62
    0xb180142d15a11640c00941a118280c2804000ea20003402c01e15450445003a5030048401102c82040010110500c3c0a203201da40c03c190780ca8440c41851400142407000e00f2032600340c108030418010039501d881118014500b0b00700030074108c4101b04000d001080080c000382c2c066901d0b6510018181c0b150300441c1c2000700c600e0050301c05030f540c46c0400d81d100c02d03c42c003603d8032071107514480040f503040701f248a007040003e96015515041c181001500d82c0c0190042284c90192a07205c0040880e440320300c01d510040041d101d00a42c0e540460340103003003d0300140920711941c00e80c10100c0150b2107080c1900c1c3d000c80440180e0300103883d240c4899403200c03000e41c40003000c0c0c0b200140c2d813401c01c060b0000103000c581242102015510b40f4940640d91030000d0b014500c940342080c4180710301883c05141011021012050000030007116051303040036109690441000100b00241600c1d0440702442001d03804026040c01c4130003501d00c0d40009489070907900c54800d0a82c585402850a03545800291410381e9004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 332851312 1250 332850062 332850071
    0x1b160c0512240f1617090a17031303050c12030702030a0e01020105010b0a03090311030a02011e09020d020d06020412060f050f04080f0d11040303030522050d21 70
    0x7244038079620000c2100d10b1903108554101a0551103801d0355060280255154040745555101d9040455000e48407064041019224249650013800308025014844400184c142c030051414040203100d240c040c0d082d180e080070020452000b094040b010119641450314981e665401c400c464588520801054183c020000c10701a0b450380000c0188085400d94440c500d01c003a092005a0807240244102c0002200400c01003461501c20380c4680380b00c40c402e081004c501040c855009103150001c103e10b8001d40e42d14150072000c007000c82c40000c50310340c3d400f5092025400d00e5011484c151f83e8898005c5c010101c00c445003007042416019240503107070148a041001e480c0381040c0c00a0300b10744128214203407400c804074556281c002c00711441180c11280035490004d140c411850117a0106010200903030342d0340c000490500e03848000304025402568049000d0420480e80201c0303000201c0030401c030690032240c1000003100031508840b650482e0501501c00c40030f11108544a60f008a01c4544140c500b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 332852562 1250 332851312 332851339
    0x110f01020a2105010b0f070203010f0501080c1302091c0f0609030c1403090d0206090d15050124120f0b0d0b09070b09010c0209040302070305030c0d081b160c05 70
    0x10001e9118038603030070300e010ba076003190008030744080312420f004604c040c480c104144414030305580000c1100a101900000320200c0440d5610100d80003a04009803a0300030380e12a21052408468a40d4040c050307407401c510300480400052031200030b89091544801c46040c105080c4103c00b03104402047d0884800d0003042010302c3c0061045422034012a5040d030800a0015000d0000064907210000927001900302c2c13805408100c4030340c00c2121f060f0f5000804000b000001072424800b03441d038880c60340011625504140000111101d603201140541040e135400000b8142c0c8012124801d080341d280c00180c0340c40200d0b074800540420001d85401007034202c00d03c4100500020443c0c41183c00700140d84082d916820b02e009944103c20006000403031007040300c00503192034200030707401c28800d00407662150342d03030f59510741103401c000c80c400c1c5d00c0d80180700942c3d03c0c590041c07212a407106008802456000c0922640911401442c85100100c02d0000e2640100180e00c1642c0003d001d000740403a21001c0c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 332853812 1250 332852562 332852567
    0x290a020a060612050d110c0301181103010c080109051510020c030105060108150f06070f080a02150402181302060f0d0605120c0112091a0403021504080a110f01020a 72
    0x4014030854085140007000034060714080402503003a503000000c0c04894400b001d049034040500200240c05001c0e4134030075007040c0c3d0244615030a46100e644048201e00d56400c20503415912950007900a90501402c000c4540e405495107054402c42c51000407540c440040100000c84415401a00030701d005100c0c0c689180c00080000d92443c00700d0003403110f9a201001190074200590307161801c00064601201145410100c01d0fa2107117000e0607540c10462103441e01826007002240958281c0000260414400d034140041903042060036507044140c105030f4041420711143d043e0040c030206008000c2046c014803903010540c101e80040c80607450301d545000f4060759501070050708464500e01840001e042c01c0c41c040c4420301d0480c2c1009071800c2440c030350040d1a504001d45e80eaa4506541c0c00180000074070100074120950300300c0d454084581391524010780391032682d404085070401001c0c104030010764a5002c07034603000924686041c10001d403861943c0f80074403200301da03a0294004100f2140e20f41c2d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 332855062 1250 332853812 332853823
    0x12020c0a111003061a1615060f090207050303060405090a021011011401290d0f0b040507051201060f0203040b07051005070f0c0b0c070204050f0f061207290a02 70
    0x288221240c0440c107001c01e20a501312200b62050b1004241e00d0181c010820601502408048255820703481c44201c10750b4540c0d01415151a4090703015964803c01c2c000700f07032104a05c20107410580030452804d92241c40b410390b05c2c04000c041034415901d880010b400b000052111310390069014100800e240e0030640040c01e03c0104807004080c961070803e42c01051542219140d04a4080c2159900802081045100d030440c01140e490036194080140888581146c810051000041c110001c2c0780032001080106654010303080306d042000038080544200c43c0c0c1e502c000d0441d621418226101d1280c0201a800d6005542c020010300341b020400f901032210100340c100a10501c580100240c1e600c1031816115010086503802c00030305e04114502c0003c01460001d5048030b820b0b1082428048030341d0010341a1079044404880d15a03441040c060407201c0c0395021508003108644500b00f051400c2d4955a9420b6180b06070740450800142c4202c881a0500c90018222422444030390740390503482d4060754a5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 332856312 1250 332855062 332855093
    0xe04050a020108060d020604030f060b060a02010e060a0c080f06010324080d0c2109050a06110106061b0f0825030e01050f0a031a0306011203090902030408070312020c0a 74
    0x440302e80000349203103000510488017907401041542042d003182c4510b03030413006e000c00c2242d40302d80d242f20352582552031034050440d0b1042c9034004070344102860003880c100340c4045c0903980c1a0342002818204c0320341205101e603003c01c84000150141d520200120050450160846400140ea812101600001c0e11010707040c2c40f014001c0f030390442e040000c211503034503c080c2c000d0609002020001e5610300c000821071030f00d40e85031600075080d81e12440052a600a03d41c000008aa4210340224400b0002c0c002c0b4401005241805104003100880881492001d104014140e0b41e1103d01e00d01003010b123005440d100c5000b40424801508000b00502c0360048a80050340403030607080e0000e078198803400c2180c0f01c0140849240d8102101d081b020b4016080001420441442c8243c10031000e031070811609008021003603070402000102d0034080c052004640021480900420412010541000c12224115403503d861a4070501780d4464100a0040c0c001800c818003070042481d090024882e4010a207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 332857562 1250 332856312 332856317
    0x180d150216210e010804110603070801030b061905010c0206070f050604150507050414120d0e0f0a030c060c02120105011206110313080306060d05010b0a02010b0a030b0604150e04050a0201 82
    0x20740d01400c00d603010309201141c0e00003d040301051402c9512070b0305040e80181c40791009400255602c4c0000707059400032110000007800b12401001800b0800c070310310782c210b4401e5849004804140a00d010f00052500620f414014001000411521094111910b040d00460598880c3c8142d2800b0380e16484251015a220b40e1180c42d074443c101c80ca4400e0358000c43c40c9440390b600e0b00e490040e25011350049540c0c41ca41c840343c014018040d404c1d0900003019445c420355284040003080b0001c01003845072440541c3e00a45100a00380000b8414165a4064a1103810400d240c0704052001400e0101d00440e0072600b942848000500d4490000036aa07005200d242c0c140b000c0602c000d0034000030300ac101d514544808030100154040341100c0011a00302c50040e194915000400e484101078400c281d009000500c00002e00700c0d0642e9080c85501d4211000311100e001c0326265840d0140c040030040c04c102c0c816070365031014510000360b9090560040c4040a400c030f6146c5003608000b6190740407204182d01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 332858812 1250 332857562 332857583
    0xf0c0607021915090803130201030c020c01050d0209031212090123041101110a141002031b0307020109020a03060f0f0506061210050306090a05010e03180d150216 71
    0x10628004140344080c16840c5081c03290390b81071a240c0011010044481241680c0d5540708000840c046400940c407801d075550b0884000159440010700301d404040b0f2030011900301038002d42d240d80e400300c2244c001000200016840320901d44c0028106840d003411410f08140000d05042e0030040030490b00e104040f0103000304092044c60000c0c1d10b1007440020303000380004100340007a00240b1508419803020006140c2a141203071441310701841c1012130501610408440b026a81015404103c0042200f950030000d41c21410034001000503088003e814401d412000700c00a10454800d50000d410b480e0002c01e0505401da582c10020024405011950032441c1401500d0711408100e02400e8000e487c0a004c00e4a411200e00180303400c500c0140c91400407240340c40c03001a1030b80d020024140a0010000649403180c11031030940c0c00c55034003810000380380d0000c1c003909207000d04041207281038000948000c03010850743d1610003209203a03440441401440400c403010403400c43c540703c1030300c2440707500e0008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 332860062 1250 332858812 332858821
    0x1309050106030903050d020a0314010b041809020a051203190503090d0c020a050103020714010906052409060d020d052e0636020721030e070510140f0c06 67
    0x40c03d45030300000240102e0b008210850804c0d415600901502045140c000350344c0c00e043c11041300141081e8892450f4110219051095284c204d881005410301c0b154108030b14483d0740c0c046040103240c0d104082c8220000302d0410389500301803084580fa10309000d43c1800340661110f002d0030541040c0d480c2d030024818100c944003246c2c0a50081e40b0810b800826150080d0b1501004401075449120121440850341e1070f00d006540e000d0046940750344c0320742d10101d07440c078ac00b031910045000b034183d82d00e41c11203020000300c003242c40781d000c1707203800800a0720511440b4156002080680d1400c20000708288150184045400b016030700b4180d05030900c003c0c088400880d00024002c1d00d24500500c9280c000030f13070345e680040f12940000b82d25007124441e0720b0f840e415032480000480c2c01c0035800b0b407443d1040b20609511060320342d61802a4805038101002021503044280d076680086000703050141080101c1e1070035032402084d4180070401c3e21181e00d0360b14148000b500d0340d640c11040f440304c441d1203003d0109 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 332861312 1250 332860062 332860067
    0x2070e07080709090509070807030b04020411040f0306020a030b0d0302010b030d021501050f03250e0a062115090809030f0118060c1823030105090a0602130b1309050106 74
    0x128000e00e110783c0c0c0c640c0b609042c865110300501019200440030b1080090008002109009040c000c5000b00f01107030300d62600f80180000d0340c2c41001e00038810318040100340281040149014181c94101070016201d003584207040d40201346030030b866030340082158044002c050f415080240b01c000705906030b075510424070b40141c0e91030100f4800107014191070801403105040c0307400e04a60400f0010212442380f006081d00d01481014481c81c42e81c1e03040041400c2c0b01a1452461035a080711502d01e0400005142042402c9512400c49001d543f86001c201c20005120380704803808594030040804029242041c504050030398012480c050290052140044d140d039018480c58404040101012041414942e507a00013400b000e62260144542100c1d40c02e0812040c030341040152281342220211a842c6400420180c100c001d2034a210360f05203005c000000c04049a2600317240c1d402070380582c0300c800d01c645030940c500c010b400010540201241051081702000c5000702102d0400c90104420390301d44908 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 332862562 1250 332861312 332861327
    0x7030f02120d11040b04030515011d070509040b04060b0d05091606110106080d0804060b0a080c0d080d020a02010516021c080a02160507080d180b030709030b0702070e07 74
    0x95800041c207226080c50b81040703800044100608207900381ca015181d0441440c281c01c2600162001d40c0000c054800001c80d078a10103015204508954420341c0201d08030b03601c030000003010348080210204815129407959049901a070700c008109000c510740f41c0904030b581e80c0100380003090346420040442c031a01d10108130b85540c025000c1103020319900b0400140e8a0b04030144c0c0c0011a9981c41400042c4080144100745c401d0000d41d4581c43d0a0034981014002c2e1044503120901c40c0d00600c00400c07888000003004924000700b91a81d604003401070420b41040d000c0c03a1107c40c81140009400d10089a041d4803551284059100382643d1020b00030040303a4070b10134403e011510107801d501300903485020300d030b1a039442449102d0140c5000c10000c024904102e9030501110136600030081400341d0f28007401503441c804410319101a0100040c4148108040184100761180c60000080384d00f65116045c10005590030010060803818800b0b002595590188214403107200030703202040b0528450342d035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 332863812 1250 332862562 332862583
    0x1903020c1b06070f0f0b16171801050a06360f1b02101d03190e06221409040b090115030503070605070201050c040b070606050a0b07030f02 61
    0x606084039000c07140180e0300150040e00e58409401d1104000041c180c0500d0f9103481d200d55040e0110004030b04d030513807155070041c0441c290103524a40403111664820000020b0091810107413843d41c80d5000494007a504503d02d00505500707042c100706004403141c20041c2220790b8419600c00207042e291019a013140c81404540620000327103603c8040c0803254000b1130741c003840380100040104841c1c0c0050325070b50b001c20300e01c4056080408202906442803050b0a007290880c1d06410102c0a402d1031282c49114240c0d0080c0b0031403280f40c21441080c802d62442403406400f80c405540c82c00b203c805080409088850100d10003070b8403c0104640c13803101c000c884032001c041c00500168940b50b48071004000c4c01000540a03641c2d810002c030902003084203140045020744090743d40c8040c5400c0c9401030354801008402968180018484550400c07012581240c086620311600c4038040c0c0340040182100703502059002e140660086500380d102c400805400340b207500d9000010030000000c1c0d031240750141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 332865062 1250 332863812 332863837
    0xe0630010b040b0d02070305091809010c0e01020d120204030605010b04031101030c20100c0c030201051609030f050102090301050115110a0309150302070602070b060a170a060e21190302 81
    0x100255130b9503c180c014201040c4a41045410302801402041400d07010820f055031a20311901480f01940d03080c41203110301c1c401071418007983e03503240700080e5440710902004810084004c00d8109090308a80c10750f1b002e941d008400380141d580d40c0c4040481904640400d9609900c00c0261a103e98040d1180604540003500c910303250300b499100d0050b0586111160501502441d002c00c9048e04451007110203c0d503050300c1d04900e201c0e8a040080c02c440e0b0040140038044080c00b08264143d810016030000c8035408a42036200c03d241e4a40036000e0b00840c001c461b010340c00c0c40f0000c1400050400c448600c07041c9070b96200901da004000c4696204414080035010030340c1e044060101c1c05441041110400307031424007502c0d01d0b8460b0f4404049902081d004e8403010052401d1101c1854a00304c40b200801c51f03420301034500c0e200c001d001501c60780000e030000c0415584a503501d1305400c042c8007a01c0002c5025920303002e14042041e410040c2d51141e1084258a10021429000c041c083e00c00d4070098254407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 332866312 1250 332865062 332865067
    0x100807020c210105100f09200c0f070e0714030f0402010e0d0f06050114010206040308070f030e060916050102030f041203170907030b0601030b09070e0630010b040b 72
    0x36020b2110b00741100402c2141c1e4064070540600401c002d00a950040390005c1c0140170507032400d0203504500803250004501c10342419483d10954039450403c66445000c140520760350481e480301180303000c0968500d0065800b074150006104010030311110310451003500c90418190100310141d040303100071204070107062046408100554070414801d1809100a4040c07105250f01d0b89511540028095003110700700d440303034014003810301e0511b00c8107040502800281490b082542d03015040c0d00c8010308840030803070b22480b00d503d180d1107074202d1130360300d010300c0d0a480150400500c40c40d101d030a850f1011011151340c140000742544000102c0d2102408854401d00701418080340d20122106403100ba01049080080551144442034403140180c030454000c08100c1e265203020700780c66000400aa041c180340002810a079103c4011199100440e89803000b80070b1801e00000343c6130b014451210a44c0c84070601c50b100d9400a0302c04440500101980d80c000a070703642c01e0044000c1c4240e001d1000921400d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 332867562 1250 332866312 332866333
    0x70f171602071701020306030f03040510050f07080403150615020a02040f020d051f06020105010f0915230a140d140f01110a030510081216060c0c0210080702 69
    0x48040340c0da840551041d01e02d01c95550030f100c8032540840c42c103044541d6000007404010b2408001402034103495501542c1800e01e400000303070042c0300d0305072000d0030b000000500b00820f071032000032100e846a104040c2d984643c1c0340d051070406a89103200e40726480b440e0070300214a030701041c9100002182154000c1c2a220000c0d820301029041144021001540034030100116202ea40a01446540b01c0c503007680b8160000d0320180350340a059401a000d59141070300500105400c008500705644000d0800310b100000e00325095141c0142d64070000341b1401c244000048503c50144a01045804035150103c0e1a02c1e1800e8070540f141c400d061543c041141922000000d42e01c0303250300350446815042d2801e004581e0300e11402e54000c4841c0c1e8000354000280a0407503501445000d410040d9080c0810000d82400c1c1c205a842980080e008103992001c165080c05c40140c2e45070184d138913400b6100b4031041120311005003c50740e20807001c030312a00e200c09601c0c00380c44c070841c1210f118010f2680100b180405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 332868812 1250 332867562 332867581
    0x5060106050906120412090b0405010503041106090306071d0609210f0307080a080703230a0f090f0302011b0912032007091107170f040f080105070f17 66
    0x40d07030110b800c0f200c10322056800440300b610b9584614000c03900c1ca0f0701400d03107201c01000d42030340750000d6008183c10310040c451070764000240caa009500883c075010072451f040000b440c5002d40027556915101e15820007540d1940124125060101e000c010200c07200d011040124a005440b10311f5080800d4001070600990f0081402509241d00e40c00d59000340c0102c21305500f0340d4401034041d03a002c0d02c00240c007511640c2c0940300c15030005407441c1c10800100390300384080d20340e0303100000c03e841d451807800070800100407a8031000c000d0380f15440c20007542c1381d907107040c2c008042d5070001940503502c1d05d010020480c100028000c0c0404c581d40d00d00301002e003404114079442e0032001701501089401e4203586412690801054a00c54004008155480c58520903406403108180c1030111101c05014110001c0c5002d5000c0d804e415466182136110709070042038420074010b647c40348240300303001480094924030661001c0d004941c03940e0b448452000361130080c0c450b0451011204514522080041c59000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 332870062 1250 332868812 332868817
    0x608070317090f060a0201090b070903050a1b15020a050d0c03051b0a2f010f0f0e0f030a080403060609050c09011115100f050d0309050904051002071a060406030506010605 75
    0x82c1c00900000010954201241890300468445805030b95a04100d5040c05585141e450f401801071400b0003103a811941c2c0e42e40c54900100c001054a40c0b03000002440441c1c280c1c18a003e42032200c1c004011400180700255580d020050546882c0190819101800e225103002826240c25444c0e5500d41400940705078465855600310540c0d50281c080014006099140c410946408410700c041316590092590b1500310340b010000ca0500100e403044d0550300303402000303401d0030901a08181c001c001034103001c28510b10048122591500030b500302c601c104107188001d4800d580c0038400402440e41c0320031411084820a0320100c1e0484014040c0011540c86050a1030000fa040420356904407500c00450f03958500650b502c64040c4509038040c0549001c01e884407000b4201200c400680841c00d850241c03681181e03002c0d060050b2401d81c006802d010007002465139440a629003155540c4a5050140001c2c0070300e018141402e0b1804042045460240102c109403500100608000c1e440d02805030340c241d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 332871312 1250 332870062 332870077
    0x1050d03050f090a030f1a01030506060d030e0a06091703090310050a18081c110909060a0f0603020a0f110606090a06050d0b011a07030e010e04020403050f010e010608070317 76
    0x40b020840d0150030f4880d83c8450008512580c0c861562040c107180241c41200c50000d03200210100c200100007217000001c1c0641c014805980200d04501076083c00c4542502e203100d440e0f00300d2140100011907652080c065004c0303d010541d0654404000c40046450780b092900c4154140c1c448427050304c1c001700960000b074028074540303000554050407604200e45804640c0042d00c5489020034a0410502140010380c00e0041c0e115007000807401041203840c60b809101e1000d030241e141c003000280c254403440e41c08000f03006030340c401d44c0303450b90b880d10020081e41c07001020000040e5501400604680280010700084c14941c1c003920b8655a8001840341c070840051481030f40a071150400100354654480d1020128056941040790b503040026400d442800c41c0b090040d090340402202d0701280c1c0c014900c0440c41401d284c09500b0b0b194020005010b80500c1d00090314a00400d120410564815801181c0807030141000307100c0c9075514a0070320f450719034512001e000b821211240c09004141d407001803a07007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 332872562 1250 332871312 332871337
    0x50f04150b03160809060703050c0c010504060c020f16090b180c0c01060e06221d1c05030c0304080331020f0301110a141201030302031206030303040f02060703021e2401050d0305 78
    0x41c02d100402f02403e4400503202034651a50700d040301041103030305101500903001c41e80c00809090707403c5903929400a05510480a06960fa0504c211440d034455901e140029200180101c0a050034821019507510030080301e440c0d0f62918a001030211401405030348a450010a4101d502c0030b0745201d41c4503101d0800355407031442d550301041a55056540e684c0f401c52120440184200381e2240f203c910482c0c8904112428802c05104104000400c401103e60041e84010040c0d2252a03e14041c1e01103500c2c00700480e03c2d4040f00034401a40c0c400782c01407a0480f402110510030302c0729074400341401c8809504001c0840c41f42000b603002c806010b00c0d21003842078070340440d5a00e0040c010400e031122a40c20b800c100c0c016040000e4184660003a10010b54000300f0803800355140d820566038800507a68140402030080c44042107850515009004910804181c4c1c4000d031001d013171000d02951101c0001e61000d0301c44040d4442c1d5012039103480b86480c10b94001800800c3c2c80b60080d24261610b03007006420140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 332873812 1250 332872562 332872567
    0x12040201180611160b07080703020703080708030601020d11030415090b0315130b0307151205010806090d2609100609020904060501080907050f04150b03160809060703050c 75
    0x159440c03509140c1c000c00c0c00da03490390416011601441d04100c50048441075000d12181d040c07003000c0d0040304a522599100800642e9180f451405a0901405610140080101090300300c103020b80740f00103603c40d4109a086e00c00344400b44400340e4100ca012103011030154010300050144070035440f01442c2031551408c1074240c42d80d84468852166004440400d544c510040c046411828070104400843d08032041c240050340345500800c2d0780305428420f8040c45c0130b82d0346a001c03080b4062802d1a40104d03d00c0750500181d038407403841035920300b401d8a09081502c075408034180840d00c140c1b40d41103407890902c0e0285108400610b8007031320100242041c80240504020054461014030030b1074002c0160b41009601c1e00051001c020032100d06500460501054038100941118003103400740a03200c6c00c035203085c1c0c0a202207002c280244a4411640700108000e07902044040910b00a14840c0b90744d958a041c4070f0703000c12002c65000000342d8403100268808002304000500980009900814551100c2e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 332875062 1250 332873812 332873837
    0x12090a031e2102040609050a0614030705220806010504060f05040c0e090708011d07021e01020f040602060a05010815070503060414150a1a1e0405060714011404020612040201 76
    0x1450009491002402c00c1d0340014201301d071541002d0b501c2d00030007085030380c000c0b603d141090107488041a10904890705070b00100083c8004e0003641521600340402c181d00e540796000080101c00c01005002c1e10009120310400050240350602900d402c0e260744120140d0028509014080509043c02c69041400303d01c0a458110b0784440392810700ca421603a0710460715500d80b0788442c45080310f80c2a1910007498041c01c00c070040b0303000554005001010100c0c11105441508003c1c024020b4660b038200003c40080c000032050360000c0d0a074080d96261100b0005a641c64500315541c50a25109503604d42404001a2030240038130087e650141d00544081640c0782d040c0c011310300202c0d0898448980a00d541e01c803030140e0034041d6850000d041980320202090442e840440b00394010707100c1c0b8101c2c004044200c0d071000805002524001d20020b0100341d00c1e005145000c0b050403001c0898402150728140740e00c000c818030b0300c4909002d1500a0302040c50203000950401940800400503414882441d0003003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 332876312 1250 332875062 332875097
    0x40b0301060902130f1a07030c03110f03040e010f08060609070c080f2703070b0903011e051e04030801030204050c0c103903021315020312090a031e 65
    0x419024000380c4611504c142090880d0341c02d18510b411490081640a00c3c05100042d408100c800aa0301401c20042506030351408403598442c484005406001e01e0200030fa981e00c001001d441a280d50214158840c0e0321440190032911040c0f0910005500c0040414507a040035030f90300da000385180c80c01c140008280d4940b0541a0300c40d12070182168000075990101003154107504851154034084843c090044500003a43c4000354007540642c00000a00f003035140c2e0b025804060301d28007240c4504038000781d410b07100d001004201c2c1c6400102c08502c00c1191840c201240e4144074503415122100310b40d007581c0a0000902c0002c1c00700d10540010080c07050300030801c00250360b030340c003501c040400c1c0001710701070002c1d40038040d9500c014103a103020001c2c081c8840e1409082c81d222050310380140c840300c950102e561540220b62142c0300b8400c54401d00780d0682e60200080030380440078618000140c40d00d15075140d40c1c2c10001c0c1c0144c000342d50101007044200710326014a40c0744c4bc0d140303800c2420310340703103c4103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 332877562 1250 332876312 332876317
    0x240c070f060207141c030e0310140906100812030402040f091b0b0f07060506010306030210020c04142a0d021303020301060905010501082a03090109140615040b0301060902 75
    0x400090f070b0280104100c030314018100213079901d000362440303102c0e840031000464003100200801000e01c180c0519074202c98504120f01d80b1484103950b0103100c6068401c00303401c081d40040e07440401e5400765000140d04017140c281d2007c1241d90000061048850724404012242c01c040c01c00c0742d01617118058901146002c1c040d00710300d580100808040302c012000c4460f0402c0090b400b51302c10b00f1060140f031100c1d42d560825100800d030442c901292503501c0c07100403002481507800095001e540100380349132540c0c1c002001d081045d400e490810040e0500c011080712648122500106c1400000406140741603c07160240041000051541130450f9020300c003050303800000c110814155040341c02c1080d80b500b4022003006200c418020842541020002020100028004030b1480080c1079441c0350000e22141c028150444100c000f526801d007920f0280c0a002c0c2e581d000d54880041300740900001d4404038040b8081d24560149035401c9401d0010b08c00039000f0039055170303415580e82e000003451141a000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 332878812 1250 332877562 332877569
    0x290103050319110a0204020702040b030d05030a0f200703090b0a0c050705041103010605071a0708041232120405010b1201060b0319020d1118240c070f 66
    0x14686900d0180066251042e00c903501c01d0400440302e00c6000750b440e01080070003489405580c0580c0d182d04a0001c03401401207080c03006d805100c0c1201031841c0d16401350141d80079803035090f400e10400900d000082d080d00c0031040500285a405604180c0f4400400014010030340300303042062440e5640d685201d03013a000403204402040c0c03c01c50f90420400c00f03000c000080c0004903410000ca4811001e07610040c003050250100b0f1240009100e41400303294603c6644140f02c406402c00c80e440c01880050045409039000c941c0e0340e05042040808901030800c4402c1102c08069030081c981c420701800440400c001c00c54614028100030303901020084c601020b12643c0154008201c8245140610980420518400c103169142407420b0050780610402c0b290444004244142500340040c0403400a1258401a001652078031003902d0901d02c2d020050f0401039079000c5284081244031081c40030b01005030f0000e09015003c1181e42040441c50005000e9000003401100c025540700c0e1000031400e102c940 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 332880062 1250 332878812 332878823
    0x6060405132a080a200d140709050109020c210d05041a0c1303060209060c030a0c020306060103200706061511071202030c090903092805010807050403290103 69
    0x2c1c200c000805282d007540003002100c00508000700c01c1c0d101c1100301000500b8801004050264201c010381e54480e031121810b0f000003512500c1c00e4503616a0b6a10b031040d01c030709948542000e000040e02001c6100365100017265400bd0007883c200c0c030041701480d05070a00464840c6506000c0d044803841c643c41802d20491040c80c0c40c143c01c4c4006003080c65008401050001011020802c42c4d48980313407000c00b58201c03548000c01584402c030003000540301d0300a98580342c42510001c2050040c5543c4801007c50050080d82503440a4032003134011825142964100ba1000443d51600380240d86060001d020141c0141000a583d503181e011100d103481c05228204009008041c0710000f407070f824080d02c7c0c0104094091104c180415901194540012054151103041c0a01c00203007000c80c01d1081b1601d00e40004c0c09400d00118225105101982d448203011055441c490041210350007021741a020701941d48070281001d1850b0780c1d1304440c2000310b104002802000c1c80b10140c601001407030a01840c071a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 332881312 1250 332880062 332880113
    0x80703110c060618040201090b030c0f030c1306030209030a080c16080d03180201080c031503030a0c0308090304050607081810030209120604150c050c0a030207060207090e0606040513 80
    0x4404001d04d03180080c5a640c030b013030340d01c034103000040c0c3e00b040e425411150050304041d1665200c420400c4103000c0d14000000c250400000c22005203040030092404039400c0c0540d07010f0985480b000c81c102d0150b6400b541d0140c5c03100403400003180c504400340c0040910a411500e640381d000c5041c00300c40340c0075401000140c0c0800401c03440d098040c0500b00d6114603000200b000140385400090191402030007024521030004007064040e8200741e4001040e01c1c1c09401c032643c8400e003070001421240102002d800081d0f410010804084005c403c4a00300d0b0720040009052044584956a1651000606a00000d00c05248100588414100b10190101520b005841d2a2032070144911155107042008041c0c200e03e040000140340003409000c0e030f8250070000154100ca000080d00c00e440b8126101120b440341c441c0c3c6008041c0d0000320082a541d00303500ba9865950340e0485942611307070122058a01c0d81241d030016542e400c1030780c000703544140b900310140c5920b0b05545034105000940304d82743d04001c082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 332882562 1250 332881312 332881321
    0xc0f02060a0e181b030916080f010c02061006140c10020409050f0601140a03150e0114030303040f0803101e0303021b01080406050402150d020d1b0c03080703110c06 72
    0xf4141001c41d2443c445050740c181c6880b01621840011900200c80216008400b26950340c0c1c04010308a488105050180c030301c1030301c984281e84c1c2d13404401603000ca55070800f0351001d80d0b0ba10214089014011071480300f00b6440c10848107607600b1382ca100c13b49080e0034040c4403204600b28204030403500c42900703a0005070b4984c240100241aa080203080b403101c82c02c0e03402842003d0340d2000352040c1440d40e010a0325100e0961000850143c03500e100a054a0801c02c1c8010a4075203103088003904a80041000308070001c40d40081c95140d020454000d0164210160844080f820003401035034031403085c9210b082407548030058190f41002801c004041d054010000703204150301044840d92070005c01001000107100d880008020706001840241074903203903004182191540030701d10040c0518840c6a0342c498011a040000942010902c2c840c164203150304241e00202e02410040605403580c0e03040003051f8192800c0e030700200701504074001c241d42c601100142142c0340018110f0822440080c0440c0e082 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 332883812 1250 332882562 332882569
    0x1e02010e120904200a111f050f010603060e01090c030f060b12010506040f03170906071a010b030103080a03050601120c05180603010e040b0c070507060305010305101a010c0f02060a0e 80
    0x6200d291225428207400d0407130b450014040c183c03402c400141c90300c41101070040ba0704505101c0700c2035062004000d15140641c040105800c058450254071403210744c03980c1d8600040341a911140b017031300b90681c02400140140812a007052807501c595060212320211104042400c40e10f5507030003918203a002044003c040803484007124014501118100e060a04121030750000c90107130b2000416001c183d1240c82000a882415070350442d00040c07480d901d0b04005c0c01c104200c1041da0420f41c1d000c500110001c501694443c00340c0e8160b0b030700044800e003842002d03070701600248409805d19041c0032840666440241482c0140104013501307030b44154450b0091141622000d075483c000c036100381e8003400180300c0910400a030903803041d0402018040c80d16520700c40103441c89421b001801c2d5010315200841d4080d05508418100d0f445141203a6003100c1c1d000f9050110307059011040d00070804061071075410340c400c101c0c00c4009402818048411151a800502198801c041000105614542d00407007482d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 332885062 1250 332883812 332883821
    0xc02090702010608120c0106030501230a0c020d0c0501140c0d0b09012412020f12010e0907140a080a06050a0612082d13180c1e02010e120904 62
    0x95190000f808003606050300c003501c40d29503011000c580301000c03940038031405094001030002c5410000030402c44140c24481e48200c49c547c02000c0030403a450002c0b0341110342070303c984010140141e0140a0000300c10204135500b4040190a841030b41d241c1c1c8850070011003110019000341000f2701c0c00c0b0b0340c5200500710034064520100c0994070485052004000800d480070380e0b03d280d50f6450902090001214070140d80304d00804c01c1643c1003a1020503a020100b405100601c58400031450065a1b0b80e44c0d0b940d0304800312001c81d10000541c103d0700c0100041030110007040807104d801050f0f442c0e46a00c40305007601e8400c0c0034905560312900d0303806120540f0b03030720f129407005054000d02080d00d0b800c103512030184902c90515582031656460141c900212040c000741100e01860000d05a40d81c42070b070010740b104c030100d4010519030180d0307065541450501480ba02030700300159246c0311840044861071500c81425018090103554a0340300041000000380032000018030110195a00c40d14410203100c11603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 332886312 1250 332885062 332885071
    0x130b0a0c03021905060c131203030b03070b210601140c06181606120f0914070b03061c060f180512040608010506070c030605070e040f05010312050f04030b01060c0209 73
    0xd4642c11a0f0402041010842039801816041a0b540e0760100b0314800400c080da55002c0040f07000e41198000c109039058014207a4503004400301c8010341e40b6401104406d100c0c0c980781c0350011300f62840b000a4101004000b0754007072414101161144140f200811440c1e000c1000420190081c42c1004a0400404480c40500030903000408188500d044503411b8011107004a00512110400c4101d002c24650441c4540702041201481080080c1c604040b61500c1112601035a00500001007110309100094901c1000c0042250510061501c0c024502000d40c03802582d90a881d800780149a02e02406804070300d500142e400707903c42ca0903041c041c2c2030100442c074114055104010410806074015910313810365a0484030941d035201203180c152a480001d61000782010b0501c030801002d150041d00000c5005002c0c1c17003d00407403a0283d480300440c0c000740801040d80c0c1c0c240e1200100c8234402d001400a80454501c01032074a6120f85070904051000d9015100148080140a00f10b042c034030030300740c2c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 332887562 1250 332886312 332886343
    0xc180e060c030c0d0603020a2402060601051605010227090702060f01060f0c120206011e0528081507030b0904020d03080a1e0b010306051f05130b0a0c0302 68
    0x90900144802092102904000f203403400440c0d000d50725003003584003a00a590081550388090f0f9030355040b4102e085a081c00c1030b11220207007a210503039400400e219100e07000503515a0320b06001d60610401a85206806441540d400d2041c203c1c420050722140004034040b4050121512170070003000f0780c2010090824003113402c0001030111484943d03004a055846034109a0b00c6020f0344001114110b8054902401101440c0c004441352070700411300d10b0680340c10035500c60b56488007000708101180b00d0700c06d0942018251000c050000b0004500b6030600c0d007003a54040325181d8440a45140020400c1050034282e06002031008450b0140314804440074143c0d580c3c00a03284ca900018280b0051400203414401c204000840411160f40080000e2042010084441564000aa001303040a040a42c007181c40c1090208a030300d0060b12140300c22034011000d140504140008a81d80e17004590304c0040d18403108004076024110034080c06d8001c00341d946140c186001801e00900e17115004c501c2140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 332888812 1250 332887562 332887573
    0x602040e06010f080112020d020d11010206090703020105040308090102031605161232070303180e0c1804060b07060c080a02130e04140f0d0f0e09220c180e 68
    0x50b0b25130071002d5076044855180a1b500340300314a0002c5501c0d4140014004c3d0b1200310b05031640d040001400c045801488282c0c00c483d041c1e52800101c550f107050318000a404100d09000801c006075034400100142c40042c41540d0034150340c0084680d042d51070a50840e617681280b004054103580300040c80d0000c20344d84c800c1b0005040b164031005622071180c00c1e03241d40d0305000c1d215003441d651030948448071603200f5000c850900d030780e034100205000f00f184412012402d900e900010b0840c182c49405015030103400b03440c1e1900003c040000d80f0410484d0341c0941050301c1d004000b45031669180584500380c016a03011030b203075441d40c50003411480001c0c241c4e05890f00c144820a01028030081355010b5842d510380840041d21642020300342c42485000340c0106110354002c840c07007008003040000142e03089454410ba03a01d8080d4040d180c1c80c00c182c0c110740d0030048e0080021021131005c002c8213034615040c1003030144810140c4400742000c1c5682c0286291b40403440c1c000110344514400c0605c9900d41101a00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 332890062 1250 332888812 332888837
    0x301050115030203090a0c0f18020703020d0f02070306020f030106181a180409031115070c020630071403010509060f030304151701060201090f0219080a0602040e0601 73
    0x301c000704400c894410150b0201c009580c09408010f20003a850b000040210303a259141d141c54103250140c025145c1c0a00c2c40a00c0c440e440455001340da140c184d0540150510700d041040403111540c07500c40c1102180705034100080850524401000503000c4008010b40e00c3d814050013405c0d1031a9025940310450380039604100c0c0f0b41c0902d41210240140e034020550b03c043c84144900149200710f0b00c00c1d40245480410802c240e000844008850000000e94203c02030001c06840c401c0d070202c4100012030003d0340e9401c0103107000d030014030f0088180007014554040c0c030840c000307800034000d2185c22107102003c148281039420544580c282c400c10620766240d581040c020130340d20880074107101e00a55814440c80d0b141c0e0f6003482aa4050b19080342001b0411514070300040c116001c40c140500d0043c0c4c29400440d0091060041c2d8044d16048080c45509001d01d6003845280c0750710305040c1e8400c161550000c110040300b070108140d454041d010140c8c035541005281105014064842c5041c0203030829240c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 332891312 1250 332890062 332890079
    0x102031005180a1d070b09030d05040e0a090f0b1e0117030904020706090206160201030b0d020f010c150e0703051e060403030e010b0904030c0b010509090307022e09080c03010501 78
    0xa0f9400074800c0d401103110070083d1100715405010201042241c003540101241e50b804031070103008031081c103c08550049041202c166940d12990190380400540480025400c0c0c00a4000d03100a900c1200222280540350300ca52545100548080705290f210314480503c60b5240010700e03015042814030581001000c00079141e680c1316904041d8019500481c140c4240109644003003000d40c2c014041650b15420004403500c3c03d0380e401c40480c0880e2070080014410f00307168034156082603015020820f94440f020041d10054044d00044404480c8020307140e000401d1805000e1b0380901e94002401d00d181103103009030a0808034071001401c824010380480701c0000014903507412a0705410b0001c1d6104001a049024006803800a5080340662050204140c2c0c00400f000002d070040940399800d0340c03a1002c2162113901500c484100fa4400c0c40b034a4003524025410041240700c4404190300041d03207079900b6035103903599a07a500203d108124204007444050001040641080300200105c0d810310010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 332892562 1250 332891312 332891359
    0x22106030f0d0c0f1220010204060801050409021f0906030b060903070302010f0c0c0b041d01050310020c010608060a0203040b0109060b0f071506080d030f0b090103080c1e0102031005 80
    0x10300c1001580c0e1082814000944404030140c3d800941202140d014401c0140c5445e42028282c46c000500740200952024184251340c19035500369542c0311103910700410880507110300c0c03a050740d00c00b981c100c0c0600190942c034800380d42d511064171035500440ca455009822250641d1a003801038070100551405a03801203000400d81e075090a102e0f4030048003102c01ca81542c1444030007448074002d07800120306680044050811640d500480188403421452840d40b006c6003845a0340d0594813540c010784800d0142d801a1804841c0c0c0e200000300c4503520900d86107004025034000d00340e10fa000040c401030000216820b405864900c2c000e100440c6421403080280c410035054880003d004108030041021803a0b00b40243c100d10320040c00001c0d120950303d070b1510030821600001c0303442c240c0e640104400600414624000090a400480e0700e90b80b83e26203254010070100460b401170015075480004041819a0000e08001c00141c2300e14280c104041846281e0304601d00c01e0b84c000d2070144892000c841c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 332893812 1250 332892562 332892583
    0x30706030e030d0c170601050c0706080705130e0103170f031909060911041b0903021203120114040606050909270a050f010f0c090e0402030709022106030f 68
    0x10002150700c10030003030600394001e04100074042400e00ba03450b42d1040d030041082c0342c4444030310024201c40c0c4514005407114801c11030f2003035090b04040c10400903d4000d0200d103602012905000345407030b0410b55007500001d8950465800c1c00300003401071051100c85400c440010440c12040e0740b0b810840d59200c80580002018081e9618a14418400e0427120f504944a03043e80204103100b0410f4070302d041ca51042d5034160150141e03140040b0000c80301d40c9a4140a00c450303d0743c44101c00c990654003030020703c0600604485546c0b20400c00000e4821500d103c060003000e1820300350404143c0741007000705a403810b44c44242008014006503c2d103603502544c03a81c0001d020804407120603051107003180034980c42c1c098403026004002100b0284800410195003410340f81000300300c1660501e070b549045400d0f00302c890000544403101804080a10011180c00034001030450302020fa5982d600826031340b140302c9401e450b000f11111882d1784c24004000a4028400b1005013000195401401d5912405105c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 332895062 1250 332893812 332893817
    0x50615041d0c04270906020304050604020f0301020a170c1b0303100509060603010905040c05150705011b0c120e09130303050609040b1504090501020f12160c150b0310060617010302030706 82
    0x48060040c090300d64005148a07510110031f540300d04d000e00300707180c81d000c00b110141e0050440c4100c09460f403030107200f211103000068442014822910344040d000c000c008201c03001c000010058400744c142005549491022254010740d07030380c582101c2c0c5d00700c20000c55218901a0008100f44081643d600c82981d054911005001420b6540c0381407011068000717074003880d08150030402c140281030b82d02d4010080140140000c0c81401358924103070581d1180c030143e000001d082c16800800248008040c20440010752401100b001340010006904001c240d80c3d0083c140020039441c4201138160042a0707000b501201d01c83c81d1880c19888400500c0e000910000e54440d5401300e016042d501d48d404000710035044002103444078203844512034a079005046080c028071061001440c21800d0b0001d41c1250190b6a803007603100d00d4541e650204410000b503119083c20f48420840526071000c01c0340a0301c2d0000d641000c140c0034074040004d083c10f070000030700e00c4030864400c0050002d40c80c0012060100c65261 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 332896312 1250 332895062 332895119
    0x60501090902040b0f310f0515040902090612070e0108090f0706030e01060b0d0b09100602250815040b01050a03080403120c020a0b071e020112050615041d0c04 70
    0x1c0001c050031a60009504100c1000d45101c510310301c203046c141c030758043e5a03000135034480d010844600118a1801c80308007082005028900c0aa00505600c0b9000b60465060032401c1a85002481c402c0300c1150018180004140d0701d0360380801c0b0503030840007040107060000302d41482039844400c7da01404040c56150b914082040000758024801021902d88454032070000c1c2000d40c0203426a4034410384602e0745400801c80c002882c0380741408a6840390012304440801c8144480048101e9100b080f40001219001a58040a01c00e241440c00c440c0e01d030501c07a213424500b1401014060f003121b4040c1da59842d00740000317411074003264290381d0062134010046c10350140894980d444008002c0d0010051000020103010140140601c00e100d0550758801c0103104410301080300f05c414020780058403503040c002503480281d00842d000708014204036584c3d010200e10803000e0b4010744c4188003e0b5410041640741040c6030103510341001030099840e14062a2100313903488000405551588007010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 332897562 1250 332896312 332896327
    0xe010f1e0915020a0606050a08030a0c0f0b070e040c0f0507060e030f07030c050d02030f040b160501020a0509090f06011e0e10080f06011806030e120706060501090902040b0f 76
    0x307010200001d04405902c400320070031140b8020b4480241110803288035090980210b820300c1c0500060094445010003141020300d851011205003d030007209544905010964101080d42c0d002030b54402d00c15902c0d502140c51015050008555940e1404000c00c0150205000c0d141d074040c00b1a031500d134106001141c01503402d80c80508510070320800b01c4060400140c400101072b0881e00168010740070342c003a64000c58010303130140c0e124840c0d0b00c1042ca103980100401e01c8030402100181010350a000710024807100540d503040d0883c0d1141d084040810004548600c25140913841e0b071f68400544800c042c200e0a14100103450880d1200040303200007214140f2180310707841800070254810300102003109299804c5009010810192082d118462030303940001c0d1154060310364160b0782000d410b0030313007159881d0190480045c0ac1c003403585c04050040c0340d03214205000c0c4102800801d409680e002071201d2508d800904510f64582c40720800714014041001030b000400b041da40319500003035030f885d5160704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 332898812 1250 332897562 332897567
    0x30906021308070609060305090304170c1809010b0109140405062701180c090e15040203010b0d0c1d190806100501030b060903030708070305040302030613030e010f1e 73
    0x151000c00c944406500000504090005640004c50704291a0000c4154480750220150741c0c0c11181c100e5660702c00c000400c0180300403442903082c81c2004003500c04002080c0005681c07092880141c5040c04098414400300310820312443c14046001d0811440c00d9141c0010310840c000101516032040d6603560018a507512800280900c042c0d68481024107180c407a004180ca14101307000c1c0c030210403000080030181260502c6154040304031910b41c0780d002880c0008a50600c600248800403032030b44003148010310f4540d40050b501130520041c80548407403892400e04200d40e858039081d010803100b1903800782c12201d0b00300450705240050710040071700d1459200703180e40b08005a100b0359141c8220410401d682a508100c101520001d0341d051020300715070b00810140780507008980c1c0e41604100f20040014449400401405201c1e0414509066407a0006410300000311aa080445a088508010554006e40c0140d40d42002d0908190243c2401c0009208452030150103400e40c1c52110003171840c60 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 332900062 1250 332898812 332898817
    0x160905040204110409050a150b070212010227100c0b0a0504030203040317030a110310060516020d051c180b0d09060c020c0906030d020309090a0e0d09050f09060108010603090602 78
    0x3c034400207550b02c580e10070b401c070001e140807106080200d20303003844051f004a00c8207142d4121003152002e2410009940c00300400103c100c926202150b44c200600c2c103039500c0c0f4504040c075075101041d00f103d200c0d00d01c81c107002d411160111440100005c0030703030040c00116403003002500034203410b20002d0365a8442ca403d904e035100725000170348405142c1500198022000f4015441840030b10824855011006a840c0381c40c0030035214a01c00c0501d468044c07000718400c0018240d50141304003071986294254010400400e1401015100d40e0005e0f8100e00d04131100700c410042c140c800c2d10701075460061414040c1c01d0484c5a006030b00c020640000d4886640440f0f82000d0a980c0e000102000700c06403070900030795035002540c4e025000b4104500000c0d120700e000700d0005184034458001d5071800c45040e04104c0c001100410145100359940d8405585503c104080da22081c401d4540c00403140c10081000100d000e04406140300b0405101006100e0341e0103030311281101c401d0b040c0802d81e80510300c0e200b8041d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 332901312 1250 332900062 332900081
    0xc0a030b09190b040504031e0c1208041406060d12020102070c0807060e01030b13051003050307060506120309010c082d1b030a0903020d022d010f02160905040204 71
    0x1541d40060000d03058286240182d0885107120411282c00d1040900c020b4030030494020b004644040e220311400c4800341340004543d0054070b4298005415035840500386d810a0901c3d000003400b030f07420041040b40c0c4101c100503645420740100680e01e85800020380c00301d40071500400405e0360613641e191050007501641c080b55030103840101c040b40c0b070310300301947c42c1120f00c20a40001d610005440c51540240315141c100800680840305083d990a4003502400002d0319441240d81c81c4240000815418005804182e10030300c1c01081c1420120b040100340d1903150b0901c0b11903041004517041583e0090030760307205103034004021604c1d500710b020051910101c43c208040d490524510b031017140c440d8800100f600e90203a000488001000b13201056690040100c6032010403002c0700c051002d441d02111210f501440241710b401100b000c2c1041f802880b40c0700c8044000000c8003181c0d007400b5a013011a03030300720808900c010310303880c607a40101c0080c0c04207611600b450036540d98045400d54071141c0000641 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 332902562 1250 332901312 332901319
    0x705060706021903140a110306040b0f12030c0607050f18030c040603060207020a060804080414060706020403060e0f03031e040c050901060207030b0c0708030a1e111309060e0c0a030b 80
    0x121400e0314009800b400020341e441018110805c000f9050010a1180010407100d08480030f00719518041400020000300000583c00045040c2010b607940e0781c00c0c00d131010782501001440d181c40c07807101002c3c0f6014015210a003405810321220a8030711400080d41c00c4000720003a00c2030060000c0002c40c1c248004000c00130380041c1041b10110034028590002c000c030910956213038169643e40c4404440e4141c05881c0103007010b0003000108202d07807040d0803900305000020300c0b940c0781c1070b015994007003207910560003141c030a501e4005415480d40c0a0241c40f0314403198a01a518501e0824081060781c24200c200c0502d200b1203601007018880d00d0900400a4100684519000e5031113007000703581d448032844101c403c00034480000f25003a1090080c2c65640e40d216060b903040d5102d4900140140005510707020180d86148241c5d0031041050060b0a2455802c50386295122042c80310b64400c05920f81140c43c0041c2000300030000340507901400c0350b129041c185403540b14041c89000f100540500510a0350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 332903812 1250 332902562 332902597
    0x1c020f06030a1d030903151f031101120c05091507061d0f15040b0c0d0603120f030b0a052701180b010e1003020d020403080304050c10020f070506070602 67
    0x80d507400d03c1d8000c1d9441000d260000c140800d0030003d0326503c1c442d603204940c06070000f110402c1104001c103040358001a0441c640700c60501355981490680c1c00960080e209242c4c01000102e1950b0480a080303491b010b0010b050005085103100988240300b40c00d6014002c10100440750306461500c1c1c00d4071200769003da4244001d01081400e00000790000707090821902078000307a100c00140000341ca41080306024820f051540c0d440d00c030344800b6800101030100c2c0c0c80c410045c100300785649100724030155200f414040a11030300030310010032a10007044043e040c0f41c43c0c40601c480d641e49030b510301d400f1a075086030031100c400400c040494800c90001c2200d018115101c0010609000018600040d01001e8204200075064140115451941108455086034100c005800c031140700303400502180203440400b501d0151340e5994180e0030350086800f81c4460300204600e41403890b210214103040750582c0700504d50501d210000759190715882c407c144c440c9100042650130020650145da0982c1a059078121 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 332905062 1250 332903812 332903821
    0x1e050102070c031416090209010917010f06060306080a020909010e0a0b09150c03180721060f0203010e07111501083a0c0807020303040f031b03021c020f0603 69
    0x41800515000c2114094030310444c100c00d0301c80009400b000480f4102003c80080c4ca010390301c0d0020b50201d140c080c1000407188011500e0103d4103800903011800000010313a514240c95010201d89a98010b0300416082c190204600600007484015040c2c044810a2958a075001c000d401001100203011a50152301c8800c8140b11170021050f204810001c2a030708014088518010b510004a074040001c881c1030000c90107150400c0030046851605004581441e52119200315480fa450121494040d40d004034110800c0b0143c060880d07803d280c0b205c25410355041080350720380058020310318810801e081044022f41c01c0300b04840e82032046502c0240456584984809840301042010900088000850a0002061140b00d40280154042c000100e051101d00803100c2210030101030310301c100148900340240c0d6003800100001c0c0800e0781208130161540c84c141c142a910000e4281042690b20001c00141e111109001d001c00101005001e8600643c40020803051087c000035401c00b03804010170 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 332906312 1250 332905062 332905073
    0x105090402070c032030070b13140607080403150b0d0c080d080f01140103090b0106080412020304060504031712190b040614041d060c0403030e0103050609041e05010207 74
    0x21107140c0c5160302c2e800c007200340d074038140911902c1a413040e02e0140b010030000e03803000854204510301c11340c4903002c7e60820340c1e07224a4601c1e03136007007507011010901582d00108a00401c3e520402c0c005042039492508108a644a1810500803440050b0101110380d076000f007600714940c4000302c070500082140d4a0064542400701640c911405940401d206011081d6213441c000e140551040d141d28540f10416030a0406601514040444240c103141d2686001000107c070041021f0192807580d982c01840c2c034040c01c00e079141e41400616201950001c000c24819280d02004a0b800d4a030004d551185400c06004e1070081031150740e1000006412100c04d00c030004d2410308113226500002e20b030071301c5a0080c2100304801c40d00c062140340310b644550000c1e19134908040e048048500c0c07080c141c041041064900c80d60400d582200c0c4003680300c400042c140205500f03e03500c408114002c0c40d08000928040c400310317200c40c101920142104000c00f4820804082d0300705824140c9900000a54842400f458003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 332907562 1250 332906312 332906333
    0x408100906050601050702101d09090d141224030a110a0b040e0406050406090f03020309180c0a18050316081b03060c031f080a0b06010306050f0105090402070c03 71
    0x11180c01d814000420240d61242007034a42590b0001c00302d40d8030885000b0f0687d00d40c44165418401d003074103624040215540d400c6014030401900c0c1c05403017480d104c3d40005150702c90550007050b0444061000c0d40c030322030304032141544c8598101045c400105035110b12002c49600d550500d03034903210701c41e400ea0400100c08400c5868800c195030210034252a60100b2060b0f006a0080060b04044040014045201a000240c101d80a80c2000582c0025511500c06890541e481078015030b1001540c2500b5040642d43d080c1940302200c200d07982820045071411071440780c1c1c1c0d000c0003004440d03030041d5a811070304034040000300001002c035220840c0110243c0c080291070300c5154210300900d11030740c85a1480400e030320808813004000e07056555412071511540e40015016506203c030b540341e070b01d056062441003080a0403543d001065842c0086c40c0002c52100020802c604040c00c0820801407512141c00103810325009080403500e40c22001e0224000740200d41c405814003003001c8001051220580c0b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 332908812 1250 332907562 332907581
    0x91e020c150105010e010c0b04020402040f0b04031e02090c1b0d0908010e0102070201200c030109030e03010b01140d020d0e0a080405030609071a03040201052101050a12051e03040810 80
    0x307080e403036a6140015074049041c005640c0c081000d003140796001030b01c85c040c0c403640305100400050901e5210340855140c440395400c14440d08800003000d10a100089050f850401c044494641100c1d900e5404501070800103040c80012060128042c81540d170b400254100c0740b000300013114036280e01e82070b00030311144092280403e20352a02c00d54510609060080b560f2145c2c06844d1402d28012503140081d214440c1c0007908402d0048040401c99a0707400c2c01a05087c0b8004e07501c001d05181ca16040508481212000a0500001c0c00c200001250b101d8207803a20807002840041e2600840700040c0d010f00104c1c040b2101600038208000104442c010150003034038001d80c120b544541c0c40b10001c65807040303607001e202075070305459600543d03045040c0000d50703103d48185091424080039105800400e100c00303020380d0842114400510440c1006605d9000401c0207185807051711010341c0751907441c3d071211603407100480840c0c0c0c880d81c0c91890400c1150700414000313080301c44900798414071400a14034102c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 332910062 1250 332908812 332908843
    0x415080406020d0515360c041211010e0d020d0201030509070518040b18072918030d0e1c0f17070b0604020405011e180b0d180507091e020c 61
    0x1403540c00c1c00d0b04940c88103e8540c03001061b403d030759040780e1a01c0208240003003039140282030030403000c074000d11082d100700f01034ae10442e004404002031800241142c02c2003050940669040381c5e10700e0159a403008802a000e40a013000241500c8003c4618284051a040190040a8890009a0605265901807041b80140301580e060b864450307100d42480019500d03030030f55501104043c8681c5002443d0801d00a04041a00e08a05c035800f00300845600200e0306420100c0c1c509800041a0609000c0d000121410380360800c2c0c102591400130b00c0e24003100c80320109050182c00000108610340605410301c42d048200105030a007035403038024195110020440e1005880c402080960802c0d0003a0b80540d04140c40300541c00408000c6000802c000390f14500c00c000d000c0c920840b81402d1804010702a12501d200305075510b503c40c03070341020f41d20300ca8454500040d6011003940462800708142c019100ca2010108040801e01501103000c444011050781040c4006140d242c01000080c8150b800108003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 332911312 1250 332910062 332910079
    0x308090f010504050a110d0c090b01140a0c20031218090f01060c24020703230403080c03040302030d03140709080d0e010207090e01090201140415080406020d0515 71
    0x3006500d003aa00b06403401451036102900d0200000c03a10071294800100c05004007452000986914a8203007480d4041c04c01d05a442a03030b804196804403081e0040c00803210218a01410084010700c4030103c87d801502c4ea0029042500501204001a4000c800000e04840c0070001881040311184d10170002d02c08280c54a0410303503214205001410320a900c1040f44154076032031700da000e40d04021418030413252029600e10021407543c1c000300c010200c0c01c50305c0c40140c0303c046628000c0c00340344502154011200c41d4560f6194141125012541900d92003440b158840c1c0c81800158510302840c0c10095041c0a00c0c0e5910701c1590740350303001c0584202c408444040350348803e1001d5804005901803444140c0220090307000c2c0e00d020b114540031124042c41244d094595030800c41c4100c41c2066040341807a5103402e06c0206560b40445001010851116024580351074a40305d400d503200945244024480701e40c000900f0b101c4660b0585d0031031180b8040600003481c02d06000c020b00d907210300c9924070444030b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 332912562 1250 332911312 332911333
    0xc0801020f21010608010608071b05062706040206220e060a12021f090e01080a0507060207060e01030b0d0b09060108010e03071a061c110a05010f0519051303030809 72
    0x41894034104c2c1c0c196250044c86900b06001200c09100080524050010601c4504038107410070a40d212642d014901500f0141443c0740d4000029030041c1d0450341c1540c00388175086031010045401508180c0c100c41150b0b071095441c00407401071484140b040340500c0c0e204c0c80000ca80880b040078a1180c14100c940032100f5884103404a84044070300c002030340152418071000080d0450a1038071080015500f406011207075036803da441c18071800d80241d212a0011541749041010400c40100600018000b0b0b02060b424003400400e4864081c0000341003684030995403a0340c1e22030507010504180c1010366002245007001200f99604000c3c4501d006540c68130300c103070700c2c2d030300012007030342d802c103622940d6007070309042c03091102a0714034001c1e103003039800131201d00e82d41038080f5100006130b01144669100c94034410820308100140c640c90f84101c0c103000d18080105101a4444102c0e90500b07003d009410400c0c1c041030040f10903005030244520180030111022040c541c000c641c15125007090001c031000e0100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 332913669 1107 332912562 332912617
    0x112060f030302010f0615080a0f061502011e0605060f071403130e010501050405060409050907081b19120b0919061e05100902070c0801020f 62
    0x90350f2081002d003117540f40a408010400641034075482104285d0144c00020028051640f4a6440c01d1804046a950b80004050140e50000d14101000204045d009002001000e0004d848a604040e50024a80a14410344801800392030601c0400c2102d8040d40d0442d1500311801044c441c417034010300c0c0041010386101c0b0404100c0203030041c0b42c90120805001c1c1078220380d0402604000030f011903140c3c40b044800b03d44032141c3c005041d030780380002c007401c200d0b6135000003145010b0b800e030b943c41d42210005444000c00d8119000c2c140c02c0a21241041800c5041c89000c000714810442c03000403529202200368000305000c1078400203601c4525450041c00e92030401c607481a03460007401711841440c1000d040ca03a40c004410042e60034003458807072042c48103100c0c13140c074141c0000303040082000402e031032002012210004d640350250700f00102c0645e00000500030035000d030310143c1c0020b81c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 332733812 332913669 := by
  have h0 := BRFrame.cov_init 332733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 332733812 ≤ n) (h2 : n < 332913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
