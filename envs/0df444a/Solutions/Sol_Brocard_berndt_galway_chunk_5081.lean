-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5081
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:40:44.121608+00:00
-- url     : https://prove2.me/submissions/a534d029-a43d-41ca-95aa-bd02a5bc8a24

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 913669064 ≤ n < 913848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 913670314 1250 913669064 913669069
    0x30d03050603011512030f0201180b09070504060b1e030702061f030804030804061115010b07060b04020309010b010f03090c1a190e01020c0a030507050904050a080703080a0501080f06182a 82
    0x1401f1013220071f0009200038456030030b01d03c42d4880007100241c05d0341e03006400314078540c005100040040900810501c01103840d910000000e90014002c20303807541541e405003561084180c2500d1280100c0d4000e000c55564041024600b080d070712008401c1100c01d040c01000081d0501c0240c000345005040d040c3d111801d008028240038104188030b07000c1e9104907041c824dc41d608803d0bd0741503c05121038251204900c0c07422001614401201c03a41c0325001004120810505601118015000760313240e0003200715a800507000c50349082c4024052000b03e003028032040300c001746101d492140c140c192902c0d00700b10035241072403550b41211140010700b40381040400c969040159280c035000407191b840da40d0b40346686a50340c03060300f4130400740121440301c0010280f1100340300080041d50403614041d40c55402d450010000d11049902802c05c0f89000300105803240002881014181c6200c014007143c2c4410f140d102060809a050101034401d11600d940d850340c0c01140415080380964122107896085400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 913671564 1250 913670314 913670327
    0xd0506040821040c15110f030702040b0a1809140d090305060903041d040219150813081b03040f06052a031c0b09071205060f030d0305060301151203 65
    0xb20400901c50007410b00020a4481e480e25044944041c20914071010744401961003500d40c00c1d01c00c0707030382c0145c1e0600341910340c01000500c00b040c03089a081002d078a007501000101e1046000740c0b00c594003820441d401c020070a81c00029a10700480d40005500c0c0701e80324041c54010043e260900140d00c16004000b081410000c4a42045126016600709428440c190580b01001c000c0300c0c080e9000c5c0c074046010b640742e199565030014843d140e03880034240c451030215845440c0d041c0b2000007500040000e40b8404251405420f0694045d15061418100740140c000c0316110400001c90760000b0000094200c003156030201c02060140c40d200d4407940111042501100c5e08120106461824a03400340c005401000700c0f00c09481182d50b9240d1014021203035001818010601034006d81508180070407283c00141708480b00710b45100c1801190303190018420098440308015402d940440d100300b15071402034100f50782c802c00180001561007450000680c890180c1d61144c008800211501424142d0216 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 913672814 1250 913671564 913671607
    0x282a020a05030d2c040510150201021912060810061a0306030601060c080c0102030a0207110103060f09110903010f0c0f0305070807030218100e0a0801090209040b060d05060408 77
    0x6002c0c3c8400c91501c078014000d5000c0c0a540154a4154641d40b00c540e00116243c0e800030324041c004000704c7c5842101022240c11a000b8000e080c0c070300b5001d0201ea940f0500071034281d1842465440e100040311081600d101e0b03e085a146d4a854980501040700030302004115100780c0d00003c00300311030f407038500d03000c0c0c01341e4007001c22540c240b108104000c85174500084c1603044641c0c1e4900441c510f0800d08245040e4040c242400304a54000010300c4110107594000d0040207008400c1c141191014030010b60840b2100d10072022000c031041e40400800c1c407190701400d60003500d1400e05240210305000607003100c0c08951250b040703076038480030840d10f19403000001d40440c80b1070900301b00a00740b0f01e602604445000b070421041640010f04d6007c607115510384015100006029060300303405008002d8031291420002500865001d20001a04001400741903203940c1c0180800c2c2890702c80741c68040c0c110000074400d070f422815060440c00040c408104203032041d8060b100740d5490301e840f070410010011510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 913674064 1250 913672814 913672819
    0x307060e010204060f1b030e130606091418061309060e250b070209191b080a0204050603041202122205010801230a050a061101060803282a020a05 64
    0x1800c000b075406d69a01c00542d11980500300801e082221200094090703a44100035281c0509020000458a8129503001c0c140c440d0313803030040081486501482034401c40c184041c204000c4e40d502160407801d00c0d1810440707440d41e9503004516102c95480725029a4030b1520060b0b402e40c065a580b03038154040c074a0340d0981104600840e03c11301d00d0a080840c1d14041c1d40f20182c820500700300818441d4010f0481da0340d860200d80c109002440c4280840c07188611143e5111003c5500c48000484845030f0780700311400e440d0014074450541c0c48a40700d011005007a201c90a00394450a8961150303104880007400c201d04071240142d5000040301108501000143d0085041c00b10180c014003059116981c080d50002c084140721f0910a502d9000032201c266950216401032086640031440c0356202445121034a003110003400b804d55034003c080d82d03e114040d1525500300c944104140d1070803501d4500307101e00d1580d00d070071401321010720401c01c0c801001c1e00c3c07103a20f5003c0e20000c80045040c50150100200002c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 913675314 1250 913674064 913674077
    0x1090b01020a0503030f0c04151d010509030d0c080d05010b030114010c0b0c16021e1807090e07140406090503300c03041503061d0601090e090307060e010204060f 71
    0x10b607902d066490001030007900348028980005944001e000c41554014246013003c400301c1c00c00010060b0081e400000d59461003094401d031100707154050307400ca544c00c4001900070100d00d4500e560403555040703000411283d40200308203c0c3d503600c4a0740200e501130500c2604c0c40d035032949011410b203140851440400d06001d40402e0769400f0513121042564000b8010b006284d440b00c07103c0000101c1007110320006c0d40b00b08560318111910b6035075089006603134425545080e0b05c807050303d41e1914080e002c640c00720002d495141b0510070042410034098004210741000414a910140656101e80243d001000002d07d140340400080c50100311401060304c4418080300981c6400d07a0040442c2040450100c016100240e0403001d1001041164010464441c41d1208008031200050203416103104029241c050302240c03001000c090400903000c0d00058545030211880c08000341c00300c00e0004d203010240d0100f401031402062550042120f0521080c000580e11401c1007805030014191a0342d0344d041000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 913676564 1250 913675314 913675333
    0xe0d0e031014160e0307060f18081015030b0f0f0106030b0a091508190c060215061e090f04122f010204030c0b0901020d080708150f100801090b0102 65
    0x44104126004441002c0084aa001d84201900e62240301c04804d43c052150000018800f9441010207200c0782c815511081000524500c2c542e02030a14080d00e00b107038200f049012102003040d07122660001c0711714240708601d5602e40703418014600403614860148035000030810b040142c0030515003d441a814100400c00c08600845c61981a40c000c20020590710002801580700c1020b0b032000901001048448046000b004100c581c0507542c0e04807168100b1103800320356207001144d02104001a00100d0403165944810040011190141000700083c103414403402d9854140e0b44074407a28105030440350720b051070b00d000182403030350040a004000628500340440b4010b110071407a40d00d05042141d0280d00312a100500911a40c4d0004201001090780014512940d4010381200f903801d800380d0707181a4080c04d00391559402102c040c5c000480310744c00a0051112040c40c40364144001d050410705641c41304c0447c070040c0c80c044000001c41e0a00c0010090300c8528010038462140070320182007540c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 913677814 1250 913676564 913676591
    0x712031202040e0f10090c0905030d05091509041404050a03090509010503070302190b040f0f0b0909131104020d020904150b04030308180d120f090809130e0d0e0310 72
    0x100c043c01d214040c541c6200440c00341017441001601a090250081200c1003501802605903005841128024012174801d0716805000d0700a54400e4240035080b41503012049010200582c00047c3c2c459008e41d13181e4480c44049a188280d600ca94400d0000b001d01c0f00190502400c6045141d101501c12100c52005001d152800719011003202d03410b5501e0080b905e001004a440c0700c10750b0f0016030b0007020110b00025a0480d410903c01221001125079260135102c0b82d0011941c030480d01c0703442d0004008808180c1a00180741b0454015000300905240040d6020006007139a2100c80c044a00396004519280f4500e8a842000c8082c0708024801c9010382c94281ea800c03150285101c0a028000b81c800003541521200017881011101801a01c000c2c444002d4040c0c180d1000c040ea2039042403401d014554801c0c49807203010710040d0881c80550420701c078181088049a0f142c1d2100640c1c0b9150199542d10a008121103909a04240c0710441514000418503103441c0d15204d802c403646007008502074503603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 913679064 1250 913677814 913677839
    0x13050c040902070c08060708270307080a031e020c070503190b0907152a022407020904060e010506030d09030308070c120201060801060b0c060f070908071203120204 72
    0x54041c2040561034082c18244440d0b403246070342c41502a80a00c208100c1056485610036104455030a20500d03101841c54041d0407000e1640c14003890350380704120642c04140c0600242100d130407186400304891103061007500c0816041c0c621075950703940202e1000c003072403814407144020340019801050910b00214492030322220f0a1805080c0311030b440c0128a50400034400a00a020046800c003007800700904000c041100a40042d014412142501d01791140142e00a614454004011007440740015140c0404904800042050044100501c03001a26038903c42071080b40502000142441540705050035140020034042c400d4105009a1986a03004680c2106507034049c9001080b41c1d5507190140d6a884012001801003403a42003100703041075054210074144c405040081c8052907940519211901601102c0e0010b0740001c0001926102c1c4108140d900004529050064580c1c40c103c0c0c900b0302215030044074000008034041014142c20949403040260300038400c42c47c091a0000c441c026 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 913680314 1250 913679064 913679069
    0x507080d1202030a06050303031f060306081024080a050105100e0a0908070204020c1b030c1302132c13020a090c11060a090c080304030503040513180606030213050c04 73
    0x400d0760200204491413076039030091300035000240480e6a01c0c00e01e250b424001d07a1050036a641f00b00c601520100342144280507010449050700003c000b60b8040d03001c40c1018042456103400c50810baa12034100d41c0c80b82e205000010a94100500921100390500e40d003515401410400c0b90400a04208104904415506d5108440d04000a080003007403505144510858178043d610030300104442e400300c900810808a107419011080c4d0210707680205140e05d602c3c194030116404406032101551076601d580042140c20760004944464070344590304680f060400217506441041803641541c0d80000d004180750308000542150001d00751b031540010003414490007001c1442c0c1d11040341400c0b0302c0c002c0f0314800300084500103a80c050710300103013208014040950181c882c079100b003a002400400110171181500d40000c0510324060500c41840149070200440382c54540d61492500c6420f900340b02ca00300354030300c50080482c1d41e81c9140100030790400c0891241c490b40d440c20092201e901c00c0c200440f000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 913681564 1250 913680314 913680347
    0xc0522140d0305040f061d040501060219020409020a09151205070b0a0c0606230409021e061603050d1b080402010e0105090406151715010c14010c08040507080d 70
    0x3010280d207003c981d00d005603071004034201e00b030b0440414840e410901c581082c00b20114440b00f100e50700010481500d00038070030300c0056081141326810348105c9030542418140050804124140a540480e00c10071171030f84403442d920780d01d001c107560316010301d03039004020042c401025000c0c2074507441e004d807103030018490310020207c0014010b9030107002c2c0400d028259000361042040b00d5840e4171140308825040b95840239035446011180320383c42c0910500d100750707030084c01903a00921601080c6002c0b030035007420a513210f0300c280080c000e905622120300c034005109640b04c0b0749441500c0909016118403200506011405003d950802c0390300c1008164030540900c0c02814868034074005035031a1084030f20b86508181840e0380130400c1e0742d82e01c0442248040c0c540e07490700000101d900d82d1140150a5070980c8000e186041c41c0368503584203c0300074080134051100c400e8281c07400000c040c01c4032140c0742c0d004049a19a0100414060180030010083c40d4541c05001d411040400061491008405621 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 913682814 1250 913681564 913681579
    0x20a0b13030912050d12020a140a0201060305030a2c130c050c030a080610030935070b0403080603070f0905090102211504020906120403030e010c052214 67
    0xc09141c03095a4900003002c25101c074100100300c60800ba51140c200c120000c010828116002c1d048102920868415207016500e130140c070000320b10a0100381e4490701141c0c04542d00d890012000c500c01740000d00700e092540d10707074501101e050700c10510745402410100c2800d04200381901c00345d40744c00820040684020302e001542004c041000c3d91036005502034580b2030b110219a51500e0341d04007217100c1c09020112600c41c0b80c01103800703007281070b2500c1c040003c0098101007201900d148040c54030010010000c10000c0c03641c003414265120351340203000181e801c500f0380b5090200b8107401040064110b4030035000b42500c0c07410418101c0e40c0c4251071041d100303916a12000101c4581d400c2d0306481c0d074512810f041490760030480c0020001e183c0e054039081c03250000164020280c0c6002e108843d01c0303000c054082400e14400850012048038020030a509160b00c1c0e0f241200f02800a01c40d1151400c00d07a200c56441d0711080c080411800842020880040040c0c8014403842903d0b00c90354865441c11a01e12 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 913684064 1250 913682814 913682851
    0x2010b010525120c0308100302011e1211031905070207121502280f02060604090f0b01090f0f0509120c0703080d020a0f05092101060305120306030d020a0b 68
    0x200e410600d01100688420f0000d000400115403181d03910920728000d5603030301c00703540741c0032200f8030000d40780c0c40002e0100e0070b414a081b07a884904122040c84220b1400c01016400c0324081603020394160803ca130030034803070000803c0840700c070318100e21605500c0b41d04c0411480c40c2c07011010355284281e000c1c0d40184e0b051542003204204807103494222020300808155251810440c040606039103020704182880c00804699141c1882982111050f1003d60b00034003058440b81c00740710003000e8050081c0ca01480b45107207240032598038500d00340209003c410020309003c51203800c0088418944201d59440d0415003807050143d000990702080483c607080055035010301c40c0000c1d140c00125817004002150204600700f805000b03501500b0344d00c81e1381e1100b95019405180c21941841909442540542484041c140700107003100f0220f15a00340c0d800004000c0e480c8d8a4291604c91094441c1000501c008108a220706041c4200030310103099000900030007a1650700c0d4044001d0060080310101080d4944 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 913685314 1250 913684064 913684117
    0x23060406091a0109080d1d0d0609031e0c02060d0b030325110d1203111b03040f080a0308130f060504050f060f131401020c06011d0702010b0105 63
    0x340c009125981c0104032002c1c5061810940e5425808000d000c1110f54200003052400032030b4255003144d01d0355406492000c07241b114480400c54010342c60b00f0000084010b0b00040d030700c0c07240320520f81c020380300c0341840960030740842150b042ca0036441b003c00600808000050720341c02c059610180303102501250303200700440441e2a5004140100c00c0c00c0010981e500c184500f00300c0c00a0b58140210000c1c90031001d8202400072009121300010191614030700e10b00b248500c82ea2042d407120032481000c1c1c0c80d105100790192920032103104070718034503080028100a425800070101c001812282c0103080f89041355207000e05045802006116074000501c401d808020000d490703500510ba002004100d9800c1604100340ea8a07089000310105210342400300c4c100605c10003c00e0b20905209410310b800800c00d941c0c5480112528100c0c06046d9000e1140591b403c60920095020700511030442c1040306401d0108603034007801410210940e490007024040d00e0340c5c00b4040342c5014480e07201807182510120513 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 913686564 1250 913685314 913685321
    0x330b13030209090a0b1e0109020f0d05070e130b0f0f0102030324130905010513120f092402070b03010f091a0301050901020307030c0801120303050c13030f15230604 72
    0x20020800d404001c108036440c00060443c6e11100900e45211641d60380355401141240b2501555034080401480310b40010203982c1c0040b60301150902e0900b010880210201d054800c8182007082280d40746d1401c1d16181c108124003140d8a44112035001010b00c543c00040d40700c0c84050b003043d0800d21049000303c1c2814600a1400e1841000342c0000c943d40d507200c00142c020008000220707100c0d402c0c8008a03500c09070541038004660f421810f079049800c0c0b040f01c00d44d0041016107094091248484001840f00306403640c6041800044440e555504124400281050410b4100da90380c14014401400380b801c0403010581950901d25001802e540410410807000b51004010f0754103600701802c1045186040d00030b1070181d0410b031400d00402d081e031707031080c0c0b0141d00c240540d10360f4100305040c0d040481d100c0e402032034101c0d403010b03045c5141280c903102803458041c00360000c4e03403841c500010150070484106100d0071071f04542c040800400f05410420056082403e0240d9102c103c400080b80300c84e940c951 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 913687814 1250 913686564 913686583
    0x1503080403140327011b1a15060c010b12070305060a09021c030e0a0801060501051611031903090e0f040f080904060f090c0c03080a020a0201330b1303020909 69
    0x250295840090342c207251207203131041d0700418005a420304c1308902c40490304003e21300b8203034002c640845103000c0450034a56083d00504070082d10380b442070306e100c3c56261300004021400200b000490510098802e218108041e20740c480410b50203440c0800110b54007050040c1c10481026002c100d490103400002c4450b64030305542c0d025104207c5012040540000c0c070216040000c0c0d404036400e5940c1d0240d00d00300c41d21445080e0105400304150150003c1c8140c0c1003250510815031504040d0ba840c001c2860103081465070301f11425190007090a0540242429008102c00310100c1100d180800516404100280c0020860482e00460350200400842070b02e00c24040a003040007250380c1c40700c0000b0580c103d403042c84d01035860040c8510600380305461450721a0340548410b41142c45900c0414000c0d402021110304656035042807240b00201d40b810b0070400c01d01d00d0003490200b904014422040c103d96445400f0f411002c01507a05c0d0b641a49040008072501118a0b550540d00e0454141c204003280c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 913689064 1250 913687814 913687837
    0x304140d3503070e011215031b15020d02100c0e01051b120a031d1216020a061709010618020a11030d151e0509060102030c01050a0506030115030804031403 68
    0x402000581a4801052540f18000b40c0c1c491b0300c040403200b800021141012016400c176030741c1c4001880400c000400b031401e8501e405512452060b41c820068042041d40c12004c0e005030819910107040c66030400c040d01c1d160003440c004004205c02c00b04098a10078030004c03582d050080204040c0c460f011a44c0f101004201c103041540c2038191200c03100043c55000034540400300307140c0352616042500010801860a201e0001400040e10400e22824642c01c0451055040801c80e01002c0041c0c4a04004000030400d81e218441c040b1180c41006510150041000300641c0c0b5013602040188062020382c0c4400348004c10048e55803035128400c40d03140c0740309514000b40740300000d1180400e2100c1c0d880200c0c000400401c68404640341c4059203200e00e00c40c0c42c52010b1111403507090100780381c01201c881d08210140101d0b89420810085c560940b0003c0351104842c2e03a94404100c2d441c2420300070503141410f100c03410030381c0702d0955071390810301d0041d804090040d401504403000c10722010401c0ba030000055 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 913690314 1250 913689064 913689067
    0xa031101021306020618010905190c08030c030703031a130f020d0e070501090f08251511010f0207050318010201060b040e01180c051207090b0c0304140d35 68
    0x15054045c2d5114010307920f4a201403815010030315a04418451000c41651010140034505010300901d121800d8440c01942c50b409008000906500100000c05102c40710034055500c52540c0d00340542214190070f150445201d02488004040c0c0ea406080b5420707c08072080040c16000050310f8000900584450007003051400400410703040c030000d802c50488000740c0c0c0d04490a61140d00721011410148a4107601d0b6000b40c0320010313410050046200700d10100c908500c511a076500c60744000003c400381d803101049001c02200712900f420301071041c0000c03855070250719141840d0b407a69528400e0807078180005441c4e8102d201142c0c800e4004000401166100300d460707980398041d41d44030100078818004004042c205110144c110740c0102d001180d81754a5060030081600d001e40260140102940d041044150340460342c106500c0250140c0c4211034000c41d12541007040c0d500c0d0b581030040d1150b200d00c050041440001d800d4040040a40300e161900d0009490070208480c1c600040a0350582d4040d030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 913691564 1250 913690314 913690319
    0x60e0a080403120c0f12021f020d06090509070315060308040b12060a050a0506181e12060c090d15230f091216020a03110910080a0311010213 62
    0x31820080c00650340a0012180c42260004007134a003c036240000409203034214026401080b24440700c45420940707401036400051000d001a00301403d190000c1418a5000c118030b80d46242d0b5214010260a9a81d8208054141030400f01c0e0b5031091440010007008030030304042c0324414140c0065008551014600d40c4543e00c03417600001980080c1e6148103000e0942002035002e01c5c09070a608120f0f48094045900b0713038103000c00c0c0310b2144d1044024114182140009405a490304845c2c5410a010204004818501c800401081400c24080b00074540d1100d0f0038000c00050b508200e03565404115020280030105150480c001c0383c403c08403100701483c0a0b5568442030a01d445c404150916058070700540d40c1d090300710601c05105517030070741c50742d80b080270724003902401e41c4010000d81c00260880d5004200f03d90002c1c851003880c4e0821503401c1d0350080c120315241003100c4030a0700104034a2201282504181e480c6544007148500a400c02804503901c002c2ca040c21350403191035500e00c0484007010b94 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 913692814 1250 913691564 913691573
    0x71a0904051608151003020702010215010308130812091903060f06090f0903020c060c2e110c1902040209270c0906070b06011b0b07090f0311010309060e0a 68
    0x84962580c0c40441d410f6400220a805a0948141c20980c0100350508007030401070110029040b284049042d8400e81c2c040400c1090155401d50085104002d580c0e903e2180c46c2c074002c0c5410300c583c4162030a074020900030855038281000c0d1110011b0079100c210000c0166503291081c4140c5034030145c40d85240c203a80b01030402d600c0e000f0800f601c2c080a0305022800b1112045401c03501780602c0a40143c100e0b184502561030310304014050341c18a4022503a003003c445ca03c459444244030101c040c1410340254540b80300885001d4002001c0541640e14144424072011644031440c2c550003060211240f0820001c541d2031f9415208041406010702c080c002c080194024020615501400751401c050001951016807100b101d0300954050042c5003401150341c0c8149400340c000c1c08250500082d42608030031505141c4000080c54080d07507040d001d6090940c1d0250000c1010380050400714180301c0700f40040741d941c071850101d08400b0f10700021552400c2c244540200810a41c2c0d000600a0350450030611 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 913694064 1250 913692814 913692841
    0xf03070e2e240504081b060405100513050301050610030c140a0c0c0f0b04050d02030a120c120f1e02120a02100605091b070303150e041401060602071a090405 69
    0x3042c00d00300140c440c0024156068001d51089481540c441c030b000340700148500c0c01000e0180c0d17002e0002401c1079181c500050501c5039030740c280c0c000220082505403110980088040040100368020400390a2000121308120326200c480c9043c1520b540c00004080d101e00000f295100c031101c1d805440301400e65000301201c00c0780d0001d03581003503403640101740541d1444101044035100109607141c58a40701c1400b00811407158282e87c035000c1c5c400d54001207030b005840580c881c1e08940e14101400164680b48275400901c00401c0c040001c08140601e4203a0483c03581601d03c00903d0310420951060342040b458a040c88404803079412000c0b60910f03035036400007010400302c01401c0c424042c0a4441050040c010000c41e40071040c0c0f03000003030b04001000318400405c1440d002c0d00c0c02140c504640358180301824150780c0329940d810100001c000031300100c05280c014181c603034802841110b00d0f2540007543d0391103e008140810709400581d40640d0101411560705000c098010f2003030345820001c10a48 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 913695314 1250 913694064 913694099
    0x70b0610050d110702190e07030c0309080a0e090a0207021e041d06070f1e050c07030b01030f14030c25030506010905061011210705060f04020f03070e2e 67
    0x1041c0d4040000c0c2c0048584580c6d006603101c18010b0102a680e201d000c0380940845103c03c020b05990300250b801040044000345084036040e2144d5100781400350a001c0408401003907458044e105210640060707a50301c0340842c06000c0c00c0c10201300910301000050060950541c9a2440d84800e0080c11071100003060140c030456154031500914245000203a4240c0303150081c40d0700b0707444151101c441d014050f401800c45c000a02e001c0f94a1903481c3da44a4001444c03c0c1c000307884d2800e051010000f0030194039108503400c0d040030003542c01d001421052540d59840c4402c10700461450b4103a02c062030f082d180c8480011908101115211750b5250052402001c1c143d500780c1c02500444001001c0314050703048050b0b40310503903000741402030903004601c2025500308008441000704200e9000819400c2000d1400303005035440c511189d007424410441d031404200f41950007504044400c10600c0d0800503140d0303102c01080c4420194080b907050501d051360215900089000c00700300081104a030700640d0414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 913696564 1250 913695314 913695319
    0x8010b090f030d0f2012031f0815011d0604050c1e0405031204030803010902180a0902030f010e010b040b03040f0f0c060e1906110705090916050402070b0610050d110702 74
    0x40001d2804003140d091421041a0841c1c3d111221041d1b00610301c0000710703800302c02803807070341820203090400c40400081c640c0904030039400031000e0603502e10070308002401850055803121000fa00780c980300d070701c01c40014034442c890b039034643c0021800303403c2008840520585580300c60700000d0610100e2003980060040d00d0182c0300304244d50000480100407030b01540c0d0030900c01415a0b1800d4003600184d8402070a00022520b0310103403400c40d07140d40d00400050580e02c240035880746840988010b109005900100c0808845801041180b030100b00b2103065440c50710b0302558030394407401c0c1509105545038000f001142e032031029409100410f079400003a110302d542d4076080c0b08049020003210b68619040303040750a03686441000035500411600010101c40025546010b036144000342d00e410742110207000710341003e00c5c4642c03101940030640300542422a0f0442c1081581c0e02c54019036100100034038022000c0001c10030034180550203490350060316410600c181c1c03072001c24045450300030640403070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 913697814 1250 913696564 913696577
    0x130f0e0303011e090b090402060c07080a200406060e1003090c0f08060a091a060f0d050304050a0f1404020708120106030209040e0331170d020f03030708010b090f030d0f 74
    0x135401c00b290040c0c803050140100030300003d4456800700100b5600c1300c00d0060307061003030000001d02c2007414402c3c100000d000d030b0045c8102140c04104110000010050306218500c0c0100a0140980080c09880307086819140c4c92844044500f0950003800c07003030006402018903910000340c00e03d140716270000780c8141d1001e407000b80e11038400071019070340740400c014842c194861640070082d42c1c51b8035040d80800c0c010261914000590701185901c0c01c076200c191115040000c00f445242820485040213051603d49400c25030f01e04500600ea241145501d00d00c00c81c1c00103410700900045c94207540041c0d03260800e40000c1d50355031401034025444000c0f010300403410300060ba031082030003109540c0010000300c1004c4101c40d1401082580360529104508001500c060110345c800b50300031701c1301194180f10001c00c0e08030b0031542c1c00792502014101410703007a4001c208101d504c42d445032007a41151791440203541c0304c4103a4800195010b00d01d001c1c454140c0309100d90118281d500c16905074040750b643d00c440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 913699064 1250 913697814 913697819
    0x90102070617011505072307060f080a0e010b0a08030316050705031e0c0102180a090920040f020307030c08100f0509041407150914130f0e0303011e 65
    0x41d600e07a20100464420b44914100402811101c0d0040603440080c503d0440d00d00202603803030f03240780c2c0303050444c03c40d49003854108001036000c200803210151002d410501c03903002c900b43d4001d00002e8000e2410902944a0507881c0301c440d001d410001c15403100403d400b084e5615a08015620782084844000000340600d580658a0255044904064105000d54608440a40081801c0c6215204500d03107100401220052000c2071024160007081d0b880407500c1c82200504000d1a640c480d000595558075100c01d40c000100e45c102240c0a54a10420095010224000240c014107161700c0825529000000300400d20342d00d540005102045901c0d03007009a100e241c4842d032012100d0044c3c0c04042c000c18014005031400722040c66202781305844125030604081283c42c107011065000043c84242c4003120000e291b08120300002415900c2c00c2c2a10011800c03000406000521840280d02075513a05203201e01070064100b250620001d1040340d80e03a5030740b07a902815007104642c40301e01034558203001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 913700314 1250 913699064 913699067
    0xc09150706060f0e04300c05070e0a060504050610020c01110c1003021b0727180b0106140a090b070615140103060e0108030d0b030a060e06040308060d0b0109020c0c0a09020901020706 80
    0x3100641340e45017400050015044400d42d8200c021035400d4442d44a1184001070a2b072902030085d2003a116440041032180c940760034001a02c80240c4124852240400c030090b40303a80c00212074070400310900c1c0181088082d42c1e0050b04004254101e590480c8070940f003824529015001884010019101040c1020001841c0d84e1a00b10501442c845820742c40d00c80d90703005107010407091601c440385000007150aa1003010050a50ba003190465102050400410402c2d401c128141c4e807080026034610b20f04400713003400410021483c01403015229000c141d074407e100e210740c0042d0980c8aa010030410707954460780b0700180f01e40450b2155001908240d0086600f07552007400c0d40c100d444107030045040051009011010b000c020504d2070700351081030015000324115000708005642180302416003424030307042c014405a0000c002d01c5c007825200c040940051a607841050458000e0100140c440140074015400d1003040700e4400ea11540c1645c003c506c0e0742c0300b94010700d40b5601c240c007101e4030240e48020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 913701564 1250 913700314 913700363
    0x5160302010f050307230d021303060b27070c022e0507210c121205010b040315050405030c010e06060307210f0203031903090501050c09150706060f0e04 67
    0x160900040c00022a580c03040f02c14904006c3d4550300c00e428a81029200b088604c1260807410034405e158280c0c040420034800329110380d8958010541d16400074031070709030307581d51740c41d1620031305160b2040e20f840081e591500ca08594407071280e000301200e4070303404c00c4141011000302803082040d6203440001040c2c01c16020350704580c1c100d0b0348440c03004003d0b0607202500c640300c0a035100e000c0502000c418108001009100c1c10010740d00c071600c0e040d4031b007291240400100c9205030880d0000f501c0401c03040c400b181241c0140280e00c0340c0320300c01042c3c80d51103183c0b103400d5015000d0400210360030035401d20a440e2010418034400e540541c101d074903140d47c6081036141217664003c40d5010803860804200030400f011071010810307002908481c6418080300c03c1c0100c8034803044014002940d40c00310402005028020241c025650706000c40c18000403000003000c40b890424400410310f4005030410403c40c10380c00c03500c0200528000503060340c4d83c40480080e50321003180c0072629442d4202c04201c1004420f030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 913702814 1250 913701564 913701571
    0xf030810032018061e130c051b0714060a0309230f010504030e01230310030615030c0b0705150901051f12200904110111031602060a0c05160302010f0503 67
    0x14040c8100c21740807544030401c000d4030540c01e500a40d00b900c08041d0031003240a074810100181d41ca2540c0e40c18910780c0849800c900c012440c5641e00540f04c100001026426040c1480c3d40840d9056035403034001005400a204240c0000c00080b200d4201003640700d503561620301d02441d035206580511011080a0b8200c4030b0440f0020007281c1c0040d50396030103503c203d4802281a0030f0a4045001d441c1816400e01981c204132017555410074416014030400210340241055580c0031202c600f600c50039a40c813818001c000b4000c1c050443c001045600501c4010403513400300040c011101e101300d08014101501030601195603208659010080c8402850195101800c80d02c140c40c020220b062180d40300300034016451100403c6094083d01c14605546008010380964400d0341000501c110000002d8400c034200c2c803059446400c148109413896100c88242c50f42d440c0c0c12510540d82c2c0031000c00c240c60003140b01c640980507101e60041c40c02070158020000c401d03a4006d80f20700350315000440d000c0700c551100b05c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 913704064 1250 913702814 913702819
    0x306050718034425050c1005130e0c0d050109051f060e04020f0c010c12110a0207140103090b040c051503040822150302040e0f040f03081003201806 65
    0x980240310300b16640c3c1c007611903504020380c01016000c1121440360422400c02e0161641e401004101c51a8036140007080c40b0140b007420010709001d01000484120402e42c0b18034402000303400c0002e0180d100c0d1601f1110003000c00741080055507154814000200300442c1e460b0003042d030107d0702c80070349a07000c50260201c44050b0342d03040c6400c51540074403010790801c0740200e038000014040c2440740e074402c1c05600c0d4010500e80e0f401202070000e0300d640098400341c0d01e00c11940c410030081c5101191b400329030001603d4041c1400764680d074640c40120003e10304090040c6c9080b6081d41031004010301c4041c0c803011110103c80c0500c200d2440300b589a0584020b49000389400000c0025103448061554a20102c09446203030340259a600c40b9070b0920b0840e00c1ca02d03413000030b44c0045c007409454200481c090f00106c24020f9070b0701600e0290b0740c510b13060f942e0f010050140442000000c101061074421280590742c00061904005018140c9209849110469074802c03000d54441085a00c05282060302c06c8000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 913705314 1250 913704064 913704173
    0xf020f0f1f200706150e060f060a0f14070803010b13060503071d12010e1006150203091201060816030605280c09120c0609080a020a030605071803 64
    0xb500111090f544402c200b00d9015490704000c03a618101e581491000f41000b10340702c940d81c6450420031100001d0580c10910460040c420300304550342c4030301302c0c006840300390619030b42501180d00e101d5083c0c020b00d100140612400070000c0744ca40c0428026016241c102800c010405480d00e4041e2030318003088480c1302c000362a030100c00090a803500d02280d0101009003c504004852050441c252044d8040c84501359000c02c014821044040c45404002c200c42d0302412461145100000e4503803007198603883c4540d0704002c684000c00310a6118100504c00038007140d40c00482c44a2665200300340d0f1009892591030640068184d0200f0900802a1007071030140e8541009a1f240100c0204404080c1d24200090403001207192108189c03031018031401000307034820b0207140c50300c010721203503058225840319041016100016220034405009903079202d28003081c10f50706c2e29811980c18030301c0c0214403802c4843d208004180010714500a444958603044600b080102c4a00c90381c03214840213024108500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 913706564 1250 913705314 913705361
    0x1121a0603060d05010603081806031302040e031b0a0b0702011503060f090803010b03090c10020c010516120305040c09110d18020619030617030a0f020f0f1f 69
    0xd02100640d8800002001c0b00c0302d10001e0703150781d42100ca440c2c0040728490000500c1d141e10810410b0b1888040008480c07a900d946801004d030a030203200346a0080c003442d11241000f203404014019643c43c516118080c072503907d2b190340e819649029141080e512804c0c020007240c419841801441c00e080144084002c95902c1c5540300001402d514262400300356882d00e034600001c000342d00035402481208030b007a0700c2c0d080c03060350136043c58040c0020510403c0000542c180041e0081030314420400e0908203a52903c04000140366584032082000309015004010341c2e81e0503030140d021500603401503010409181d280d0320310b0411079083c85898070b0700146c04d11041d44038820070b8100303921064181e02d00070320520082d40401d001d078001181c26042000c403402c61260300d0f42e0500c5204002d066140340f02c014400a1400d150316446001c156030200042000d03681c030b0f168000c00c86848044001c2c4222258001900b00d1982c4603400e502d562182c03650004142502e25100380100800c070743e002d503001001cbc080d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 913707814 1250 913706564 913706569
    0x607031a1804152405030c0f0d03050d15080109030f181701110301060c03030c0201050103210201271106040e010b0c010f0f0b090a050c0f0a0e040903030b01121a 71
    0x403000d00440c59569104c10251055032060b00350740750001002c18200c0c1045042004041c01c20460101c2c19000e1070049500d03503c507039120fa080c0d1040c0c1e41c06040241d03541b28441810070242c000c0d000480c400841c8134a000800100540c00705c140180281d40b02140079480103011144e140f0b40c82d03420340741441002800c0c0020049885060404e41045000013149002c40d50922400d404c244c0c095800302c0c00e401409006d1607014040c2e07804001d4184000c014945c195590101e24549420070310714055418807018003181d00035070200c4010100d1a0204180c0101c5540c00d00c2c152003001c1007203c40000d025030116180c28504140c2d001c1d0307000000c80c0d40043c2e017068103560f219000807040c03050a649a000b00c11541303050f40320384103496101c1c40020491221010501051480290a01c01c00a00c3c1c18204100280d6400c10381c3c00200c407a102e030603900d85040e00102c5541e8007103808a640141344c90302c88070415800d030340207c0108800380c070303600c0d1900400b0300e0724803c90b2203881d81d11001c100851090102407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 913709064 1250 913707814 913707833
    0x1805090105090c19150f0815060d09111306080c0307080d0c031b080301030b0c0306030c240f04030201090b0a020304140d0506100906050f0102100902060c0607031a1804 74
    0x118114002c4c3e072000d0396100700180c130410b054201d880100d90340c5c1b80e044514681c0294821303400450310582036890500103000c01c503548030308910700350380b20383d9001d10600300403881c00f4500910100070010143d00d034290310b6480081003e403041c444544541c41c0c90300e6150501003842000c5a10400140090b1035110701d0540f03c00034002c01c110f080004075844901002c0d644840c604180b40034030401a1030358154984001d000e2005081031281e178405000300145607030300050710304103008141d0f152021003c006e4403041140310b82c04a285240c2c1c0c00131420440000c3d03c40042c208a9000b40d03200301000da614420940d442c455402c146d401a041048140500c4040004001691001501001841541c1d40b01e4a09284040e50040d0010005042c02c000070700703650264002414045030520701c0303804074000103552060000312550b94291614920400e41d0b6070701c01500c03144101501603504529214000a008260526000700c0ca000c814410240500308900390300385400000300f1504160f103075910790f400e24 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 913710314 1250 913709064 913709089
    0x100f0609030b060d053f0a030905030d1112070f080a02210c03061203040b2203050d27030b040b0603010f0c090e063708071805090105090c 61
    0x4041e580c0c0045000600410414030210010705041090300442c004d0203a0743c048441c19242c6c1d00d40340c1940b449022a001d012145a06128140000c06020601d809421030080d0400c01b8445032609200c140c1d540c0003500140742d280c00340c01c064612035890740710a54008039800c154200040c980e03030010343c0050301c6a008104024400c11012500982d079030828501300c0c421030329440011808001c0c000e95040c03008444900d281d514000e141841d040150381e210350701820103001c5001e2001e1001c07540061890000501942d045001e50b40d08000103140a44004441214000b0340c07070540d031980402c4c40c84804a0810350313a01c1f04400d80c1c1a00c0d030f40c541d040d000a0103003c00f07900d035503100000840c0140030312a40c0207580c0700303031152444207103060b500c907098402c01000c0c203024085081c40454001d18804040c10b030064195803044d206203010340c2448020486400c0002144620301011a0181000c44144a54075421360203101d5036030b50720a8582030b00d1b0161140c8801d540305000c1c1c0d09440c94401940100c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 913711564 1250 913710314 913710319
    0x70b2101300609060f0c11330103050115080f0a0305070302010216210513060807090306230a0b01020a0201120f02130312020a0314070311030a08100f0609030b06 71
    0x101c1d562074900807104484002c49840b99a110000344665182c0542003a044080c10b292010780680c0402544602c0c04001030442440e948180c0c8804a04100403a5058412440e208100f5a100c2c9050340c020003078840341040d0704000c104d0003c0c082e880021000881c05090001e0200140e25a030117855640103480200e003595001e1100d0300703071206003007621035170240030b401c0740120190b6906c40300e480c54140d11403002c1003020030803c482000b24041c61000c101d64051800644e945c0d5043d0003102c07490200c1e04000c01d8141002c8140100c0c055000c020303030034414a01a01140b40d1250800001240c042244d22405a002921013402540c000c01c20b0800081403054041800e20185d07200300c04030b80c040007100e2500c030711221051003400400e0104d46507c050700d000600e4103010b20b0320080d00c035a07811909005442d000041c22010140300d6180340c00e030101c401c4101c0740c44400f00d440c058000002141c5040ba03200ea044400204160800d00c40c10460704e00e51164030626003140c441c1c11000b900100a140c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 913712814 1250 913711564 913711649
    0x6020703090905072d0818120304080c011a180c0f0c0a050d0c0c0902071104021215011e030b0d02030609061005040b010926070b2101 59
    0x5035242243c042c040c403c208070355515059602000114080003414581d0807501104c540091080035004118130390082405012608804001d001d00b91810307030b4410101303035034110100070302c010080350001070940d01004900030310000c0141a0a48104000501e506a00c160b11015600145030b01c0341d40a90441c4104a81a02d042c89013009001c42d6884010103030082ea120000c2e50081c0081848000002402444d0800046040c0c0d15446054101405103032a070b0f5500040d0b0604102c81a51200800c010180c0155141d44140e00c10045041e01280e0840100c0c0740c075491514150701c640030451002c4265514500c11282c000e10071001441c14000094124800880c01c6025a0b820042c0700d03c14030804005000c14985200142d01400070340c2d00070b500860400701c0140301681c0001640c0300303851503807002490030301c540407003610113207900c1c8201503182c0a0060049505a041c030b0060410308890008980c0740d10b508100710784072120900c504401c1600c1245110304101e80c40b03184180b4480c003c510079 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 913714064 1250 913712814 913712819
    0xe04090317070207140d111318060903031b1b02012303010816080a03260108030307020c01090e160504090204140f01171f09050f060a210602070309 65
    0x2041d0500099810902591048004010402a07200b011010342c0c015103001040070074594030903542202940b1172500c00c844446901c0340460310365000441814180e6160107000100d400c120340100f5402c0803d800190a2500d2401401030b03029001d548851300b941e50240c00e100c41080800161004281241048a09a046042080844410000072120400092740e03945003030400c40c901071034801e100384103402003001082001d0020850025841d01814502000c0302191801c400c0520764040c0803010ba542c40300003007255200040914898003a41d000c07075541e40821001903c000714980308440400d10403100107028112045450344000096040440c201500c80700c1600603a00190807030900480081034603d00c40c40c0c03c0003583c030b8100080c01c01d00f800030504400d0810740c0b00002e103a1606412115082001085905100c1008095241e420890341c1064018114400c81c1903c1e007601c5083e0640300400c07080999640420321030350303140c03090300001d80c43d80d681c0004e5085044164180403048400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 913715314 1250 913714064 913714097
    0x12c0301020309031207090e011a190918020403050a06090311060901090201020c042a05090a0801060e01080303100e07090f0e040501050a020405030703060f0605030a03090806070c030e040903 84
    0x140d8003c5800320041c54a90314915541038151100500d15000c01c140c4c03070700c20005140e0001c88107040d0780300400c100315040f4500d00f400c10140704100300050350584502548150700d601c07000d29416036007401014489010401521001e0340668000900b00d50030180c0d4200014907a5800241c405209041840700d10080d9600700e410a00c00710744210580e51100c1c0c400c0210343c1c0c10720102da003e003003c550412140c01c90442c0310040410368800000702d010714600f100611409031060b030307505540040c8005d188a0702c0c1ca41c0c280c0a02a1482104081e001960008c1a0554044162480350503843d605084082c5008003000400c1d6000d88010b00b072080b507050114250300f202581d00d018181d0950103982c6814985003241c211138000704001d00d10351040c0800d20855a001c5510005c683c0c12040c086401003100348014001c0c00c0e41e82c40107905129000c4a4010503400115150880c1c003d00c084e61906d41e5020b506407050100030b54000c001580c11482200b9514141d0310565403070707000b858005941c202c0c1990 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 913716564 1250 913715314 913715317
    0xf0d0f051c02030c0c0106060309030509011d190e0c0702090c03070e04061202130c0206010b1b0601060c0c0b040302010905011209051509100e0a02060714060408041d0402012c030102 80
    0x188104c00300f10000d0400d14101090085200030001c0d4a000c0203440c09039200148a4000e440e43c5604010070000b64102d81e1002e0801190901e00003840d05401b494050710071040c884c110b2041c845001c00040006079440c4903001a80d010540240810120366a551507007405540010802c0341440075a040c00000340e1298030803c006007a414182d100030907c580104a006a95607244c242101e040c04510701e0420341c00314001e8112400010815120380c1c2284854000c0b4102c141d090303906114400c0001a910b50100c07956815a004d54040300000d5101d1000a15034031841c04040e0100c0c4c2c1801041041d548602000950000c514034000780c8644650740c1e0314100000103603000c10384110074042c450403000074048039011400301c0d40104540b03a19800400c0d111210071101134400d0038049071030b105215a042e0146020b222203030559030585040d150800807904240203c0d01042c1c1558a050040c6500c6100640030b2901611100355a201c403000b00c541d41c8580d065007600d04080c498201400d42c50900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 913717814 1250 913716564 913716571
    0x3062d030320070b0d2d050601020a02030a050703020114070308010501050a050f13030303051608040215041d091e1f2408010506060405130c020a08030412020f0d0f051c0203 76
    0x14000d9617096440c00b888151002080030301d0b00036146050100e10620322110501c0500714149011441c1e54403000140e05000d40380ca80650140100c0d0fa400c4108500403501d001503a100341c8ac0d44030090100300110384940031341078005000c030300a03e0041c480780d8003030005051001954540b091500303110303c1c403906050f00f003071a4504012103a03000034000c140d0103000304d81d40f0101d901c0303040501c014111801081080e020f00040d001e66004022802c4103642e903800c550103405020101c0c00340b14103050000740c40f07201c03ca560703180300d01407288034882414a24041c40e40005c0c4a0000308841c0140108070755075150f500e0440034449568cd00300544114a28000d00e0941101c10002c0030840d10f0700084d9801d4507401050303280710300c10820041c001039580541e20009507041800000b100440309009034604500c42801401c4000e003c800c00041020007950618001d02640c203841303031048200c011540c0c0b00f000d1864980440c2000724901002ca00c6800600003881c1d0081907100c40781501c2c0c1107601283d0054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 913719064 1250 913717814 913717829
    0x51e0f040803120603010e12091f050301080d0c03081f1a090406241d0405042004050603030a050d0b0607060e150f0c030c0903060703062d03032007 65
    0x11607036a00004581d540584c0c440750035170013070190a034a104295240c2d0714004241510180c08103135068140c44040d012003045c040300e04401000002c525000c0e20381d810900c140001446440840c00b4114415000c0100f916816152907426440382d010b0120288802826041c0c2c400700f1603800541203060042030038a070008074101d50b0b0b80700010700c20301040d141645c000c0d801300c10324080803054081c60070550410646040c50b2400a1031940840c0c40a18010850000c1e882814078042c0003e0002408181800d00c91440206040102031410b02042e100c0840d88154140c00a0107001e5481d4041c200810002d0f03051140020080803040005429410a4809480c100d0b50740c010030700d94038801c201234002080c01843ca40c87c0c921300043c8201220304000c00015403204040045045880c0410039501003101c020f0503106d103480c0c1150010300815403889003103128050b01d490304007850b5282200240c0000c1c260180e624a0341191003e503a442c00c0c8001d44c882a02c00070500400141c1e00340b200344d0191090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 913720314 1250 913719064 913719067
    0x1d0601030605090706020105010e0a0915050f061c02090106140d05090c0301050129090a120605040c050111060c13050a03080c0d08220305131412030a051e0f040803 72
    0x143c50a180b40c45902e07005602568940380c010f1047c0c0450134506a40103490b030308041140c81d21340c5020704801200d4003800c8075207810b0406100b9011070414400f8400d84081d6000c00e0142c00e01007010703c1c0c0e406010030294100d6500340c010310206114258071180d803d002080a45004104042c0c0c004a4208445080964002c0781c0c2e2100749245c20b00506006003001080c0d000c049442c907104145e403100302c0c0b4000b0100c5000051441c065240c801d050801800100480c0f00c1d40221414203d000e0b040480702103034413415246001c521980100001e0289082850040c45035680d0055642c60316444482040707070343c0911500000b03141c5d036003484940c00b07903103d481400e445a04010009140280c3c03280c3e6a81030110100070885280b00c001c140e08076403900c040c0c9805050140742810742c0c00748565003603100c1001f14a01c01140702445c0b4540100c4100e01a6a042c0c807802c2c25210813500d0340980305200700010350400c444403002452100b05054880c0011a2a00e00031350030b40420b2503903005030b01442c0303590030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 913721564 1250 913720314 913720321
    0x1804061e05030105060910060503041b230a060c1104020702310911010f0e06041d0606121303020c0306070e0103140106081f050a0803250b07031d0601030605 69
    0x102801344a0304003030240c40c40c0e009810400356030024021140100c1082150100000d014085503500484802248100400100e61a180000840c0c401c914001600c81c1c410030354504141400c01e903620845406076120f50719102681d5481c00e5410400c480254071070b07001d1000001580d0385500c9000f04045035a00800d0418640401103621007074031804401b0140303015a601d02040c490300070031001b41000d20304101c000f44000700a0343c0d4541c030384010940046c3e01090214404005d609011a03020081c5180750a947d5035604200b410321421155014400e1054085a1507690308a08200301c0c41c801d0040e14202c0001c140464542902112030320005030009401c0c000958140c0303e12110114a00d03900c680c1503051a4028190b120050b00301d07100c1681ca10840281c1410382d5071104003a1100410050322a40e49403805540d03031300301c1c00709052229140b0707080840100d80307054011003180d0b000100d194141e4410350107074000d0416500b8000680380c801107000f4941824802240658410b000c001103508 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 913722814 1250 913721564 913721569
    0xc05040b0a020d18060509040207031205151201060b180303070b0a0501030c050105070f0b07020109080d0507020114040c06030207020a05040e010e0c010e0315040f0c14030d030c051804061e05 84
    0x13800030443d0400945410b5007401110b51200440e203050000340c80141c1d4800003450100c82d085011b115025083d45842c090002003214030141084001c0c00312407401c00d082c03403010980c2c01c0b50841c0c841c40c65000c0041000e20303106045021200c85000c00141601e0506400e52690034031400c3c125000d861160307039440140304020455403444040d05081c40c2003820304120fa6550342c031844903031401510504100340001c9016100b50003404086500c0740100d0344440c45680c0b40e90182c841a99a8400740d42000d0303240d4070b40351504371f41601c0341c1d0300304003581c3d002850068142d0082d03004007010307604001c104102145680341c41c000c1102c00c81081c0000160b0a160390419410034034035003000b60401c03018405c4160247c0d40003800303e011400b400150441510707280707441365251004240040a180440e6400900868503030402e02c03109005805440c10400007142c12401c540d1100784a601296050040e601c1e40c2c258400c01011042e0701601c00100b40352a6884103440107034580030103c031488170b02e101340041d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 913724064 1250 913722814 913722827
    0xb090a120f020c1909060b0309060a0507120e151311041e0b040b150d0c0219120c0c140a0b040f03022b03030c180b0a030c05040b0a020d 60
    0x10002440c09001080c0c0c4128001d480b243d00340384841c07041581400c3c0308004013020781010010000d400040203855514003c003025600100d420165a02841d0700141c0a4507440c0a41c0388a40d0030703170381c510034201d958110f41c20040048450011207032003070000c90003000200c00f0090b4042c81021003855140c5689140183c102c60010701c0d00c1d0300490a05980d00110922003902c81482c01001d9000301d41c01d0105000b140061a40d803080b1a8072401c840000c500000da040c00400c80143c0f805400d1013034802034030003680c0d0765034800f1449240750500f00c1410041740030a80000b105070b107545000c411104042d20b4a217090032550300128403d0103001482002d0345400a2448000c1c150305c1700307003400e00e850282c0c62100a0841e2001034051100021560003001c2c140002c0d682d414505040d104c0562000e04000b0018228542e021020911020002080d022107800400845522092032490000000710407405044d48010035814004140f101099541113a0b01601c079185065004012000001303100800b45c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 913725314 1250 913724064 913724093
    0xa0b0703020312071e021b0d031b1a070e0114071a070306151809110f070807060b03031c0b0f06040803030f0610020c0d030903060e100509280606030b090a 68
    0xb07650001486081c0e610350000004403211040308c2c0c03640884040d04064070780d054400c0601c0c415284122800c01000642c0720348480000c03504c06068815600d003413094540c640041742446c081080c21740480008814500184101442404042007103112000004031112003942c5136000f1984070001801041402201c1d40301c040c08a1611072810310403801e114803051040d010350700a2071b0301d0346411443d402c035100440c0d0441d02c0e81400c4954800b03460404000b540c0145404407121030810085e228185000410f48219030f84070840d6882c08050514807030020724103500c0141d040700302c9100c1c000702680d9040107400104040d0340a541cbc0c0e4075051400c1d014500c0000e09a504c00e03002c481000454503800640c00003860420b482c0b805503002d49040075103404080303600003010641002002c100c00302d00805c7c01400110b02c100140103544682d0207468445c1480c0600300000103584081103004d5907085040c04100e80900c000080343c85e1641c4900d1008003040f585805158840e070408001c00c0002c1c141c0454 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 913726564 1250 913725314 913725317
    0xd0234030212060411041419060b0c0304090c030221190905071508070503041502190f020c01050f16080f0304050f0c0a0b03060d0303110a0e090105040204050a0b0703020312071e 78
    0x6498147d10b8144860b0101400882d4039180001100c1070342034007540003402034426500d801d503c07400006400c89d5a03034094001e110840c0d0070f00c00c40c030004a00138002d940184403141c4803110345400b8800e0400e1502c0d401098140948407001c0d070303805000064800c00d07000c580220050400e090800061616800c20401200100300990081041d21035011045e650000c1d0f21110087c0b0358505100d19101a000300441b040201081c1d00b4851903254109200c03441441d50340e001d9400007e042001034449004100440010722020052807048142c0044600300b01885000e000307007448002c64140c121904110340c00c4466074007540e24410440d008008440c00c003902260700d10605414456150414080075040070301070509180890308041c0079030850030607200c0003030320309031125110301c002000c6205070200180110650700000c5a0303405c040c004c4500f5900013420300c00b52545040d8002d81141d02802c019411404240050782d0300b20402d00700c15005103401c0c5e84105189010391404110010281036180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 913727814 1250 913726564 913726571
    0x9070501050906030a140f0103140a08180402040b0310030c080a08070209090a061e0b0117060918061e0c0c070509070903060f0c020d023403021206041104 68
    0x446607a000085400c98a01500c1c0540c80b43c0f2a0303c0b90310003a00308828544515160442000170060b646e0b800f05049030301500704500107402010b5041e0b21200c2134080904000410440c50301c52041402c0004850f031009040145055501c1210141c83e40080d20a1040b080340b1030b404209100010500c10301030100358000d04003a030aa6a59038005102c0c666000340036001c0720f00001c58019040c0280440e454019000f8000780031080c2c15203d59038001c0384000e1000e0b10700340b456a0154443e86440f0343c260941004c255031394590b8400c04c800102e008010080d554803101a880e00980705004035809403648240c1000a03014480841040d40c0f030040900311420001d204245944400040003000c4800030385011303285840d040300458000c14583c001610a90030701202071180c2d081c81c0e000383d44445071603090350391080081c81c0403601c0d482c01d5030030000441402140341d001d103950441220345203004290881281c1e0395a41c04a1001ea030580b680c1e50550b080791003000f050001150356041040380c2181c040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 913729064 1250 913727814 913727819
    0x3060e0112060b041107030c14030702090c0c0f1c0201050a0b100e012c030c0d15020f07020a09050a0f02030105060703050c01060503070b0d0f1512050c04060b09090907 74
    0x1194403580328a000d4503441e2103600f4602152100d910400f41004610149982d41c0c00508001e420b0701c1c02540100c5400c50580500302c08120f022060740c06040c3e008001c9181034aa04114086035000a40c1040007402150814211490704200d0308881d003600e0b90400242c880100c1c0046e084404c014002c3c41d100d424510b0841c0107999010522080c11000d049c4500004032000040307030700340084001130991317a82e1200c1c8069001c11202d00e00810f44021822070b00c0c2c00020100340300030072240c2c403c01041c01e0b05401400b000c040172900234064a84003415201e08000413500004d901c40d81c0796202c0003503543c1d07d006102c180310140c000c4081a4404103020340c559450400456170301e20550324003801f002000304002c64402029003000d8010030b0001c0071610a2900c8091045d200d034410314900288a10b030508a0100e110540154002000d1b106900d0007034515294982c100c9d1040844121080d006040c0d500d9859a12480380c140030380000031220740c842900e403050200c404005004a0182d91225004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 913730314 1250 913729064 913729079
    0xa0c050a030c0506131e1a12010608040f060504030f08150303030a150b030108010209010f020d02190501091202010516030501030f2d0b1905190c120e0d03060e01 71
    0x11008407201a00c0c0c960340c8641240e45507171880315a40004000b640c3d50060042815000020070060380c800f1090401000c80001c0c680c4031501c1200310024410f0040c9004000e40c502501d6034030703881801030944005076070700c0740e950394219901286c048010442560203035001c2680310711000d43c010034140743d05030030b400d1100010380d5030702000300040764283d12401ea8404002603079124000900078086075644950b107900301d05020b074100941842c0001e03c106005920320b0310000b1b8041d101049034000e8811019807a00c80440040100d100303848640d00d0b00c06c0c81c00010302c030013901d0320031811541c000903c0d0b082c03140c1040b4a81d8131501140c030030141801c0051001c10b0118140c10304240c0c1c0800042c00941c024400e08850301600203107036640e0f80f81030b0005028440c1840340c0130303c91076901020020480c0000055000c6580030345200020304401010ac944d801c1699000c105a000c0e14108590103043c0c44000c1c5054603981d9100500c1c640148840c044100c0d09402044050311003501820300c21340c1495170 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 913731564 1250 913730314 913730333
    0xe04030801031704030512070605100e07080402041805060f0a020a0801170a0503130509061c0b0402045007030c0c02090c09121207030503090f030c0a0c050a03 70
    0x40c0039440a603010f07039801c1d079020044400441c1d008040d6099070134641c01c507001d10780002d40107031100ca00f403c0c001089545c103140001f0507034400ca80e0100c400e45401c130040f034008100600490b0030a585032080d8840c2400e0410024015105000401040ca01101e252684040c0642507040302401484000361080c1c21001003410740e4403086031801d01150746040d8a1810380000e102420300d0000280e0f000403070700c180510805541003654125081e40b126824407041d07181075013468405840c5891220000782c00003502c160001c1c0000c0c40801c0f80d203807102d2440c400303415034044210024136100740a40e900030310591201500b101401c45026002c661600c00c0103211004001504255a480c210400e41d8028100c0e00d81e00c43d0044c241001504c3c1407218801e40781e000401040c0300728010b10001c0c1d05688001012280d45558004172030900c6080d03a01a22a504050400d00950003015042a4480710410103003156900c80e01c02042c0c4100d1390700301151241d0700c0d604242e0103000c4070301d811310100d0b0b003140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 913732814 1250 913731564 913731569
    0x70210110423042a03230c0406020105090c0105270619020f0c150f07051002030a29010507080d050f040b09160e0a0b04090302010c090f0f0b03100b0703050307090e04030801 76
    0x1000305001c0396040c003030403c142c0a2048030f11204407880c02d02003c080301e47d02403c10f65000350000c006907100d50070020b9807050813041d050300140c010403151210080c1c6506c09489010540c15055122010341c0001c0e14540042d110403070362071502116081084d038100035446103002c01d200a010f1225118010400000300352071502650440000e100c0c1c40d00c2c4c00300c022100c0868115003964000404110040069407098400c680c0e50b42c02c24a44c10981c02000741f0602452181044900010a0610056416802509007582d161a050003c0c61001001d0b004491103141408041c012610f010302c2c1a9980140c0030f0014801079104103c00c4480b00d40d4451004141d03000d803040034460b56242002200502100c00351260024101039a9104040c3c0541180d00260035544800800b1a101c600841c1c80c0e00311480f0b84d0060603040c40d0704220100000c401107802c040c10600400a091301d41d000051254003201048002441c00030811141507404111503000d04140c0000400c1401d254038010144135060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 913734064 1250 913732814 913732817
    0x140705060f04140703120809160e1009090b10080f1203220c030b07110c1023180f010c060c110f1014070210110423042a 53
    0x210041014000f078424001030700c2058804a5078090744030701c1c2c411003145402c007074040443c0e0070134089080a440414881c50050486130048400c5242c04010080f815001d0284041401c884901042d8220280585040103005201013030301400d200c0c9001183c90a240d106d5017580c0c00140041005460109240d042c40501c410102c0c0c83c0e4aa0240c01502128521300e10108200500481e404000a20800c1011203026074000701c42ca41d0340c014151032021054801213030b51b030022140b07400c030351604c5d90000c030f01d8020529214507051340ea04400e05101d02ca80c289812164008210095060701c2150b00c00041d81080e01e079041046848000a84014980c02000f45180d0715804c45003d65445804000784d600784440c04c4039140070090801d00e44a92107610f20075140d9044c041c480d6005003100d412280100040d13401010564109911b400c002e2808a030310f82d215102c20031000a28124082000ea602c00300e07070311010781480300501000116030011a0016840b54004906400e045000c1600082e0803800d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 913735314 1250 913734064 913734091
    0xa56060d0b1302040806070806010305011d130b0f0115030b0d0201110a081b0c030706050a1218080406020c04050426040302120102070506011707091a100206060114070506 75
    0x203110028038a48902e03200d20740700920102d00000c0111000a410740a9141502c0d400302d640c64040044054490901038000b040680e01d182c2944007002030b0708940c1c012200c800810042c03209030b0381c00803401c506071222095107099100502c891003102000d88001c00c5035080800c0a00e25160114140b003d010030080e0510804480b600c100020074007510b000c281d800b509150303070b41d0075448501d0030010040e8409080c51144682c644101c4c1030000d0441c0507541c01762200d40c03c2c08201c24045654811241030003803450385440c0c4030301105c0c481c40c28240c411442a5141c94803103085c294000c1c9007000520b0118440c80c04d260900c03001c01d24071223940c4101106400441b030300300404002000b00b489158030007504011410502125054198050900c142c81101030700c0c001e903aa5950618102072003c010b010541002c101008016102e52280ca0070210344440030300401e0a40c0b00081c021079052030100090f801c00c1d02008600d6a0000703c004081401ca0042c6040c640301303494840d07480d20b000703110b100320085 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 913736564 1250 913735314 913735331
    0x2030a0608060c03010f090b0f0414070e04051311190303050a080c19050f0705100626060f28051b0f0414030115031101080f040302060a56060d 63
    0x64000b0340c89e85101000d002403080d40000250002800021102c4130001060000454042c2c6818080d403405140c2d035030b40141d0f480a594544c1c03940c5100e01c140c0d440d070103a41038507440c051f42d2040301c0c140005d501a440341922203010070b001501d0318000a21112450504001c01d9161103502c00710740b03241411074038100707498420000400b000c134400e9040c003030301c1071113202030000054075a0740010003078484e40c00c4c1d8124412604600d03100c0700620140f01002a411200001c0d00c00ca002c4d2041c075500c1380300c0c170090040c0100c8010080d02401c01403000e6001041d00c800800480050841c11500c0c0c003c884603882d071030190150400e001e103004600400000300102860300442c1e0f41d09400c6454684120003034041d46951721700d403000c000d000d0151b031507012404c5280010300c0582c008030a14441e07034254014080c1a1340d8103100704001c094514821001018882c509030049402122505151a038014204e03c0300d204206070701c400f8018441054400c03c91810030060340d40314001130b203030f000c4001c02d00400d1898 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 913737814 1250 913736564 913736569
    0x612150b09130b040321050109060819030c020a0504050a020a02250308030c040807060207150e0922082109030702150c240601030506040e030a050c0f0102030a0608060c03010f090b 79
    0x9020038010b034110880018040076040d47d10880c1200c0f040e0508104066540d104a41c50750f40300142000341244010039000030078000e840c0c9051441c0700400c01c4c1d034117036182c10004007103400581708010a158041001c1ea0b000c2d030100100055610007165406d0000303c40700e51480e01c0c1045000c0109950804004a554000410262409000c96205560000ea01e0f540300942d594820700c1000750350044105c0d8002c016010300800c00f00600b01902d0300503d680d403201d50305080c00c4501242141b51154898030f40c00718240c0d00103048400969004440e240e4119a544982e00e41d0150021a041c0c10030020400141c2c4c030101c6500c0040c26200311591240c180740040c0d420b010f85503070011100100820542c100702c100c0c0d070000e4401c4100342c8041115880d201c040c04101d03020f45410920f581d1007000314002d0a8015005484500c01c0c0000300e60348410060a0a800da80099513074003841e40e15440207100c02e03042480166400f60315a941c0504540c50104640c4450641d44100c0341c00c196940f0031040320340c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 913739064 1250 913737814 913737827
    0xf0f0d06090b131502030c0702060a0e10030b3a0c0f0b040e0901050702212221030c030f0c0b040335190612150b09130b0403 55
    0x503080007032042c00e403501c59802244034000d25001c0791402e00414200440400b40d209681c007800118445a00348a090f500340080c5a1084404500b8403141000c034140c15504e01c40140d0a00105503000300e100400170701845100181c0f032035129406008141603c00d2118074260040e261746c280e1300e01c042c221002e803e000000c0d442c00d8115030703016030110b20301141190030300c4000c1086608403043c7c000d640d5141d0003550b00b2140180c40c0036005801c160304890242035907807043c0800c021001d2907a80303000c3c0750000220354112844001c0c80c2141e04070030b00b0042441580030303400d00324005911003100306840d550010143c491421000b41401074405d12291480e2090a8082100c0c3e4484030301c034043c2c282424090081219170101654040c00103030403141810000d08080c40303850952004c10b8541d2950080d40402a07404000040e40543d90080025440221400100c0b4a4042c959004a881c01c8843c0c4500342c812064005000300ca400003400032401303420508080d204e4000840a08503210f07490b044405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 913740314 1250 913739064 913739081
    0xc030f0d0204180e060f01030812041410060306060801150905071e030212010b0a050a0e27040b0a021e03040f212309091509010909110f0f0d06 63
    0x4901480200d100d03400b1440d4003640d1440850700032180b171030b99440c49454201d802400020320300d080600034841040b2054100c143c21034403c00790b0441c00c0b2032101003240ba04000c61f0310001394503151801081485458030900000c1c3c00c291000b84a001008c948040412420340315440c1103540d03a00004001c0e51007100c21440c40c03944c1450340c0072080040c0d0f10084c042c2d00907107052244414180300000f0110003039412961210721540301c69007040c5482c403041c5d0340c0c1000b03140c410350001400d2010000e11212410302c80c20f000d04081e1840d0050906040004269030010400c8180743d20400140480d45480e0000d12610794030000f07a140e40341d41301d1400881045080400604526010552000103185400b004010840550b500c0c5480442d0300980e80c8009052540031300b1283d01044036110364103000150680c4400b00308005840400d42101086141c40b003680b0001d07145036500040000c122903201494040d02d021240c07011841c2d0b082001505042460a01d2071084076040308500070000b154002244 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 913741564 1250 913740314 913740329
    0x20a0f030306081e06060103051b0a110a0812010b0423011b051b0d020f09060d050703061a0d0c06030c0e03120714071a0a210609060b0c030f0d0204 65
    0x10341140c2026003200d11803c0040c0c40200c1c5c011071001482ea548203102d51841080030030280801900b83d8090304003150311130380e00c100030400c10008401001c1020011315400620820015a90310740c40328200380400c00c1a0003c070700e10b040c2044104042001840799a61101c8612021084164003400603501c80d5555583e4120028000100038140803001c241e680c030103000595101070710080841002800c00031054000d51002d0101814152070502d0040a503001e8406000022101080d44409240c82001c1c1c0c0700301c4440707440300403101500d04501011340b80e403030054035030054280d0380d40e40c1c18103080c400380500c6c820150784402d440c2d8480c1c80341e20700b0802d014001e4242c40c408828207203800060340c0b084006640c2158100101c0c045075030001040d40480f51180d1413a41c0040c81c0c0e9032074003001d500c003503614010040c030400032010f85c09072030141187d0000ca0f503030700054130303442c150382d040556485034030440101e42c003401031b40710035440402110514880c000c0d1403903442c120000e0342c2d4001d0007180c2044a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 913742814 1250 913741564 913741573
    0xc0c01050a0603030206150d06230406020304030207150c1205130806100b0313080f191e1409011206091e06120f03030b010909111c0c020a0f03030608 66
    0x1141c01c94650010301600d01960036241d607662140c0c4400c080d0304c1c0103117210b50894004407034035001c140541d1116250180418104816101c2a40c440310724000035030b030039078015500005000402d50100442002020384029020340035079820006006030130800c50240481da8080c1860054a219104640b45c8510307411551001f5a1507091286d90b0b15070032036003017001011008011620316008410f49114842d40480f0822010f8582e41d14001d0760481220795042c09410b0019280d14840d500d000701c0381a005071782d40c1c0300d070f2130b600d450062044101e114004240081c08281a40e21540308084401042d028240030545030300e181d40c0714000300190b5204903502c92421002130003200d00761031010b511710b18070b40007400a240c0318281d41e803800311311079401865841074030212000a40660004c460603c814188448141d80c0e03101c0c801c040c2c0c0c03590414410108400140803610721a0f40103860b4039501458804c0000082d4020041e41d03c40c1100b8014103254005551042094840e81104010300405000d59 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 913744064 1250 913742814 913742821
    0x60312040807091d0d11070905130b24010c0201020304030b04060213060323040204090203060907090f020421021504061e0c020310150b1c0e16030204050c0c0105 71
    0x141c0c03900b42ea4021404594200000d2a0019480c42d44442e10140c55101800c01084007a03000c0d901030b280d4407440d040c01e019030720000540100c0c61090078854000c54403030811540c03251401500744100200301090100d586103660b080804003c042442d01c640038244030310080e00c1400141e1450040b9840209003403000c1c420441040019005800c42011522100c83c606031a10340035801d0b504208a12001c00d00180000301181c01e61490b40e64200b40003800c0081c5280071900407070305250084900100d254040b40c000c001d401141d20940000e14180c29003141402e04040c2541140700e030b80c0c2d850510642030311480b403083d9070300c00002003c550801041980d1316962081c1c007810440303424010b0184080c510652012060040e40c5980d10558000d0203400c005042d440b40000418680c50740b00d0603800e5003a00443c12103080402400928403468180b0400307c640b2100030240c9134824916882504040803140b03ca0507846503503000c1e41d074112004521540d034030700501000d0150021590b00ca60030032050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 913745314 1250 913744064 913744079
    0x150c0e330903010e0105040c05030705091b091f08010e2206090614041217040308070c03180306150803040e01090b1f050d0e030a12021804020a1101050108010c050f0306031204 77
    0x80c230b0708488003601034400360b940d07031030070080c2e154012281110195403401d9455645e440390001000f1504004100c0a044054260080c5081380e800900202081c50000140400311881404a50142001c008a10034007400554002d08807503195000b000180c03549120002c1140340d822840d20208881014090351410313040140460101411407c04074819011081c4410103a510291240d909a2140c041d2501e4400c411614111391a0b8241e00300040d80e643c03200340c0041101010000c600800d004528076112032071403203050080f40d02501056104010820128511000c114111244094009604c20b1040e000c1245103c00e164a5103030b907408820031b2081d0369003101c0074090b14031001004210340e02000c011242e030307403083d6102c1801140440c6003905160f8015001010070800c481c01032138100035050046403d981012031880080340c010001c0600d402006d204031401414818000d0010410800000d0107a105051402101e928000f000a659403410004503603004010052180e541e41c5d550407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 913746564 1250 913745314 913745333
    0x1c17060303160c092a0c14030309010209120304081203130203030a08150f09011e082d07030b1308070b0109021c1e0207150c0e330903010e010504 64
    0x6240c40b107031a0503030000020300b0a46041c100b14883d00190251440c100b003046e00c42c0241e001049a200049240701c42d80707180140003460044d64000c0000d0b80b1070300408104415400e01402620b05640180b000700040740d00003a249a03031000d03850089a59407079400080c8010409400f0280d018800050303201d481d968019500c07403140d81c0000e107481c84030314000d0800291460807420107511111360380052004c01c600c44000403e040c514200c0c20340f1070b540c5100f030070f080400c20052610419840c1d100520115030400c0210245001a00070380103107070459961960081d006498032152150910300c0208100c5807500f114ac0750b6800404800c41503940f4880c4801a5002c921f030490018007142c112400c0c510345001c0d850806074401441d96102070844925002500320290980b001b000c01606020500c0141c41003892501341035036904401045401071110300006005105140b0f00c0038100c040c2d80340b9480c100c41003107516117030000c1d554840b4980000d014016298840180b94a458180310802603090b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 913747814 1250 913746564 913746569
    0xe030a0306061706100507020a1d0c0304030206150609040203240f0a03120c0f0309090606080c09040905010b060a050c010515091302040908030708091c17060303160c 73
    0x10340901c6000e45030b680440d43c0d00f02010800000d003141d0008a03500d40391010045040800710b141c03203803c00100c3e4002800000c4160310900c2c8002c580c002d0072010305030744e03403809600c030900404103403850415075002540c0703000050080001c404004130482c01655000103e40e8a40001442552207041424104c3e5241c41c1c02864001100d01610142d4442e003000c0741e90046000008280751640b80ca55201d06c021042c03c08041810000f00701040000103492469041141c1e000c0ea407812441402c1c0104582241d000c1d4010000703110b2a201002090a4100b049415400c4169004182400240303440d901404500a03100d50080002c0b0700c5594060b0300c40054100644001c0080c4450f803508243d11840b8940000f40a0300305000c103000510009003040342200d400d2002d080010888083e07210000c458009650000029102c0300500001040820a2000d5106031098000031800100d801404900242c106269554036070400105107a40600980340300d00b1000501c0305a880c11454900010b16460 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 913749064 1250 913747814 913747817
    0x60e0f06010e15090d1b17060103020d0816051207060f0903090527070314150303090d0c05060f0903100903080f0606090d08040501030b010507050d110307060e030a 72
    0x84001420561050a031202e03080000741c800790f00b0a044261054180d40155a900d421094030804200060340303144582c222440001d4848103458240300e220202d1591103600f41d64280e1040d0018409641c4001081c1400e40d8442c031142d950f031902c40b42550014190a802400e6401000880e0411030a010000d000d907500c511400c0215480c10b072180380480d0300980c0c0282c0003e9001100f80302a08240000d40e0244245c2c0a201ca41c840d1211003407440c000b0100c0b500c0000949860700190b0038040c95410f10b4003c03c4440f40c10180d07e09000200c1cae84c90003000c035124032038074030020584140700b1503241c44400382202404c003a695100c1540c15080992050100d10b000344034041c800041d00595100e20801c0780d525076950807550b01d0340c001070150f0740d1002e4046580140c013041884056503034041c2c40100e280c410f510b595110303450000054216890829400c0c14400104140800034601080004250001e4280401c14280004e00c0ca0f207180500c503002000c503803403c81c0294003404008040c14001016 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 913750314 1250 913749064 913749091
    0x201140f1e1005010f0507080d141305120d0608071d1806070c02043e04050f09180a0b011401090602030d0c3c030e03041710060e 57
    0x7504009203000007180c10724490203802106000c158412400c034004c0043c00d15041c0d0401c84142c0318003c0c260f110091080e45603a481c0340800da04060100c03034a50018060311841d800c6000c1d9202e0300d48814249030b410910b48030010300c04002c983d82f0f5005001074404802126045070302c64100c90b800080d40d08004c8101d69120000030625218811011610410b1001420890725510410303032b003280001e0b00881c1d009403105811a0204000140c1c0340417100c5102c418006da0341c0300c2d0f0001d240d4145020345000108401c0200380002d40750034105810081c0151084000da588103d200b003290f00f07640490f00400e01600d012181448000d81d1070f07605940040c0d200602900540c001510070704094440c603c0543c0050161a500000542c0818440011030a21074030703501c0050307a043c080001140210300b2002e402406d00c0c00c0c1d92041031840c1202c549a042c1000f241420190300c51b524003880c0b01d0003000303a880c0403000e03507800ca080c402801e14840d050b4003030007456201c0d00014025403048480000d00d801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 913751564 1250 913750314 913750351
    0x10216020f06030601020d0c06110f190306120f05010b09012d03020901050607030e09100806090109020604150509191d190b060412080c0706050301150c030201140f 72
    0x4002d4100c2c1c0c00f40c03a05030020089612010025107010103650305c280c40503590340000a0300102600018907240d2030403d11140d6500c0180c0d10800341c0d00c1e000d40c02034105440c042c41840304040c9505c40305a42e036003215040401c25054540180540300d601d407030725040100c80c0d000059000f11448401e0448401e0304084042604a400d5030000030b1075440043d6002440400400c068145100100b40300e038041d1404d40c5010a01e03001041030354505031103070046403d104100300141d0000b0300555030015516002070081e040b6035000550940140d01981d0701401c0d210b0038045030f59018004540b00e12402501d070320701340e4001900c61000d129051044501e0550f028007014510818140f11a208481074503405032042034126550700105004c040c00c50704403c1c10400400c1c0080e45445400b00a0b20440c10300e6954615441c0302802c240d8154070041c00e0090506c01804035409003d240c0e071900400d031034100100052428103d016001c0d064100000c00002424081d2494004861070b1060f035031010031005260 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 913752814 1250 913751564 913751569
    0x9210e013018140601081b03070b0c07080d0c0b010e07270f08101413030507060b060d050105040c14030f0411150c062404051008010216020f 62
    0x40211103055229a005650001c00c509a034441101500700b00d014400e120042da89200b1501c1c0b5400c00c040c1e055100c03500400603140d007048142c00503420203600c0114807a000c00070075940c40c1c0c2409400005130003c00c4150412000b0443c5000400c6c9400885511402c40031004e056640c0094041d00d9a012850004c14280420600140a071409540e03004c0800841a20f804038103a100c12803212405914000044505141091a02a05511025201700c041d07000740d081c00c485611281c1002144580d040101083d45000e2052110f605818507517960902d601c3c2c81001410a404030a42c0210301003441c607494010365002c14140c0f001610104207042d000c04050b80c68007964114244e090600304005500c2c2c0c00c900c80d03800e400c2841030304e880058000340b10016081110752031819000c0c81c000700300c92141110820840b41c1040d140c0d480c81e8241000012000d003001034000029010740d807900041540301e48460741c620010f00e0440300854031002c01850307042c41118440b4050744903500d800724200c05031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 913754064 1250 913752814 913752857
    0x90b040c0c0611040807062c0d03030203090102092e0302090616050f0105040b04060501051801032a0618050a2103030b0a03060b090f100909210e01 65
    0x52580c503000000d41c103a5651102600b040d40a1000d0014203020014070081c0c100b00c2007001e0b0165172954098600c5c0034400580c1d56240c0154001e03c2c0d003041242181c2303a210401454411070305460090703903070390741c00003124064441c695100e1b1f08450600560704038a03d8951502e030f80c160300e0084c404451440b80c1011030680c083c0b00a00c0354841c804000e13800c80f482d029543c520700d651280054452003481c54102d2421900704641c00d5625401020800c41000f007280314490150004a9880e8080194104c95000c101014040141b1905516051000d40d50301002004070321000140411102070315480c00070701c030291a5060601085202078042451321700010850180c585541915202081500b000c00f8511300300c0e5400d4051550ba04803901d111f44580e403107180658010140070940e16111014404602c000030020001c800820040c0b041160001034a50101c03044410041420412400c5c1000b0004c91011a4140c1c00a580246103c0301c3c1c003c41500209030090b00ca69a9544281c0c2c0000f40c070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 913755314 1250 913754064 913754081
    0x30a031125180e0d0513080f030f16051608120403050a06020a23030601081312140f0d060614070b060d0804080a050a05010524060a021501060306090b04 67
    0xc0e103480d00001e020707103003220104034001c1800701c0340442c030b030400114564140407401340008005a000103200304401c50f42ca1805006101f00401400b03030f0109602c00c19124080d0142030000e40b040043c621100c40001404481d02580000941d8142944146901c408280078401c204c81c0b03011380102c1110f00c0099000f941c3c102c0c4c0d004005412500b03610b0303483c41d000307510030074030321080c00382c611907020702c82d562840d0303e03214005940e4107a6945d080480c005000000b009081140c00154a040c84001850f02c5800d2169402175003010303040f04210010500300ca000f0b40407940e00d51030300401c16003c050920b4000000716200b9469401400410a002244500c180c1202600054142010a465080007803081074501e01034084942495144c3d0683c1d0308090145400b910280d0080e4484400d01000f0f105064109030400400c0d0612642e104c1224804e00c3c260042074800c03070011482c044941c1c004d11840c0c01c0b9404040c48146550b850f00c401800078800d50182e0080c0c14a409040501401c0a00c0745494 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 913756564 1250 913755314 913755373
    0x40b011a0d02400b0c03040e091f02072a0b12040605090307050d121107201e01140c01061706010501091d07030906111b19081602030a0311 61
    0xc094204401d8000c0e9030702092217080c041c031080000060b02c104802c2e00d036000baa2820082d1000c1c3c004c1421917079810180c0908510001e104008000c001980c01c2c2c01c2c1894082004c400d00300b6517855410710b01d007140c0e80340d00c00d01001800203400c11000d02c2c84050588980c0c4100803c0140340c8503044400c5d41d038060003c0040c0326921180e203440c990760041910b580c0460460781c02055010306400311300c410341c10202048a401e0034006503100c0503120603040d003000c800300b0359280c10b081d00440f240c0c0c00f8030380480c113600e41480110404460400030100450b03051100c070314001d02800c0d580f954030340d910000c606002c1c4408d00840300041142d45c402c4804c101101c82160541210100000c900440c6400150128050541da141100000392890107035088410003c1003007511442ca036a031808150041d411040400d81251400e0300041c20622442804a60041c6080341c5403a4074a1848140c1420418065807501c1004009410964810066941c4440000540780320003c0610720314104015000d804c40c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 913757814 1250 913756564 913756687
    0x2072105190803190e070f150305060105041514031602060f0c04050411120403050903010b01090b07061e020408010203071709120c0a06060905090c09040b011a0d02 72
    0xb4914a020300d0511130140e5000c40000700d205407200d0043c5032403190751084e00c0b1011000300401010419481e510780c2c801c6a42814803941c544000001c10030b00c96401542240380d8034512600c0c3c11481411500003181e540d0728029904c2c20102900d4110100659590006210b0040015540b0200c0c40820307002c0d090907540d003420542481c04000151816058200a9050030301c00115800305281c0c090780190700a45402d940c030b4070310400f0b040c217642420816606110b8164401c01c003c0c0280e00481d03440c5500010300041c050300480011941084a1a402d0a030f9070003c10080341c140c2040d4000d40c0100040d0301e85c00c6d40340300c20303000c2c007140c854085800e01c4607600505818021000c1d240c0080010404203020350781180d52903510141194140d82221241c2c1355200100403242c89c00b0050005000700442e461001d5240503640c10b0f401301e505029400011f06803842030004c1140400544070000b80b200b00542d2110719901101600404201001984050003440f10316103241c0d0308180d0440c050100b1841c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 913759064 1250 913757814 913757821
    0xe030d0f0c0c3f0e1504050607060b0a0b0f040602010f05010e06041e090b1e010b0307110a0816110906011d0d05071d090c0d030f02072105190803 64
    0x41200107550400c400207030078041c080d019001c0c0b5103e04454a003965150b004810880005110058140d00d84038010004200300a03c6280c1d203040c2a40c4040e40c2c80080441c0a080100104031300c925641c0c82028a900007052000ca8440c0a4010708155000381e4000c029030001c08000e48140e403005c1c886d51b2203044101010800600b4180c010098482c0b8440c02c3c90f080000540090b4100d07800018141ca0580700b140511131a005941c8400d5000180c0e402856000c0d418031901a02511002e002c00c0c050080000850b101e810042c0400000b007078211020369202c1c0740000046c4003a560308a011204030030050a90513052400081e90350140c00180c1d0b81c2b03030850300356800810a450a010300a03600141c04100d40c0c000480400840018001e403201041d507100032001001c1c1300300c4005c0d100c4c41c6e89410a8200c01c0007600e4050700e00c1d0f80d081d098940035582141d81e00c001c3c0e00384405500862050a07c00500040d00d030303048068172035013a2151040322003070040307800f4240303a2101080c4c0013402c050042010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 913760314 1250 913759064 913759103
    0x402090105120604060f1203031103090c1e040f02030f060406030b13020a090501030311240f180601060f09050d02030c01260106031a0d0308040b09010e030d0f0c0c 72
    0x2074540c4080d014100084d10764444420b030000f02400c0c0c0c0f0200035041e030303003010304200356250080ad0120350601c980c49040d400e100c07a6054807940c000c00300301d01468030b840249915001c00440310315030360743c080d02c20842041d02112a4000e0340c4121982895003110350080360250905101d1081145e07000704020340e0b29111083c0c0600c0410700710100760781c041142036020480c61032602c2240e00031842070b00d56124890804503d42d04041003a1203601140580300310425402d0314281c0600e50200c0342e480101c2c4d4646c3c45a1004640c4681112004040e102d440000b140c0300d030304138161900920a9407242561155190b080000d84a03414000035099017001030400e502c0d50107103500c0d48020340304021401c00f154660958159103202613018100180d1a40d00400c040ca0440c1c0340ca2240807030070313210004042c402c0d0b02e010384526000340008248400301400240d0183c003e44c0708940841440003035a6488a212810740054101075005c041d100749011540000c046c09603041815480e4810900d008901c4000308 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 913761564 1250 913760314 913760347
    0x902160827030d08070e011119110604210206160521130b0c0a02030d021f020a0c030c060e160e09010506010c03030b01140a1d06160f110a08030304110402090105 71
    0xc1030341444040309401407107010034801182c017008a091a400d1117a141d04003102b200a1400034240500340070031050100c000e45007102c400c4410716202c515030240301440410180d00c070341c0a40041584400c42184104080403072249c4000031450341030701c0c0404110f801940240701d40c441c81d600d85105a031003003000700c00ea100503200391400c90099a20303034000fa4000c42d05001800040300b005811181c4042d144840c0402c03202e0134422012804c5040c03030920000602a07004a22000d400e206407a080ca00800906030080c4c000a80b1400c1555480c0b018801c0a00b02011907000305600e0300398080000301c0c003250500c150f45c860340c816510f00c08001002e40b8190002c02400c08094104841800102c4004080f0401030503219400c0e651030139218008860741c848140b180041610850041160400780306000c400070600c40d40285988489128602e88103001c0c00214407520341014500303900180c2c050020026510590013003100844110307920003008100d218002d03c0d00d011420a0100d1034403003030080b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 913762814 1250 913761564 913761587
    0xb12010611030a080603100c08090d0f050304030e0a090c0e0405220b1306060f080c01021b060d0209030604050a0209070206070f11011508030d060f03020a0902160827030d0807 77
    0x46c03d0f226219152640d400940d2008050328010030102d2017842242e05007080b80c0384a03e0340510b04007502c050201e60050030f41c40302030005800c01c40300c49803801c81c1e50340b66006200248071000c410032401c010a4000781c007800c850a03680e8800c1d882d00c0c00141d0350001640c1c1584200400145950b201a603641e00c0080070070380030b441000080131011405000804511078000030381030389800c88103c680380c02150b42c075041c0b041c5612411904003c40c40301207045111401c3c0c8207a41c04a0f410754a07601c08403c6000280603510145c1d83c940705c0e035424801032041c080707803e5081c0303402510348031030556456405076070703403a01a00d03510001081030501c408000d116980e0b40540e81c0c005070000c500301c034002c024480031800c0b980006281d500006001c0e04103074030b148252001410b0841c51007420f9495500050182c080c6481020901e5400052248109450a0640848580c40070070700b40c842d0052f40225210307103140b0a00d04100007503801e01001078540040c003007182d0591035941c1206662040c03c1194010b20f040b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 913764064 1250 913762814 913762819
    0xb030d0c05061626040b090307030f0305060301272a03031407200123070f0c0509011d0106030b0306042a060215010e0907120c030c0b12010611030a0806 67
    0x520040c044e405115554074600c000e10f007090750040c01e003400c01c481501006890740c0c400c1d0340100007100004e904280101c05940f124280001c5a5448001003170150003003052003c1c1d400c1109080c0d0700c1404030301e00e444011a00a010b603001c1184010407400c444042d01c4594000d0160f0100e0400001e4031580074520302c00442c961040c1482031385d5a61420600c0c0c26000595210030651074240c541d40e2100b51550f80403400c01030440400a00c040b648400c1c42800070280405a1000c640700a012212000c4001088054a4075074150ba42d5200e00c03500000c0034004122090000c4000504541f090060894544005014040b1602d5940c0d074900c082240003091040b43c503007003c9040c01641113441910003003d1540140010340b40c881d8072400c003244141c0003100c1948105080c0000f903200081c1e18004d803400f02148881d00c0c02039003404095803905501c018845000000c010840d1403404ac054080003c00d810000460390701d4400582c1c1030700084491000350743c0b0502c9241481c07441090401d4000101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 913765314 1250 913764064 913764077
    0x5010f0b07060b1816030510140d022403091915020d09051e010e01060803030c1b03030a06030506160509330702100c0203030d0506130f0b030d0c050616 67
    0x15010303e08640c80c0d0407903034981701034074035010400819090701a8a0b4020704420340240c4c8141440e6074079000310083c00c2c805003d070384045200070854075645100c1c450420288040301108032007401c0d07c41ca070ba00407101e80030329005030200c00c12968060107a89541c10341c04a02040000ba00c1480c0310020f40040d00a075003070030b8030b442e044004140c041c4255800903050301c41c051030303400380c2007025400d45001c3c00401c41c840e07240070400c100b00c0e0400300c140c1c3e070442d0000c0300d12941c98401114440103800c4c038071080c01060000005000c400b0b511540900100c0307115105450699a84122180321448420000300100d0070820151402e440c108501a14101e034075603c140d0b080061041005202a041182c80200070000440714190314120828a0403d070841c644010000c000ba400b29031a8041c00342c1001040e6281c40105202d6a02e04051030b0400d01c46400800880b41c00400201c05802040c441e580a4019502400e4505201c0d190342c4010f250000300600c0d07243c44011800007102007404003181007105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 913766564 1250 913765314 913765339
    0x10091a0f030118200a0807050f01170c12010b0c0c101809380409030e030a0b0406062306070f0c08030406020d080702100506011110050a05010f0b07060b 67
    0x184071012034a050700401c001d0001350301500b5256801003031101c0c141e21802c600303001009401400075151068402c2030300c00156406070500103a4080d0702c486040c01515183c1400c10a07115049030107040c001a001210700c1040e40e03517601d14041d902c6030500340c1c3c0c45c580002c00c0c3c604040c2422190003400307880032701c2c142c3d80074240000c151443d0001d64001d8601c80c3c1d00c0b541c0020000d042d00d036142100d840440c2440c4158000700b03242d100e1031064009003500507a1038014101c14140150484003540314041c0035a00a840d452414401d0f0100c101c40c21103045250030000300303215144146040f044841d1034007191000c003c0740d0400109030050a01160b0411142e1800c1c00001d9803040d000009100000080d41c46da07080010207410908001c0c0704000300f00f02d035001c20260321b41c000b03008940c0c902d01400001c0c05889044c01210000914031210a251140c0414842030503015407006100d50340c802c200308120390301c9003640e2902c40c04178420f01400c00300034000c10303010440ca079101d00f4a00c803000340241c24060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 913767814 1250 913766564 913766591
    0x50117070216080a05010e0c0a0e040f060f0b01120501060e060f0c01150806071403010e060f1906030b031c08090c0a090c030f2d11030f10091a0f0301 66
    0x1c2c0c6904030780516000411144c0400400b400381004580c12840680300e4031005034040345202d962442903280c000710b541c01140c14802280d2081c45c09680202050015440025000e409880101526070014000c0ea54a003014102d510640e8180c519541e0b55440008044007080055084140458036241d801c0000202000c801d1144581c442c0c07400d021030141e1483c0034229414403c005050b8001e00458582d0013216070801c508480c1034884581a594494441802240d182054101e005801c52050041e194000c1c0e1580c11881c01c856642d601448812460300500d501ca40d1650213604e41c0b06200c00d007054500e0b000e800499840781c07500049070340b041581c00008409190a0b130183e9465603a611080007265414015084008800582402040c0700014030715000105902c400c0b00b80721380c40c81c04c003250f00c0781504a5912000c1e51300320301e5141c5c02c000c540c1d40e10b1000300383c5400740440f01e6203a000403041c1550181d08500d034480c542e07040845c00f00b40c060081e000d45649000d58036544c0d03440d0000c85072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 913769064 1250 913767814 913767853
    0x703030b0a0815070509010801030f0f060f0f0b06090d030e010c08072f0d021002030d05010314070815011a0702130507080903121603060506040e090c0a0501170702 72
    0x10240b90004201c040300200088502c03c40150003c0100141080394506590700503007403604480d40641001e80782000d60401c43c0e2210705500c0014031150038500e80706055809a00080f260030403c150070014400703800c0401c42c8910075911140e421900d12854400400d004000a008002c6c040c1020f101c1e4405581e50196580e0003e801110284c094442d0b1880d003031102600d40059001245884981c402000c000918100010360001d00c0b4039000c114000b030092090094a085912001040c840380d40c4a142c21f600144404100e902207100314507001410010014943c00a1202c0003c019481c1e4204401200e45e03030302c0805450006501080010f0050310f690010100c030300065400065281481d110060201e00c014040312010f90040c080c3c44007402e1b8450015403c0701d089050b102403920350b804160080c18036644042e91082c404a40080d2080c50080c401e4031640300d040a03910264501401c2200d1086503006180c009900c8000002e5141c6607030719241d400442c140100c488044808486c190b94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 913770314 1250 913769064 913769069
    0x3140318030a1713110909010b1c05060c04031707030933020303010807060e0f03030f07050d05030f0a021602090702161a03070c0c03050109080702130c140703030b0a 73
    0x76401000c004140c0401a20f12500601c0300d100c2044080d54640710340d50b511400e001c140344207407036001c08141c11000035030003070007800030150003003d022104504401e0340d812202d4090320709004100000d0b42d02483c04040b6815290301c507210340003d041d50308e11030740c2541000000720107222204101044d400038010b00d0040000108010000042c0c1c50046145180c00c0c150100082d58000d000600c544a40824144103441c29407070004d29a00c3e9a20002d0407203503980c50515098000014894051103048000300303400e42c058001c6a0364482a0041110f4521040320b60441c004016404500d0042a81c0c001708204c030b050141040c6581126000200c0d81c10068548034090f0b403141681c0d4144020310001e02004141000c9458000b40314170360003051900c0010030440c01c000710088094100f0081d14940e5000d5a08140200101100744c5403880503640301283c01ea01c11581154900d242c40c1c440e0141080303400c417555a03960b11103201e031041c04030f5030070060040b4145500e5907405c03180c54623000c0742d4000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 913771564 1250 913770314 913770317
    0x5060d02071406040302340305011d1c0f21021b0303040816030c081908011e15111c0e18040f06091202010f0b010c03140318030a 57
    0x341c44950349808401c071800c0c240035040d103420803020040421b40218410383d03000300855008024100c00d025291141041c0c002c0403003141007510010090280561041d000400040b900340400b9014555480d0341700c001200e540a054030100032802c82a124224000700d025139800c01341344015010301c0c41d0a41048204045210941c0071580a48504440400c401d1121800300614910700b49078803200c9840c800c4110320790359040301241c08010184034000c03507002c15411035001900e0759000070401880c1501c0a00c1107000a0180d0004140e04030b429070403006038540c072401d96103518a00100781c01080c114055000502160420318160100140500311460906001c0700314000b01c403001c0581001c3c4c100340340ca4002d0070740070801c500208845102c95002034000301d01030344441c11890300300050814908000e02901802c282d000c4415015000001000c1c0216014054400000300448201c2400c0c01c018001074032101d40054240c00140082d900005494042414107640d1502c4900d55800610b0110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 913772814 1250 913771564 913771567
    0x5070501230315150708160c030b131a012321061006050306030a0f02154603050c07062306040213060809070f06020f1b09010b0d020405060d02 63
    0x3125032400d643da9540780300344c10389564207000c6641c4501056001c0c0010104460612520460602c02852041c000440e840340302c41e1458500309248003a40001600202c480740050049901d00d964000b09250507039615590320f030380102c1440c0e000c844d040d0311481959000000003203ca1409403020020201200b000402070100e0b003450681107040b2045a407201c01001400d200307210b502d40d004a0704112568100c0081642c0341000d0000402c88803181440c40304241c400501c00c0b544c1d0707001c14002400d19000c0d000000802402c0343d040d00f44461a604c848900c2100444081403840c041d61043e0b80000202002030f0406040da91440216000204009810440c812002c0280749541c002c0b02d81c40b40c002d65081d401c060303190302c03001c40750301c001e000d080240043c00c070004401010070002c08000740000d0002d540c2e80c9a441c10040d450707065851040086005207140c4138107204501c001038040384001307050038400d03030701e02249251150000c03014844116000c110001c0c3c1369a85402400d4588020880103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 913774064 1250 913772814 913772851
    0xa0506030a1d070b07020114130e070f02060601080a0903050c1506100e01090b0318060709051e0307030b06030703080c10140910050a0902130c0e01080103050705012303 74
    0x402c20144080814070503480100e041c00311440f207006075201d0f50b07820308140e0304015003580c40010701d004100800f010240500b90014a02100007450350080070503480d80340e201e10030080c1c02c90700c42c81c04a5640740480c03070b50000b04107d07048a0780300011090083c9001418405459132041c1013411800403500d6002050051111030b01c0d042300e810368108481e080040280072480000781003100103200d81c0e0320390100403002411061400901d02011501c0d00b095680c90302c1c02d408054520b20460007464019540038201000e4802042e030700c2118050b000340201590307451135441c900404801032600f03416010710180040004c0c0340201410f19915900054a021141901c02e43c003180c040141c050703508505031050183d02c0402103002590b40400907004601a43c17400c80c114090b02e01200002d4001c1d9880890028180d0180e010400742c90182e41e5105400402800446000300c3c05e02020b481600000c60802c40c0350b0095815402074401a1030710900c0501b154160307105038204031030780c2440303002005a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 913775314 1250 913774064 913774091
    0x15130302041b0215060103110a09060e0d08040513140f011a0301031a090f030a030501031401140c0310091404030206010603050c07140313030f1a130602090a0506030a 73
    0x4211001400e8068103604200b0100020359402c400030500c0b4803a1949004202c16910a030003844114890f000c1c2641d5030503640318020030340400e51290000045e86500e0342c010340e10300700280703800840c3c00c0b200d4941446e04010070004100034440310300040e1680c810020122a01c80c2c907406104030038a0320f142ca4258035140c4203000d040720000419501880820040c03001480312040c54101c245c0c44d20340302c542c45d60f4080ea000e140501d200c4103000d05200206501010650607000b0714180c910540c8590302136007901c480300c3e090303943d03080c0d01c01e40c401d001200140d40c580070f50001d123900010005d40650b94542c0d658244003143c19140d1140107401080b000c1005150701080f46174014142032504003c2c031300e0b11714400e6046016188004201c80c0282c43c40201e104400c0003954249130416044c26011640c0c0c0c0340c03a103a1901040c2d0200d401030103504c2c1c0c4110000d0252561071080910040d45005005180d90f42c2000f940030740c0045a20081c5880003090742d85501c80658490403400743c000075406811041c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 913776564 1250 913775314 913775321
    0xe07080c060306060a0c1401020c0d020f0d080606070309052e08070905060c0a08040b031803040302060a0305130f060f06080a02240c010c050703110d090e061513030204 74
    0x245001c0d407010824891291076030411504104014034082c6084600c0e0700d401030580500c4a4544815070020856904d04903010540d55802400d030f4086924100b082c418040c1c9520302d408042c1e011903547d400041c00d609000000f490160320915100728180d80300c03800a0310100b5001030401001e109080c03407a10745030a11020054184d403500b420748035860581001044c54810340680c6028032000f14200b4491035040140c001c205504c500d80603120343e00e541181c1c1480d001102c0d894900c04007140e40785060203003c41181c3c00d4030f4015246a25000e02030707200750080c040140980781d4007503c003540080820700d031048003402c107131250708045205c5664a044e8019104ca40c0c01410701c541000b501c1e0710051303943c821841d000f0801c1074441e05140e2a2105510064017a8940090465080840c0308001c15440070080c0401c600c40e860700c5105042080c0d60301d507078405840b04031000c0344202c02c0611068813030321107965010500906110078614400c0c0102e6450700201508510b07141c001c0010700c1146000e01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 913777814 1250 913776564 913776583
    0x3041217060112092f0a0e06041e090501060323060105040c030e06040b010315111e040801020f090301050c0c0d0c1b12050105060a0b120c07060e0708 66
    0x40d00e0290314000030311540a005001e0700050611031034000c0e40c039105406400410a003600184141c120041514440c5103103c001205149010f0a44001180350b00c0c01a00b040180d84a0b01203102043c0d5a5905000090045c5244081c1180082c40c0414081c1072900910b292144540000300350b0524514002e07040b00521000a24400c42a0501041c18000058034030b0450f9002c640c0440c0d01c40e10080c0a0300101401d500520403809214200418449032007003141c1224030a40040101e101c4488070082154071070b820351300d0102420010301c0950f11208021407071113041c401080d45004d5a4210450032680002282c419506d404134a1403d41c0c5020300c40c165006d0a141041c62918940c03c90b015181d411804d04007051000a00441088c011440c802c021648003044500782c0d1503440d072107152484650301000326500e41c280000034900b810010056011103059044040c2007081d1800c4e15040083d0003080646400014003030780c0c0110741203014032906640c031440a040d2031350900094508014085 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 913779064 1250 913777814 913777817
    0x30e010b13020706061223031e0d060b04060e18011a07050705060a0e10021b010507150c0903050712030e120f0d110115180e070f0303020102030412 65
    0x241440c4429200c1801010030141940801692910705180250040c10550003145d0f03140400705030b03d410407914070000b030442c2500250340c00c03250004440340303a5684a0341d102c0c8100000031481041159100c80040c19a8041c650f202207010391310303000d007000c070358110b9403050001490744407030343d08c1078207000300c006110b600c9a904c14101581400e044e0826002508400750381100c0c000703028011b0140c10310031000a000b0042803903590b100f844400814005443d0722b800e12400b91024105085030001400303d07101c02c4007600d2009552910700054400343c001840a803046d000d41064101c49809910aa403203101064981c910075a040d404c0541c03610307849400600751400c100040c000031a400000300c4c4044401102c0c8100b0b0010412a03040c02e0200c0307003059050724420395805085d0150000d024820700d4501000800503200b01c01c820140050341c910800c928070844035064032035280703150040301825012100320340c3c9441e0346802c04001c4819940c82580141d50100c10700c41044440c440b23102c0e003003c85 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 913780314 1250 913779064 913779071
    0x5010b120307080f071712040c1d0712090507030b07080108120d0b1318020f0102210c01110301060f09060518040b0f0d11031203161b0c03080a030e01 66
    0x1160750f0409584200f00510b820313107001040b840100680c001200380f83c0600c10190684a0085607400c080810040d1801c503804500d02d640030039000c1344014850624014502c03007100c4c6da1904c043c155441ca1901070607040740768a6882100200310b003040351100942c481c03240309c2c059241200004000f00410707003042c411604140c545006004a26040c1c589888020400140a400780700000340602e8006c0507160714242880d44041a02c4d4000d400d800344a4002d880400800c030141c1c00480c0c0311001041c5041c4601c3c4222644040c6481850140c508406420000148811140c40600894000740c0c800c40c001600f40c141c07214195440b0701003200034000b41c10224104807a00240711050802010442c5c020356440030039880541e100c845640c0310b0311001c1c00c40c1c8581249410950030508450b80380e20300034410a5086040c03081480c04880c42182c0b000c211030001d0f01d001c5011105a09013030040e2443c03860740d20b240004566403410100045100e6034070340380c1d00c00010b03002405859000c18400d14036450b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 913781564 1250 913780314 913780327
    0x9200402031003081c0c0f030f0b01170402030a081207030f0b130507140c010e0c0a03021c1401140603150103030504060e130c08010e0c03010503070b0d0e010905010b1203 75
    0x920034001015030b42d000740020341340c00403407101d07451680310300080f484151b003440ca20005543d000302c881d0a441400750340500c60840609450800d958040d82003500007950341c044031072410340404050780c1040c80101640d402440c1e948440c64181c014900d0050032606070b6007845060b5801d403203044010b8490310001e201c428007482c00900818000c41c2e803100182e07121f40c000303042075115110042c0640360301200241c803841c0c020349841c02031010b480c110380f80788142d650081041ca07000c4882000c481c3d0081081c800d00050985100c81c010701710304222401350001c5014000c0507801c0c010342c402484401c0441240c1c0c40c1a108051805110403010003503119100c00510210b54414210b90598600d0b04101c803402500802003603512000d44400500180b40c00003040c861581300d0101812034104a5202c05e503500e0f40da880001e1807000f0710805038140c0c03169104101508520003c1c2030125040755001407612508034500f42074441da40000c0b5080d075910110003220386088061175a0060304007005605190 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 913782814 1250 913781564 913781581
    0xd08090609060a0b1f0905010f2c010c0b0708040c0501050a170601140f0c0d09060906030c090b030f01031e030e1e060403030f020606060f190e040920040203 69
    0xe000f0300890015a01da40d04c00c00b1a4032010040100400903d43c800d22452070540f00800080050040d6800034424038a902d144912170628881c0300caa1015910112001017112080201c400c046028188007a101d00b10b000700b07800c103908520030b00c03040d11214924a030a250210030340889801040c10b00c0000c0c03080c80d040c0e9600c41442c00c10700280390641c82e9188c84000040c0e5050307104e0155260100000074602851a84260141158582e550101c400d070034082841520341e50041e000741e600003500d942003086240d20075007003034007031810300d0421070040e13520383c02400311503441181d070583c02c44c0742240108104030414400611441542804003044242135070300900300d0011a40d020304c40d418903d46203030a060340c040011500e0310010300460382d866803403030301500420b0b40c2008000076008e9513000480030704003074003103849036450007410514181080e4031b2150310044500c03a03401044001d04a01d490b03a1110700c01c102095001d2041a0221408108a02e40d050581003880d03000354014000d00c4043c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 913784064 1250 913782814 913782823
    0x105210a02010c050705042a02070602060f07030b0904200307060509060d2406020708060145270f02010c05010b0405010f180c1b0c0e090d08090609 65
    0x40d542443c01219211103414403a1a01324590006940145090694912035000154161000e41007099203560000c4040c0f06a0725400c40e0301c295000740c2c000c4000505442c0c05098042d50110781811f0004a03000c0da48003041c3c40c018111011651b501d009840c1c0d0301030102c918500140100120000c10340c841c1007000081c9140610101540580c002140b40d240940c4560402c032000700c0c4100c2e1420f204943d00340d005003408140d10480016024041d40443e07403000110b00310381030780c00c40c0c150613090140220102202070b61440c51600100844041c002450305600d082c400700e01c40d41d100c08602205001c028802c601030010305c0b981c0010b0060360b002c0004a10314002507146809090000941030541072a5000d001383c04452780d0f1003490301c0d0001c40d410480806a000f80c1d071050309012000354591304040220360305081484082070413060403010a0242509281c007403331007446e9450125640391070792550030105950349662074000d06000260346501c051090b42c40220507008100606040540641300d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 913785314 1250 913784064 913784083
    0x31b030c1a220606090c081f03050303040f050a020310021b19030503101212030507031e1503060203010306020c0f1506060a0e090a0504060c0314010e1308030f010521 73
    0x30820b0301d084031000e100a60b030001005101000040c0a80290000001c149083c110741c16601503801c0b2480c60004100301030010280ea41c04001185540c64130303112541c002945800440d900d00c100803140c80103841c01d01201c65500364240c0e01503220b00802c0b49041440300f2201c80d056140d80b00080c040403400101e03812042c901d0b09030510998039102c07620365611903d2207400980c0040e20360b00404042001a1010785c002960036542008540c480100450aa0784030080400401c00c10841c0910004000e61041400141100509042c10366070381e00c41c010fa8100344d00944025a020034a1240d01c8003d11041c0d0715500f0610140072005203200c88204504000f0340b2142c0121804a07484a4960045c0444604481c0007880c00b8014986043c000010b49070448088038200e08119000700c000d03020b4041c4503880c000341c0b0002841c41c4c1c01c0004600c0c2c0840c3c000e00410350009882540303404142c40f480254010f140301c0c818400e4560400d0b0920184080c946503034401049103003500b603510140803626420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 913786564 1250 913785314 913785361
    0x1202252f04090602041a0d0c0c20041e09110a0503281e05010c050f0904050c070f030809070f1d062404030606050907021504031b030c1a 60
    0x828a449081c128000d000f40c0c0c000714002c1c01528150030035400c1034805046800d001001c14008234408900031182d041e01c1002c024001501ea00300d40f248d0382111450700081c0c4101610010352070142c92200c481201c001903054203030950f11102501030142a0301c910200d030302c064404820140c42c0c8400b2a40c0e95000200030103612030343d04211280e4818020305903417113941081580d110500080c010140d41000d050782255558607110000d840580505c0554031844580d410f41410400c2c403400b4000900b80007044481c0d40c00c2c040000d000040c0303100101c800c219029590f6003180d858000c03c01880c28156804c5140342c0d90040a081040c0f80e0b0f6514501189000c44019041d07e0300c0340c4022501d0301c4c007580e480b001c600054070340d1700710014198005403040340d000f0348040c4039103540c4506101d20148240c405000507046103500e66160f0f202c0e5400c490700b00788245000080c9242000d004910704e0700c0c2d000f086000813500101442407200c016480d040345102c5101000c21420220010708902290300c00740e11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 913787814 1250 913786564 913786571
    0x20303180106030c0b1210030c120c18090314030c0301030f110d06022508120c07060c08070e0906010e01080a060e1003021507080403031202252f04 65
    0xc40318500390054002141d100509040d282d8541801c2d412581080c0c0c800d10724001e1400019080d12462440c0900700c076000300001b410a8100f00d940003903107501c0003041c3c0d0300c00303480100001c00c40751707401560b10f07403048200740080e4062403458000c003007501c0b074490440c1030346003070047c8100a541001246c0c11a80e00c401424000421031403c80c1700300142420042c0d01ca142c0310200130a008903074004142c030552034000c040e2030101c0c104c1c03550341201c0c000c0c04c0070301f029409102c84031032001c40040b0ba6400208203090103080c41e010f40d60342000d4403040d1b03040c1000909040140010b00c0e802c544003d44401045031034108914140b80004c0c602a0003c40c01410892100007082c5241c504d94460006092491b51a445d14600724510608030350b090301c01240102540005070700c0d100484010b031000d20f83d001444a20342890341d14111140000c402c0b003101016030070840480d100d140010640991418580950711001243c1000c403554603803a0000007002130320b07140f6002030403012601104202002c0b0b4000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 913789064 1250 913787814 913787851
    0x170307031209031e090609050d2d050a0f0605060109181d1605152704181a060618011209050732130c0c0506180105010b0a020303 57
    0x11140d0004283ea10142c0b0300c01c200c40c882030f45174482c05140a40b0110b4417503501c015550414000100c1c020310000d0020552a684000a4001c1c2c20300794986650018800c0c2d00c0c2026515520304104002c1822203e2241700d0100384100a07860040650004003402c3c4201c1c0640790154020079040040c004400c0203a0303500d907101e00740c428054500c98020140c01200c9600d0400c1c68410003070326490040340d1141c00000500202d00f031030705040381d8011040c43c920b902089020011241400443e00d502070303001c2e440303401c8400540c20b6840e0790320300749002e84c00003a071044c8441803a220001000d41064000e000130070200503030806084440041007001c1c40c0549001d40242c502000038400600e00070403501800f40e00048040c6107048050681000000140f0204071074111201b208515960a9420400c00d40c2d207030803008225444075a9000080c14481610140740d070b00c0505140045070180c128507500c41c0ca01440308030911403240503000300d10401c1d1511411460107560390100030041c0902d0120701510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 913790314 1250 913789064 913789067
    0x5010815060703200f011103060102071715071205130203070b090406330807080f090f1c030f14150a0b030a090b0a1803051b030304050717030703120903 67
    0x142451901800080c4c052402e00f816942c807841d0a0742820302560030004a188590303800e4044a0003104145c0042c10f12074500360400740c54000d1080c00c00114003820131022001120907411602c20380320707652620202040c22680030112040684010f2010644a00c50030050701e0010f45001625001483d10352500b000500107405411305420809000812500c100203071480310015014008203000036926441e0061000c6880c40400c448050000b00078001198111101c0d19405801c00d00c03110503103581c1e01203c40e0840c1703066554000d440c590f492007140322101950510483c154038101000074080b4960b203100300644a04090002e0960300d480c5c040d4140d4035581d91009000030030300e005285131685440c01e00d80c00180010780d019684c2d016040c00144c0c11525a2050301504002c080c06114403a042e071b00e084035243c210f1505846035000861008480010400145100320700c118003c021031070510350030721503a845c0c040c5100c0c0142d00034804100000d40000c6c8880a0320f0788080006000b4015050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 913791564 1250 913790314 913790327
    0x709030602030c0f040b19050f04030633060801090c1e030b0907020c01030b0d021309063e191b2901080613060e0c120601030c05010815060703 63
    0x43c1c0c1c003015580020b0001ba1807039a48060524045040a0303100908a10641510340e0700c20400b0342c00f076030f070010802440002c105520542c8260701c45201c80545103065110b0401042c0c84508040c8200000c481c00c100880e8401041c90241880c070340c0c140100d18113801b002d005621b88462440c103541100084840c814440d9103d01c0d01280020200109410b0004c0302940702c40c0c0c0c00b41c10300c0c0068100b001c051028103164401c04103d81e4050301d05040308405400c00c2000f00400350b012100746403074038240d003821201007821041288900c00e418031425020110458024088034807007400200500642e80c01034641d0b4001d0422044504021400d80c001d402e40000003072000074000d200e0a00e01482c5281c0903031054941052489070505800c0c2a40c941345400d5540c407085071038200080060714014001a071035008160001d94140448024000c03a100064040c00b9110741024241d00c001c00400c00d000310003d00000803e02820103006034104813862240e000d0b402c000031801210f0018011041510401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 913792814 1250 913791564 913791577
    0xb04050316031205010506130e0411300601050a030f06020c0318010e01021c26010602010506011b0f03082214160e0f0c0c0f0312010e0709030602030c 66
    0x16045100ca0000d454054890f00303419004442292030b00e07001080c10f04020048a0413985034a940341d0300c06180411008110400400894410b60b40c2404400691201c009a0444003a2404600d81e895950080151040844c034079403001a44581c004010a840e00000e140541c3d4024044041d5513030b260402602a00c135421045d00f4511000851b6002014008180043c58000742da40501c00707858000120f980d6900c1c424a1150180002801a07905015001c5400804440d50348040410701d8151600e6100070268003000240c2d440e8801c00607d5039000d01c8440300e00d01402428000003425841d02c21000c0351490004040c815178101244000b00d02480400504110040340f03000d1424600c0c1001a508258185181e81e20442e14440c1d903039003030100203030155040c00c4141629039640c080b0304c1a107440040c1403106550070400030041001000d00c05030039421004d0000710b0b40c83da2038808400210105134405144510880c3c1480305039644801460101e980103140980c481d19141031003001c03072182c035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 913794064 1250 913792814 913792837
    0x60903030f161202010e2e0e010203040b0c070503090f040e0d180b0405090c0d11070c08100c02192306180a150905070504020409200a0c0b040503 64
    0x3040d00840108444407000b20988200c103104403510a1101c2070b0b0903280e8200b00d021084d044103901600300d10342d450002444d14030440700810500001200c0c10210f0354078040b00c28990f5000010041031120010545030809501d041803803901d20651240340d100d00900c00d0140c840c0c814400c581c02c682d643c0307070004203007044540161110004d904101402d03a03448071441500d041080d031400134410f003e080603501141c2025100c550b01d90f461640b0080c5540c0306c1e081c2103103140c0d554110140511200c1c800b40c06654400c0c50000342e20382c100070a151910b214034040254150030410042c02a40d808030f0051450b45030b14841d40344258840c60300c180203401162205d824604502d40741400ca5000049030b81c011a4500b400e001d401075201c07501c64030340e019608007401811000f810f0320085030140e4820300c3c10f070b805002600c01c000e485070005401c0c3c0c1d01c554400500d258981c0311008014035403120302442d100ca0141c0862500c0c2402c20040d2100910540c090041c4120400107024840b042c0125040603060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 913795314 1250 913794064 913794067
    0x10801090f02042606090616233106090e090c03030a03140f160f02010e031801031a13180209070305010312111c020f011a040b060315060903030f 64
    0x443c01e00c07013000c001c49010140301c0c032501c000318515000103c0e5141c000c1114104030060b08100300c50940d101203c1a1548204600001e600c8456a03401c802800c04401c4802645481c90510030440d0702500003180c0c1c810440610140c1080019046400764041381c900d0001643d9a41c1e900e1000350900b80000c1c4d056130036001c001288594598542d208005054041c513148000740c443d02e40c50500c0c07a904032404040401714010b02d1070900d002c0d0171a034140918a10010814a50140c160390031a080150505c01041d10310308484551361701801a14020061144c56403249032580300000c5942d400f10800d030542c1c0365203c250296814040702d5401915401501d2603400703040c403410040c01840248425605e040c020703429510340c60310803031243d01c0042c09000281603c02c01000c1304c21000460180b07200030340c4102450345100306801e004048210282800c5030000010040a10054030303e01c41d221481040200200441c44003d96202e000140b01076a0580d1600700c02404685184514034074440700600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 913796564 1250 913795314 913795349
    0x8130212060c041805090a0201030e0f1626121b0102130f1a030402060a2a0302070501020d1409010903020a03150b09040f1106040f0303030501080607020c010801090f0204 75
    0x3801c02c0180200d031103440d44403a90074082c04011003100e400f51a014242d1708120b420802644c40790700900411030517441640c159003011840180342290341d060440c040050f80408100200002241094030030510b01700c0000c50b0649080582c89032156a010806500c000c138171204000c00c1c07131a1100d40b46003000005c56a440580076034040da5500c601c2484014809803101095a40c2040091844041028072660558031290308004e4160030883c003680030012001044000429800c11805100a4000c000c4401d074403541402801c01c0e41e41d80100f819584440c0640c1c426a41c0269544d06c1c840707150802545651088004842c08840e503400a58884040e580c0030040c0701083c66201340030100c0480420401d20f4400038014140c4080310301401114860700c0103008991f1200d14124500b000815082c03800e911213076194409040ca030030650019a81c1e40052001d0784080003101d07080101030004000788845500003c2141005004d1186015207034a001c500c85041501a40d001d8444207040c01550740c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 913797814 1250 913796564 913796581
    0x30a05190207081002070503160609030f0f050a120617100b150d05180615040b0a05090103081e0711310c02160906050307090c0813021206 61
    0x4020448141410040100854506000180b11030807a107042001d0140c2c14183c529010003500200e0084c2d0b26400208001206500032a01c0688444d100d1000010070b200d80d820020058245181d07000c0c18054178109080724103400c0030581d10032581900c1e01540090f450002403000e0592036200f6820f401d0700901c9030082030404140545402380300602041a045000c04200440c61210702d5104400e034200b1402c050103119030449580440100710b080d48489010b25100d14261003141c2140200482e07076110f0ac128071b050b0117121881d1404035000c2c04e140e401c1c100040d04030f94041c4402001428005500741030729031000088884000100b11460700c80c445401c1003481d40000d550428032642c0c0a058484032041203903013004070f641d01000380d40e8007250700343e0201005011400b40d2078254822a03008114285443c034518000e0025210007107402031500c02890728011480c0c100030304031400d003038821540551003903000760f01c2802c3c0101c0030070081250011074480045101450001d0040d10100141e68 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 913799064 1250 913797814 913797817
    0xe01062601020702180106270302010f0c1203060f05180a020c150109090c060f021507090504061403010507110d0806150c1b0a232701051f08060918030a05 68
    0x207d16581b50508104040c12244a0104201d0407500c03801600d81410300247d44107040103c3d4500c0181072074401e0080507118007036440e226080c504000b03519480140400f080903410000105404e07107a20a50001070816a0207a075802451144e126a01007010b040400080000509141d0341c440510b00c5941c407054980d0280200101c1a00c0f03110440000040b410700c01c2106802c40b509650140003500300c00020080140006003214040001412010075640e031141704000081c401150303040301001d180d5040c1429248000d1a00e81132054035103607000e06410118802440e9070b014039108109959039000108005d0340d0300b940e10100c1d00007041c4603400020005143c800c1d000383c80b02102c1d5500c2201c0030046040d40c0350040c180e01111000c502071035000810105043c44400410751092514402d0140c000c80d90f4260b07421303542c00d01560041007503007404005115503a10328901201c1c85d03000c4080180a140c40642080e020f08962000145041520030303210b0607400524003a44e9440c04140c4004045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 913800314 1250 913799064 913799069
    0x30f0615031f0923030915300f01050a031419201f080a09050a08031906051c020415060306060e04020705190809130207060e010626010207021801 64
    0x6007402104507204401010301840840c114081c021890840c1c42014030804900c90300301ca814060701405094401281d94803402c81281480a42c0c0005080023500c542400c01c014208030705041c52a401031080340c403452400e40c15603410140089a0242540f0401c1c1f03001410b100c070060100d05940a078082000c1100794690816000010403440246402084841d02e12002e240f4610070010700d15181c0d05000da00460b0348204407181c002164500fa8840905120300341c1c50480e6420f0b0b00004119011007005015007013000511001c1080e01d0800d07012484280203c0e441b140c0007070305004941c0443da51900501c6034806000d05940d0302d1541c960000d4080d01d542d02449000c5440300507060344509140c42500e0b07060750010003c00500e00280c030400e04550103280140c804900c00c001c9020651201082d44540c0282408010781c5da120509002c0122003841914880690400004000e40d0011200c540403004000d81031490013011081105d009114500c402034120f42618501c0e02c11984900c0502d04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 913801564 1250 913800314 913800323
    0x11010501030809100e0f10030e03190909020403240f090506060a1a0d15150203030709150215100e0a0609050619260303090a05010b030f0615031f09 65
    0x328591550002e80d20081003070300d100d800c006c007481c074101c1c1403500034000140410342e8100010004c06080c10941554001800070042000d00400d210419903c91003050041c000f0080c11418035056541350441610080018040c2c03aa01030046100050031f98040421958025420041e202e078902d00300b0b484003021500d040c42004106000113400710100410028075001443c91440c1c14681c131035a5000341102000c41070020207840e00403c5050b0a02c4048880d1141d0340c005640360718000c1c0d8002e000c42d0543d0020001c40c40d143e541c6c0c0400c2d035000075014600042600640c1c00c40d80c1d80d10001003d50010f40d0194040c0d640000910007808040da1081c4151880400d06100c156600400d010402801038130700d040311045800b0800c06052484420a42d1001c5178221300e0b07000c03c03000340580c40c40d00300b544e221009402c0b04c425a03041003024880c200c003034607040d0098040b40710107a01d400c0e00c81000410810052400c9003040103155001c1c03002a04d500c40c40142e40e0042c2700010005d9008101d4885d0888 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 913802814 1250 913801564 913801579
    0x702120307170709471207080f01050f01080403121808070219080a080702040f0f391101020403080c1e0703020f01210c050d291011010501030809 64
    0x1c3c03000141c17900d007990180d451405482500324203803400c0421059174014000c4040c0404040c0d400003040c040c2c01900259181542802c02d0081000100e80680c04a4401c5150840040c02c42e40c00c10915a44590181421038032088038000740c501600006846070069a01000e82d00e0803c015031300039220842c003c1e500c80c84021038a94511407180e203580661201503120b05240000a07481400415000e480a440810b1004080603c0b00c10340700852414444c0c25200c03000044501c0058029503000c2800d03402800400c200c00f0740c042044c1700b4134210715081202c0300c0c1c0703103041d142801d40440340116441030890307a9910013202942e4480c0041c9400c601200c2c486140040303400000102c6400b076a8000786031004801d5450011754a1414900c1100c03100820040c00c0306c2c007e080b921849840c400991601559124000880021150b4101000b292100d100410000d40704649034042c5004809079440e070203424044c5429503540c25422424007041d800d140000c410840942c0151030108815a03400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 913804064 1250 913802814 913802849
    0xf1f2105010f0b1c0c2606150105030109091a0a0b15090f010509130c02030c0c0910030b090a05030a0e0a05040209010e01120902120303060108010e0702120307170709 73
    0x94280c82c032004945a0100300d80002000c92003204c1c40d6616094440c00b20000c204d0ba031007140c07901d03940700711034820495000000c098035907000a20010ba4010031440020300c0c5c9080e850000f1b4400c0c04103004220040d5070742e600c0ea408003c217070399110080348000611000c5920b41b803840c55014000c0041c0190180ea80b004031100d207801d1f01000c1d21001100103100b1221042a4001102d8581051941c2548140921514071850341c15208081c402040799025654a0a220781224501803840102c140240551400c101a5802c41d503400c0c4140d036400000701c5500d40350b040c1c2c03491401440c03010107400c5010010b1056000c40e0054580d28145605584d024000c5a5640c1040102d0140203a20340c00328a140d04c8100096210300308151414070a4203000130541e24940224101d03058004101c0603d510000c14000030390b03042052280145040941c1038114600204000e48804d24408622032805001c004030b00d006002d020844130003424015246840e04d042c0400411125003403007482880184140f00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 913805314 1250 913804064 913804091
    0xf0c0c010f0c060506040f0e07080c010c081611100f1205010311010c0302010e2d03030603100c020c04051314030a1b1e03090306140f1f210501 63
    0x1804152066100c4101d02d00c20741e1a004040c2c6002030070603500558420107a03195010ba8807408460301075a0b00104103160810302145e10b440300a880c228140b0421031240300014500301d045035404110080c80707440e018113a15206101d12000020b4660103402d0f10901c0604581c09983c41014a015944400280584c0c0d10b01d80d044603003c0c000a80700402102c0311002a5008141d400c28081c0b2030310000503006000d44115003032104100c0504d40502c2c420fa103000c5811b95881c41161000103840c040d502d14203210000079543c5a0031181d0000302c0d5122007018650070b000740b05100e4514000b52080c060341c0303003600409c40e940f15540c03c12196070104981141c001d000003c01e507000089561181217544000103000c1c40444151030b070451300c004180b1519070402083d0074031002100e100e0b444209500b41540303000c80948a100c01c110b032884411030208210424450b6074140c100c2e84142c481c0480320010404c16070116400d8016019036040c0303204150700300c150b9041321212180039000810903800300850 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 913806564 1250 913805314 913805327
    0xd0501050414070f020c04050115020606180f041110031d010c09061407120c021219060203060f0306040b0907050d0c0b1c0504060c1706090c0a140f0c0c01 68
    0x7101840855000140d200b90003154104040c03084c60040b100c070181c1090000c0c00752002600145200f200d11041762041503010407145801003c225240c030307001040b80b0382040d88440002d040250058024021400340000d2107a01d9016010160542d42258620007002d805410340074454482c00c2d0302880784caa404d40c1e061080749a80741041d030700c042d41140f816408440016201c0b0910032800307010049440042d60031a1064901206070f258a40401a01e004015010fa4201d000e44516002101100141010040350f0034a03190700800058607074a460b000b1400c0003801da14802d03094172440081c0002e0008803250103104034112002c903030885848109015821036100d4004281c0c1300c4001c410b0010000d014050f2881000b0b62020350118100401c1c82c5055a00c1990144c814070b58506c092152158045000d48040040c492150207504240002c101800401000052000c1000c54610300e080d20505040390b120401032107481c5c44400402003800154010a0f80401c0ba2140081003003855001c1d82 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 913807814 1250 913806564 913806581
    0xc060e030d030f020c01050405011a1012020d0e1005010e0a1413020316120201080c03010501020c041109040c08160e09131e080a02010e0316080f0d060b0d05010504 72
    0x4014044450111100307070301408601948080f200c0d02070240c000f000c3c07402d1007031910a40c0940d00215480710740903103050705041141c1c2018050016110605c0506d50446402e9030004011000144d4600c0f00662a000030300403071890322111b02980b12031f000e92008913040f06041e20013013142d1000e540c8500b03030010f048a90401b01d041a1400000024003007988140c2d8020040d4006401e841076040c8208800000c6000b680000204100009211040d1750344140707403540c0030030312504d418615410400081d5607880d0305400b941c811030301e03011a6800100e5030800e50300e1130a000340082c046c0500a031000740c4002403c40740072806c40034610580c140244038405000359028050160300041e2514403c0c2940740d2134806003503d028140034903034420404506d94015002c2c2c010000301c3d40b152080c4400a003036555486e08401240e000344881c81380410008400581980c0c040c0c2c41030790341c3c1400a000860390041e45101e100d42c0389810400113103404260010074000c141910b080000341c4e2210204802c030340402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 913809064 1250 913807814 913807819
    0xb101401020c09100305070b0a0e0612060d060609020d090203240708040812012d030209060105070302011508071505030c04031205070506070909230a0c0908120301030c060e 76
    0x104100240b6081800c0d0040e00142940c1162841030340f05d446007490800c3c1c66010002c0368500241c0d00c1d61141d4440ca82c03041d0710000300c91592601c0305802c85892a0300c1c1c06414148202410352941041142c1944601e00401481c4025520b84c0b800702c0343c0c1001070409060a900900455600c06000610182c650718541c0c0283c80c400e0701902c2d84a800c55110200600450351600308000101885100e80b840b6402000c10a1000d41a059298918040184280085c0f00075900d032070401c2c80181c3d502c9034265803040082c80c000c0c2c0c5658850030304a000d8801480d905420104501c00441c1035031003c2554402d488884011a02d10b0041d03400440d86031004031607070301c400c007414481840000c1d80301c0c12051a40d81c252428a092440d1616103c1c24140d080ea01e21010071421030003081074080c9030249072a143c041c1e0b506500c2da06d18036042e46c4407141000b4000e162a940d40d00e00300030094016100b04000d8084d8000f00d42900303d50b5986004c00364400e0000790742c441680400020090700c520340032101741d10301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 913810314 1250 913809064 913809073
    0xa06060905270c160f0c0b0c0705060f07141510060503130f1b0312020a080f131d04111f0c0302070b0d060513020c07140a0f030b10140102 61
    0x100b108520700039001d054810260400c205104050544508112565016003142c418500440c50305039000c403403503400895410030a000a410040c004910941100c1080eaa42552076202c161400c001c0c0c41342000007070805012000f0014071f078100140482d0740f0741d245203110400d80c0340c42000d801c0c0f41020380f080e07000140b42040000c41189030011a00f000a00c01d200f060a001010f640380001c0002d07003441000000f403a60300400078402d0460307100940a800c1c0c0040c3c140d600745601d030000d49105101d0f541241ca100002c0c0c00421810044581c0018a076803c9982c101d40c500d0540406105070a4500f83c2c0e821080e81402400c078982a900d10a00c24040c0900b00d4404508210580d001c005c010010b80560050010000d40118a00b0062000348210900050464244070420010340001000403020620500084815000c00928a000d85100d02102c206601550000822042d901e4100d100d0441040ca000010003040344282801103035011007421f0380940766010b0784c0840a00c00c8510707006030322 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 913811564 1250 913810314 913810369
    0x23010302070c1e03060c0203090307210201050c1623010e061207031103090a02090a020909040b10051c030f02060910020a020c06040b091912030f0203120a06060905 72
    0x10303282c9106890300c090440d4030745000c2e613075100d540440b0086c03404000980c000044025241c5002d00201004d04200c075000041d84041c1c0a292080780d0300d901e4002d042c0000040c0a8454401c20050040e103100800100141c83d61981b0314801c404600114000c0c175100c000f64500c1c03441d8015080c40480b401d015103020309010405410250140c80503010380181607a9407841d0070702d2030000000398882c1201100405051405205006c00daa0008003032203452441070001034281c1e038410094a0700103402c17012954403600c0d83c034003041d074002c510390000c0e0703110741004030040ba074152a14882e00e0740e50003601c40c4049180c402d5016070b1500403c0f5902d415581110b1b418a517181041e5014100d8035910f8070494a240c04c072840416041c1c0e100b41c01280c824040881c507200b00d46404000001768016030140300e031802c1c1c545290303031560001e101001024081d070202104000c6108109030780540744450203c18550800c0c40c1c06038010061130003030320006008140086143d003482070213091200c0251544001c84d44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 913812814 1250 913811564 913811579
    0x40201020a0825140d08010e010303111204270207111e030703141c2c0904120f020309060d050c070c0b04050f1005161b23010302070c 59
    0x43c020111503040d503039025000500d015146214040755032184131450a6003e266161900c1e141280050208100044005102414070b03205d4483c11a07505040c12000707403400c410000e06050317000713143e206400000b01d00010540c1c65031401041c010340990100340000d1520004000381c0c400c24002a02108030704640e0201400e1103607103161078860030841240c69540001c00641445182e5000751401d40ca1205600302da404180404103e12506600402e04e0a03074100c0060914540d1203055285c034140c1005011f50760030319003000d962040303006140406614040c03410140f4107081030a488001a0598035100245000004a402d14440148040d040008034005003000d004000e001900d004424001400004c02c050a000c01800c080512141c40b07505102c01d22401d00c4084000c58070a040b00c250300301860ba00304044030043e4030260400301201c142402d021001c100b601d45c1010b01d00d00101000165041c280f40900a03044011481071000b01400c40110705038010304902421400c0c0c241020050007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 913814064 1250 913812814 913812817
    0x4060b091809030f0c0109060e060403170702010f0c0216080316021512040b0702010e060106120f0b1201270b0601050a110706080609061e04020a020c06181503040201020a08 76
    0x2108210b130700d02221032006503050307000540d06078004d0f0b4480c0380c00001c10801e4003800e009104400c00602e802d14103902c00402d184010f12810601074491404100040d00c01e410084c009840180c0c1400780007010a802940c0c1d0170042c4c0c011417001581d120200d05500088100c1d070030303a4500c030f0042d0300c0c007802ca80070010121524500c440501d001007188220404000703901368400c5005424004581c0340200e00a402d51b98000009801e0790809401840402c0d04440381382c008003120500001c5441c1e2800e0710070005c08500040e0b561005411188071039040054101c481e582d88021400803101c09500d62201081700c1d0741800401003881c003000a1125441032020b05440042460a9004800b40c4082c40741000615001040011075070782c00c1000d9800c0807011550080c40946071095003241c0f0340c0c4500320082094100920803a0000340c000281d62007007086030b0407120300800595440e400c140100c0c00e4000c1c409540c90007100c600760201c560203000740a0328819501a0040c20f0341038029641c40350350707 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 913815314 1250 913814064 913814071
    0x180f050402180910080f010504020102060f0406090b040813060e13020c12161211060106080c130e061f020a060c0926010b04150e0714130504060b0918 66
    0x5610220602c0c01c400c0d9250811180145041c070400390041e420901c219081c8800c2c1514003507140c2c146414000140d80c009140c9901c210b000c0d60081e0262641e28148002d0300540c100038044103502c405200c24052014001c201007404980540340c1c45603502c00c20340d103800444960303a6210f0356110a240c80c20a181d001452240e001205444034103110210050040d080382c0c040c0b01041c41d000c01d103030040262a240350780a09100f4104000c51035440500c295441605014820400c01c00d54003007028030613100300380c07980400340c006050240d98403800032440002c4100c0d00144145400b5102c6014850700409110154055501800c035107009602c07031801505118516804003d4049800a00c4070b201501010485050f01080340d030450010858a00b52440c02c01140e204a10740301000d03c5000c100c0b0400c5003259103c001801d030542d5218804d9a04103130019181c142e00400040400040e44200101400e5450482e0b08111060311000418680e000d035036030054005a103041e80521002140d10810350 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 913816564 1250 913815314 913815337
    0xf0f01080a150e0c09040303090507140906240f0d060608040b013803060102160819062c0d0c031b06060503011b090e040206030705210c0901180f050402 67
    0x401344d140404e218001c1120b090700081d54904000c41001018000c00300281941000800140f10b900c0008030303120780c00b0f484244108030003d1284014159100401c82000d06a0101600c1e807564106401c0154880c144042824ac0303803502c00f04185000e042c0581c02160020200012613081038007a0340104c000c003005c181180c455402440390b00d8868400440404154a6525102c0c06d018001915100c44171002d2021a2107030341d0140030344000000d040300032048071032200c0369090301c9081030070041c0704c00b450b245c400e0501d540401404079000c1c0200300c420805002111744c0e940c207109049401e82d00b01003000b1700040b5002d0301c41841c184000c400601840c01640e00142d400e9480c00020300f120804500108401c0d01006407032595500640d02000512402007000f000d403030640e00107042c40c1700042070701c8140800803c400f503d08241c0603c1401085403010141668103102c5020b000a401005480340090502c240402e080134506a0b0001180d41d00640d50b5501402c0c8020000031350002980904c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 913817814 1250 913816564 913816573
    0x50705070506041508090705011d15031315021206040b01021914160b03012d0605180f090f0a1517011d07031e08030f0f01080a150e 58
    0x40039a102c4004000401602c5110140104481005080f4003001040703140c0d10781014004200310398200114803001035a4690107182d440c5800001480c241c92020118442c0c0302c080104060301c42000401145a4011a042c0088840800070a001c0e0f101e0100c2800c00248005c02003446401c00b90005502039005005865080d80c00440d50038401c10007081c25100b00d21152002c501041043c8030403111402d0b20051024030034100b40c3c80c0c58485c4810721508410400b90090043d10050706900c030a4086050940781100d20b9440900401c140c101d034086001c68031a10107418030a00e40b141c1c800c05c01401c054000280c0d6030b01c0d21524045010010010000141c40e43e000e000c0d28484084044050002c00c01850071110b52100345034210f5001c1051814901c0c1c00d114a8030240400042d40c8c1c0880ba400381a04a09000b11000954140904000181404001f000348056000940c404c107218002c8407102031801c0ea030b640c0d140d0b40d070b070740c014074010b0070040d00052695800225508030f1100e20341d081c003c59 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 913819064 1250 913817814 913817819
    0xa082211180a0506100c23070b0d06080c01030501080c121f0e0705030106031703130204061404050f160509030106080a1a160905010e040905011d060a050408070305070507 75
    0x40340c02201221161041c070b40c0c3c0c108002c803130300c0c002c191038152000f1441c000f05c03111400e0f0740b02d140080b90b054a02c4c2c59440c03a4450039040580405c440c0018150701e44056442d5420411943c0c00303040540551441c1d07014501c81c07c5899403081c8070f160304a5100000800b4052100010f001c02c0440c110640c00c054000d2009042e500090321600849030300c40f8501c00610b20300350fa5102d07400d040c1d50347c00c920301c643d04003c1d007040410f0306035080c41003e0072050002e0791b407611090348060200040e1000203400c507040800004800e8100300c05c03400015411b4500740200d03604c00341e81003107000c0d084a100a1551044a141001c1813050029003505030019000003174071078460030100e00e464031000d4120303070900d01c0700a20f08540144245680d08035140700c250311114207250a000e40032742c0003800b645042009001e1001060386c5d81d038011840c100c3d00a8002c212460703800b00142100003c508144415101d14030100e08200c1e01c910400d07100306d0b00000c0090030484551790403100e0b58031206041d1003511465901 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 913820314 1250 913819064 913819099
    0x9031204080703020a080604030c020907050c0601030c0e0714031303180b19051812160801051e04020a05280803030402010f020a03080a11040f0b0a082211 68
    0x3400504120030051003000e14610410024400c1d40d08030f03108641040d0300780304c0083c1e04480151351181e8101e07010002070f0ba0307112003200d00e8060611512003920070540000148000c5c055103e05a50408140f0386c07242d0355504040c4d03011200810031842c448810000114a404002c20801e80c843c403034a02501490585046d59000e80c2d02d40d000070000310381c001200e00030614011501c040002c503e040140c100f01c01c0ca150030b08250701030318003240075214012002d8240f210502001d00609902910000703100d4a60850368000c0c0000c80780444649020b885100303003001004440c51042d40e00400940c42c1a0900d400d00c050743d288200092544800c00340890030001403480901c0c09000690300442e0bc034078050000600601c03140303800c5000c0d904044440d90220f64407050140d4002034024010441d0362015031200018451030380481800c0f1024100405d40d614040e000300402c0285640f24102900c80c4500282c0c83c4c481702d2006c822250b1000100800181c1c1c2c80405180280020708180407003c09040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 913821564 1250 913820314 913820317
    0x2091803090310061d0912030a1d0c15040f09110708070503070b010b0f2b090305030108010e19110f090f0a1b0c110a051909050114060f090312 63
    0x1180300c130344030310f0300f8000c10030181c640300d002803450702d05903d290500145168503040c166501c0c4d99002000400120940c0c01c03a0040310806000724030441600c40107400301a103541c03940d92143d10030480000c2403240c44d8444400e90f0159151360b544c52500a2400d1440401000050302072101801c0a02074030002c141110064004e03540180042c40d075032400307440c0c0740401b0801608800d58903401031184007940030401054031201c60301f00270b80b1094040350b84800d51010034100e50030001c081c01d004059082641c000099812188560002d000e1a003506e0351040d11807c40c081424005101000d01038042210010000b090340c00140c25006000c1164002c10400300741200e51085014a0304180300ca048018498075000315010008d0051204c26844e0040401c44140c03006030032031a100c3c3d06030009a444595041c014079005010b4208548168150407071a900e81c8038801c801480d1000015030070010544400c907113880181014640314294a8403400c54000005154140c0b044810401a5001000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 913822814 1250 913821564 913821583
    0x31026030705211204020d02130f02040302010318020d2616030e1009180f0c2708030a0f0e09010305010e011a0d141207061512020918030903 62
    0x28084001c80c4450780e20340c0003a0f40900e00c0c0081000c03c03d40c1e11850640d0410b541081e4100c652890503d03003800025400c11501c0310740005035240a28042c500c010550003001264403e07201404541032040c40503c280d504404043e4018a0207060b5600081c0e561803003002043c00341c19002c1000024011002444d0015207801941e0350b0f014000c2420f1540054400c80c01310811541e071084084004c1000b003101d5254824081c0c9401d003812145036480082c1c0028241d011007c004202d000c0250360b00030041e2003003145034141e8034890501e5417101a8801c0d01c5500f500c41400c02140f81103401c8900f16107080a217400d0030108402d552501c1070301d69582d0842402580603800100389c81c400d00010508581aa00410007115001d80c0480f9403a25202045601203421083c00d817007501c1d05540103070502c6141403004100c5680000c00c1d1701080500d92011000320052012460b801c0c0c0c580d2540e01c2da1080600e0003a41c00b0034030f0130002c0c1c240248a003160030301d00480001e5a0514207e1008603240c07041c0782 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 913824064 1250 913822814 913822823
    0x512030c1c05010314010c09090e2103071b03091e050d03081603021e07030c080d1b050405010215250c1505060612071704120e010201020310260307 65
    0x42c00100180720300305102d4988440140300030410401002e00c050102d4500f88201c840c84c1d611a40b203800f1880c428003246400324540e16001228000150f80040d140d8400c45007000801e090250ac00b501607841032a80c4101ca6041d01c0d421603450802c507000d069500c00c0c0703a03c0380b000341003080041a81d0b00d90f407170501e028500c82d4444506ca814601d40d803841e1842e078502020101841030100c0c189003040444e0900000180c40c010596850345800c08a4081c5220500946181d07000034030381c070074007405904c403540000d4110b9203c418596a403404484510443c4034032801644103485912500401c1022560000c4120407a424100013201030709056005940018001c21065042c2500b84107410140e24100645104104402c1c5800b800040d01401130f58508400b0049040004041500800c02040c4a00e2469a078290743d10b000e250030b01c5452003492001c000202c425140c113150b035005000383c070700480420b42a42495070030800b003c0c4251820405108000034070315850749220600740002c0c000f59004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 913825314 1250 913824064 913824071
    0xa03050429090616020c0d02040f0213150206010b1206031609020d0615020a0f03030b0a090603060b0301060e18031b15010b0301030c03061a040c09050f0405040512030c1c 75
    0x75142c0c9801e14500819414840030144120f8200030b80c00300390205140030032034054074804090700100300149030f9102c001c1d1000707100048101c03c00d002e680b9290110782001c50f40200072002284100d0711031100f8812150030080500c1195081201182200d5000e0300144c02c6601500c4103004003030411f002036100c60003280c0d0004088018000c00d004079001343c00716410302d42c4010300d0404002c0d03840004c050041d001c9065128080105442900141c4030031000404011805031035640500003403140e807200b02c407118a00f80c040241402c040c080c00f1b0440d0000d502d0801241c1e1a1800c00b030070040078901000c8140410056451817942402c0350b8040c200c0f2000050011010600c2c2260b500c407010b03004656141014030041000900c890010000d43c2d41c402d8011845e0880344400d1080c8141070404154041d043c800d544020583c44095242103540495070501d41900000500040f03d0040d030f0041c105800c200c003041c4c041b03503800009642042c21700103000c0c034000710480d44404141c50350300c10001450f01c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 913826564 1250 913825314 913825321
    0x3130201112e060302030c1005070c0305030405120f06071407061113050d110103390f1803120e06071b061d0d230f01061a0a03050429 59
    0x10b0305451144240b0300075a0030880203055030006a074a681c040a840e101d20140d00031038440794450b070103694416a0041e014030540b80c0b07901d001c940360f030401d003d0b03540100004c080780b032a2843d001603406200300035800a41f1440d20340034802c46400c1c1c58540b602c288858100510b6001407410b12400c000351205801290b03d44110010010710060103910241c480e03040070500e0b00201d9403035028201908001d080004a054242d06200000c8003000c503100d491505146041c1c2e0814a5039112400c2030340290f441a1605444007800daa054a69000005c4c01c3c1880300c0003030000451200044008a03d40d00348074000c60003c000007041c680c000a001c0f80d20040d1000743d024a0074810090784007400c0c0500f480c2d010030000800850003001d55a240701d01c15219440c500052003405110211140c0714405100d40034540c1c09042d0b039030741c4500380b150260f940c6410070004440400006410001400f031000a19041070b0080c110054003000c0d0042c1e40451a04a6414140c501400a01c8000c030111260001519 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 913827814 1250 913826564 913826623
    0x20705010b0409030834050a09050102120d11040b0a090e072a1103061503070e04050726030403150507031406060a031b0206060918030313020111 64
    0x201d0300381226000da8101050b003000240c00400d9154080c003103203c940842d071003000c101c50f804e1071400311410680e821041e82c1e094190b4440003d0030410a2a01c482c002d41d81d840e00126900c0300f21080c0201009428842140502c80e150864504000d0f0410380d02d0800c0c2e21000c103c16180d0245a4100204444c05c0c402c02400b980c80945035407041c801d04060200220b03900562600000504440c101c2da4540340b83d01c01003040607000c0d00c050820140031950507140100001e41039610038019184288147ca46c001008422401542c3c41389610101401d000e500d88545400014403140c0f06115984a0035180c040b40101040500011400ba4148541041e100d0091404668000d0861020035081202150038034144002203500240180c1c2d0304c0d0740c2c40d603c41100b1070007802c82d03e22241c40181c09200c0c1181d0117900080c514024181158014199284c80d0b01800d02004d80b21031100380e5400a0000070612402c1d002001c0185006051040c005840a12010f003410302c00d910301100103000d00111500b90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 913829064 1250 913827814 913827821
    0x10615050415020f0318010216030b0a1107050a1103150a0507080114030a1101050904060906060201060b0315040c050d0e01060602010b100e04090615090e19120c0c08070902070501 79
    0xb40c2e20380050000c501c804c0c82141e4a91050800c100314481300401c018071140d108018420844100210340d2042c0e40e103903e005100c41c1400c1e070341005258101406864240e408030b0031640c5480d400401058008002d035600d1030381d142c0d103c1199905009080c40c40c0445059084440d106030801200040c076031030200c0f40030780310140c1a04800000c4480b80314004064030000b0300445a00e4105070b41007940d40c51040100ca0318403501c800e09400504044000500c00643e420030000d54500e90000e01686448600d400c159001c01c43c0d54a001409610a01c0c0081c00c096000703d2042d441c902e0301614004030407141c1d00c01c0e20085c9030581450780d5204010803441e49e081c41140d188040c211107041040d191000010a8030401541171442a40d480914030104051640429001810818003a01155a507030031500142401c024041150240d40c031907081124003882d1807440c07954045460848815203000071549a22a280200c40004400101103072405c420801c41c401010042c2c00580d031520341d8600769095 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 913830314 1250 913829064 913829099
    0xc060806180919060209040e01060321050f030a090b0915060603010b0f0d020702031623090109020901030906021b07080601060504060c03020c1302070204181101110106150504 77
    0x4100000b40010356001241c200d4070300c0a14411a80c91000c03a040910081c03062543c06903100d86054482c0c8010f04040d0080d00c11a4004c42c6601c10b440e8040c5544202003909210310000150204144603002140b83c01454010103880e800151721409035031040740c0340e030043d01c0307041e03d540c0042c000000889100032100e60090050304e0545c20341d4941803019500b801600c8851a03040c002150010081006505440e80a50010112501907046480511020007a0f00072842c80c404103071240e510b2076589201c10340d02c032140034000040c40da282050703050003500400c184504064403141c150703000c6401130012f0705615000c1582403090310b4800140350700e0203040c0e601002640d000403004104c2c09030000190340464000c0c0c10208400c5121707140490909420300c0107644c0c000102d88031415410090303805440254400d03034041181001c596404200354048600003422001c0d0000c42202075440b03410402203804410001140040c4c548070400c06c0d074280d0700c10b4240012804101049000c001c602030425 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 913831564 1250 913830314 913830349
    0xc06061220031c0f021c050a02150405030405010e180108030a09050f0904021c0804030308100801090b19060308030a0b04110301080d050a0c120f021014040209040f0c060806 76
    0x204080c100c200140300080d402d4148003413210100304080c001d0003d0700c00300500003860001070414030005001030700284482801480b841c842e0611615603e200715005917000801036090500d06001103e0512050a003d41c101c2c40c005410354890503440005406005028040e5442d1031078024002e009260700c0e8451440307003448030030300c5003240c80e90000e13030780c2003a01a00d1206404081295500350f125a07240300500300800050000b05143d402000c6500528508440342e510f41d070b8615210303081e1082580007034615420f0401084204442e08410f1101c84080500840c3c07079030b0380e901d408005410031540d0031119910b418081c00c141c0380911135036440711100c514050444d41042c0e000c5039130301c0e400040703c41171090000d09807400500401c48900c4140d4070101032509014400001801040380301c0256026100d03818240280060394020b0404203d460b08840425507541c0c0c00304103d044024005540041e0000d1001c00826070b161101c0004d41602d03181d0040070308010080c0044810210104c29 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 913832814 1250 913831564 913831573
    0x61b1006050f060a020106181a060c0d2015010f12050d0e061c0b12240c0909270c01120c0e0405090d02060a0606050a0c0606122003 58
    0x10040d5100e821040b08078500f60f44003034840140000a1b40100030765000901000440201011955842c1d0040c0785216070600303840e40703000d80c00c4e018882140078103040200320fa000052440e1501c0c0c80f40d68940007000350180b5000d00b41c4044016507003460280c9460420700b01d18400140303e5000c0001200340181100c154010f4529070726180c4644801a0b505c03a40100042400302445c1035a6001c2a1110400d8800e03a00c2070207030f100f201010045c00c0c1070301c81320b0180b005801603104040c00401c62100d51a0000711161040e1902070594154500050103824468001d22245510752160180284600d40318007107040700712500294150f0701e0b8045000c001c440c0e030008503040324a9038040d4468070303403400040003c100340b0036428041c0c0d03400d1204111190000d00d800d081200c1d8600000700340c64003079041d80030396803961104101802580c103036001e100c0105108100100c10544070740c0c0c107802e003540070f04c42c001032103074603100040c80d4040d001600341e801c0643d06074031000f071441c1d82c450304000c90310440081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 913834064 1250 913832814 913832819
    0x1030b191703040f0e28052a190c080d02042409091e090503041a030603060c0304150e0102070303061203090b0c07260d08091c0e061b1006 61
    0x88000000a010350303942e201c080008624886403240a02914241da07061b01c032098599640d0410081c00b084814031108a2140c421405019481d10740100b070600d80d07030a140c03420951003650709140d817080c00c41c502044412241030300450902c401900340c00240703000150342c0368a4a030214000d40200203081e241c0c000c070150071240480e080380c549400c9603454034000ca060380450010f440c001240e0000d00c110303281401400320030008040014029101042e030120b80c1ca9098680002c4140030031500b1719016803244010462020950002c0c0d5402031040301b09200802041d001402603c0700015030034200d03074000c599007040541500402d00030741030241025110b0310050301c0c001d048484500c612000043c0020f02c0040413103080c817034000a490246036074207181091807001003010350a81c0c401031090040320781903082c2034802c0d04414050664079009010b0380800a03036450041d100100d40f44e00380300c001d1560b145035032190005040442c0340c0d0020886d042400410160900d00d408820242884c0351a005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 913835314 1250 913834064 913834079
    0x14030a09030905031c2d211505090606070c080d120c0e131808120a09080706050712050106110601290c0a08041e0e0f070c0201030b19170304 62
    0x20b604035400c03075250206a000010700c0c0920440c080061aa1b881d00034212132130312450708a46000080c030003c220031008280903030005401c6032803d101b014850703450740104100c07620304801c14a030010002802d080c64145299101302c607025103984404030b00d07004940756040d03468000340701800d40c20444000f4005850f154400810044013412000d106500001c0c0c1146074a01c0c50703010341c0520b4161300c8100d1071980d00d400c0c0091150407031f42480111001500000d100364659004014800d5484900582040e906603603040140400804c000d0410862070b03130f20180e241450180500810150b210000b161001400d2030342401700c1600402802c12403c013602c00811f58611009400c070302c90340001516504102403607418890300c448007030030200c1d0120300455002081c1c0f030400c004412202c41641142e03070b02c5154071109541110400c82d07501061002442141c012141c40c00c0b110310500d4001511740440c0f0000d24400980081e4203082034200e581440220741a5880050030200200114140f525000303c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 913836564 1250 913835314 913835353
    0x602010b0904140a02100e040f0e03270402040312020f1c0c020105041503060f0e0c03060d0f061406010207060905060f0a0203190c02010e010c030804110114030a0903090503 76
    0x1c003c100c50700e00a0f00c84410314040c0704080d04541e0040605102d40c102e400020083c00100d2111440780e450041d40004007409486020545811280a1030070b00b42d106500d2030000109540d1410100b52404072144030765203d2005001540c8116040c2d021980b450400070700d0010303411102c0c2810380c020341c1c2c00040450801900111a2481c0c0fa0a21105807903200484c0c09005070f512800300b00701c3c2c1c00c0c50200940d07050f400c058141c404249850700d001d03030fa40a01c0143d904087d074401e0011841000411418240074040c141424020300038160181005e42e607510403a4112151050003c031540306216542d030b41440404000e0149182c100c958500300800240d26101c4c40e084003080b4a0001101e0702d07418001c0c0140c441015258445200e10b041c0e81402900c0c20104c0783d4203d0000d2101c02d102c1c150307903004450505407142c043e9580007580c1c0d0b803551922107050480c80d83e18144070354100e070454814403e0008500c035407440c44020030b4140d5507140152008a154100600c25000320425006020f800354 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 913837814 1250 913836564 913836571
    0x11070b0114011101050129040b03060d0c051f09090209010815010c12020a05011407052d040f09060503071211010c080c0105071d01090308092e0201060602010b09 71
    0x1c2070301122400c00103882082c4442000403040d424040001403003d20844800000d00c00443d8042e034440010300302d01c07968880c6008070a02072400b03002280f02c41c10708401d036880103845070b4501d8000c1034484000034144e2255001865030841c1504400090320f501441b0ba60040406d140203604002d884000079040d284000c011340884190810001408e078860004000340903013203ca04070f4070240000009442d0144014107a0707032982400198105484001c034500c0c0305202580d9024100f412604d03008030307041102e500c0c0c01d082c50142c6854160381c0814400500050010300358181629203014903000070b4640f80d9000e01e2107500172040c100400700441c40e24882a91348000c034440350400290050b20703d00c20b20303000504110008a13401001d0401540300602030083d42c1c803000c001c1d4280c90940f24002200c4d808841c00202410403c00029003040c0160104c41c8004051103290400070700b0000948141806089007502145110001190280f15000142031144000d00c4032884c04008031310848000b6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 913839064 1250 913837814 913837829
    0x71104110c10200f21070f050a21021c02040e0408031003061a0f03073f050705010809150f07120906061d0103022404031506030611070b01 61
    0x12440c00c1d44101d20240044805120000750302e8444d50301460460083c0c10a25140c07811000307209440c00020300550340320348104010340e6000c4801c1711260086400307400800d881030a00040300518801d80304105c2c400104040c00c0c050043e200c0070404900401041082814903007248100004e010403070181500b0b0760301c280c1003011075644ea100c01000c2c6024228560018014030f10f400130181c0f0250440c92648a036a030b00311419a8003d010000b05502c0e10024843c05c0e0700091489040d205c9008412462060701a02c4000e01c3d6100b81c072998001111200c000e800c0345c40b0303042280b00380255070300314201e65000710402c802041c5032903213440150748440c4040c0150690403100000500503070300c205014840b06140300b105001151042c54a4405004940550415036032091025100303c060000c0090403a0340041c16a09410031036440070114180c2c2e020302e0045030a04100200c080344075442e0385000c0c5012658002009443e5041c90400c03134211107283c895640040202001150750f1070b8859065681d00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 913840314 1250 913839064 913839071
    0xb1806070302150108030406030e2e020405120a0b0f0903030a02070212100605090108010b0915310b0103020a170a0b1306030b06040209060403030c110402071104110c10 74
    0x1d0074164a400d40c070b042d43c0115000e04800120300650007101510841c2d80315242404100f00310540c0e43d03200c29204082125081c014a202040d000c0401100c402c1d0001c0002c00601e0305480c2d5011614902001c0f1540c3c0c0c0c40c0e0310840060080245000d02d144e8004001d8440c01800d00f00720155070345921010b4420004150081221419540d86c1041c40401050381303000c031001403006560754000f9020500c90148542c8a0000001340c960041c051007a2042009002c2c54160f501c14131075111003d0900035140e0011918080e40e000e04541e641c0315401e041110040140f0b0030b90340c003404400d460100382d11904150042c0700c1203400a402070040000b4076031034a0140284e96420100320020000381c100c0c90b0384a800b403c003d5044a50701e45c01002940c0c0100144429a07582c2428441079104503211281c00c52020881040880e01c1180e0070105a44241d295075200620340002505980180006490302e4800b00184049031407d889001c1a01c50305e82035560418995140d42516060711884000c0399030b44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 913841564 1250 913840314 913840327
    0x20a1101121a150306030706030e0705120f010c0e09010b0d150b072604051302040b0a351b0405100503010e311e0b100b1806 55
    0x110001441e019000004120035100070089504000c120025940580341000208158100702c00841c0d02c54400a402030104905c0d000c400c60060222a14000450261600c0807c6903030b10b00031f2101040b90003a0060064040d81d2881c5e500712609400d05006103c100c03035000100ba1170f9601c0c0141150100c4e400780340c450808135038840103440108501c84e008201c912002c01c1105082e0003070b003401c5000342c0c0c1e91400515460b482410b550044040c0c06032055060000b0400b03403415000070f41544001036005801c0c2540c42040c822a0b8012980100103e400021178214100101e5810a090340c140c3c80241c60241d02000d004444a0000d80140c0e4103042c02c0c048042024a0241140c00420001d40204456031000c140180146c01c02e015610103040101c0102c0c0d100d0300d54003c034042c0300c200c8281d0048820750aa184c581c082e4003580c0c1c2160141e2070007260030404d184142c250350600c1d001e4130806c0040d10300045800c400c103030103070070825480800740f011048601c800d0705001102e1038140c941554900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 913842814 1250 913841564 913841567
    0xc080a02150106110106080f0703021012140f060d0308060103050a09020a0905090c0607051b13050a06050f0d050a0b100e070306050112020a020d03050c040f030302011b0807020a1101 80
    0xc11040d10030700810030150000030115801041a001200a64001c00c14951580070300c42d10350206c6411039009a0180d0001d001526001280d4805418207090035482c0c03030300003403101045d80c0c2030280389410305c0c40319010410782c0300c0c2031401a94031400c02c0350500c4d0032003800c2da40078005890240c01c880c10180e40d80300040c03503202c169002401543d0000d00300c8422562f1890400301074036048550b2000b6001d0784145490504048040c4e840c402c0e80724001e00007001000400310301d400c0c100343d8502d40c0000500d48410712681984a542c6c0038261298000c203890b801c000a0042c00c20f000040c0030701a480800102010580204110015950100c0e84401e50b0300c0d0741d0642c14036814241c0201468412090034008100d81551246084400a8840091000b802d511201c124042c110000c1e000d600b1501c107002031644290700440e0300a10056000d4113082d120110350f08440c40740d400480160f075465107001d103145143e2017090710754200e03450102800c5c5041c96009407150031118009240c50122001c54045030f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 913844064 1250 913842814 913842823
    0x1d041b05040207080d150803030730020a030b060a050d0b12010e0a0c051f1b06020a0e0a1a04030b0a0e0a0309030213090308070e060f13030c0905070c080a02 69
    0x300340c018025501c0c0c0541d810b00c88a26800155185011131414010901c00c10b01e215500301200d0400002e182156a00e5074252002c10850940310500340d01c0440411280c42800c40c0c1081d000d4941100607125243c2d004050121000100b465101e0081488582e0003a64000d080394000030b500d0324003080000756400412203440c0700d03540341c107040c1d400e103400e10141c90000220001018000c061001215646200380611076132402c81084031004c040188a4205000b80c03500241c0d0000588031481d0031125480780c10898002180420004038442c003107206c5480c1c00186140a005a08804190421108041202803040d440024442d881070800640103051a43c0034038071440f00e240994034840018034000308118074a0108038425401c0c0b220500f40ba480900c500110343c0d0b8140c0b511441c0e07484002c0151030040d551401c841e4445c404100c000c0030300503410041c1840c804610041c840703440c250301d41119400046e4100c04601c0d4504020070030803640c000348095032150032a60480c3c5c0c0f00d0a10400b06c0c2072 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 913845314 1250 913844064 913844069
    0x6090d080d0905060a14150d0b0103141204180b0a2403050106020a02181305071707061106130227061906021e03220f1d041b 55
    0x10a400800d104040821540020010912440944000d640da0b1a2117808a48004030311603010700709200010b00002c0e154840041a450042103080700021598404001c100242c10440e42c41200031000c0c001d0500401a9200010f10150420305080c28800030300c9825074580b10502c200342d140c404846064a4403d482c130b02802819041e0f20044417000c1c018042d50f403201c04903500003483c01c40000b40d040c1c8080b4803000800c0e402001100c0c051a071001c40c0b80300d1030002d0043c0000c08024507824000480030041d840044c07a0103100c2175101c0d480318058904040a070340c490002d010070740c544444c1010002ca012648690300c4c01000c010012a070020800c040c034500305501100840303070103a190105645030f440740b0400d021103500b0030f03504c403015200c820301070036108010159100c2c5850901015040c4c640c407500c0d00d2103d088a0502103200344054204507081c11685100f45189024090311980c02c01140190088001c83c0d1549280e1150000641400510190840c2c03548071880032074a0250038003900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 913846564 1250 913845314 913845323
    0x270a0b22060e01090e060f011d0417180f03030316050f090a090b0a14061e190f081e131407060201061403120301061d0a0e071d03030906090d 62
    0x2035038444035072000401c40171040d1145841600e001550054101c680305068070142c80d00e2000c424016032442980800203407045880d05011b15980d8200400324020b820000000400c183c03142010740d040c072622070000585a8000d4004000300b05004c540740f4004101d614007450101d0b07503014080080f54007030103650b0700700350f0081030003000041c0c20f04075170011030003a08100c0e406450310b603540034800c500f01c100181050300520148a1198040300364000d070000b144164400714070703061001c511600d2100c10602c40c50301092085440d41d00d15644280b415503c8100301442d000313000102d4500382c6030010300402030401c0c4016180305004211503426070131042c4003d0000c9807819a2911000380c00780c07100340101c03017100000c4140203c2516000400c074003440c51540c01546141d003808021640340304c1440c4480320b0441c40030b221204545511075000002d09081c0f110044504142100625145941d120511042c0c000398194009030b03030100456280c450120386035959031660f00c02090050000c004041e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 913847814 1250 913846564 913846589
    0x21011010e160612091110180806160e0906040e0f010c050c0c0118050108270c12010207050c010e01110303090c04140903040902070809270a0b2206 65
    0x44016a00700c8825043c0d94680c0c039003941d112812040caa08860b101500a00420f0070346040d01203a0402c404042804c11452500c40000d5401003100c0068050650081c1083d42c00070342001800110385050f159100c1d880d00d40392801c0603a21b00080c0e00d08038013400c00c80c0303d07030796498012144080030449002d00c4640000203111f58252100d0142140e0807a2025082501600d61a401c0d076622606802c8580700c69103268420041c01e110044445004c014440c0182d48d400c0515101035400222105078003039407120040c070103141c0c24024094071003518103003e2910381c0180001400110045404d41c0251828600399230740740b2900c40121161000e001c43d00032a400008140041d128012038038070a4402e00791001d01c5140134444000d00407000488680405400074030090080d4079841d00203001003801541d00508105076480012180c5c001e001d00c8051084c10410401000700092890a90207030304450200500081c0401003610107a174110440d5a141c10b6001400c07042046500200242c00440729a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 913848920 1106 913847814 913847833
    0x3050a120309151506030501050d0627030e03150702070b030714040801050609010e01060504030f0507090e0312011a0f0a0e06031f08030403021011010e 67
    0x160400da210260700c000f2a1072142c1c031088200c0c05040c0050f50800030340c43c080c02111280e00140615040c40e004020a40d1340740704c0540d00da50040c83c082280702c400c40450001415034060104924031501c992010f0507072010041103e410300b40c048035008900d42d4a43c034140e0b0001c4481a006034440da00074850554000091508116a4104440c031018140d8141e805504990801c1c0801d80d911400c02c011452300d00480780c014400000e66441c107504080c2c0040a40c81180409441c00b82551b104104009c03042000340002c218501d010805410003d528588035448044040750006418001003424240000c0141c119000c4564840c1303406c03019618084039801000c2d10303070700740800c02c0003c00103074031040000d5202d181510254454054a210110800001c6400240041d4002d01080c0010b85482c0c9140d110f86140d824220350720215401003501400c40314112425501070301001 = true := by decide +kernel

theorem cover : BRFrame.Cov 913669064 913848920 := by
  have h0 := BRFrame.cov_init 913669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 913669064 ≤ n) (h2 : n < 913848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
