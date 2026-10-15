-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5102
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:45:18.905436+00:00
-- url     : https://prove2.me/submissions/62dc7f98-f079-49a8-90dc-3d6a264a296a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 917446043 ≤ n < 917625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 917447293 1250 917446043 917446069
    0x140a0b1309060204050301050414210421081c18081207120216110315191404060b011803020a05060703050d2d0b06180310091a0105040506 61
    0x4000441040c1d070318003031000c1d114076807100c1d0b819800d1009000034844c0c40d01c0c6880c14031248a08548400031a000c40e10450202d0300e21101031a0300078001003084c200101c920340b512102d03940c002c8040728010340ea001010b4100c00c0c1d0039450b5a501445246000b403942c0705001c0800d40ca2400c1d0001c50250b40e8039400140306010f20980b449031060081150180110098030042c1105107081d07494541c40c0040520440d41d4132015100119401c1413540d480c20080381b9480548a400402040c6603107042c0007254004d0410001c506969542c0303002644030aa180c00303036000b54418200031070b624603040001890b50480b9840e5040342001c3c0c1d00c04100581d500b0503c0d000b1548143c031456141c112506003540c0e14000d0b0368411580c3c50400e07c44181084000d211400412860000c045000c10860294400c40c4e41c841185900000100541359440c296100b01e40c071903803c0202102c6001030300c81d0200c41035540a1504503002d4080307412540035011381d001351b2405040300755010050780c81d05000140c3c40c00c011790 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 917448543 1250 917447293 917447329
    0x5070311250302030409050c130b0a2a05160f0b160b0c07061503060c020318060306120d020d02010b0609030a0b22080903010608150703050c0418140a0b 67
    0x100900b054024425100140505001004240b40c03640c01c00e0050b81c401041b225414840c0ca001082646e5640300340c035401000c6170348201c1070040c501c3d8400c030000c900040c5040741100a00e18840003a40800074403911a4084004400c034525005184042c2803103600418109202885903181207003e20080803401504003079004a01d07151403040c111107119000f03000c2d00443c240f80c0c1048485142c01c41e0841203a00c030340d10400007142400d004070780b24028030500c0d0950151207400300709145400b2019641210000b030520241d01d1071016110318198612103640003503041400c0c40c854160b0207210f031006c00c1c0f1056480500d08094000001d80796162210024004940100400c403018101c801f980d08111212031518010f02160620840503080415003071b01c2513003400f03400710740b050001c10020301c20440c540c0200140e0322100c02c140d016200050100e0402c00060100041046680c10104101c2d503001b42e0005620740c01000312031781c00400a054401c1c090525280c0c4000342ca4525140603a00440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 917449793 1250 917448543 917448607
    0x4051c1703070509370b0a030e0309060c07060f080f061e040e07030b0901020408060402060315270f061f020118030305011701090302031b0a05060a05070311 69
    0x21905640f180102c00840f60003c004220400303514410f011040c088140d1142c0404411800300c00c000340080032801580c0301628180100014a03000781c01006005251809072030800a0341d101003165900005c081038880c0d404550300b0804140c00c1000c60789440345d1860711043c185001a802c0d0188a8080c040c140115111405000c0b0706a2058900140900092050102c950392244296a401c0c550209a80c04045076003c26500a014800c65007140d0429014055075aa15001c100d080e4000a0a801d03150701100301e0800e50381d96102c1c11000c2040c2c01854411210b0120004011480c00108100c01e4603d00e0010702179503540f0030800301c480c0d001d0f480c11011000c0c01740c40d01300e0141c164a01c03087c070360701a1801da0100305a05034104506990702e8a810744011104103800c58240c1e50107540140c00340c2c2042000c1a42407038044190705004000c01c0440e510f1810650740c4515216084518442a41e641c800b070200e655458010240307180d02405009050002c0d48402c405074501c4060640104501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 917451043 1250 917449793 917449801
    0x7020303120c0d0903030209120718090309030515041e0209161205010e09160e0103020607060e0f0a0302190209010e0a0e03030c0703030f0614100e120304051c1703 72
    0x107100222100f8444001050003500c000d442c000d00650003200300c4a1003450340ea480c0c04c034441400034010b01101c0203010701c0301030805290b4022005000215095040051a901c003001280e4104075409040040041350356081c5454140f40e04582480108c144a000100c03000101581e04c40d0182600030006840c00840b1541503030b0b090707407640c4116110785e400701d00700800020410f03100510540b0a140c580180c444002121107541c0c15110240622010340b551480144050300b407000141454034030030000007034403403082c2280174545002070412940d00d5105114070ba0806506000c0415103601070043c0c540720030140d40c0096850308050080c0c0d0400804e10000400060031030700040302896000095075980d0814402d100c145610040064021131305002c941860b0680b50300c00c0001b160310300b201c1c03401c3d4010b0020802c40544608400c2d04100182101c607010180d030b856900c0300510013507100444d981c80c9004140050441147c0c0e501244400100b001800300d9005c81c4089034030f803800b8007442d40d250342d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 917452293 1250 917451043 917451061
    0x606010e030c04240f03120f05120f06120c1302070602070c0e100807140f0d170d0b03010c0f050a1809061d01050a23090c120c0702030312 61
    0x400b4001990300038104603010103480c032498440001d038900002c00c1888a0744460007030004a03420b110080003c003001103000d5000d0b10510140149a0407031074500c2ca025503945684602007410303902641e03c0e451500901c05503181c1108603221526420000d0040510b6a90014120f4007a019098504507000110303241040369540c11a01301561116a809146807034041804140350708036840c800c406190080443c1c1004000303607410884020990f42c85e40001c02d401400f0a0b040d0580c045500610007084542c00500e0411400c00da682e0400709450f101c6842200c11000d9070b80346540e05010303914028101d03080a40c026508801d02d802402d10076610992441c0440c0c41c00481c14106036030380340080c03002c41c4803030080e0424022100c007507000151101500c07020158a40080c0b0334140d200c0c1c4412400c00c0a903100500080c00014141041ca40c0d80c0303c0900413407441c076030807202000d14400000341003080340154480340c2d4110940741886802c100156004c26600c0c840c29800449804003200042c0101c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 917453543 1250 917452293 917452303
    0xc1e0501032003011514040605190905031e0a060f0f150b03014505010e1e0903430c0b030a020c010e0d0e01020f030403140705030f0a03020c120606010e03 68
    0x40d081ca07146d07942c0d6a070b50302c100074000d40014258981100040d0350703151030b492141504a0686800401a080445e0200061166151404c2140d425801035419890110f903940c419078a0403004d0100110751958a2044401103880f070b00c403a02007410b5502424807819001c441540d041d07030b0504070508006c45c1c0640142c440040034a200748540030203400e4101c80c040614030501040881d020080c8a45d0740c032801c401d56103840031600b1110340002483d1a40905004185440d001140201034a2806406140100a0240c00c9002da000801441039180c0417414030104040500e8410a00944284840d55030840724499842810100c5c6404004603d0074a00c65040381d24448408008000351b400c00d91005d5107441160141101040d40304401521035400030030441c24000e020005145000e00b10b40c0da54151500080e2490034500c1100d40100f06500d04000c00400c21442000629018825241c001c4c82e1640b11195a402290007407000f0010306800520f60760070031000d0810100c07004441021910700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 917454793 1250 917453543 917453567
    0xf02060d020405150702010203090f040204120b1603050f0c0d060b0a110c041802060304060902030f100e0d0c0f02010c0611120a0c02190c1e05010320030115 69
    0x44001440069031003590780207004807542a101c002071490304407034400e15401008000382c0503030030401098007203140c0220081c1c1105d1000b880107080c00d481d10720141440495100845003010380209005d03400f682c0c05400c9801c2106d1303242c144291301d4541100c000181c409424864200d1001c6014030b002a99900108054400520160b445100c0780b40014000c44401d0840410741c042c10441032141c0c1001c1c010310946d00c60700c4000c43c8008032070394248001c5900040003554550380e22645800161740c140803030b42e2039284000040c100714808200e640100d40102c488051a58010b045005051f6040b240c0d003080c464105000420400f000c3c00103a0340d03107800350401004a880c103050148072103a940068440b415903a0200c0c54a5519150707000308903400170800401581c08010303d00c0841041005d5400c00510441c188020700c0d90b1551400340800380d500013004011542602849a0350b414840d68100e03103190980f0410981d4900341240c12413006000700c80b916481c100300700d0074440c001c011003620 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 917456043 1250 917454793 917454799
    0xc0a05031f060b1305010e09061e030703050706055409070f09050105040e011502100e0a1712070f02010e0a0804030204050106180905071b0b09100905070b03040f02 72
    0x11359129000001c00a01060007810f0201e5910314140d9510300344011924400c06003d04911103070a081a1404c40035038800d604658140703d110404130001d80c007841004018a2182c0b41c3d503440b18101000c590810401c0a8032000000c540c0407680504810340361201c100007440401828a152440240114044054042a0005542001d10052580c03103101e019251002d40d503411031054039500112503034881d5200e491260360364440140300d155240d41c88440031412070300484440c5440072050001b601c50380e003501130454114001035000d01014800c0f580340d00c41062200c91801d90002c3d4012810301c009081e1108224540030144004c90003540030400c80d0b03641d403040300d00e40e00c11807501c100b2660060104038001c504250000400f1070007000c0e52104070184c20b04000605041428072802043c0041c001420043d44200e039890490007076400004180c014000c8400c540f801d42c117040d24248084c0c051401551404a00c030001c03c1c3c0118811040d651a505056943d4549082109000c40c4020000e98 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 917457293 1250 917456043 917456047
    0xc0d1107020d110a080f06190902090705070b13051c112b030510031104020904050a02030f010e07200a0209101503480f020c0a05031f060b 61
    0x82400494a1020f551550480b0107031091515161000d440d10080b141400e0580c1c800000300b215a07554540141030120880340000b03059030b007900080c900b40340c10340300704010a00026a24050000744c000e41c0d644071080d04842d5130041626552140e03100444002c009143c0b11625950b500c0c02d10800603c3c01805000c011030324082c41700025440002070001ea001035070312400500000060082c06020301c80c1401c0905d2000452568941080030250b010f502a809a401c1010203036030354540c401c04d40101c0c0410001602c0707242c000225200c03007006070008207420300160304005050358044500c00120380f140301c1d15044511480b04580c903005042400a5005200303c0c00c010200348000909001c035103001e8000c07030702c1c030310028402d804031180d91004161040780300c4854030004e403040391442c03040c00d0a84901210701615010304a082c0320705540c44000118106030740c46c00584d040000203140d1000b00c60b100450b42c68880001c2d074500045007074840030341003c4416903402c1c003107034404402490b01003015a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 917458543 1250 917457293 917457319
    0xf020405090f0c040b01091a1207170622180f030309050607141206030313321003180f03030c0f0201050417030a06050312071a0c0d110702 61
    0x80e4a0710842d064180203407181e80c862122502d090b009200d410030b0180c41c0c4443c180d04000205c40c0c2c039541c00b5400e0f0071001c410860191002d40035102c642c4588103564603021191100f002049212102170584da20504503210507408040d4101099240503000c040009140cbc4038030707001041950048100034241c0c01c46010140e0a058040e00400d244c2441001514030036590705006907140305034a1101d40c4c084c00c041c030020044d0f620415800fa04824001d007201d040540c0f02480034464001500070204410400a5140c145034011100385090250b9001d0701808100080200e081c411380d550f024410907445900301d82004000250b080c3c074840d0007050244a00e2220304014020f403d05400b1900014800c8114102c0e845c03040c4112400f40c3d078448861001d0b8214910720707200039040a03011111203a610310001071169420401034140b540040c001c9a11504235041a8003841148071216103c0c081c0e40040029207451841100d50f0b4103080880068031010550502942d4080e481000b500440100d401c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 917459793 1250 917458543 917458561
    0x10021b0a0804050f06030702120d09150e0601080102160b040c361a01030905070506040e060306090d020706051e07030314220b0414012910050f070f020405 68
    0x2402914030584e20040e11514990074031800d844103e40d0341340140c221502d02d0140503900d10040107074410000e40440d10034200c1e20381408034854036034820317401345e40d40c3c20320003200350184800341c01420302070300131414034440d01f03510801941c1c405070081c409240d9030000b41c10010700c0e0754a480604403500a00d4107500e500c0804400d80000300ba40d81e06024031081d40e8030b18002c4280501603c1c5640c00658030300c83c600cc1001540613040303c150858503800b90030004141038889001030001480c0c00350207100181414000e1504001d00070301003030881d40000b5850180c2d0f40e00020008211141464401d68444550007251a107001c1c41e49140307540d4200050b07920526504d60402c846031183c00d01d25428940340c2006403845001280d14040306102e0300550507010400c040211035005020700301201e003034501c00c2030f101c3c21942e0b4009807000707825419003400d42c44580030703054100741034081e501e0040000070000b010700360307004403c807045800b000020300104100040c0c0b40d45580b164080c0c0103000b00d043c45009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 917461043 1250 917459793 917459797
    0x30212070f083007060b150c010b0f0d2301020409020703050309010b090405060705091203031f06020609120702120d05040617040b071b0f050706030e010e10021b0a08 73
    0x3c41040c41040c40035240d5180040c0c11030b029210481d240c1d2850800c041d51518080c000301019540d000d120620228800752502005020b0247d80800020385540001c08004003a400c940d01f040c00744040c8007000740000c40c12003600c40c6089450103031038840d0030703c0e103486400792069030003e0109070300200c1d8641c101078010001d1809812000020301001c50424140300615208680c0940030707501981c00300e412140201c0007441e0004010f0508403001407448c011524561040c1c485240b8440d0705400c020581100a24000103082d40e48050102030a021050300d0f80c0d400220710590440b5800500c11046645410103c0080202101a00d000c030b80a040081c1041d04148a40710108502d156501c1c170503c07174004954801c541c17100c401813407501c48109c11a042c0c441d084a250009026220220120303803041c0000d40d2040c41040200310050400c9001030030b5802c44044500141c0c14803101c0d50769558049040c02c1104c0c01c015006840300070800038400d803103081960800e0b01d4010710041505210f50480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 917462293 1250 917461043 917461063
    0xa030801060e0904110411070b090c120a052a04050412081503060a0c09030b04060e0c09250504171624050f1e03070315060504030212070f08 62
    0x203540d03180242e1003091042c0c424003240d00800c05040c900044809180c1a44626981c040075421a070602c0c51680d508038440d8015191109282e111040801c00303460949016000c4145c2d01000d001d0484140e40c440350740d200f501c003102147d0301c4c200382c0f0f01c5c3d408000903001d58500c803001801030000e800c00d4181070031400703004650000003070501d40020340140f0300b485866400d4070000d4000c0c069982c036040d04800a2001d04403030010010700010001c085200c030210b41e402140924000240c8040900040385000c3c481107003940078010b81e5040043c4030760710740030081041c51101d07910b285140002c0411207041c4101d0304240c0019685640c848040f502c00641803c03c84c1000704181505a11000c045d600b28103a2018035001c8124001c0c01c811681c03103540544050000102e08608044802c40200201c5900d648043c07104403000c010030803425810300611102d07040e40d0320038841050404c0302c006c2c014400d90001074001d000c40004c1ca1400740701084040010402e941500c0b4080340c030344400f5904d50394081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 917463543 1250 917462293 917462297
    0x25030206100503030f3a05060405060901060c05010b10021f05041e031404030614130201050a0311090910031407081e01090506010b210c0a0810080a03080106 69
    0x80300280703920034110200300c01c1d03840090085041c10090400710f40386500c104a00c040b0a1502d403424950400b500480107000c5c80c429054010f0541d01c019518121100200304520440c01c0070113008040e201c810354641502c00e0fa107809001482c65040c00390240081aa0580c1c02c000d40804406640c1e501080c43c2e0341545842da2005000c840314108030341610300584010342003140340c0c00105400911100410310181c1309081045100050202c00c008503001940240c905684898071980108200166168007152241040341d0100868000800300d0050354030f24070a142d901c040b50360302644420181c4030b8800c1f005040c503500385064400e50b50f1020300d52204580c04c140c881d00e20038566002207224000d4840b540002c0000f11224007600040d40020511a07429550360140440440d1052280074060030000f030685903216086071510001c0710446d52070032403c0204606111141c10540219901d4103528646140117840b0107600c0d104440c282e501484030362098030040020941c003d003042d4100c0c0c4461b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 917464793 1250 917463543 917463553
    0x904050d12051014030a0b040501050a060501170f13080309030d0b2e0909051006090f0810021b03030f060405010608090c0d1b0b040e0a020403031205060105250302 72
    0x10001d40d2098950695401d610141020030500c103440c035105140300c040c0e0b00201219141c040c0d80d12048940e510907507050710740c1d035110780422210740954022400140001c1c64103116291001c210600500b0340a41141e044102c4580802c100790401e180030010250885a8582d1742e041c00031030141d40754441595038030a281012024801d51416195886c100140000413402080d1a180e0513600b03403484051003014054464000315107450075100b01c1d440b9100341a0034000716400d01300003402020f030503407181c801c92131a02814010280c010031080c6040101c4000540c40340c2c036a929202128903c4005411544004020058600c0c03002a500780100c2090b01d040050f031340c807503100b11986682200e0904441d8009001d0f8481e508203400d140d00c0241c05902401c0303e05500c00c00345441034400d6408000251404038060103280c00010489070041d5003c0d404601d001d00d0750f500030340b00071551316910403610350380c00000e00c499000c1c004486640c244008080b030326202e404100d550800250301c00f68014418 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 917466043 1250 917464793 917464817
    0x1605030111030c0315011b23010c170907030b09061503061b07022d040e0c030c1c12030509060709030512161712070318030809010b0904050d 62
    0x31001c0b80c0c000c0c501e81850b83c2c90341e07451100703401c00002d4544185041010740300c4441c0d803010303a041707501d42041c2c407848a802003d8a8114200c40f209501c00b001c8030300364508001048200d07005060000103c0040340c030351032a940c0d407002d01800c0403050350014103001c40c041c040055811004c602e0074859400f038101d40b080c294400e000d00d40d854400b1503030140e0340044013042107180d203180000750100a1000b8000d084c0c0c20045a858200031200c0b0000b203500000b40c61981e42d60380380a024952004645000406000269400081e500d8030b0b5000414003944000080013081d0240000807503080d60841021400f01117910f1000b070040208803a00c0d81d142c002e050100d458036204000040403650410020711005002100d504266403103810080d00a1600c46132000000f544601d81341030101895030190349031103e4105000f074005004082c0c40030540741201c14040e51500c034951003052501850710302c1d0259074a000050045c001e4510007a800020003041208000d40000c1d0b80340440d04a58444408601e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 917467293 1250 917466043 917466071
    0x3021b0a050606042a030209030d02030702030a120903050105070905120607091a07021816020a030f030c0905210f12120405011b03091106192016050301 67
    0x640300004155810580110300b03241303030030b40041402122480030034142c09144224005080079039207041e00030a4010403c8483c0e480c0c1402311683c009036600184d4a0110194000798407140755140043c0050040303104091018411003a2002950b4001c008211605010b070000e090707200207126140c0f0602c20307450f1400d040f80d008202140130f81d502d46c5410300c0a5092006203d424020706585907141c081c20712050f00540c0e58a2600c40940d1242d414a01c0103081c0756104909070794070420350005650024401100080d80100c1c0710301001c00c2c0345400541032039690390860341001c0c1e613841a42e0001c500c0c4e2401c1828000001d0002005403603408139000700c00c07624160b940360308200d0366001c0c100c00180003000518048800b5154420303c100000519450358030044640000001c010100080c1c1c1d4a0005c2e007000802c482c2032491260894416080206445000303040d00042d00d0460f0801007000c00714540518851800c40d141c900c00c0301070360403400c81c94503548105942e501c00c9500c03070760811016a075144 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 917468543 1250 917467293 917467303
    0xa1d01050a0e090714040306050a0e0c090408090f09250912080f0f07080c0709050c03130c05031c080604020301050d0201050a140706020301150f050d1505040c03021b 73
    0x142064451410002c260010070205042c01010718003808025907800030102480c2e0014070140d03224100010703103802c1801014040324040d44568409622614081c90f41da92034001003a07100307600c442d100d5075540880000c10188090b40301c0c1e858002c00007034180583d003c00e8484809240301c01585030420718944210031501298148200709085503101c809402084a4800070940300240750a820301d8090750040c85640d0f9409160103845042011980c0f010301401403050a0040c440110148001e04000bc5601190700c03001c3d00200e14544180016020024022545801000024180d825030310075160205001c40000001c0b400040e41140054020f00c1e2500c2968180c841c094120040148030b503005454030745c410300ca21b006200c2802940d002d80c0400c4401800301600c00d0401607101d516025003c650302c0c961242c000c0c14810070000c040d03071759a40081031ba0074040c681c4078041030701c04c886007445215520581149400038203101c0790112594041d00241030000c050300d4400074400c4044040d64a031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 917469793 1250 917468543 917468557
    0xa021c020c0d080f16020108072a03021e0a050f0111040e040f0c140a080a12081018020702132018061810110a030f0912030207061206031104200a1d0105 67
    0x106c80a000174640c600020496043e048bc03290040350100100741c1c0c422140d610b08241c0004107684044400e40801a0501030783c079060403040024488824179103003501d00b40c0114010704407294859400207003071000002552000541100c6c1e854000d54a403400790b4012006104807500901200400250900c4002001400300da00080000440403000e00700300c0e003001d0007821000070740358001404aa0400780d00c41c031880501d24180010381d2013a1f04d10602c0341800d082d80000403414078148108003170f6101009040d03d890703242000150340d5044005880d40042c59814442d030011404181c1001d4206000e002d4074181404484428080405050850f00520000131034000c03034004106c20710000e0701070002241d491035a8204081c0050b11141422540301d0040300981c01641b150000700556501f0001c00c0180511242050140e103055444c1c58501c0c0d000050400c1c0141d0780e4004825500c00ca43c041c0500106a401045640b06607502000707041140e42000c03400b08800800202e00a980038100b100c00c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 917471043 1250 917469793 917469827
    0xb011d0603011814011e14011b0302010e10090b01140303191713030e01020303070f05090a031a0103110d030801030b090703050d050a021c020c0d080f1602010807 71
    0x7a50707003814510240540064012400c450b00d80c00310460b4032890086880c040c0400c08000c09803106000b040e240c008500768000039011050385419200d03640d201c5542c031500750070301d24654000d8503140ba0490040445a940950714001c102c1c9075070140c80c6a410000150380138440d00c00881c0d880e84580d080d4005c00340d4500b5410780c010407030484d003400040e898108100c4182401d500201d0300501042c140c0340300b195200700700c05180c075904040503002038001860550a02c015400c6103000680a84101000c2c80303100c041c4540030408006682e18900b0b200c020b0341c0d020031041114800300140308a11417003804101c0b000e0b0b100c0484045582084282c2e01440f54142c0e498008607480c54482956004000d840c04009024116012000c10800c02054800074400d580e41e80e40d940d0072110007800c01d030b5800030074808044c013034500084d031581c00209500383c0501190880000409468078082d0781c8a1041040e240741404124200c1a003030b000d0005d804c25000303880e12007003aa6400380c12605d43c0e07007201618203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 917472293 1250 917471043 917471047
    0x813060905030c061c0f14060306071e0536091506190c1220060118050c04090f020304060b22200309060405150103120c0c0b0d0b011d06 60
    0x100e1044c40d00460781501c0000c610004191b54042c01890a6407060075100c2544040d50382880b10034141040701681c44401d07440c2030900400c6003038a16107407006000f540c104001011031140701d0650706204020454021200c5038030102d10340d11301d1240c011402c04c1403030710a91000d00010010440c030490300410f404000c000030300c0c0c4071b11240c0c411109500219050b0401045120f1b41e000280a29034100c5400a03c5e116000201e40340c8062850014070311002d040386e60040070040107540302144925284070b511040114895031240c000c10740350b0041d0b60154481902b4400f4403601e0310410b900a6010301e0040c1e0003404030242c918140b18542042c1d040807540b00e03007003240801c0e5040382540003841d070469220f19440b1140c005803c0c50102c3c1c10907240d84005e5000142400100702042103002c0d11030390010740d000065803445e00d8400f5814060700716103040c0030b0114280300c10061a0038a8201914444140503119403060181d54010028a00302034007040302401c84c0c108100445080092400c4024100c038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 917473543 1250 917472293 917472307
    0xc160303082202010f050f03150a0f120609110604120606092901090f0305030c28060b030c130e0d02010e07050f0409020603070c061107110f0d0813060905030c06 71
    0x1117881170100328400401c00244a007800884035000290301501c5c419001200c081014020040c0c40c9000e80d0040c0034080d000582041601ca00605030b0302e10076041440040d0b83c90150a1106882d492000c0d901c1e84000009408250b0311120a848001c00b4015002005000d0303d6004600072200c1e803110804002500c11880a86031510040100c40e040061600c40b00c01550b50322103100f02d0341c258104640301d0b00041405840d490041104210f103440080f41e448104104000e01c00004106c0103001d8020b135228400e200241d01c040142c4014004050b010503103001c001081038005080c208102d02a602405600c9804a8414080d144954081c1070160010034038000070409000c041c88809900f142c0c03100722950160361044007451082c4400d0301c880001e00f01c523250510856002d1043d400455200b44071440c08544041402c000c2203000399140f5003042c10b0000041c445400ca5403000705104000200d40929100c004842800c60704039889010b4120345960070191502075442540303070400b109006030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 917474793 1250 917473543 917473547
    0x100e04140f0f070303120212010513060e0a02031806070504062a060c12060e0c03041509050f0c0402033105060106090f140906040f020c16030308220201 67
    0x204440c1500c00d801c40c0d64001440c642642000340544030110141c0114608009140d044108080c0101d000c00d004c52816000c5505c51a008406003d2940204500c18100d0901c0c0c1580d4440d40c068810503010302800e181c11a04c1c400070758401c1300c044408200074510001c4114001907140e021384000d0b2a068103045c00c0c200d0485e5442618030410407240c500500011121860441048800380500c1010071860000440909450442c510f00f00d140d52501c1d108010180040f000310360030034a440d650300d98170380700c80c1030501443d41e8610402e8210b519102c800010401c1c00503040407030034019000d80e000340d00c10380200022408116150500020608a01480d00c00081c00844035496510b00c03005100e0569102c0c40d103080002d8011902264071a041480312500348440d80005118a800110711140c001000c030394805006071249000340d8130381000340d00c50300d20b43d0150355407411601c040712078014040c1108080d002c95440150045060240410f98401031940e241c0309007800c00480100800442c6c0c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 917476043 1250 917474793 917474813
    0x270f02031005040b240f4518070308070305071b140423040203070b0d050f011401021917160b06030a03090b1c0f1b0e03121e0403030f08100e04 63
    0x7c40854401c1e02c0d4241200c4403074841485040d16031102d0003050201c040030031400700d064003804040301c800d1004d441b501010000140340c0182c80d84004c00c40d49a00c010301d030a5901e4015030700300505101200884415000301079100004540940504c104071308001020b01003191540300e540310002e11030f01d84507190303030340b160854603040741c4080c0840766401da80d003c803083e1a800c10301490b20704c00e48403000c0c1710300940182052809401c8502d11ba82409591800103507030348204200c502e000740994400e40ac00c3c0400e2058903131018810036100340d65840d002c1d044d003400c082c801d082164100703e100040342c8035050001e1380300c2c81954181c5550106a00f44804003000da0081150401210500d88070b0905912941c00b5140e8a141c4404020481c8040c2c0030085414080310a002400c020306400d00700b0302680c0003e00045190100b003800c0b40da401c1c540840c0c00700c1c0c81c1007a51400741101c0010b0000304069115400b101c601190740c1c0d0310170403500c421001d0041d040a621500200f07003203010200b8080742132898 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 917477293 1250 917476043 917476069
    0x112d0607032304020312070b01060201050105151210090f0b0301060e040f2d0609020f0411030606070507090e030703110f03030105092a03060103270f02031005040b240f 74
    0x842d01060710b91080e00c4500d6001b21f038100c0c0c0410791140100491502402035501401044441c40c1456801e883e03280c0300b44c0140408014105c80032070210350034a030610300310b90180000300f000303000100d80c0100fa0000b07440c0069055000e50301c0c0c500f0006800c80c0c45038200303006683c800c503503040030072058440040150686411400020301003d805102d4080040420b000c10701c91500441c0c03401050041001d004c3c5c1c0c801c2c0c020302640c2444066800315800c002200da00c003104070b070320f991519803070b090052419007a030b080100403070303e400c1c030b404800c801c0080906203c80c402d41e00c030b84181c2d001d80d401c0ca848504400450001d94401e0005014510b010302d119540400007903900001c020f1740c402c1c03010800350b5840c0b5104600c90004103100065a00d40600305602000c003108620301c1602c14410805428040001382071441c41c81c00141c11558240403040d140c2c0c022a60520040c280783c1410910520140c420521584c0181100480c41c842401148688100185954407800303600061040ba00c070109 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 917478543 1250 917477293 917477299
    0x50a09020a230316120302100614010e0603040308180709060b040f08030408100f0e06101e050102070e09030f0f0a030609090203060f04080f0c2a10112d060703230402 73
    0x23040c640b202d40894031905000704140511113000c03089100024240000400407540200800c10400002c2034001f6010f541218801d050f050790b051040e010130b801c059180d00920042400c104e0002124544040a00180c400500410605980e904200d942d00c0c803451242440b1038021030030202501a06601001d0710368204800414481c0030340c1103d5003411021100d1400f0302029003424882c2002d102485001d000318180d0b00748020781000000303552401d5900c00c60181d00030303100020f0030090003071094940c84080041030644891900807500c5141e0000da22002c00a40f60100004000106001d40d202d80303034020340a441a502c5003407643d1812080148140c4541804129590020140b01e00034946015454064007051070201081051025041010719011000071f1100d401a500d40c0b110054414050900c01c00d58485440401e00f00141c51320300c10035142000c105204520580c100b0314a1f00e00304102070f24590b03070720f02c038080c1c080b01c3c3c1200880d0300111070781c44145140c000312a55150458001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 917479793 1250 917478543 917478553
    0x150d11120f1e0a060306140a0c0e0a031104020d050f04140d120b030f070803040302090619061d1009170d08061306081902150f0d050a09020a230316120302 68
    0x5c1d0b2142025101007840c0041c40e400c2e8a0100a01c080d003a1155684a2142c0d1900b0310f050310300c50000800d116031901020340388090826499505a0b035a904480316820071000034400d9241036404042024000c40701518580c82c010488003070345c000031414440401c0d00e0348900342c0c003d0034204480010008540b00d10340610600e0b440712010407040044c2d1b40149582e400540d581c40c1544184a42d541010b09800e005920700c080400158143d08008000d03203105245c44a07000b003004544804114180d0b030b07496007040350045014030b5194043c0400c001d40301e00d80240d100f005c12540344190346035088180b4200023a1010f020952614060242c0c0000c003201e0040841c003e600c811031503040a4024940d40341c0751180c5001d40086080c02d00040c4070003080b00e40e11340d00300a01001000410710840c0c1003a100b481d6110001002e102050b485141e41d550041c00050019443d6000d01095192020b40f1402c048003071040c28944e443d00040100c4020181020030020324600b580044006002c048210254051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 917481043 1250 917479793 917479799
    0xc03020a06080f040f020102160e060f0301021e03100f060e010f08060d0206090301110c06011d010f290307020a03020106080c06070b04030e100201150b120402150d11120f1e0a06 78
    0x160b17840c050040c0c08150072074142b030305104041210072240c0003201402030f4014004410038a1007482941a0031001508060b600d54400c8801740240380560410072500c520302c80702080c03855000709aa80d207808280c0301c03210b40c001401001d07238400307504841c219400014000001c005043ca8400f4001420b400341c000b1a1210b06039400308099040003000c030002d58042001040010106007500f60300c407401403c020080c1d41456124000c1720380038005d08200403094480d40301000100701100c4550f83c1030004058590914840003900e450714184183d0042d820250042045080883d401c1d04140005000c1860000030b6610600361000041c01a8180b003801500c030320850301d803500300c0085901a640005400e00f9081d9100440c940c0303c0e000b00e10f01100a00406d001c1404050455401580468103054401c0510420500511a00c500010424103024402c0c4900b4a2032001e0164035410740011070151b51000b620805040080b41c4407168a4606406042e004c1c101d030001da40c00060311600810704c01d407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 917482293 1250 917481043 917481073
    0xb0109050d0b041101030f0c1112030702210d091a06040501051804052506080a0c050406030e0115060c1a091e011b05031501020606030c0609011b0c03020a06080f040f020102 76
    0xb4032390f00320b0045102800031070b010708020b000030441080340302421401c1d4101081c00070740c1c804900400d03d03c0c007080341c00d03000d580d44031030030985280c02131101062085000c2d52418110380343c0c0101c454070074005204040703011840c1a01490303042c3c520142c8103126031102007001d80c00c14000500300360361500038030114048619844e4110044510740070b0324400398a00e0034034010070302c000043c540752a00d407428402c50b11007540320080f0780032030780d00d0316001c11240d01c41d16101d80108140910018100045807001403855040400190007500800703020001d4450745551225442e000c40f00b1500603003205403500765040c4282030704a200d9140c0f400000b41c041c00c0710705803480204e128104402061012003008a5580c2d17403a01280501002e20240c00c06081040109980361454042c0c688101c0c0d002c10480002e901c41c0003603c5070500f260121900c0003189003130908916040703001c103074042c515603180452868090000640184000342210015542e9070321003002440d0000300890441c0520340c0f006441d50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 917483543 1250 917482293 917482301
    0x20d0b0a0b120d0f2f0106050406140a030212030c0109080304020a060c0c03060c12060914010f0b04030803060a03081801021b010503010b1b07090b0109050d0b041101030f 75
    0x10304030100050224409070030041108540080103607280d22920780c00070700c0c1c3d03404100380d0702c0030000d0300380380e0a08803021000304450010b40940c000c6041c1c24188510021105400100c11210145c4007004100c0c1c031100c550410359034040460b50080e00c1c1d61030410041c20021001e41c00016800c0550b03041030b05010300c0310b0a50b01001002c1c2ca100d00048240810b600c0d0883d060300c000e003c1e9040c0780c810204241d50b030a011742e045110140c10140d90f030000e5408640120742d4511403c2809070100600c43c0c4503a0802c006080f510010780000d4180720004c03501c56101e40e1310300f05607820f41d0764480c1403074655510100a60702c000c10709600503001303440c004000364002014007903540360340d0140c8a0590703504000a10701002c004400e01c04d60003030403200b44640d82210840741542d1070200440c2d03450204050110260f00d005840348894811001300003a00a02c503071041ca04560241e03101030060f40d072002001170a01c100000680101c6525001c43c0c00540350030b9480c90240c0b41814081500c2102c5080c4078121 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 917484793 1250 917483543 917483551
    0x51c020a080d12050f040f06020c07081606050903060a090201050403020d0b0a0c020106050f0613080303070503040b130c060c0f080c030a080903180909070b07030f020f150a09020d0b 80
    0x90ba010081030700c035868011440f028001801e4000f080649444104190060400340000e003d40f40315021070303420b001c296012100011040411960101c0d035504040759112009446145001c0d40124086611849042201c444010050052084d503c2d034901050080061004c00c9051020800c00000140c80c0d4601800d45503000b24040810f600d015406a01511501d0070440112b91610006006541d82d1103130a440116040c0d8100f80ca604188510110781016508001001c1c400442000101a840002903100c0c030b05c106414800c50315403c1440c0d2656207014801040c58000003824060184108484180e107801080c0c0030744d92842d01e4890b09900c1c2e0081000c20300c10341000504840d4a0782003a500c94010090b0401145020070311600c100741d001c0005090351040c208840402e14006003004940d025050410290359903121600e00604041031014000c005030051402c032243e03485010905a40f0064501c8004039103030b07600c1c4d0031100201303505081282d0100c0c015102c000800e105101441c41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 917486043 1250 917484793 917484809
    0x3050607030b100f350109020306010908120901110c090c040501030e12090d020a030602180109080a23010f06080d140c0a0213020702030a0c1401020115051c020a 71
    0x5402d0100081c0114219164450300500225900044503183d0000540d20f4260302c0c1a1415481060b980c1e100055588900e000001100d01100100e400c46840d030086010b140241ca07007022a95945070305540b030b03540101c19800000410311001c5c0d02da501420140340806444010341e41202159400600e100c4016141d110542d0008101440b45503090b100e2a446c011510008005488122140c25400e00c1006101c501400b42d007040c040840d2035005400d0040d580c41203095454211191f0002003414404101e18006a428000060a21404281c0c202c0302e5810520482e201509501c0900406e1030b200640b120645d611250381c2000c040c0d9100f100050115070010b0300342c034030240100414042810b80c114100c810f04010b894540c1600203460002582d040d00c01d4840814001c90300c500a0046440203034050040f80310050070041012510741c113036455440c078000401d03d080c00490886130b84000c6c2e0401c0715000c207401d100e107140c0315010008201440107829110003c03a07003c5090044a94006c5070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 917487293 1250 917486043 917486051
    0x603010e0a0b2d0d02030a11031e07170705090703020705101e0b0a0b0f1207051303030e061225020115050114040317190c0b0a050a0603050105010b2212030809070305060703 76
    0x18084c5401d01603400700b5600010f20b11164001030300cad41901d80036540300b0b06009210740200400e04d0003050003600002d000040c040403040c40d00643c0035010354010007080360369005054940780b582c4494032500c0b07040340090300340100050104c2e100c04000d040f80082c4c01c2d07221515600009880c5004401050310003080040c4c29101e0007810360034004100c000e03000806000040c46200d00e041c0002103403000700c941500e40b102c0e0300c40c6640c0109060b4441c031032440c0c09821813401084a8040d450b00351705004a0718600030505200f140754101c3c2250b40c0c6100d0340c05400d40b02e603410401e9600c01ca01c0240f140c1c244900c003a14281d0b4a66640314090150b41200502c0700700411841d81d48140107900c00401c8400c1e0500ea0b115401943d60b0541c0c40724000c1c2150a85a40d44002c115407000a90001c0040c642c004004c100c59611891140900e401049a80c1104160201c040c07903904000c0e1202c1003118401004040700c0041650151030180000380703100d42c28418288000041002000ba0301c1c0540d1450728005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 917488543 1250 917487293 917487323
    0x402191503140f2503020c060711210315011e020a05120c07090e0f01062403090f0210050f070b010e0702060709050f040b0603010e0a0b2d0d02030a 65
    0x981c000700000c0542582da4018420804e01103e561500e00021000b84003a0203801d640c14401c2c4c0082c010303511408418407401301042072140d00100140390b07241c05c0108a40c000c02c0d5801c3c0e0544a600600d502050000090000c02e000740c040d19000c3c1c41c42581410300da4000c03081d5890703000c0da1501e9040c0460059005100c018140407007030049051414004a0040c40c00e8007415400b40d403080300d071048040c43c9a40d08418042c040b4140b01e07402c2e143c0c03986002030015542c0c80b0002a0083c40c400841d00c0041c085000c0d100303007640688142e00c03606a20169220421149808002014000906100901c1403c00032101c005030840c0041829500c1030746030781070b194145010700c4444140140344270290340c80542882011900301152030100e4004a540111003045100814081c0c00d00031704c41c86e0444408000851711011501d11070b4407415000b40100615010340040117000345000c1150b5011a4081c00014080c091407220070f1183e00e8064401707034080c41c0c246d0110307191200a441c140d50064101c0160 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 917489793 1250 917488543 917488571
    0xe240f0105091305310320100504060606020c0f150f0412151e11090a060806121c0c080702090c0706050a1a060c0703050601080601060314040b0402191503 68
    0x8945001c50002d50503040d017050300c90b10880341041201409004450401d0040410036400744038003e0408416a840300400210280150006550448403541050f1021030164030005540307820000040005c10b10444200a000600a084101c90100171301000b200b440f03515040d00410040044a1580e840604641018407500f15504400c64905003010750031050040d69080020709542d0040c0d0000c2c0131044485562418840c0080f82504800342140000d05a500a05050320a45007076590050f0b815451582c240c903100e6a4083c201d0b0b4450700c0860104091042c200b01c00024800c1000a18148940d0009580da1030b003200c910345064000100c0d10204215070058540146002e00203101c1281c20000c41d15201102c2da40300d42c05120045480f1814501c20003590004582090030340e046561910003654441c1024060b09000c40c0c00e180c2045125412090f8035403185422407013600c0b043e10f440c0e0070800e4405100d0412400d03044074127000300e80010b400e01d501d29083c1140d140090030203520303103034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 917491043 1250 917489793 917489821
    0x2010c0624081009030c060f0b1203090411040303090e070210060f15090503030904020904140f090d05040608060114070b0f010609050405040807062a090e240f0105091305 75
    0x7040c020b5800c043c11300300066005002222510752004001c1141c80001580c0401490040308469103c210318050f141d20b01004401490803182c152014081804040b1002001c1c1c460b6100c01000148001c1e008c1054002c0303442c05a0b000101403040e83c00d45003985c2980015980150445083d03003000c50010065a0410410300d4114951030034003141c128501000a9103034020380140700c0c012500040c5805c03455855138048009020b190035003001505101e4000c1040c8482211081554440d2181a6103114050416a41140c00a0341c0701500d503500c0c0e000455500c0e440d90780029451009005174000240c0801a50303110b041c005420b4041980b40c03040040c011720b5254000c40c02075103060240004a820b0b0340c1160030741d41d000741000c42c1001103448001603c891024030b4203081c040c0c45682d0480c0c41c4d84007281c0c4007158100b601c0c501e002c0d2112480000100300040b02602c1c1080403600014040c02c000e01c42504d08401410454240060480411011410f1201403074140340d6500c2000f41c00012008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 917492293 1250 917491043 917491063
    0x702070906060e0102151315060501091e120212061f090c0c0602180d060c12020a0c0f0303110a050403050f010506060d0b0f0a180e06060d02010c062408 67
    0x34080b84902c42110020f520b030511740000070107400382c040010f50320112505d0007d5a00f68841078803003144000c100d07190001c0203540511f90010751000c0c000910401c03211240c12489008043c400005403420b688503040c42d402c210120381001c0c4a850906441c1020300005100c2e1416203181d458598036040c441a04144503045440c24a00d40f032410410f0b96804070543d810a6404030006031344800891075441c00d15a003641d4641d00440c00380c880000c001d500e0300010156201511080024410045c000f4141d009840302d00000818405410300403450b00303810100340c2c43c0281400281194050184070050340400d40c00000304400050400070003008202e0701032881c10140c020801070400000090b85480f1b104a50128941c42c5d4032014030f181d65104514801d100e000705042d2034560355040c0400c41982010360440c0302882e050492003007200100718503106500041481c00e045c0010f81c010b6401d2021a00b0036a60b5039515000900c10b60642c500358504403c1c0640901d0000340341c99040d51811001c01d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 917493543 1250 917492293 917492297
    0xd1e06110a1806090815061f050c060112080702011b120c03090f030c1503060e070c150c0f0318020a241106061003021c05010f080a0206090d03021203070207090606 72
    0x2134000c11030b1010100d01c0310030041a9101140560711041c002403110302d04040135440000007006c0782c0d81e0306a013180050804002440c1074440c56a40c1d4007800405450070840505440002c10903640150300c00d400410306040c00b60307510304400e905510380124190f40c036402c207008280c0b00881c0005060700440f000340240340e031052100016045540e0240c3c00726007881140045d503031040c0d641400314080c1c0c100601612050046000c40e2810300d200030a2500c6a94054800b0b282e039141051890403180980c04007044103880b01f604641a21400f200100181e00c50781d01c0d500745640d81c0000580d19480510000c00e84501003000d5088030003243d0318085c00c0480e1040c11300c80003d25225000402044d899805401215125190302c602c800a901a03c2a0310304458009000c1c01c0d940d10808096000030b058030300d84000702c10a00d4584c2030059450301550383c040e6100c04244800440ca04c0c008103a0401c0ea0300c45d20586055a00f01d248013421030300b0517030305803016030004401070002c0c10b034511031000200710700c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 917494793 1250 917493543 917493557
    0x61c0c03060e04020a03021210090803071e0801050603070306090f0e010b1905010c080c0607020124080a021302190e0f010c0f0201110f0a03020304050f0d1e06110a1806 74
    0xa41c0005c0e021081403000038042c03036a034082c449031040c4c2801410200d60170020b05010340321561410b10178951084900002141003030000010074501d000032900681c0d61034948030400c2e400d01d0b08001c800d0308024503010405403100c0020a41c1d020b203000e804240a035001e004150111003625180c20b5942032201c0d18090603948010700f01c0405003140d600c044803c05c0c00c04140c0c40849040080140c03090761240c15640c402c1b007080c880c0301c0d50305520402080d00f0002442186040d0500e0744840740e12580720f00c06d51684075020b03140151078442007800040c000d0301170052418030046521603008028001110128908041d02d811604021440c0042e082d8240b0308144802601d0740e0f0004904202000a0704100f60000d20317103000c103000c008088080092104460307682ca16490029600d85c000d0007680d001c2d060385c50301039003a030030034420304145203034002c04040c403000026090a586658100c801c2d43c051f501c503180c40c528822180000c0540150582e220080c000036250f0900e5140c0c595030004c0304208072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 917496043 1250 917494793 917494801
    0xb151503100608090a06021c1805150108210d150e09210c100617011a06040b0c0a15060302180402011d12030f030f0109150e06061c0c03060e 62
    0x4100742d180e646c0d022100503211500000c198183c5140310203000d110a103040c5900a0152580d0380503c1c0c0244a1400c4a503e0719020a5040c0030200c28440c00420307030b01503104c8200400080654240040c07103041c03e941000659100c600070740701d180340a5266040d030404140020240d0040490340003013118000c045400240c0600604485991102848190003080641700d4240520a850680039031841c180031440d02e40e66000784050f00c11043e00c10a602c3c02050200d51080c2c03600750b90084400400341401c16280038451107141d031200100c85128099102c11070000f030200d920390704100560242c002035050951041c0415885007070f8211100d11200360400006030381c00401c1070f004501c040c0a50010300c9403000840c055680a489040082c0004610000c0b00d451a80146114001c5020619031699948410a0880314040522040ca8074030520601c1809011800a03800c85e41c044c151750703d01058502007031105200d4403c0d0400d19512003009120307403075141c01028003600210030078581500f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 917497293 1250 917496043 917496061
    0x111615020706210b040509010b0316080601061803150b04143d08010903030c0c0b0402101b14071401051e0415180e130b151503100608 59
    0x50b40160418043c0c001d021190711404a5402ca500c940c4809003003400181040780c00309000c2c00d00f2a005030b00910882c1c2c20106010301038034600040342c1802010740440d9003080d20455540b4001c0908665007204d01000100080c407031011051102240080001d00550741030030001540c0e045c0060441e9444404140030600102111100601301403590015035005801c6030184041c03841145035040503c80d9038000b51220043d0403072111644039940800401440450545840318601c901500500002e40068014280040b6040b0305406070300306140c0030124009802c01d00180c1500031101740c0140c1072003040c112030811115021300b49841d0354044044801c00020014051074600d6141c50300180c03080008032045108a80140010107210192414100006045400100e101c142c058a4440c000140101e41e01c50130307406080620030007100001c0c503848000100402070842d160700c49446005c041241c1d42c0700007044803407240821b0303c0e44a00d000355040c1c0c003026050303214100380050030081203100301c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 917498543 1250 917497293 917497307
    0x1201090804090c180311040c02100f0212010e1e0703140103110909060c0a05070204112b021204060902031501091a0901030201090302010c06092306090c100e01111615020706 76
    0x51b5050381c001800700020320089103031429031000d8581e050324100000e01c8121542e0000c14000010b94580c0c05147d9a802c603000c02d904d0108d4000131a01c11400340407884d0901c45c00f507150421300300d1401081401202800078500107007a44121038003801146100250300b005d00b074260f4482003950203048903251a6071165418071504240c40c0c2000303800070b501c104540d1203911044070000f2150401d5290314080500642c01061030000800c00340d80000c0064000d003003402110611002c00300e40020760b48942c1e61350340280281e0141260305000d41480c13031560040d03050805008003240900410b100880e0700c0c00e01030b45116665124081d080d140018405030b60400000e008803942880c0080d2026140e003803030801403104480042c800010903491072540441c030364005060000340415244140c403203c6e0310030303038807540d0381d00700c0e07410a0100b480c840c103440c040c9032501861441818030f00c1ca54140012024141011038003100000152103405104103024540c0361050703490a030000f4000f560030000040c01c11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 917499793 1250 917498543 917498573
    0x501031a151b03372a06140a0f050603061b0d111e13090c09121a0601051c02090402071a2a03061201090804090c1803 52
    0x440030000780c81c80c40307540b84401c40080b4080c8505490726810610550b403010540100c0000940f155045a0b041d0025129070581070101e0399143c1100d2a203000d81388404e4900d0240994010701d400b105440003141140c02001c14a000e9404c4991451500040543c226444600c0340e40a552501c000c104c00707030720000780c03181d0003010905c01c103406034480201a240901c5589003034490541407041d14001e0b002c0e5000a00f11540c02409200070701ca00d80e00d040400790042a80c0c060b556003030710344100044621a44842c610080c0c5240c6440455154040380aa10440f03a20803202444140c1c0300c3c0300128647c82145400c4002440c100e45802c140e05500503040c0c10780200a10402e500092020050392282c4c1114400c84d44000e0f04800030201542040e03400b0b034100d4030101d40c0580e850500d1000503466551080307036031504600318110303290002480304120041a005001c1d640e03800d060700c0402d025002a00061002c4c0c00007054506103004020303e8031806200b460a07005002c441440001c83c0c0300d4030980a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 917501043 1250 917499793 917499829
    0x90d0804080d091b030b0708091b060906070b0108010b0f01021b1801060f0207061103042c0f15191e0905100f0f03030215040602070b010f0501031a 65
    0xb180c0d140401000100b40d0b806000700818078902c21005900c03e0406004100e178014030000003541d55aa00948000d0030031100b51409401a034441e40d620461048002ea003030102412560920407142c010600541c4101c10654514014074010030401c082402413004400094450203462101c1e1030000c1e40e51700c103030b0b00b44540c850070100e07402005885094144032280c600c0549500c607540d550304003a0042c41c10040041c0140500f2902181d0f01303018000c02031102022900544c038051500940c1648074030381160500108000190035040040450690341c080c202c6014110040e0030501c01c550710700780d018104940503a6200c0c0e20650300c851240701d95811500c1e00c203407030036042045a0a07040240070729082014400d1619041c86003141c0c01d02c120205607003141000c80e42c0075460b41c03407440b4140114803000300182d200e5051800d207240b164150941003440780c80d016003401d102c0c1c0d4500740c10f103509800c840410f0b640c60000304021340e030601502c1d00094501241c0030001c074281c0b0106801704549040078131 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 917502293 1250 917501043 917501047
    0x8010317070819020d02070302060d0e0309100e0a15120e0307050f0601050a0b04150f021c0203030613020c0604060515030601080105060906090108060a052814090d080408 75
    0x850103500e41181c0e0480da11011007542e480f4007114203260b810901400c507006100303200400300c000b400080d072441907e40040c0310300e04200c501c01d000c10250001c4824132a46003c01e1081d150300361582d14009011001030785500440610000a000c00c00c10f41c3c7d4004195562040c810f0500d40d0380091070610012841c0c540858506441c1d1480352a5110f00e58000780745100d00d9041446605003c81c040703041e101e04480c2d5410f10760303580510790078500650203103410840343c0344400301000d4090000141c0b0040a401517032045c407c0001200b124590400c5848050b8100008124491602c40b1003a52002401e20b800c605244450204980c0e45e5401171004049a80e0382d400b040c414000d007010207001a034003c00710750596859920050103440207540d1580201492004070f0361501d00003078620f06032114000240b51550341e549140340a000090002d03203110241698040501b295107004e140085040b00020030001c6254805405548001b411400c0c0354001d05095030305a64088503040c0c015801818807a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 917503543 1250 917502293 917502323
    0xc05010f05040f051e1804061109090a020328020310051c110303091314130210030507050d0c0e03060c162405180f0102131e170c130c080103 62
    0xf02080001c0900b40d008009203c4018681403026821f446503100704010320080c500c8941c690258080c040c0200e81c0581d0b803500040c0308140030b90103581c1c40900f0942c242191341c8003900369256032030310700400c200c6590004100155000c104810710001c06040e212070b0804c1c02c2c6058401142d590180c4010441c0304801c515041f142d40070020b0707034800000285440460408202900001d1801d00d500600f1600c55070001360a200c00059078146054010b04140c0d21010b010f80f0482c010b201c010f00b2030084c000144000d0031045014840ca013025543c80e1182c4040780304450402d1b141440042c1810709403201003240040c02c1e803004641107000d0b58400205040710822059510918000e40728620007079280008201c130201c1201d4194a4482c0081c2c1518840c00403540c00500340d01c101c240f1042c0c00350b0712900800941e0300d02c120303049a8591044000d4042070b101c90751030441400e00011900c16503ca601d000c0018901240e003403c14450081007040b02c8100c00d40c010b80000014803015205040c401000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 917504793 1250 917503543 917503579
    0x50405090a0b091003112416060c0f0e0f011218060905010203011d0c0702061b010509060702070f0e060603040219061805100207030213020904090c05010f05040f05 72
    0x100c031010700014a0b41d445441c0240310780c001c40415100c01d443c1d52603001c42e003101a007414041da80d00c02641c142c40540c054800711f00301d9410342c0321142c440c000404d2811941c1c0412051300c1134514440045d0b5490f040e9405a05e0024059a405c55201d4401d1003a140007043c01c0c0e030061071012200340309110205442180e4204c3d480700c9180300740c0c007a10031410f29014000700b22040d0700460588110000070308960b4440307006102e80039011610444000c104006600140c50004003800c2491071744e0013840c29600c00d102c06103003550016200c103100c99100b00103004045405201200250031f10685403400780d4a0000e00900809000c0c20704d43c06444004041019512800c200010040501c01200c642540d10200200803100d040c030b04c0c4900356080d0a0200345c91421111b0030550381784940c01400c7e41400c5400f08a8007a000e0802810741c07540c01c10412003503460340e004010f1500e01515007049801d00c0c02c00050a00005102c0142c00c2150030001031200100b40403c410a50b603003540c14090000f24038481c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 917506043 1250 917504793 917504801
    0xf040b1e0405070e071b0209043e040207023a050f0615030d030f02130b070515071403130602280807020c06090303040509070804060509060106050405090a 68
    0x4000041034660800c0300b8800005951000c564104015020b50303a103501c01259104060010420302c0c14040c0f01c2d240c09481c10600b16900a400380c1281c0b40780c2169103d05c5500d09500c0c0c007241d0700c0302030714041f09150b6048018a5500100e01900d09610f008295400200c0c41450415221281401390800072500000c09c7d00c0f00d104565180d03142e2450380c140303007402a81d50b1000096980315116010004034981c059003030414110501400408800b44054401c2d00500703040700028000310307424070030030100054400c4010001c1c2956980f465a64541e82806810120050070204102c815030091000c0168000e00c1c2c11100083d02100355100e8903400c070340d106c0000f10b0903c003070001400031072243e401ea0b60f2185849081c19817010054603d0f44065002e40381048101c0d02c2c40c0c0941c10100c4000351a0901600034002c0041c024142c83c80c168030f4000050703180005507102c0340002c82c5242000304111582c03249039002003511005040c85d40c50304a00405600c2640907042c02000c1e202c000c141014040c1d04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 917507293 1250 917506043 917506081
    0x70f05030a020a142b02010b1e03101b08130c03060b190b04150908010f02041701020f030a09050c03010e100f020906071209080601120c09050f040b 65
    0x16281c1e500c651240003541ca00000005031101c520301e0310303840c640000c0064080c041c0301072684805010040c141000a450400301c0280d015952140280030484e81c42c0307003041c0c00071003200d0020a0b030451003900781460180c50208150001e880d068980184810002850a001c01d0030728064030281d440b072400031404040c0200040140304002c0001c42000303056040410050300a903041c6a2280032004203100d041caa0340300d5103a038103400300401d00041c04562480d00400c001400c2840d20a030352801290b00310364145c0740c2d14880796030100c0c0a205174003855114014451b500f0f0001d50904c3c821861101c480c2c8406000e8001ca541e036030584a041040500442e10700120040080116003031032500d45484070018620440140d1038009100009021842540c81200d008ad003402c4c02c210303e651350171078000ca049030440e003808041c00001849103401c02200b406060a0b44403400040100d103403949400001e600070014840c105001c02061036414503c00381c1c040d8002c240401c0644600c91008140303420b42c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 917508543 1250 917507293 917507303
    0xc04050c0d15120c061d010807030b1507080a09060f0203030a05070c0f0303050403020c04060602060609060102030c030a0e1e060717090a032f030a03050304060b101d0301051b070f 79
    0x90b0031a051091300c42410b0100d4400d0b44640c04200f06800800e400d03024100d43d0701d8045906030010503909486a40110001034002d4814040000440500703002030b0480c2d07904507414080010203000305507200800700000c11407401d04010000203048060340386c0c00010301040116036100002030036144100113203224140c012410392620b504508009004c4c0104880c240c0140c07240c0d049000e02410f0511910302201e03d20f60140c80c141c1c03500c2040080324200a80558114070040c4803c0c1140034003840145141034003a11074100b094011414045c428402402d010030318800900281d119449031002c403003904e6800518030007404400d01c003581072401141c81513a001642035030040200710405101c4e901d018822150140a1aa400984032583c034071403107c507416800000e0070303a0000e40503401640e0040d100713000c08151011941c01040c2080240c10181d000901602c0c0c0841c1c11020050751151884410b0b002032000345000601d01c4034010142e501040c0003080007400005005c81d0200b0809126488 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 917509793 1250 917508543 917508569
    0xf0c090604090213050a083a0f27090905010906051009050a1a060d0f0507050a0f09081b0102010b0411091206041203020a0e030d030c020c04050c0d15 66
    0xc0c1e42d80c8000350010060203941d0301c50200041401d00d8001c2e83d004c11075011100510400b406403e50f0321298480005480700c0702c454000c840448540c00d844480c0303059940d500c81240b112101740c000e0142003200302045481280180041d16001000c4c102c0043c0d0304495000f20700710343c1c18030304a401000c030790002401d0545007405000f0010340c0320440b28211148200709200c6a02c859444104480400420340c0d07004080c2c1c140d65086003001c9026040e04011100001501c444481194040c0c0b8422100480010000501440029000351541a400325140ba1100090741070040302070380c95442d034003070702c150a10182c480718072a071003500030f0024900042d009001d101440d00b0500b54540003002010300c1a1480001c00b1816100010300ca4840e80c1c002d80720210f00840001c0540c0203601121640c1d00700080c2c82e4034604292401c001c0c0c440210150ba40008a000c21400f0007400c1000f4588680d104c0c1d4103003000c0c020f0751018502510200144002d00041ca0900400700741030800c43da601c040a2442e503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 917511043 1250 917509793 917509799
    0x4020415170f0628061d0f130b06070f0303020a110303040201021e030c1903030b011403130c2c090706090504020a050c1207051908030f0604020f16110102070e0f0c090604 75
    0x44411b40d00d000005040c188020f05110750104202599195a05c5030482e0b00c1060000200794660030442201d6405001d40745403042c2a00c4211400001c4c080a40200e42c000502c86140740d40911841d0800245001860071802d050b40000d403195503c0000c041c00008512402441110600c1102e10310003400c401c0b5811050a001501001e4040d0030301075000c43e00d001c0b000d8a0950080346070340b801034030412001d482c0d550b6200342c031020301403010f02c152006008900301007984c200e484242c0c0541e40000d420084000100e215140303184000501d06100e80d0440d200030051b0b95000358080e42a12000c460240c0c0302c030b8501c20221000c0c00790810404d4076205d07414074480040110701c02010b460b80a90240c60140d940580700388800254a500208030040400c0040d004540501c60181c01110003003000d4903003510b07910844410b8019101c44400038000300061800c102c0074a04a2041180070b00281148078900f5981522003003005044012007819000041c900c00c1c4000308603102120001c0090741c640352 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 917512293 1250 917511043 917511047
    0x60d030f1e08060a08060739150f0c050403060207150c050309300c0703050714031e0a151401030c182c0c04020415170f062806 56
    0x80c141d03100c42c00360001010106805c0310104030725114650715120a600590503041c80c0d1801a08100c04551a991005070224200d07100f02009407854090780c1921f100d070000d2488102100c090b00020161507260200e00c031070113034000b000d0300c003240c4e040b07400113848800368200038016654100c094014645040c2040074002e07000405076020b644c0e1401182c07588160341d584200e188200400043c08801e8903d102d080b402e42d00c1c0001c0c801ca4682c0c00907203022035035a643d0b46140c02d1464224150041c01d45102a40b1401d04000c4107800c40c0f1b180d5024115526400ca009840312075100303000d4258540e118502100891540100041016184045409696030b080c0141454501e004100380180c082d10b803110b0003c0c3d01e000741c0c01d07020840015028049240114421071840034041c42050f4042c0000700744040e0b5640c03000d440101450341d5001400c060724000140400c030200407800c03940018905000c3c13400458400700f50321035010b950221000a001104d0107075800c0001380d00361181007a003004241d450f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 917513543 1250 917512293 917512307
    0x20a06300c080901020309070308070f14010b0f15030f040f12020d0806030d0807110c0603010306090605130c090b0a0806090109120912060209010311070803011a03060d030f1e 77
    0x21071190380d402c070300c0d0302c641c000c2c54241d200903608484c099110100c1400494540f4000f042c02501c121040714402203180d40d8600d2501c060001c070728550f5075840d0041010306200e8000c00b080482290084040f42010003010b001d400b0140a62181c0e40400c00020100100301c07101e5032505400080c0424200315510707000f50b031a1398040380280000d240038042503181c00d001074414000082c0380c6482006986500301191250fa068a00d440580715617050150a034030780718000c5010718016100854000100e060079020350340050410a4a441141d0410000c104440c036200e080d2017000d10003040a40381c660001d9000441504a8100c034010300c0280090560150706c4450140d10910f0044d40c4010b032081c056880d840d0500c03c0043d030f03c00d00c440a0300041c0050740141107600e414180092100f003421499560340c0c0103494100c0300c444000006203c69038401207a000380c5e600b0044901d14501d000380110700416040b80700141031102014005200e2400703400b8a200840300d07a03103144601c07190001d009101c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 917514793 1250 917513543 917513561
    0xb19090501061202040b070308060406051206040b01080c060301090c2c03010f0b21150f0114060a0e1c0204020309070509090102030903090d0f060c03140a09020a0630 73
    0x114818582e0a03c44151500075202103e800010780c5017000a60b4a0076512181d00078443c0d940241d03215030103e070076580d140d21107141850b40d000800d11071815280ca0030740d40030103800ca540954081090415156107007422641501c400043c041407460749501700303680210b00245c2500312500d8020041c80d11a8146043d040d42c040c0403802448900340d000d4281c01204d8462801e6500820b1840c010142100244140700c4410000d204503030b20241480a5000450802d841c2c594082c804d4000420120100c00403e441c1190b085520350310b40481d82e10050b215501c00c42d002da000395840d02c5944008500011040c00080d00944150351f2440c103044c9403503d420a6025651080700b073703071001c100c1c440c105200392031050f0101c030001c502c1c0c00010010401c1c0d11110b050b040f42c1003801c0c0741400c0d00050390f038040c91285400036140801d19042d207030501110400000d01c5100068540740c080710142c0e44041e40d140840b6032508001c401d00b40b44c0480803e0800076400c0c030039030442e00040b150b101641290b000c1003003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 917516043 1250 917514793 917514797
    0x70302012003041e0309090905101a12070803120403020c120d141c090203101107120203120a0e070801020f220e07031109031608071502100b1909050106 67
    0x413090101881e81510700c5480050f00141d4000c0080c130070a1081e038030880d01c1d94002d034200d60420700c20714021400ea5400e8044192445403110488509050061a90003110100c5010340451400c00032060354030300070921b0450710101300700c000c682458003c1c000d080c000100a00244110b8081200d516a81c20f01e000e103040000c0ea804000741c100319040303816149004951408150340544080410b006480c07070300d00591341802646940128540c092250144030b0003030070a525200c840034100018a02c0b480c0c450710055410811110f02840c4003c03a80c00d5100460303081c0000c446641c400c4541ca0300655400c185050f40c80010850364651141c409080a00980400d08005141400e9034008a030120720420890f803140307401080c81a030003900900003484061944a050078400c0000034500b01a111070340000304056402444160800d2040a002d08603045000c8a04c1600583c001d60703440d001030301c00380070035550841c0340c545a580400c43c080d004c000c00013035042c054841420000400c03080c0304084c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 917517293 1250 917516043 917516063
    0x100917070e010f050108130c0e0a060f0605030c0304021009120503070c0b0a0c06020c0c220f110403030311070807082205060904050a06080708030d1116020607030201200304 76
    0x41d0200002c4804025503130103940c2c40e9540e07240e2640c0362001c0030800700c2c106c91008a0500200340070420b0301e205803240030300100104040e45001c01003140c2c031485030000d0042210400c1000038609103641129005a81901d80100100c82807004031031442d00c40c0c2060761006c00d00c4450009100d0000040c20040f80103c075040c002c80d9031034140544038440c060b00d66000c0751140c03146001240d941c1e40a8200d00304000309039001440c0e01d0002035007422030050707030002c031b924403c507402c000d50000e210307014031a07514403010010100e0355103403608180a0391000070101901d40503980700c070303150344001d079400c49501c030030301d1915008036140500d40d9402c151a51490110281c559005481d1002c0481c801c0740c074003511203443d0142d00e005210283c0002408091004d40318640054800380402070040100004000340d40c48a61078003e10099542010b03560f400200c0c1400344d60407050022400c160000c0d0704440b13003035131407803180703016409440c01300303c4e40c07058005244c01c1600d1058554000c6214900c43e142d400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 917518543 1250 917517293 917517299
    0xc07050c100f0c140105072d0509190312020c010f02060609010e0612070f05131506081e0f04150912030f060f03050a060e1b100917070e01 61
    0x81da4450000010001d0300710008030007028028200140114042c5240c80c03981c83c035812255081d03038010b1b101e02001904105695480c055a049007411724807000c0c1400403102c000c04002403243c0100c0e40c10324420319411004039501501400700c7c0c401140c5c817030701c0580909210b00e006901e40c13411003071050200303456104080c0318502c041081441464002c0030a40f080c0d09003521500b21a00040c000c6030820fa40a000c281c0c0f0802c00c000d004000c0c40c1f4026035002c0c40b400d1100340000e0741070100a082d20917080044442d8030311600c041300002d64880340f602c841680c0c1c6103c003c1c006082d44849100c0d221007650705100d10100c0c2c44813002d10031400b820a0740400e408640d0100c0859200d060040c0040c0441c80560020a00c681c005070480707641d10801044c96501c411001c1c1c1c0760340c1c16900031665603100807880c0341000000d01a200c0da60100c2c002801008003911f80204403c458480c016201c3e046040004142074010400d2a001c0c02d03ca05010340000d824510300c030759901c10350080c82c0070903500ca0000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 917519793 1250 917518543 917518549
    0x70e0f13050c181206190905100f060b09010e060315060d0c091a070b152706152209060b1c0b1e120118121805010809010e03030c07050c 60
    0x440900301d200e90050170b0729a291004480b80300141180780d01034a445000d000046102002881c14900d08854001144085c1700c5a035000caa00e580d000200e040d40500020030640e0300720042d03035040b0f10f081d0744156981e9a80d4204050715261013007515441403000c186001800c525a0000301c00c1c14054544c4c0d1111030304e03600c01150402d084021006914000c00841001130703403200030f10303030000030503040541c19010050004080100c4115850b0741614030794011040b504454036801c0c4c001c001a1100e032912050809050200d1050231007002607940e8031a407070140c22880d400900000d201d4490f0030401161180c900010320307030240741c141810714410f00d00c0408281a41c4510700c2c1c00040100444101858983c107001212030200700c02d070f805030664890080e2041c0a000c3c00c54100c0911964032180e030014945144128070803c0514100103080c2040c00891500c02420401e40d40242003040e4181e0340c0709180c60140c03801e40801c0e40a0f00020041c0040100c00c0005000c9551194060303072442c02440c418 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 917521043 1250 917519793 917519809
    0x304150603051e070f12020307051201090506010e06030307170913052e060f020c0301091208010e010e07050d0b310e070303030b180f060a0905070e0f13050c18 70
    0x24a40b4007040c20802040310b49105000c0d00c6c01039102a00351003a0694450001d034030005150300703005140c0d44035048a01007140c1400454090100008c1c900124140640401d0b94fd0140000040079003001030003100c40300035500192505800b004040c1c000c01c2c142c1500710405024107541042c07001c010f83d03040c64105200700c0d15441e08551b02c4068540c0451921100b181d0803060203c0c1038042d40140000b04c421600d080c0107201c10540501e400d21050b0000810007801048142c0c0a12044190f02c80148090360f0703203401350b907000012072800940310501d00d070001008009041c03041e580041c0b10480910418140c540b00d000e4901035656801091001400c44429551403a02c0680640c2012406100082c065881010114009858680d0f480d0310b1040c0c2c4c021440e0b064400030004c250004c0bc1000030310b441c5420002030480d0350801d00c035606145801800540d800c10310300d1f01c02e41c0702c3c41032110a0b0b2907903140c410100046c4142407040d420600c10441d0150f01140342600c0c00400c141c3d00b21001c0c10200c01d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 917522293 1250 917521043 917521049
    0xb010e041101080606040905130b06011803030c0c05030318270112030c0c0e161b350903070515030c070f06110901020d02120d020304150603051e07 65
    0xa034007111080d10900445200c0b90050441e0350001c001c0c00b01081b6404244a230900c0b61046a40b007402551032070400750140e940085c801c40c100104149030103400d81115120b041220351600308481034011074503003000042c81d1500030f5900b6110104100c034082ca0356880b81803081704140d903e08445c0c121040049545440b906070203004076a000c00411880403030b2409108070b9402494851107030300003a43e0b4811124846e41c0300400580c001c0c000d0042402006041c40c421214500f000403000b1071080703144110800304a40a00204403410b038804090021072840c40200e1404c0004880746600d60100710401e030005080303d4001c1c41002ca005c01c541c204105600726043d9061505815039071450301d0940d182d404110111102c0b2081c420110000d00ba40c050800c40c08000c1c0304041d212030901000a250242c0c08000004652162454801a48842d811600742c0041d098003d83d59036183e00300300c45102d58030541440300901c1e01000005005003c2850410075801032800e02c4440c0711600c2c0b0540da02c0c9140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 917523543 1250 917522293 917522303
    0x501023106090830040b04060f0503010f2607170705060f1c02040b070b0703050901052214070b0304050f011401121b240c0b0f18190b010e04 62
    0x70211a140c400d070714402148400b00d410344e104409800c2c000e00d081c070f5005a8007640a24030f010a045c4607a941160030405140900e1505900790743c5495a00c88100c3d40c64820300811220506403ca101c8142049101e01c0800100489003010741e18506102c4421454030340c1d1116008000c80803845140407000c5441d000c0d07244a02505042c0b0001e0414422000304207007a010341e90030070001840070301c090050030301c1601a24500010346480705010b01607030402084508242d00d010304004600320003103110014085032500c04140e0998a02d440712100d40c2852540901e4885c2600005080801400030342c400c0d4890000d039000711801000c0107081c0d60082c85100043c042c0000144003100190f0001c9403850f0041c11403210074000e03c140404d440d0400d40080c00c1c1001e121500e000c010040c09003503204001d880c80c10440c0e6010545515510100180001c0c000b481800003103041800c1d01119180d40b00078031400e80386404541032105200400800048a1100b1041d00020308034003030b140790341c1c8515040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 917524793 1250 917523543 917523553
    0x5010807050a14060702010e06040f15080c2b0e100f27020d170c0a120e030c0d020a08100e010b01080606030a05070203040b1c050604052205010231060908 68
    0x207036006640004234048000c2e04800140000282d1026840c4644014904c20500e240e22045040004100c40c4001703044a42daa40100800701040f500e00001c40501080300c401042141e2402842d00080d24000e03071046001d01c50003446410181883d8424000300250010800211508401d2812b03052115400d500c01d401c442c904036005810309614103542a841150000c1d0714600c00003079040282c004000caa00181c0c0505041410013503182c0c00032000c10b90600b84005250341950009540d000e4440d900c50045103418a5030045480d0007401c400a07201176004d54811b54240c02c003100061522901105240d070130004403418950080704540d00400010b0300d00d03451071f40c031955180080c00002c0c1418045100800c40000c030031002380c0203030180d1075243c58460102d030034911800043d92400703040d09100d68035107030a002403008000b440d0743d030380da0110703c4555845d14241072980c024040c001c0c0d441c9110702580101a0304403080d060002c403040780e814030411840e45809040310304415a0050784100d40c07003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 917526043 1250 917524793 917524807
    0x100908030f0a090c090b0306010512030a140702060f1e04060c020103091a0117011109060306011b061418060910150f15110a0c050907050d05010807050a1406 69
    0x1c001119070080d442000420060107598540840b02820b42c03040b680143d42c0d4400c406a440c0611500b07006080803200b9140c035500343c0e200c5036228402d054481040c0102e03036844003402c6050401360399aa07038006240c10b440d02010356441003c9c0d4080560019220496441100040c405406540c10341e0019550230b480510298010340040c002c6080545009035540c40e044200003243e0103450283c051100850b1546481000e054291800e1804000c2001000d01904c0c0f915110700b0706a81e80700409203400e01c81541c9a0030070400b0001e242d0300160446042403100c0080300b00084016004a00000f01c03078404400e035069981c0c96160130b0320b4007a4150407d4a104860b00303516084018207480c042c24980110707075250040c0001c0c00c00d0b42d000812444a01900e2902c541d0000102d81481c0e10703200281501c68082e644d0010076840da4050300307124040c0c0718045070042c0e1090051f80c030402c49030300d0100400d507110340e010b60780c3d8440c41c0301d850f100b0b02c580c0801040c2c1d140c4001041e10a0080a030000e400c1c410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 917527293 1250 917526043 917526061
    0x30a03020a0c12050421020f010f09090e01230402030a170d1806150b030106052a010608010b060f1e0c1b030d0c120e13091410090803 59
    0x1200d078070740c0001c0040319002407000c508070403002d03c03240e16280c40d1281c0d95890800412a401c015103400c450314003585e100140540c41d044021442c130704c82481c20003510300f00c2c0e04040c0c1d24480e003030300304c110414135200a2904a5105501007003219042502c2008826903c03000e100d06014102d400075019048040b400e000103081c50054000d04054130000c0703040c941c000480030300321003841d1080386450903070004080520ad000d20400c14070350010800b400449080c50511902840184546400c1180004244c225801884c1c117030007100304081c0101da400d005078480d26000e0071850054404551070180499503901d0130408541200c1c04500c42c2130305050f001d80d5034105c0000d15034281c0744d041078104201e008000c0300f84061260128110030f220f0700d5a002c10141440e081c0d95806a00500200c400b05e4004941000354040004c003030b52034020f07482e0403100013240d03103441d40d415400360450411900904100d0349905d0b5150400c81407048903010a402c0e102c400507238118100c090b1007581c040010a107825 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 917528543 1250 917527293 917527297
    0xe06030c091908240f04211b110112020316110a02060f040e0a0b09040f050f06070917070302150315210c01181502070e070827030a0302 60
    0x91844400b0100080d661040c00d82041c0ca440c0c420403468031401c1c8400c41140d903413410340d0341286840455580381c0c80c042d034500030450003030841070084000115020384520310540142e900c1800642d01070030f030102140f4150840b10580c2c082140452481c40100c3e007030618501c2500e100d0300580301c50307403030640c503101303042e52500315030400c051442c09003000f81009a1908402000160036046e8065079032441e0016654074000041c2c580302d045810604031440c03c0d59413104068000b5000248230010940a26095244c2000d01040303844a010305010402411342114002084a610552445420391001c600f00e0302d810660000940c8004000702c0c181d60400510050343d8813111481d001c440074803000e40001c00c503810f40c820044000504060700e0b4807660060069003205442030a180c101402401c8004020b681789010f41c84c4034000220710000040c2c4200a10300c0181a05a030704011818040402040c400301100d03002d0b030f50981c1c500b10105c10f0800210304424003180ca4040c5040c01c00e1514114065 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 917529793 1250 917528543 917528569
    0x30516060806030c2214010f180e0c060d020c06010305030307180302060d09240f0b010813080d0216080c16030302030a1b02130e0607050405130b120312070e06030c09 73
    0x140d607a25001001c0201e1407465008c0c10220444248076481e00c450003000b01e6030000503200013411b040010b842c04000089803030380320303804442d103a8854a4425111000380103d4000910320300c80d08000000388407002c80214059142d507a565420107404124125541046100003500706c40200300c100c241403c03030343c00324401611560020b016820f00840009d404d03d03030500c8840c46913a43c4c0d4501d81d00c0054501c00d00c1c00000b828200400a807400d060308440d42481500c010f40700640000700840d0300303041c2d035040b1103c04411002c0f24040d9040c5091000c059089802507010314483d0565403902c285050140104980d4540d0043d80b404491580032900d00303842402413840340f801071541230016039a0941d0405003020f80e6100081d43d800c2501005d240c802c014204005120040205000310313180e0600d4189440c3c59071b02d0100320182058081030103200207642c514024000400c1e0755400180f820411801581c45650b51044035030184104205403200340c0381c0f541c18810070440c009160428400034061 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 917531043 1250 917529793 917529859
    0x23100608042901030c060306170a17161a09060c070312110c010c082a07290a060e060907300212010f141504030516060806030c 56
    0x1142a0800240b100c030300c080c2c200310750038440d40c10144042a4144505001080200201e01421204844203511900000c0c07001d003041070307803910310801030381084200d40c040b440a481c124024a0b95003410701003400301003c000e13401131021003c41c040380c20002d22070b405101003205c001e1400030160380c142c07496800300301d02d04000c82c2c0f10400b0460041051003d0103418004000101d81c41c0002c3c0d00081028000505000381d0a1020300c107d884000c0c81003050b20312099244409503950440c1c1403400b2903007050f030300030380c451640c0820008804451aa0050103181e0b428001c2c48007a0300c6041d803403814001140c000790030040c4800042c1071588a000c1c0031003440d014490b030881d0003d00007607a82101c801c01001e02500f030780000d0802100d030124000c4c4c40c0184112a5001d01160410941d110305101109006100d0003a40c0000401d81000b04101d030f0007550702c441102d94400d149a8544a00800d92003a1070110f0320032000150310b0308000c00c402c02001e00040454150441603205092441c90b6074401d210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 917532293 1250 917531043 917531093
    0x613050402030a0c030c11120d1b02150106030b090c160605250e060304120519030515120d0807020109060203042102031306051c2310060804 62
    0x19a0303100c03480194041c0c6840700002c0b0700d4031500d200140030703183c02c3d540440810030b2010706070008400c0070036020414001c0c1000c069882c800416140c018280903504c51643c402c10b0681c61140c1d580020341e000855003d03001c110180da0780c80200b60100d40707800b061f01e0380001ca040002404c1805800c02484854660000b404240e44076403141000c4071012a86806442c3d00c0c5141030704404107140191081c40c0ea42e24001ca8104546001716102e404003400c0248001508010000c1582c010000d0f12800f1100c2c0d00c03400c821403083c04008002d40f00a0b505810031601ca050040040d04168003980c685802400080c80b0454810908440c0f0040041c841004c40d583c80340f2840008189000941c000d500138a010107144050218103d00e06074141c0d00e500966002308500405556850303111303000c0360814200907840d002c1c064127004205003000721300c0140700e1800f8442081400e0303800c050140014106081840c56a6150002201c00340b41c1c06800041490580024000f42200c45070071135071424405151 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 917533543 1250 917532293 917532299
    0xb04060212132102040b04020906180d080c1006210b060103060f0306090b090f191a010e09010b040b1e0a0e0106020d0807080103120c0309080f0a05010608060c090613 73
    0x1040004200e80d180250f4095030440e4402d42c6882d024208405030216000c51800c03540c500003581620032030554000456403095450000e544109aa0003480c1d048042650348007000c00901b030f282c5011841145080b4a40035000c201c0c0916003000407402d600040d0030009034511600c6041d05210006c00c43c604040c0c580d40c0c0401c070205140d0082c001540328000115a90034903140c4504003900c01440b001055020b01048030a0010000d2120340010341002418003a0415040c0b8201c1c460308150200e2000c90f244000107049a43c1c2c1000a1081304400d00030805201d2110812069036500c01d40780f5401b12907030084042c910318901c02d840801c200200b08101056079010f1882000c0400d03848031000d45c01005201c0b080c181c100c0c820a500c00401e1801c200c85604640d01c1044a03400c01c0d0040c4100920030512000701070140d110000035245d008121021581c404040d03070ba0361100b5210031545542403c000203403400001501ca40100780161400381041c241206201082c2c10491240300d940c2c000c48400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 917534793 1250 917533543 917533559
    0x30b0a090f1e151d012303060f181c030f0e07171002090d03080402040b1e0a1719020d0b07030f0501120c0302010806030c15070c0b0406021213 63
    0x2c4148002099002c1102e0f0000c6a04030300c3ca01040d88151000860f202030300c018002d40340d1205066411403103d00051507401c000c01d44003649031500003034040c455681405a19440c200380d4520801f10302035100780400c040144103484034106c2c00c90a040c05490140d240c0d450f40280c02c01c03407054900300c10024130300d995070480030b18148260340003400c0c0001d240c01d001c00010b001d11170a1030f034607060b072000e500e41842c110100b0a00c15801030046c0401900c40c1c0418215551500f02c900161801031546110046040d440a00c50f580e41000a10400b002000014805401c02081c0490b04010380a400c00500b50001c0e141d61000c4400120ba024180000d68400100901c41d00c40c05506a035030001580340ea08d42040040342c2c0107030401c1007a01e0b45084204002001c0340743c50300550340c0c280b80c100b406484100c0413900c0c0c03040e212190755121103888464034400d868400030f02181c5002d4071a14416030365424004180e8400c500801d00142c04c16054a060903031200010841c40e40710308061540030742d0718055 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 917536043 1250 917534793 917534831
    0x10b0301091d060705161e060b060c03040b0f040306020c0d020d2f030f0703051909030209190605131e0501030b010308090d080a020a050f010501050303091210020c0a030906030b0a090f 81
    0x7250100e0401f00100c1702804504d2042034280703202500c205240540409036941d50740190b1080340d20300c10000604409804d100c000351303801164005429134032038515881541d11000081c60701c4005104221141c804188036860400600c8c402d03211142041400b000f4505810f2080c00e400720651008100703006105096200400200d8080e0f03903407a03103034070407801240c40c0c4ca00300400c480700b0000d4034601070016030f50704044a6085940f00840514023591121003c016000c9680810750042c15440c08a00307a100700d1f00004030102d0300955810800c503250b00660115402804091b040c550303020014400507121034014290781e40004c5c1000482d00c00d541da401d0719517114001100046e04a42c0e43d2741c04100c0100920070f01404450000e1089604090100c1e48e203020352803040d4450305042c40c11000302c15060208101c295078422066580d010040125a035036228860300f100000c121880000d10988a4401c011340048000c0a242e0501d1078003150030060020210303a000304076558581c01d8411400801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 917537293 1250 917536043 917536073
    0x1b010c11011a0931030206090604031403070c0c15121404080c01090813080607030606051c020706050a061e050604060c081b160f0806060402160b010b0301091d06070516 74
    0x1054119404c2a860000d0038024040c00300591a4042401c0c04006038004480417100d042d854082500ea80c0c03218401c0312490f0315043c0c0507080c0b40c512407002c10b001d8070381001070000400d41d880e180da0903000c01c080902203940700781c410780d81c0601c0d410104000170740c1c060040213030351206030010510201c540c8401c80940d201400305540c884000c90304001d41c42c01400521741c0145542400c00260707107000070141c071500c142d0356060006204801c44205e032403034542c161500d2580100c0204042e1400b941d03014000c0129010300f41250354101c1c03000c131110941c0e0030030f5004d841010304041d0506151401c19518862200d4007113810902c1401460350404004e02920320a03502c0300d0080c02c084070401d550064003141c5400c04c00d2801059813051201d00400540325401c2003040c1d50040e0307035020100b04030300000b0240030700402c12451803000086000c01c40e809941a240151002c1007048500c000a20481812031500c01d1036401660004031035500440160141c2c80d1070340754800101d98a40c4d03445900081c404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 917538543 1250 917537293 917537371
    0x70308130f060c05060106081806151207120b1b0304030801050907020109020d0b13051c090504091112030c150a0510050d06020a051b010c11011a09 65
    0xc0c010001807100440d004020b000d1030604181c1e02295842c0c050705d40605000e94070900400d00c001c42c4018420040904100318407006540d4241040b985400580000c00c05d04c40c4254440c1846084006010420400320341d41b107100100340c002d41d0b035500000c0b040001e0215042d03810140008a980030018015441a4842e41e956200c40d03041c10100001000702138a05011a0300d840c004000588409400268042c2c008503003205940c0d0304008000764003640d500040240c042c2d81c2e0082003c1c0d5488101145005458842000541c0c85e141808225000088003520b410320b42d00c50324006081c18001d0406058900c016a403030007081990640c039003062030074411600c0e114a030030003803920307200d22840783c214146007074005c0fa180c900400200103444450000c0c00c0b00754005018421680103000311007241110440444101c141101483c1c000d01e00100145e02085c19041407070010388041c400c440440355280b03a1001b2030003944080c0907500000800000c4d01550350702c00001c1c4104506c69041d008200c00e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 917539793 1250 917538543 917538577
    0x3141b0c03060a020c031605101b0801080a11060304021206070c20030622050105040f02040f0b10050901050f0301121a1306020a17160f05070804050d05070308 70
    0x501d481d107400201107595491062115800343c44000c400c440c0c00c1360030302c5908800d8003000e0500c1030924032904059a80b0914102514a6039002e20108400d07182c810f8691641c0c5030ba85000440e200c2074050802000e071400414a0081c0345800c80107541c1060002d844501c3c107002c0d00080b54940901962180042076001d44e1000c100500107100c0250800f2180741056035408070f00c00312b030740c59102524a03941900c01c6800f10591042c0000446003454121000748100d0034a8144089007070708800c401e034050b0341080302d00400c1e003480c1e0045200c1e10700003810078500d800c00c059040301e60340c01440030141049801c0040f07503000b503007001c00f95010380003204110111720290f140403800141049940010b0f040c03207600300201000007801d0451081c1c0c0110f00940d803020100d408031242868114024007460f02c0c1820b1110f1648441621944500d554452100c41c400000090b0b400c0c0c0661503000300b000c101000144100d040054a0280300e901c135008a40c0c440b601d83d42c0e01500c6400c10060418a140b00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 917541043 1250 917539793 917539813
    0xf0501051f030b06150d02130314030a0e090903071a0901240e06221d12221205030702180114041a04090b1e060102070303141b 56
    0xc0e400e6081e401d070407001e40c00d09040ca1070341c2d00780c0c8141000306a548200a1100c80c1100a4401e40494840d0032101ca400c665582c00c20b07011192140f954001601c00350940d05203008441c07000801c48041002c07540794241070540e00420803512800061a185882c00288909800a06503030114003440891170320300500342c58019131242c2101c40d40d905991081d050048100122040d00c3c540b00195844a041c0000966a500c040b544c01c0d5540980844103103460b41c40051921203546c0040508443c4a080060700d44089000540d91641c0310005180e500d0104004c2040b0001d0b4205208820b05442461400c0d582d2941c4106184845100a40f20b40d080083c91408500c2c002d220b201c80d0b030000b00b54a80172941461028044242501c0c0d1040c0642c0e61000ae0307106544c1150541040d9810080092044440902d088034000c05d00362220003240404040480100511803590740c4107000690040c401240765460894110341000080c2c15044020404e040104606a804110060000000b0002208 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 917542293 1250 917541043 917541061
    0x21030910020114090a0c1203050708030406050711031e07020f040603050706080c0316030e01090818180c070209040f210206070201050405030a050a031d0705120604210c0f050105 78
    0x100c002c01c1340c080c0d42c0112aa020000d161802840b090b240e04c0240c071045102d4620381964103214406020341980c001200b0041003051079000184074129540d640d007100092200c40c0c03a0b42e4000d5a0004001b035900510007900c00c0b103c2d40152011a0000308600b20500c0c806000c10b04844840e0800c0c0c80030f030030101c0300744585904030607141d0300003134a1003601b40365142118085c1e40104640014008054031000c407480c406809421106403140c2146009660302688101c240307107080d48401250103800d8240d000103040c44041d83c0d8500c00c375031078001140f0301080ca900700180a10000c00450324078180e10486000704a41401da81c904182d402605191f40401c00006407801500604201c1160304181c1004001080841500c4c0f800c10796040080e1a01c90183c4180c010f04002c070300e0b01c2ca4240d60001102454400015014111801a5034291086c2c4800420540700c490403580030f000c1003980400d040c010720460748401441859450841507907003096407040340c054a108001c0da8583c1d100d00c20701000d40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 917543543 1250 917542293 917542331
    0x10c09090f150608061e01080402011124070f0206042a030503031501110d090b210907090e03130e070c0503131e061409010203090d08030103120509210309100201 71
    0x4e4071b0094101c51400708600001c110043c0140300a041001c190f40350380c4800b908020034a1404070401c0c8000c1c103080c102c05000f01d80700e41101c4d00360000705602d8016a006001090041c042e070342000c164004084103007401c1c0d40240d60000c2502a02000800001c040740c8140b02541c095070310b507082072505664000c001018801100d021600c40e0b000400b407081025004918002140c031035490940d101c1c07a0502e0078102d070642c2c41000d40700c03c08050080204400d0041034000076291030f00d5003005421149000aa81da016510040d0f4156240302030a2040054415007180c2c4111185070107054400c159840754107503008850603130006980042e09002c012415001d0342c141c003038160203c4800d6482d003070000f0581200108600b0212000149910042c1d1081c42162210500503001e0f00031500c0e49c1c505a14580d2003444207a400da000d401d42001710b28400c030102c0d090005c9c010070070760425a880c0b09900708041c140c0c6000410703100030015610a62034640e200f681d1003507541c00005460182d120448104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 917544793 1250 917543543 917543569
    0x109060b04051815030109050c03150105060406050d020d180b0601080c07034e05100b0c01090b1e0c0a0206040b070908010912020c0102010c09090f15060806 69
    0x414400d00042c860340c0c444194125220302078414104850300e9400c0a440c0c408050702000da09942031000b0081480800680d41c49601d1040c2c04440c6407190410705084003c0003030044c50b5019800b000100b0070b0921940c090040781c07442c10340062a0150f044c0c0c0203022500d41c003c1d445c106440c03059201c01800040682c1907400002800d1618152178580d00c1170201b84500303980141844081c900601810b40a80440c010401140b401c1003501c580c0144d041600a0007405e40ca100c0700c0000e10030311420311090044900420b001d00b42c1064290030300c0303095401034001c600c081d0001d640c0c9070b81c40c1700410306112159000308442c030030340e64080300b54410301d40e40f480004068074400403013007240c5030005900041c0e995101c0e030441d90800c02911921320484038003156a114030300075803c0503590000e110009500c1c00150b9100e40031924504041c000587c2a110000001e1005c600841d03001c00c28405030f03800005004421920016540300e5603000c5000c44419a0000710000303000d001002018101942c80040e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 917546043 1250 917544793 917544809
    0xa05010e070818011b0e0d0c05130e010203070201020c060a1401060c0501020910030605130203041a04141c03050105120d1209150e0105060108040809101407030c150608070b071407080303010906 85
    0x47c00c10b580d01c0d03c0709081040d2185078020a001c0c1c0c00b5004800003540003040082400009650741d04000c08000d01030340241803644014054103021614409552007100140695080e01d942da680c0b800394240c480c806440000e9070705540070012142c0d81d80e07800d0102d11680069440c002421030810003440144030039040808140b0b481007081c84013040400602044410340800103100e1036540e40f8054070000703d000d00048a51284e0002c0000d2011010380d0112005c0c0d0319501000f0a81e81c50f020402a10805c895034481e0790040c980c0c0d110010300c2800100c3d5075a084180c04500b50805a443c030329503003a2a510070071308a0b46d60b020007043c0c0f1000c0c050349400c500240b0f07240301a03043c6915540154411007804c6071007407100c07130040e00c0003900070030201484140f0806c1d89034640c0103500f0013818142c05440d0448200410726418100e81504d031041106071808030380141411030a10400c043c40f503000050680d00d5061a00c1004040401000650007909210010790b1f260752604c0548420340b032203508030b403070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 917547293 1250 917546043 917546059
    0x907030f0527210a020309090a0203040219053a03080f01080307021005090109030f050d0909110904150e0405160b040302012109051c080a05010e070818011b0e 70
    0x20444015803144000320840043c40d540c841101100303034030b58400e1790382d0140c0000c1c4107000c100301151694041e40c4114002d5442c8840d0002401501001081a00a5581c03160144c1e48825440c858168a0303007000200105071021500102107011a10840981c2200001c10410801c041c00488400107401050044020340c24129298000b4032802d0f40d03540140308005011400700340c140c0c422142c40c1c000315007101c00002c040c0c0807030a01c59200c0704800103000100d400b0034000604950035200e92442400d80c000c1c0030b400c0c20810420400600031403070495050301c644c02e0300420207041c4001b005000710b101350002c11910005030901c0b5401c0d8100d6211510200d0180020005070f40c002c1401d0b0000700c03001d002000005180500135006003480c00001e0254031592801d8180140c072480c1c0503119005a481d0700e80c00f5603070360312504184d0b40c0c24094545c4030003489001c280365034000c00005400200c03605c40c00154124102d07020303084444021047e1141c0b0168105d1520494100d8145000c01605542a80f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 917548543 1250 917547293 917547313
    0x9131b0b0a050708040f060c0605090a17070f02120303061f0f03020901020a1b2607060c02010c05010c0905013203060d02300f0c0907030f0527 63
    0x480d81d0244031440000d10800150240401c81040708480c090700125902105542c2c03038010081000c2201541180c1280c62301e408502c1c0281d0020344503d2180c0d01604400c540c204403d2211410b40194001300c1d060040c100e03003c001a6203800311520541440e0005640303c0c0b801004105081c0f400300c4000c003040d9022182c20380c045500004040c0d40c40301da0300f00035035100d800d100103c4c138160481384c02518202084640d500115418031010040b40c1c144500a841d02c0040d41c1d046200361a80c10150303006500440080003181c0c052400903050314014105545440810346405094580200b40040003e90140046c000d41d03030042070b01c00c0807100c82244e04842c00c07240a126104081c0d002c0b004141d402c00800040c04079603503401450501580501019045080c11401944c503130402d440e280d5030b41104203045204040001800300900803060002c100e02061313041031000c9080042c01d80410181c5a000e40f80b0350340c80f0750017140c0c0516035241c0f40030624818018201452852032040310443e400900703541c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 917549793 1250 917548543 917548559
    0x6180607112a060d05010e18031e0717030919051e1c020304090509010e0a080d06090207050d0e0a0f2d0e150103050c250209131b 57
    0x2ca04480950000701e002002841060481d6600c01d0703244507070202d800a8114002d154039009079048030f9001c0014501c5403180d010201e000070380540c00400d00e61081c4040d92840864580c0d9441040c00c0c20440b40c9029a10786a0002e4000c0c0c020003003031501d80000178045503907001c000d2075451030044508110003c6050b40d813107485500003004071105000c0401c200b8520f10040c0108411101010590308814041c3d0102a4580c0c00a104035401c407407401000811580040c0a4036080c0c035000d20181c07849240035591442e13550042c01c4180003095440c03030041601c0c6158801000d0300d50044005080a100e4400010421818400f0f068020a0b80a8040043c05104040c5409482c04115010400a200b000c070258241004c41c606c416080c0c0c1ca113000550004440d23801b0f0080e0010081b000b80c007055207005401780d40c41940d810031f49c04010024507484070b19446ca4080d22488180c103064240340b464000a50000c82980c03070611001314040d6003410484028a80c00055550309042d2414610344410307 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 917551043 1250 917549793 917549803
    0x7030e0402090607121e0f17070c201e03011505031f020c150f07020d050a08060310090302010b01031a0a03020603040c080a03020304050117060f01120e0618060711 72
    0x281540020b01c9204105c2c0d00482c001c1c4840480200c0b251403140924500078000090341c03001c903002c9a1600c2d00714107100d44000c4241e2246d281034aa41a000031550b59000181407502500d8040c42c10340034000ea015620340c1203141c641d0b207100038026000d5503408101400c689207140059019950404104010348020860259000f8000c026229404000303006001170f1140c480440001e0103402d4094202078040100300d4040c0902810340304150f41c407400240d90f14514210304e240400c60911824003028411408554490700207010760310107000c0078a42d041a6904c200003140540d440b0038110115581c188a00e0911740c15502c2c51004981c2018041070140b4141d00020b4024680000050300303000b0410a00c400802e00d00c0e00b2606412202d0400944a8200e401807600007030741c0c02e034013003000c0c00c200c1800e0b4000c04d401000b40d10300f5a0a50010f61b09250005032840c0b00d16262203907041d0131042400054464561003841010b0070411402c6181041002070803601070140c50341081070340c2d44000036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 917552293 1250 917551043 917551057
    0x7030c03050c070909060903030c02030c0307021e12070825092f040614030126010f02040602010f0e0706020d08101a0d0506010f0c06050c0d0603050307030e04020906 73
    0x4155503982011000c203070a110300c5401242d021401c5c0310400080001300d41c4a40e44080c081e0742c0c00c005145500303404980342d21800d4030304c0310140d00520400000d49001415072a03d00034085508030310708013150109082900300d01c0c4030201c54100e0701c400c110a001c1803186211209802007041c1c82801040b00c8600304582c2c0e400b070130801590b10080c440340c6045e5058014035003540e0b80c12044103540141560340c0c0d036502a0082100142c035100e204422810810142c0f4140d59402c0da9441002c090340070021821010b6a0541c04d042d900c8815001d54418580300078005002c2542c000326030601d44045070703020788003d40b003500c150344e0146e04104082640814030602402117032421002c0ba49911010f2003000c6150707000414071284d644035040900c91400000c0143c106400307000c1c01580d84800c01510f03582c0c00781c02a040032030510244000005c0103a8080f590010031007181c2070400e0900156001158080d4000f181c0c150f00c0003034410103054022280d241480c0c0c0466080d0720380128100800ca05000e050303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 917553543 1250 917552293 917552297
    0x90702030d0e070305031219021608070f062c06010308030712060302060f0315090c090d030306080609030345010f0f0b1219110a0305030a03050f060607030c03 70
    0x61500c0340203001c00c3c00f065000315000700890382c44410040700a024450262030110b803011010043c0d00c40c0050300c2c02907031540e208403039100100c4130041e1100b101c1980030f4681142d485154921a000060285c4141c10100103458a1f840886440c2c422903844541c0c950700642c0c040d0701410040000480034800c4a62024951525003481c9161260302d10180015802c0290b120380c0225024411404070406180b01d03000b068003200c0460603801c18410202e105981c092510402042000850309219003024515446494005821681c4030001d42c01c3c00020b948003000c0b508000140324400b001401c5902e40d0040311a41d5040468081d40b0f80941d40e80301c0308524142508a00002131401000c0d40710540c2803078421001d100a04004023500024000f00c4071603031060744082c1c40e000090303400040461944032104c4e4150030034040398075081d01d07654000d0b00b890b6100c0d081c0300001c00050403d0000c5c2031444225100824507003050101d107040c440c0005c02031070140341d041c0041e801199000b400482d81da074240c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 917554793 1250 917553543 917553551
    0x1b0d0f0e0a05240c16450513030206180601180237030c0806040b060c0d02150f040506042028050109050d060506040212090a11090702030d 61
    0x255492441c3c451002601407000c000071401c03010601d03020401c0808800d141c42030410403034881c0c500e043c00c4282503064120040c1580340064a004400403c0c0d161801003070260290325040c10810016108100d52402c050111003001604050301000030940124100c4002c0500300082c40ca103659914052041080703200350030070b07006071864456044030030744109410b00503580c142c03400d00300c0012451110401500b00010080e4640d1030300c82e1192904884c0c10b0740c0c9034a040d44950041002901500c3d0f509a4814400c01c491100c4040422012803548901d80207480b10280d41940c10454060090440d0300f0081c041c0200700c00100003041c210303403240e40074903900107200c4420071410441d01d000d01e103560000c00319007550408000140e02503d11003a02500031700c00e0340c1c035000111035052070340c464203401c000d990349108000f0b0060741180c0d522900181005003080c209248514041005480c08900d68120940b42810f1208290180c20355400c107498114841c1043c1400950317920070300009460490751 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 917556043 1250 917554793 917554819
    0x50603091032040209010501030c21110a0c0308090304140603041b060e0901231c0501020a17060a0510030c0c1205040608090a050a020f061b0d0f0e0a05 67
    0x14460518041c0c110304080c2080c1d0b0480544404120b180640741030384203a91301c0700000b85a40c803900501e0390801040d51a5500b689902008004c07031483d04400c1c2e1011174a5500005a0115440250070860260358884425030f451f401c2c080d0003183c010b40800c0e8160410002881580e60b0142440001c10b4251821603482d9600d003403c058880ca0300c036000010203141c080010716a40d2111720030b410705008a44821140c0d03600d00c07030804005404600b048001105120b003a81e145403424403031511003441003100600c2603907956424226030100e02c0c0c000105104080d03503d0400c0c68020515805481504d54030161421b200010300310003d4074990030205a260107121038800e204d60341d120707845544641c100c6647e9a02640241854015014940c0010130318030001e18030100000b190404190014003900c8002065000d01043c48840480c0710f07000001042801b0240c1c01c91480b03014820344041c00b604540b000713180020304001400498100300910540c6030503040d500e800d0b109085070b8003110300e801d544103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 917557293 1250 917556043 917556071
    0x509190212010e010501020f071d19020a09141c0816020402030f06040b0d03050a050a0528020c0a0501050421020607060218060f0304060c1206030602070c0506030910 73
    0x8954180780a090410100001d044060301014078140c40098003903a01d050403c14203540d969181d441500c0d0520100031003445a6540804a160800800c14207015015507200d04075090341d009031100c40c009803c40d5000c1205183d020030925240c802100d4128560180b007040300c440090200c4094400c0702e001650945988050291000303d030b03030144c015902ca20304504245114a02291b0442c0568202110100146408400c00d07459550680f2298100703100d1100843d20b60f0810000320301031000400135128680e0300c40c98229481c0410b071824026581e0300000c000d007000195000c0c0ba010f100802010f020356a017100c00c0d60107882c12542d0400050142d003140c3e184841010314069048800007800c1da0a01049030001d0014400c420b5420701090301c1d84052000d940301c2d070440001f0161041c004900003031504d402c1030347d2451700c1d1b140244000c0d4000404200304c41c1c0540c4110382c4544e00082c4201001140584280100803c40cac4081c114588104140d81b01c24072903110000b055542c4290f103031810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 917558543 1250 917557293 917557297
    0x6030c0210270503071e0507140d020a08060402040606180b0c01060b0f03090d0903201807050c150601051e070c03080405120a020109052106041a090705091902 70
    0x78100101c5442d090001e003007298990303100d428280e0304201e80c0000a040017002103540c2c0c09043e40039005024540c0f403c800103480803110002554401000c0041c0b00c096030382c07040b516000c0c01d424000f0389400c3c2058030400044800035804403091101038004003207640000425882155120070605903038040e644c02d51341c01020b191300803904031070020a401c070f8003500f60409176114005150848502d01c110141c240c0744402144002408100124484110a002c1250045601001a1602e1510f429002c0200411030048a019002070b00206410b803040d0400c00c80ca1a00d00041d8190025034100400001d0491043d2f034540842d51407880f0a001c180d82280c0f0842e140f0a4020b008018141d8a81c580590a64801e1045034400d1701d00446900c2c2410011441040c4541d05840d403070b0a651405007132100c00e50f02c41d5075100a02c413007040016100941481100c4c4203a2160306880401050b00102d440080000b52585046502c80d01040c00251598000707580c00034180303119504c007041c007011460b0282c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 917559793 1250 917558543 917558591
    0x80c0105070507091d102009030c120f0d0e030a060c120216060c0806010c0605090705030307080c070b03040c03260d0609062c072606030706030c0210 66
    0x3c50b02d0001c04040f100750550702c00240b54251010381e095401102c8802050319040c149246416010700640144190000010714583d4005400e88180440c0c00c40050004045500701070f04039040328cc034000d00c3c07c205001c4526000000e0412404601d884808255101c03881203000f4201d0b680ca0707000341030315809405541589404040c0a542d120800c400d221002940d041080360040d041c0010040d5150055284500c9414180c0d105808000d00382c03039140241c100585240080d0190000219041c0c40500040089602940316569038440c048810b902d4200c207644a031074040410b1092000042444404404a90304590600641804a04441c1640a558440c20f41e0140001240700b00c41e2040c1d0401c208603100c0c1d50082084a680300300002587c080421450708001e100800f0040c228900b01510388c1000c0245840d440441454420240b01c803a0040c42c562201c1c0781604000c1a46002c10594015010310b1805204281003803101941e0303440c5500303100c25000e4403484e0b11220742c0c03a02000d038400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 917561043 1250 917559793 917559809
    0x10c1421090a020117070815010e03071e050a05060a030e19050d02010c09180905100e03031014010c0f02010c051006061101020901020613060603081201051801080c0105070507 77
    0x200e0401c12103560361030750501022804600030120407100c40780456400d51040f00b5946a121040c3c0d51010145640c101c07480e071050511001e030b0004030950300c04000540c054850003004004e50040fa81c50703a050080c0c0d5a004920a10380000e003070240381c4492099501a1078182800304e020280c9241a41c203042000d10781c1c1c00103940c5114200240440003071800410000c0350020000c618401d8000c896080850040803100c2c1070450025256003e55480b2074045c50060055035a4000742e5900c600c00d941845403a003003180d001000348626032160083e400014076201d03041424201e05c400c006801000805c00241504464400c0c41d000e43e4082c141c90711960740d100d030549010f03620280f084c000900b100d00400d00040c91040117441c86d03500c1403089600c0020160020510b560301c0da547c800042d08001c4080b182a51500390000001d046a0f025051b5950315039400c00c600e40c106010f001e40781421481c541d480e1800003004001c043e10100d0038000415080c601166154070508189240c954141d1007650 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 917562293 1250 917561043 917561107
    0x180109030c020f0a03030906051c0615020d0e013e010204090c020304080604060e030706090c050922020402030717040c0317040b0307050a2c12010c14 66
    0x41010350207080c141c100d9200712050025002c600d424007403103810740c0c007008020898026090101c580100080c010b40d44640611003000b016441c0c03868140c0d000d95000c05825204e680b42c0395060354040c0081400b800c25440e0a1b0000424540000c007001c101e54100860145102c00420712031940000d0401c0c5003c28035001d90742c2105011501c0e000f0b51152148000c2640380203042aa558808001c032011035210720000c105544070341c0c07030f604000c05d82c0102c500e00600c03040020381c0005055000d0000c4090040d01148202480c2c241481034210000f401810365404101141e504004060203203000950196801612580d800109548070280844001c501c881844200000c00035900314400c2584e102d101c90711141c2c116594002014005d0740240703480440b05200203107501c3c1c07240c00034240200841c500120306031003c4200102c000039291540403951001803502c0d1a6081c81c0e004000840801002003048000c1400b0080aa81d0010842c3c4550180019035404001442d502c070a2400100c5181c07075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 917563543 1250 917562293 917562311
    0xf15010509040c080f450604031205010b0a05160503450603040f020f060a0807020705060a021207140303090a0b070f0e01080406110f07052505091801 66
    0x14040a41c1200c2419000411500141c5074a006c1140900010b000e014500e05852034503680d0041c10341541c13500380c4501b050000e144840f02d0104581c0e0b0289000c0c0d100c00002d500117440c603200b903600580111042110801070b04c0740d480c0d40481180d28038a0501c0307103011040d03640d01d0014298403510400e02c0300031800f0901004241c110348001d00c1d8450102a04502c01031816201c89850441c035900294452024400140825455400386000b10f200503c00003810881000080c0541c010b00303070b5640040e2444c401c00088640402c4024041d143c00c40380c0600b0601c241074000e64801e80c08820703003841c01000c140001040340b40801c1a4505c800102521388074605600320540d10904038209591803180c0d407012849450255055a07060949035036105071131884800103440e1f8140240c0b0442340185ea881456640b00d82c40303400b034400b8400d00c0000c5640c803a590300f45a0b00e450240f00c0b4440c4085200300325040031581c0c076030800045400c10703504490390350b4403501900451040d21412102e030b5400d0140c89 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 917564793 1250 917563543 917563547
    0x3403120608030408010e0115361a1c02090c090109081203091204030b0a050705091e12071d090a05030c030418020a02071403030c12070b010b030f15010509040c 70
    0x410091701428008102c2304032135182c12a8a000d40d841004049001d0001c0070f614001e42e142c0d2030109a0020340c400c040074540b40c800400320303600c80000c5985001111038660b200e190207840780421031000006106142e203240c0000301030b448090147c11891800040030f81050340501d81400c01020200b080d0340a800c83c2d03040c681074552088a81e08054000c110003c0800c15180e8107850a5035000050b17800c5940d40d002c0044010800a800c0c0320611005020000003940c072541d502c01201000c010604040882c0b009000d801c8441c1c3e0403682c155005108240400000303024003481362800706c00582c0682e110241c1e103904005036002c1c050224040055000c4102d8000030043c400c8903c140706903481e1a150401c004100c0c020684210010781240408114050309100f904104503002003e0782e01d032180c4900b1891421042204501c02c242c6d0205011b000c2c007071810640c038010440d1048551030740c50a040c0000710400c0041c0469090030340b402c0020f00303c0e449841a1a600c50b0060001c00040c01a5800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 917566043 1250 917564793 917564801
    0x2120307031707050a0e060702130e0f01020f0304120e0a030804060810060c0f170a090305120c1e0703140303091b010c030305090109020d08340312060803040801 71
    0x106401080b050203035001c5610007040820300c102d90503a6090700b06101c503001100c0441840c10300c01d52142080c004400541d5400640c0c8a840f01d01450010f203d042c0000d44d6410703c100500c100e40940d04c1806051024100c110480c2c1d80658811707400f24003c510780782c0980e9503000724a1420b07002140000040104600540108180e800c00c1e00d5800a641d601480008040c200380942000070b01075008a10018001c01d081c8500306109080c1e145401c0c0c5d116040c00d1941c0c12030708035080047c600110400504c10140001d85502120311007941c46c00d100c941d21203a0310740501140b0b2419a2040b945030141c078400380300040107140d001c1e0309080d14111210215540b40c10940d88845940100e90751541d8126081c030300e4002210b81a1a1040c3c8100c054030194014480180f40340c005540324001c0c540141e42d0b01c00140c80c883d10030b291a44d00c500b142d40c40207e2003244814500b40c02c44041e421100d001404e8070710b010b5503507413518101d07261600d071100c000050070762540a403c56110104c1c0104070700d40103401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 917567293 1250 917566043 917566057
    0x9240f0a23070f030e010908030a021006050f1c05030c070906060e010807021002130b12041406070503061005070c030b0601030f020f0d020702180c03040209090a031205090a021203 79
    0x342010511141103a0400901c0b9000340140303450842c00380b1030000f0380120084024290141440b600f6039544620310350440d407212140c800142c01c403180200340c04040344110805800b044e594044405040000300d16101c54003007000103020407581c1082d0801004104445c01d01c4100700956140c1e960781da441c0c0c805090a8020302c00490071800221500303511500525202c1c0c4c40c00c1d40100302d03005800210400960241d07444550200c2d04841c046a0408281c009003940e4980305104442490305017085039000c0c1140b100d50403a50000000d204c2d60300c0d13101d0b01ba29000340303040b52070200d0350f500414203580d03911811030002e0100c00b0310a400814090500d13901842030000380c8007072120a200c0e008440c01c84c81850307094208210140001c1c0312903945030340907054161000e4404071000d089040c00c07080700c0c8800c03241d00e0703410103001041204600302075040c90f802040d83c1008048141a5a40c05441600142c050071002035480d0005101014100042e40f48160060840201402114041078490b80440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 917568543 1250 917567293 917567327
    0x14240d0f1e1b11070f0b040602010e1b100306030209150f0117040b100305060c0403020307060f0807032004030b0a18080d020c010609060816080309240f0a 68
    0x445441000540d03008602411010b40140384030340e0007418055070890003a102c40d0b009886a400082008545619140050300130411100d4403645858002420b583c0d0041e100e051542003281000c02c042d6282110082d5403d01b19a0b03c4032070341024000710010025544060b40c02401c56050148070b011071586101c81040540c0c420162407448030064500c0f180c0c45104c103410b507118074002404074403c050003a40103414044210081c0341d490722100e01c0c7c18001e994030300c09648000b4041003189070070010f8200901c4a07040c024503040c540840070b0601580104804241a200c00d1100900300207441801d002e40000d01400d42c8850700c9041c030f0003150700200c550050f000c0c94440e0b00c0c4042c0c11610f40107240c00c4e0340004001c0c40c200101300818081e40008003044503c0d0748520010035410a54001c640244c824040288100326041d0704003105140258400c3c0ca20350404c00c0806c0d021707150000d01460b81c00703c04217120352950f441008960a0700c1002c400000c0000041070b052902a48055000d0b2801e00f0b070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 917569793 1250 917568543 917568581
    0x14040b0406061206050109151202090a080d080a0603080405090403110d0f0e0a030b010312020c0a0b0307080a0507020607030b03120a090816060f110109050d081014240d0f 75
    0x16030f00541d401f1001e40291004081d10300e20105409109500c041151000340b8005400c2c0055180400c0c02004590860702580d0400e002d0340001a5101103001d500c102d445009015092450302c8140c0988528002c41d070041640d00001010702d0700030ba0403200d181c110758045480ca440d00c1c5000074005607600c15058005081010710101c01e1520750340480070740c1d4000308140d44591a542d502d45203480709404003401c0d13008661040d051940c5980d0071200820001229694031714050074000d048200003040c20503a0f03803404c2c05202c40180c0c001400c0d03034007205600303002440c54400030000345400810642585050000036042012036441400001100c0c6100101c0f81e8064407034094241c451900d008003800503c003c403250103042d124481078040b14062400005a101c402d0701d0303503820240d400104502140155042c0100320780c213880c3e040d00901d00104402d0b514991140000e05203050800505107941441b0101807041d0000c40848040105095040010500740003518000d003c800500f54144014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 917571043 1250 917569793 917569799
    0x171204111e030706031d01020412030e180601080709080f070303030e1207020f150304060b09010f060504090507020705090702101b0519091e030b1f14040b0406061206 73
    0x858030907144400a001c3c3c0510380c200704040380103102140f000308480d540300d43c03800e003140000e02c020000381506902c8000305030042d0502500c0e44010841c5680103403c080c480c1181d100f840601075401c25030901c0d2094554680e0603045540100c645c101c486d5074001c0780d0014880800000b04a4216482a10140201d07000c10450a484003044800080c501d001001894014a4509482ea118000c01421044035810f00705a1010680044904489155403080c003081e0034a8281c511a0042c14a542e0080086051000080c00350150b4419001103e0b100c1d408140c1c03182c002e104480c040d29000e44803500750f1811020003592404404a4412181e14009507000500104d24a8132680d54058950030b00d000104000418048110340190081040c121000300344d039442d013800c000c9190840b8031010090382c11800c21062241008d086078441500404104134022104032412003190b014000e4000c41442c400c3c04940900f24a584855002e840e00310046029500948100b10b0780307032080400c2042c0380d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 917572293 1250 917571043 917571079
    0x10f020f010c0801030c0e1b0a1407050a020a150c020409051519110a0e011b0503030c07140102070b13110d0602190f02070510090f12050d080c0717120411 68
    0x38103403040060f141c804d1030142d901c6a10323080288000291494811000554900c81103c0d81e001010100c0c2c4582003804414254a400c4103960301406550300240004c041941e0f0181150b0072040e0000e010325100d0310000140581031210b480b070030040c802010003518110940081013443d07045070b01c11141ca0440f41001800b113000076549000c00340c0c0c542003c41240c11006440c1001d42542081d548041c102d01840060401d2019600441091407043d480d40880d1030800325201015400e40314580c8140808000705640c50340813504211842c0c080d0003a00214244500c059540e40c10a68000740c800441303000300510b550003400e081d40c0c00320507101c001d552500e08032000040303010007000580c8040d8044c0160f20300b01034211804817050a00e030303003120b40e1901180b244103c0d550100c051000402d42c890180401844000303071540f058a8128828030b070200d28a506030043c0e14014001c411a0752580355400210001c454007004899001101441c1c40e01d81b90780d04041290b41c150040240c4410220912 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 917573543 1250 917572293 917572319
    0x120506030d0804140714040e031c02090321030708160e0402250503090f06030f04080304020609090a0912020a0507140406050a0e0105042702010f020f010c0801030c 72
    0x4401030281032444544082281c403038a0260066031141802c0c0f0032000003000400085000b0704510441d06010300d50201008101c401800c0201146e07001040030025648002d101e6058002142c50016151049480401d00d420007170ba0751944c6030341d25002170301c2e021000e0201840c4120001e44da5201184e440004010700d504480036050b01007001d8444421861400742c000d07111440c5000c0480c02c1006190050580302540404140c2d071a4200040040550411307000b40200700c407040c0d82407465800c0521809500c000300600152440b00044080382c00c642c0e40001315042000010041398050070301c4070a50000b802844000c9403c0c0140b03c540c007e07a0360000c1583d0390f5564101c0064901075241002c00841040010441c1740d2042d0380d90b03c081925503860402d0000380005030200b0110390f0405043c80b08407641500203085900c0310b41203101454040c14030300d07508503074280ba001c54240c0f0000c0e0140d25015040000c2903d950030702070403109855000000318100d0b806002224849986c3d240f012902d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 917574793 1250 917573543 917573551
    0x1905010504020f070b220b061005030105090403031104090609021b0715080a0b031911040b0d080d0f02030901091a0f04140304181a043b030403030f1205 67
    0xc0c48107100c82d1010401c07402080d0f070310a5060b0380d0110b0001e03040f080d40c5500051b07008111040d40080043c45881c6c204158146440d04240c03d100d460343d4103010000e5801c1c0340041004080603120405030f10f8404160301a1002414100000d201c00d540b0307140042c000c1d401c00d442c25024040600c00e1808000b0300000e50030119140c100100c1c0d030703100303009900f1070f1401c4000700500d040c0d581713407649480b103918100f000043c4a120f84080414545991031320004146565041d184291f0400d00140d5003030345d0754804485c815600c02400c5a03142d4140798a28040d00ba0300248011303a901c080100020101d064000c0011144140c841d960581c00616640819900565141d00098202400a00080c2082c5602c041d4071035400300322030400365940d12109418100e9080001e2880e00c5082c4c00401d007188003d10000301c0011942400400e41c1c031031503016407600001c80c0c00002c0300c20341950b0240a003580c0810002c080c003c01036a40e1341d911382c240509004035102e59407000030842030030248900c43d2441000c0c06 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 917576043 1250 917574793 917574817
    0x106031b0815030109051c02060a05040b070503220c18060f050409020a12050706110d020a1e0206041508060a0f03060506120d030603020a0b04030302031611030303190501050402 78
    0x202c2c1c0707a1124090860810744101d580540d40c2d202c1c4007000ca101004049804000d004881002650442c0003d052001c007504243d10700342007906001c0060f0180340050f40c40701403481c00302d440759a1032803840f000d100046292400000c5240000c4d041c0550307914240141c442c5a06964130012102082204a5281e449000155094143c01340640c1c940b5420000c4c4880c00200007a401f180c95910030007210b0b031502c404403401d0b840554104035051300102c94800081c5884060f00c104050f105c006501c1c0c6148060082940f09a011110280000791071001810398000e003010307440740c1e00c0f0321103502c40300050005000891302480000e1924584a00150151407012407181c10251030755a07668043c0c40b0107410503500c01c1d4100e2200001100070050744050a103140c0c5d000c81d5091941c010300c940e80017142c11909a002007040144042900081250b149260740268403902c03981a0074409490251501059418080081030002e030b40400c0700b00c00e070131342440c0c4020030039a41c3c0c07001000224401d503c18042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 917577293 1250 917576043 917576057
    0x308011e0317040b040b07020307121a0402011e03050f061c0b090c0d0f020a1a09120c0303070c0e0919120932030303040c0314030d020a05030106031b 66
    0x7001450442c440700d10b400c10074502c641820344650080100f50400e8000072200440400c90805600c4c04200840080113072114400c3c6911080e2103d49800c50038100805c2c40b180c0c10f030007003011a440b4200342c0c010501d40184085140180d90401000380c0000d0310160000381110010901e98940460100c0f49592a919040b1201f241036440b10f020303910040082e941030144603414461130311254180c9142034402e805410a0082038810403e2400d0207800c0708105c408074800500d426602e007011543c00160445007000c4890402890a02c1c1001c60400c00707801d40404282c40341000080e0504405541e1851b0f480800d56981d0490386680740400481000c0d0020300c0c00541012500c001110041c3e1007030362400c00e03219511100d00c215141c01c8606001d040d01080660344000388a16442d205250a044001d94a107003001d031100343c50310400380806800210950445610703004c003001104c4060706143c0080d9180c055202c0c3c05015900244103903c01300341449070300c0c075008800d40c140c415408000c0e120f1031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 917578543 1250 917577293 917577299
    0x50d0617031b070b04030f05011b1b05030702041b080c2a010b031c0f0e0604060e210703110111100b0301140903091203040e07030f090209130308011e 66
    0x11280707604156542c0329004504012650b0032078180200702941c0503405a0300a4446494680d00311007445205c2a58400104480000d0795032080e6614009402904200300541050a08604601c42c9010083d4854075150340e000404500d4902c8100e034090a4907002da680c0e07103410035005103100703005000c0c001c40c0325040702074400032018800720301c1410705600015009000c0303c00b0924010f0a5000c034212154100c01c122385060b8880340040d42c50b00c55113003031146003901101050660003580500c0c02405400042d0040580303504242c180071441c1c111858480c411043c117881d84809550101f034a84102c0e2000e040041e500444901d00a441024000c1c00c03036843d5025110014107040c4d038501c0d819525a4034044040700d0304242540a8a030381c40c00355a56000641c10003281390100c00b00b0300070913041400104000403031262595030000e070b28100452883c010300d941c80000c00304008000c0d03101840c6000e115408805c200340340c0600e032094880381c41e140d03203400080505c0c10b0848480040425204003c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 917579793 1250 917578543 917578567
    0x12211d090a06031a090c0301151404150905011d04111203040f060305220201020304060c0c030212010b040e06060d11030f060c07031d060d021804020307050d061703 72
    0x1065212240710700c000390041e00c0f9034032500b0301e060541c114241a41c0c2e44003480180342d418000f0b522412401c900820400780d550b032000b203190f9194450614210b503841d01c280110f0300d550304480b42c04904032015561503038540d400c4400805003030280000302416004954810340342e1242c034a00858000411181484a00781003121344101c1031151041c5000608c00010a10100040326000d4038044d20049041d281441c01c500364038200c500f40c801c04190003a0640050b0b60084121415140701d481c00c0e111014080c10440d03240801f40e84001d4020010303c4140d40345c10019030049140b01c808a8003440300051262110b9074400302502c41e243d0110854400740c0008a0910501f900d075840034068070100f0104041c41400d1400c101c2c1c03031561117900001c900c0300f010f030302a40640030351141e2050b420480000c400495202d000711402401c441e0790010b04041810f2580f04070100c0c18200520541d640d01d007100009205400c65031401c40c20340c0c20b0a4000c1014200d2180a0b2200035410000b141000320030084 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 917581043 1250 917579793 917579809
    0x403052103040f03020c2d06030c0f0c011e0902040b01090305030a110c03060708010501023705010f11220e0402060a0c170405130c0f030b010912211d 66
    0x131400e5210350300140105840301135210100500542004100c02c10f00c80c0c10f600c9003800c0b9008a0b200b10001c0080121030300c540c40030342d0448629401425100c0400d81e0142d070040c511140ea40c8010070f46c0d90300c100c154104a822601c0d020381300f43c2e024000000303c0f800540b070352a070354000108903800600880c000305110f01d1559aa0414800403140850000c1010a040110580c0c103400019400d80040c0030079601005490a01141000030f101c01c00c69007008880c0034a621a40f020105080f000c4220900109400802013001d82c04d10400842204046c1547c0f21b9120309244140c2401c1c008680075404a0441a0001c66400c3c48840942e682c2d0303503081080c40e80c0138401c06001d200c07811505601180c4075400110700c0303030802c0043c3c0d0360355402d100400002c4040f0f006504081c6040125640a681d4440c04180c81c81d0b00b2800c000c20312a48240060b5032400705504800d0701308007400307116014000130b0304101c0c1d080300c4490807a50b00c1c0e004041c8201c859184105c450051008040b03042d000906090342 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 917582293 1250 917581043 917581073
    0x31401020d06050118092c03070201032d0c0e0618010909020405031f020c06010306020a0329010e06190801090609050603030406081b030429130311030408030f040305210304 76
    0x503901f0203220031082c00c901100b9107004c0e10885030340041030f07690865805108058804c03210f20001c0010403000d44044500101c10070702c451440751258007007018540a8601e1091881e8010f142c2c07501c070b041e640380b11403003014580c00007030000300701850000700d441c0c0d20710803a401e81c0c1d0060090442c1482040250420204000015000c2c0c1e0742004583c04524080c440c0b01d000c0d610400d0056034640010780c0040903039805500406082010320840c0051401107245240c10b02c00c01e0906030380700801c000c00101c99024a030390001d0004038100b0f840341c2c40740c1d01071a034606235207540804000c40c0d51034044400071104100d0750503401d40c0c0b0070001403110a00840d01668400ea5078101144250b08d10311803881c058109940440e0000200c1028900c82c0304400d40c22146860f4070182c41e00c0c2da00e08840030108242030313800d015052008114009280c000c040c1308880140149400710b1340c1d12001821000560303400344c03005490780c0c0241039480ca2401021540c900c1480c041900d4103046480360b403070b00c141184800d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 917583543 1250 917582293 917582321
    0x4090e030d110c06150a090b0d02060417060c0f120c1315081810020702040b1804021e0904060c030b130501080d080105030a110a031401020d0605011809 67
    0x44074000840000d80075907030001c0030b01c12146880c0c2c0c0680341801e1a1a102904241d802e030315910b0b00420940340c03000440100c0da0035200204101461101083d44a4900071740070f50804000980440d415014411000c0403c0c102c0044502c69a10075581a02900455206102014003041182111201821190380140841e005d640c54000008600a07a2203107035400b0820050b420205030300515044040c0c5071388585103410741c2c03480306020b812003500d44862007840c201d85a404030304e1405545541d8015480c14101030304042a0040207a080e814007079040314103d1081944240d4107034500134412060000e0754001e04850340329116a50b0300d10103000c0803144802050360755450101150b0701c819403c001394000220014055050180c000d0070512000207401c107005074070b001000ba989001404d214010f0300081c40494843d090f400103050071180b94400342c0034042c442c0e8003031004001075008111400b0340620402040b9900e400541e1041c589a0615605410701034041118040d06d07003100030b03046184 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 917584793 1250 917583543 917583547
    0x3040c12031707030b090108010213150c0c080106150507031b02010c08120405010b010c02011b02030f070308031e191a120f011107081801090b1909170304090e03 71
    0x1001c41c4500c240380484103c000a070700c07040600c2c480e082071030100c2d016204540003545440004440c40681480b188500064000c24202100340688116400c4240c258800400d600c0a9078440c2c4080c082d111354040c003088006a40074601400e0f00038011601556815210080000495038151808420b200d0080c1d041c0a40b200003d8001015000145503501320207024401500703103410000e00b142c00d2011040d05014191403142c01503a0410199955a940c0c41401c00303541c2a1032000c02e003030a1200410724550701c51500040204055000510703c1100003c0139041c02d132059400d4041505001e4568901c1615a005000320301d04143e00b10076828100712312420781c54040c0b00e010400b094001052110281c0021078400ca64410030700035034150b0350501601e142800480d49030050385100708003040354540d13a500c0303c800d02c071b9018003140300050425052164035000500701c3c0d128403404400100700002c0c81d40c0700200d21681c0c40210000d205d5000c600a500703050801801000408145500c01641c0c441 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 917586043 1250 917584793 917584817
    0x1b090a060c1e06150e070210020f040e010f031709010e092703040306050a020406020d0f030b030307061a03010608060604091103250609120213140906011a03040c1203 73
    0x4000d00380c00d9206050011315010b000da144181d991250304511645101841844080b544c000381c861503940c18030100580c1d0700403400498140d44103691001c40340080030400055005e0340315a0180840780901d444568a41103080e0030101c0d4480d0070100741c00708400c0b2030881c0503420002002a4001070805414600b01c0441e5440d040a21101c40c8600c0385520008080c810400e541c042c094014014150540c105800e000b00a91210300d00800041040b4403c01c843e180c085c401c0d0407040310180e0107030a40307a4400c2c49044c00405400c86202007114041a00309001603030505114010440300314101500b06034841c081000050a4610825298003c2c0c03103060094980c2c05100c45074150064002d6803450b11201340c05070b05183c0c0749070f0240e030a1000307144040103c0c2d851040749104456048600410900b220310601c0c004101d18180000500c2201c001c0001e06000043d070316050f560b11110552800302010a561300d01d100c2200c0003401e158445108201d0b42e0310b9484050000c81c80b9090015001311 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 917587293 1250 917586043 917586083
    0x10e160f030b040f052a010201020313110a1805070e0910170106090203010e040507122604090903090513110f03090705090405010f0612081801261b090a060c 69
    0x403203104c1e038490400001c14a40b01c07030010b03140008101b44280029419850b1506010100003003da0000e0550b04603091504456039903002c0d001e000c0d100e42c041c0c2d1100c40b292403180c00000c20046407042c01050201203101d02d01d180000c0018840e1020001300700d03400c1c0c1030000d9460803807a501030300a07166486500200d10032003580041c42c0070340881c44002c000341c501414050b241c519207510100b40c18150066010104141ca1b01d00f04070b0703072001030820600c010116a0031205200d1030740002c4c4014034141160041584c00b0004408440d0300301c90410002d180b100d80b12003121000643d6a030749500030071042c540f911421005c7c59000c030f564015540c404d941c07580480d0070180e0840d41165642d65403c90204034030b1241c8505400341c4582d5050152201290365000072500c0780e4074420001d4004c45081071405e0b8810007440d24001d6000404c0d04150281d248094103a03c4180c1d0322680182d240145803d4040400003034580d80030008000b50781e043d16001060303030462030841003510008000d43d007942d1a54 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 917588543 1250 917587293 917587303
    0x80a0f0516050a060b040603051507050d050c07030906020f28230d0e060306010e0a031b06020105010b071208040602041a0903010e0c0918030702030708010e160f030b040f05 76
    0x70b0180001e0018242d8615205044a4600300b400c2d1103285409000d2020800c0083c160400e0480e84080d60210748400d00b084c0d0f06402541c001002003400d201c20070a800591001400c80c0310300c02c2c0c680503000354507040c00b80d0f11485912808030855000e11240310024407025080403014285080c00310681d000c075141c00c03c02c11000242d02d090190481078400b0010802c10811110514a00d0040c29a4680c0c500044c2d9900c0081c068078104032400d4202c844039942d07091309038015580034004e42c001c00300c4c800d22100710800328803d410140d4a0b0200001b0310207501400c46a4143d03000c2c211500100ea054400d032a0903902520980300b440e03080c4004a080c4098088101c0d28102407504292221850002c15013540d03029840701c0d1071038100c0707214030540b602c5a076902908140f0144003a40b0405004d590075186015030607010354544100d040005007403030103503c018034a014100680340c1c0002e40701d4810000103014411065172408459040002c41c4060f5001500144103203d04c8450344119100d01c3d20381 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 917589793 1250 917588543 917588587
    0x105090102090109060302030402010806311b0207050a090507090e090a140109020a0e07111209010e150a18180b0a050411090d03020a0c080a0c050d080a0f05 69
    0x581d400a0014034660704929003d004114a180540c0303545000d900080203142c000e0005030040313010354079100d0702000889450350b880c00130041e5454155040406440a480e05110164004400400681c0c40c28404100703842034500240414409502e001c0c032440040000920407000c00c0b904c2c8a010520311000c41d9014040c3c0450300041545524074280314040001c81086080240e151400b00030068449560020464440701100c5c004e545c0c0d09070040e51032540c5d10006048502a40400d40301d25120003016001c000800e90315104581c00300c0301885001d124406412485c40010f101030200a0304c100403502000c1d40b03159400c0040c40d0386409041e0000607110400b0049521188005614100526030600500b001ca5003800a03e0444406940d98812500014010f901c0440c1c1c034000e040c002c024030344125034000c14070202242c2d00e8070309a803030340b0100c401100c0d4030807605000205450280f0a15502c140c200c034600d49400b8843c00d091b510046000c05803424000c06001040d0710301105040f040325 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 917591043 1250 917589793 917589811
    0xb0708091c051203060f010f050903030d15090203093a020307060c0305010f0915030b04150b06090f040b0d060e010c09050d080913090204050a061805091f0204080105 73
    0x96007140d8584142080c5502103040110752041c070402c8010750390090035032202c8000703003000c41982c400c04030100c425210b9800b10580512002845410381803080e030000f141c0090200000b403180f5150ba0342c29044e8442582c003440746038407895500c0d0095006002d0b11244c911600102040092070109a5402c9a42d188408002d0b0b000414642c0501c140c0740214035580b055490104100c0d07041c0301440c1c0c079012442c01618207450b87c83c00d0040303140008038003000c041d40e0410f07621500d51505190003036280b0003c000e84030400781040c1a070b03405070900c4401e03120682c800030144480e40d170010040c0001010403a40f034591200c03030b020080010500510a4a040030300c0c0000115401c1410240504a0a0658000c9020b50750f02d40300e80700490280c038240c4004800840c1c5241030313011100545400b611907141d01075441450141481201d82540e07000c0c9013260003652941d40e40d00d0b507503044e07541103c0040f42c0480d040c1d00145000002011a107090104401034040014149510b03082207030b0031582d0880301a41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 917592293 1250 917591043 917591089
    0x20a090507080702060106020706030c1106041131020a0c0f140c010908060a050c0c0f1b09130b1914100509040c05060702010504050d0f030e0d020a0b070809 69
    0x71264001d01d941e500c5000f0780010b040c030b5450010001c1d5100b419200300402c06070b540011002581c401da000c841410380060450351103007440d081c03407030500d03543c04c3c0014860400c0b0000364200030b03410300212140a05a1242e601c2d03003110765045102039407000d0314800400459040b03010010b4070f558450703a91603005080c85c145040c2c030050340a1510030f03566069070500c000401c0c00c2006240000b0a00d503c41803200c00442ca41d02d0f800303403180050242c424003a4150258403910f4070400700003d42150301020502000304030441040c103202d00b051051320302c0c1441e0610025804003140e8480342182e0019030324940305000d003034100312810444074502c80d240d68403400c0005001400452643c00d0010b0035088075074a80c17605007035036913407121a003030700c00c00d4003800020408209681c040c0f0280e0300103041c00741c0040c00350000d42c640381000118428040340400c048010240490411101d0f810300b01e98058403211441c1c2c18524410709940003444220f820b071604000680d401c5d1a001003264104513000007001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 917593543 1250 917592293 917592301
    0x10803041404090b190f0e0316030c050319030c091d060a1d09010b040c081515030106030c020706031a010503040804030204020c1b01050a0f2615040e03041202061303020a0905 77
    0x100695403c140500c082c1ba0802c000700d010f801012013180d007012101e41072818100307c80d00d0191040380441c2c4020300140008919409130030045102c0007200300655401300289024844103441d16143c50041c5074105806580c103103502c0420350603c07604007100504003110290707103003018146a01c140203800000f201120078041044024090400888022641444030124021009001010040c80412801c6210f084040142c0f24004619203000600310001e54075078440601401500ca606041d400500c2070010001c0c00074464403440740c1b00c10f1114491401d40095000440382034101401c02e88190f03008110010041e40c51348001c00c48100300700058607041c1d48003504000d1342c0c5010112241480800c0001a8071141d000c030b0700000d0072055042c00d07829800507410a00303070005a0a00c0d140002014014840c226100103041044044115030500407510415020340c1c0f03c1c02103204803000c4440783c202e924010f180c80c4010701900c3c4078035074140110641e2600000d0609443d030340900b0049680d10184 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 917594793 1250 917593543 917593591
    0xe030a0905030a020904080a0e0301050a0509060f0709150522080607031b05030c16142104050628031505180406050a061a130806010803041404090b 65
    0xc2801400100c0c05800042826000300f01e885a00a0009101400000380007902c2c90299014900039070016000b0446031030f0080c0c0703203001894290703003104540c1315120000d100710290b495464820140c0e50350764200145050004481c200344241c2c0d52040c04005d20403445158410012000f800c04004201188280340098085c2820710180000702003604090705481003560101011520000900d021690b1b5940c0144901c1907001e02d116415000d402200030105105180e020b605580070312b80d00f903400d04090220313410026050009201d50030842440100524509107010b0031640b05a51003c0c0e4034a03070303903045a40b043c071103c075140004a40d644502a00c25908166030001a01c01581d104555068410340c01e0f1454400800080c81c06881d603001880d420900c1d08a800141030303084031103001c03a2450400c26550b40181d94030284401140a00040300d0340c00066aa048415080c041c0d86424148400c100d442d407082441640c0040d01d40302c070800001c1c00150950b109080000d80c00c0c825079980070706 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 917596043 1250 917594793 917594807
    0x60a091209060219030c150903080105060901080604150b070b0106021b0d020f12030417060a0203070903030809011104290a0212090a0f0e0a1b0c020103090302010e010e030a 76
    0x410381044112030041c0815078001598510024100c0c1600310f403503040e49000c842c0c43c140032600038090400078240d0880419031741c022000301ca20a4445000d40da03200c41c2884101e009030340103a40050304160101d517503030a00f980321240c51503500006c26425502c80030f0b90081a40301c3c0320304490140c0b01c5c600400c0401d50500c4690012510055240f05110746000001c1c6c0000310142e010b03103c0e00e10f24000c142540d0301d02c2c4824003080505010340e602c8540e02e0580b441c0b00354581000f40441d004a10005600080d14401c507403089031540c85d0340540d00d05580302200c150304014424030542d07584002107014030a14001500c02030184189a00342441c0f40900d20200100b01e003d1b100c6400c5090114825598001c2441814104202040364680329900d00081e01001c05030b0050441080b800c00220364000b102081c01c0c46003584c1c19040c0100614200451048183da09a0700c00085050744403100540c4240c2103807400d10b0092001040811180c40082d0855240d0750b4581442e42c00010f95003150354020790 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 917597293 1250 917596043 917596073
    0x60c01110c0d1b080703030e0f01180209010e01051f03090c030c06020d020f1e1c0810080307030915050c010501060e01120218150f16140a0f23060a09 66
    0x3040c480149945184c050301802900a090544400c074100d00c42c982048543d82c00f00412009008280c2d0f05d4041490130030078000240d0181e55880c1c008a00d040700700607200c0c102c4501402d40d01c1d80c440e158401e28592441c91410a0415480d940c4840124400280300c074040d50142c40003600d03070f40c0340140203460248400703404000e64100e81c982c98031000001c5681c940f280d00c1100155404a0801e110a003000025880c0c401c0c1c070012611212202580440c0c0c03140309188000c0d138a4245615201001e98030b000d100c20040005828150900844820f21001540d0b10354504001d13082000b0000910309603082600003000203595080481c0c03440d83c0c0320014200038400c10804602d00340007480500d480040001c9510f018400c0c810102085c80481d50886902ca4042c070000f07610742d08a0001c01a15064003031090f03c0c00010282c02c0c202da6240420181d000380c0e48007442d02d803035010030b5840c0007a91007245100003802d190481141c003004414040540704c2c3e07000043c001020011890100d01c0d1812403d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 917598543 1250 917597293 917597327
    0x207230c01020d1d09040c050108060604030b0a0c17190f0225050a05030c0304051009080627010903120e0105221707030f1e0905060c01110c0d 63
    0x10510038240d801080c004244940d500d051210070800e1880400704c40340015a0b030f40c00180150800c401e004641003184c0503120241c0e54966561248001c00a440c085ca000251814a80d6170210f9044606540300782942d4503d81040104e6050b8030140785401303030f41181c0786001c01490003015684c940300c5100c1d014606444032030460a1800b140111003001c41d0940d4201c3d040c2d1010300000e024014104840e49005502008481e03840020302140d545a80103449030500500c030040340540b10f180910f044d00240c8804a00806c1103079944200403492004404810150300218a06414038140038018990030302d000361143d40c20001c01d0148003044840c0340403c008264544000e1014000f80ca0041d40f0818440008105a089050400b90320610b000f45c441c800500000801c7c00400d03401c081d802134600a2501c804101500410540804034076001c9442d00140b10098140818030340300028001203040d000001235000321059081e003c030392147c2c0000046a002c05a894103140d4032042c0a43800c07041c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 917599793 1250 917598543 917598553
    0x70e060c030d060506190e120102040320040606050d021c0f1a09090a0308040303061511100516180e01030c05091806040f2a061b1106031306020723 65
    0xd03010491b4190303031441d440700c1004003c60100b29030b691030882650f000d60201000b10342c1c07140e417881d181840e00031003120039042055107041c411040c580f5206207021110262141841e01182100d08002540b15106005000815080e04c01d403d8545218214007001c0c035000c0000c4822024199914542c01c20b07002c180316040383c074200101300c040440e00d07280072640340c1440251a02c9614040d4003030502a000203a9440300b894a12906542c800303035980e807460218007507680400102c011031040e600c0c100c030001003c1005090703448041c1d10480c4103d02c0c1240180e403580041e034039000009404802a031058461208a09043c003d9140000c030751500054550b510a510003080815a92141001031000d8040419444c40358188a2840c21070903511090b14501c00e01d00d03002c203c02000a002e64081c10001682c0e0085403600c5130740d02c22000103920380182014030042c0440081200315800244040c1e9050584800310001500c1800504001d602c2280d02c0700900d0140814011000d12a6045003a1980304c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 917601043 1250 917599793 917599807
    0x1120902130209011b050303220b040813030b0f060307060503010f06082517070c02010c1202011b050d0b0618100e100305010305160605040b03070e060c030d060506 72
    0x25803420a4074840c280e98050707101d0700a240141e80d40d188602e03049030410010f0040340c08025000c03004510448941c1c2c5000407000c1440030512034540c0d8a0801016400b41c94042408a202c10000d8080000c81742c01e94180d154580d03070354240401c402d8844170302d184403c0c41071012a00d818042d41000e4403907032402900b550705d810a21100311100e0b1242c0c2040c8048000480c0c401c107500024003088400504050052045010b0000e001014442002d10b5400700c00c2c0c08200c2a610400400f0400fa805030340d418803140c0c140d114410300302d07507074400e01040d50340e03501c0d161151b1031301208840000c6200d44c0f01d2a880b41e414491810988400b40002e6200b00d070100a4000c809282d000c0c1481c1e6040c042c0c50126809814183c19a000a5100c15095001c1d401140170f010b26030b859003000d41600d21410a882c44000b01c0300031214981454000c0102188090102b40001103092020f150b1000c4d00b850440f605102030804030303001e83e211b800107131000c0d0400210310326180e40600807203000340302c16281c661800c22 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 917602293 1250 917601043 917601049
    0xb06071a01060f1707050702041a0111120703030e010f0606022401050a090e0a0605010b0c1506090f040501110706020d0c02070f0504090507051e1c02090105150d060b03010501120902 80
    0x4501c0c051404d4111000c08a100c0c94411019070328061f40c090000c00040030030707048015500480e10784050000740b110100860717440b8085035140c02200072183c0d031800c1804a580c142c01070306008603000250340d079900e6000405101e030b01642c0010003054014008580104d41e03981c015918044920400a0040c80104540c3d2a0740000c201100d0030044001100c5020410580c1400d903c808040c150700d09120000ca00034a9840080815401c4142143d000e013008103080412194100e640c41d078860b48140001d00d100c00200b940592040c417a90000500c0004a81b040d1469008001e050302e0b119400704151140740914498403107407001e81d000400c4014a0402008240304650082600aa459960420401c602000060003404d0b00401b000c58034900d42c2d08000001c0698284e041c3304815034041032417424620080600d40c0707a000340143d4440da0a00c810b0140001c1c204500c0303d42c0c19800c0104518500d19072044502409030343c3e0199a89502d040001006a4041c580701d4642516111803040140c2e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 917603543 1250 917602293 917602307
    0xc0c0f070e010515280f020105130314160809040506030609300c0114011203050d2a030606140c060f10050a03030509040c030b030a0b0a0b06071a01060f 67
    0x1030801c03110b80c0381a07282c81c61303a41024041d0f4012811441c200e51031110006907201414818a2499034030880240c0090b00e0480c00e0b41c409441059090717451070640004203200d01030600c1030f160592202440c10928052500ba02d8901020684070018081052600f81c9814044c132604080110020103880c102101900d841c0c410341c0e285100e245040c003046180088241103c00c240c0e0040040c8a43ca6411583c4401e000e80304640311212050700401c00421044071444400c079046406070b64039400c0c911300c0207448000740449030304655203114840010b580203a10100d8241e001a8a40d000b080f064580301000d000880d41210401c82c401e4240b014883c540c000141c003560041e80c030103003a2490b496024106d0200c010580009800c00108070b4044141078200e070040c03024210640e020005280210402c9007241d2000c0c0480c4d506400866568011405d00180190444040d81002482d0342d1f01d04000781680c0e1060000301c0b10084882c0c007001c0340e28980740c3e0043c01400c030360030312003491120290010540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 917604793 1250 917603543 917603549
    0x3150501030b150307051509090702190303180b131b0b0a082a03010807050a0308090f01030641090103200411180d0305040515070b0c0c0f070e01 64
    0x3c0307a104a92005a40c1d03080100c1c100520002d403504908000c81444000c0e80d5024048050180c1131980203c1e5a035440001e01316041d1840000c1c00c0c1c2c40304550b0b60108d011f070505050810036010f0805580f0041801b0124031380c000c981102ca81103100b415440d000d5444e10481510020000038108108900c1c1006011100c118000c1c1c605070000b5a40e50807171640b5500000b0076070b12030001c02a000072010960b400194141e403261421918a20356a50401080c14a42d0000502c0904103005440403400c01980108442070705041c049400380d01c818102c2c1401b030382d0304442d412840c901c0c0e00b185600b40500c04100510030701074094050807400c0c0000b00702c10703c50600c8000c00800400a1203c018001102561401c3c4001001400f080f042c29141744040d0300329500741c03549902e944420411520f0701c5052100c0446c1d050303e40a003402c0c5400c04010540c004501d07600a180410003901c00015098800e452158080e21360a40c2c41c4d030702808202e464001840789084860b4440d007014440103480314480303411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 917606043 1250 917604793 917604811
    0x1c0504120602040b0a020105041a1e1e0a020d11130314030c03030f041707020108040b1528050a1d040f0816050d020a110d050312070903150501030b 65
    0x40103000d192075402442103501c0b00e601141c01040d0806880c1d0f06420050140c0c0c06440404100c44010460703032a003000c2521a2018800e400030005814007100405d079034005000003800049200401c10820701200c2103030130044007540000c407100715407820710030004082d20101f04281840c1294005d03290b0810303180009407010034091070400c1e50417010403c40f0343c01a14402602d40300d0400081c8069002025507003102e80c0c04041441c4808041c5040a560242ea0142d40360b000ba9200c544900fa448a0007908007505e40c02098075091080d111040c0c070480031840c9190750822003440d442050444001900140e1160580b044100104208a0803661030b1850905040c0072030b0310780d8a0000b034450303920381e070052803c400460080300c19100303807a0b0181c025006400380c03012082d1614007240c40c0d1041030001020b200c100d05410b42941440c04241075414482d0045a142c0322051100d90403143c400ca0b91540016600c1c4000d00070401e0311186a0300c181d00000b0b080c01517505558500c6000c000c024110b9803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 917607293 1250 917606043 917606069
    0x10b090105210a030302031605250309170f0c09071d060918060a0806101a0405040203180d09060914131e0b060405102607050703021c0504 61
    0x1050b640280c400c2c04801d4441200c0b4858824030300503010b9001146e0300b02c600507108180e808800d004e41c0441c1e15184100149805241442034034400a5030349001c1501008040f82001c141988105092180400400000e0038041085040c040ca0b140c0d071000d0090060700c4000a2061041d00304180030304c4044414a0080da014203000072911034019039a44613840981c00000480001107066030301d002c1c41040c0d0f41c0e04e4805481d5a59180d03078910603a042140c851420b030f01049014103c812a6249d4100100f07541d203043d680b000040c3c02c2e40c10680300c030800c880b1031b41c2c942025910b04000d038451160650508c01981450100b0180c9081d0fa81e204248209a00344090f02d810713501e02014500320101303e0070400c02241300c0746c1c101e5184c2d900010380300011031030400880d480785408800d5030100c6400600300c800c9007081c1d42044070751001c0040010521681040140807155094162910800340c940d032749500d0b1314030360070020302c3c05030990b82010200002e6004c00003401d078031108480c107035404807000075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 917608543 1250 917607293 917607319
    0x21f050702150d1d0c09330d05070e1006020d0807020f1605010207090b13090203120705010b100f08010b0f07080309030310080f030301050d060b0d0506090d02010b090105 75
    0x20740b14400c000c000c80140340340c0521080464030034107003480407400b07003012240080081418010721640c00e5804018403014040200850304e40901c24070040400e0240540c0142c86d94000325080c004007400c21507003030b013110505100c500110301080e54820440c003a15550f0b030f0b180c83c10194480b400c41c14020100604100080e01c0b80d402040825440c414410480d10091460301400165203034170301505005000d00ca00004004450340200311540c00b00900c109024901d040100c8018105030380304907007600036044e01e42030110003007000c1c002160241d03001142c410000420000c0741c14803c0350740000d05c590300741242e150591040d1224191008000a1a50b4900f00d200b03d0007540120403004014100001c10801f403160040042d500a8103500c5140640e0ba4a030744445450b021000e165140c5944184010005850002020007a0502540c0005018510302c4d0200d042e410070300703000741c45a40c88641031160f505410010b001a81c44240300070410780e12000001172070040d06120741d070311907280f101600c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 917609793 1250 917608543 917608579
    0x40606080303040c090e0c0a29120a0f050f1807080706030213090207151104090606020102030402121c0c02040f020415090e070905090414030a020a021f050702 70
    0x84405011800100c07034a03842e02d4a849a80c42610b402000d40680c149103071303103680b2003000440d40c0c00b6070401060000b519042c80c0402004510b1040c400c0001541da110610040c1c0c21600100040003d600040d04245070908501054800380381d01c04100d10b01d03013001c110441070101c030903640211044003121404001686400c0c41d062107500814600d000f459030001d1450382584c005c00a00604c801c411140607a5038203200101e001d00030020b0320000081c1c030b03035070745920503a4000501008400360450401b80c5501211045030040c2c0c01000140c0e6000052106614020b0140c3c05586034170341c002d1150b07881e074103a90410783c41a648403001b0f22030f000b69101c2c119502d5420178214060030300821500c55980e5a45100006407902d0342c400411070410010840c08500741116104100070707100c5022051421041c0444a6030041003640e48100f100300140a15030203200070f2060060580c001c00319525240104880c401e2090750640c4407885c000b07c05074259400c03200b650f2200c0d4040394402c1c46001c1044003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 917611043 1250 917609793 917609801
    0xf070c03020405160314010b030c0d02130e041e05030904020703030e2b020a080f0708090a0902030601110c03060105060a090905090a1205090f10030905150105090f0411090406 77
    0x2000b548642804200039200c003002c41301c07050555095405000107101c0068002400c40c080c0500e9031006801c00001c0e562000e118014240f0201d03100c40180740c0001003440c1394404420381c00c03056121896005020900c440d803000c0140c01007500b00c6402d50a09282e849a507240f182406640c01141c001c80c0c0c88044c035000c1d501a2a02c19541c1c0107075000d040d20a0034034969016120700c101400c0da030041e81d10100620019080349010781c01001c00d89001e0100520711615003003884100e45000082049038444e0301c7d04070600303000340310845c400340c1c0b00e003020000904815031240031191280d000ca075400b1140d40c0d00080b11411a04295003007030f40c402e81054100c584110325007065843c41e040c41c1c2030080c910740c009508410030707019070281581d402c02c40324215860300c04c00300344070f40c40078500c01c804a1078600b005410308044000d040c005002025599040d0074420f00d5415101801c20400c01007025080150900b68000110186141da07450542c0d5507000c200d40c840f9440e03000d00b1b404000902001071b2640 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 917612293 1250 917611043 917611049
    0x182307050904180b0c0a0903060b1c03020601060e1c0803040f0f03080f060d02032d19111002060a090204020d0e06061e0a0e090304050a060f0f090b0f070c 68
    0x100078044580352025514209201c0d03c0b003203d010701d00e24001a92800380c0b005a0f600b8500e81e030f0301d038540709155490754805003104c02882036008650307020540d620703a86410100000c500c250060003456241680c003504190680e00480d00600186010030410410306441488041c0e1080c000c640f0307502c441c2401540200d00c5000100880c2095040d0001c1c16003103103913b40f1411a08079130488595904040c080c5d0f4944140c4003e4056010340d80780c40c00b80d02131f551801c90744001c0029020508450005030b44c600a175000c011444007964080443c01c0c0b00c07000740d07220040d41094921610b0300b0302c08100203640e1000200307420100355541c0c0d0384800b1555203804a80100c07000c1c000038080c10390071141c01c80d121241643d070030380701d481d031400090902d400d403600c04260040001c002c180403a15100c50803040c1c9400034008901e5000801001c101559550f0f140c4006c0c051a9a5501181b40e00340350190100921030700050512045400c01c010310100d040803100c004d00014541916106a0301c1d0800402c40303d03030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 917613543 1250 917612293 917612299
    0x61a04030b270303010312050f0405040c020a020a09090b10300503040e271009050102040905071808010510030201050702063f040210080621071823070509 68
    0x465002d0707000001010354140c03402601c1c604440c50307407002d051320301d403180e0b03041c05001e950705000c00c020b5031609601140301e003542401a5404015aa80080c2c1c1c5007080e40c00c900c15050340e03541d04105200525244983c803900004c0308140c0d65042070100031411500000ba00001e041c0400a43c00c0c84035540d880c02e00391a80041201d45503504d40d0000c00013100211a9440c15086c0303e0101c0c4030800d480d0072500e10248481020b000d00c08520710b445400361480030400d46032503400700000940d540c40c91207024480c21555440b41c0c65002030720300315070a01102cad071b0103004140c1c100030500a0303820342803940c0e40460350f09080590340e42556101041060040c0000310540c48200000040a016040501113014242880c100802080904500b501650981d006500b00c95010540b0b15050f001c0c0c01c0d165004480100b41260490615001c200301401c0b0316200003164020560410098050801b021103883c0245e00900c81884000c8a0300060007000361888000703415800402e6070305000c1d2003207031071648002e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 917614793 1250 917613543 917613601
    0xb1f021515011e0c03080a060b03010b19080106170703060e09010c020f0a0b0a02031f1202040f0c0503060409060b0a030c030c08060c04090e101b03061a04030b 70
    0x3100c0810014241c01c940340070800b9440b500c0f080c40224086070310804807584800003100074030b40301110403040040440d0301d9190761700808180b070180000558004c1c01d0b8485421350b10030031400481484205d02c0710000c103100d442d000600002d03401c0041604100c5e10101c80c04110782c3c411000300c6c00b51030302e0343c8003105000580040c8140d40380306401084243d40300f0340031609050310154100d581c45540700300103002060040007160060b41603030001e40c2c0004a000e49011100f1100e107100130316001550000120791074807a110310440c1024041c003940c078034031290f0401c546c1404c00000741292000402c014882c55a901140c000c201c590f1b80f00019028000e000b0092061f281d00c0c1c40102c2d0102070205440b000100c010024002200013110f40c03003074806500c0241070510305083d604c0503010700c3c0842c0d00c907030182600c0d03648861068404c0d0311f60a2040001c4c10458030200700040c04880180e044100b002181454140740507904c80111012aa400001d0310002c0c4c3c0c610343c908508800c40003070340d2904038030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 917616043 1250 917614793 917614801
    0x20c0105060102161401082512050112030c080a020a0b0c04061706210c060a031406030714370806090c030a0f081204061a040b1f0215 59
    0x1544081e00ca0907080e000c03520080304c29a982c03400000a807245244400000e5481d4016510400303540303400041a8981c03841c151582c2a28545042d03a041407800040c07444005407801d41e0baa802098010101c07141068002c09d0f1588005103803007070340c0a0103040c9500000d04001d4541c800c114039000170340c2010035800340d420590045510340d071051049a001410302c40d00c4020000c0d0303001044d40514001072160142000400c0e02c420102e500c0c10002481e4016003c52120347c1c1c4400b80102060080e940d0001004440344151150020020700421701075031091030240060000d01c0302003203055800300c400b0280d12078584101900300000158180700959a40380000c00c855244403001c0c2510400000d0f0380b034595a15106503981c1c141910038a80c507038440c500b004040307480344203044a0280142c010a00d040c640f07110035010400190b80458846a8400c03482c2e0394803000c0420210304580440d0184034098461001421000a103440440d20500c4444000c484e140200118050883c42d251409450302d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 917617293 1250 917616043 917616067
    0x60615070212031b010e1513060c0207181b0e060418020a0206091203040b04142515050d05130b130b06010507050a0b060604260c01090f091e02 63
    0x2103104003581401c1540d1441680d406001e240c43e841d40c0303580204143d926140547c06040030143c1000701800080ba05000401c00302e0184207182d507404e030010720780345140c282d0350200010500604055203181c07000c1c90042d8184003100c154000c0303642c0390480a070400200040e40c40c3c03007903030b00000300c1c2c0300c003480401c03d80291034021b045020041e03029120715a80d00104184c581002419219000108100080001d01c4460420f5002806001c1505040340065601450551500114a000780c003030100c8403001c0d60290803101c040c082c030841c2d140c0074840040380646103000e161b00a803d07113900d41001075204003880d040c6030b40154200b000040c250038020842d9001940e440016210380042c2c40c006542075025904940003a40d00100520a4040c1d64884807410038001d06803542c8000704006c002f42c941452100d44000703a484c03c80600c1c44c0301864506030319250405202a061205000080103180300d814000401c4458030000800c0e40040c10702c4c00d1000000d0722443d00401840441c110f60100b03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 917618543 1250 917617293 917617297
    0x30f02040f0501030302060a1e1103061002012d09020d03053004060902181609080703030905011d04020f180102010509100b03120c010b15040806061507021203 70
    0x50080d2010401507104a2181050301c1c0d09020140143c0d10480100700e03100310944c850542d524080c403180703500b150441105c005440c01d42d83c401c900078401009201182c40c2c030b10754144190010b030000b0000c034608040014002c40880180490240e401c100340b0b0304095030b64200d48101603000304000b20a15903482c0141c03440e0400c1190300c14000b030701400c0300b1215428031080d60302c244650010318556519562000d000c0c041c2100200e13000812020040441c40401ca52180100b6200d17480720480c0306a4400104030a200354070210455122007c1000469001007802040c6c8000386480c1c1040d2002c0f0091207003842c45150010f401510024526059a1800026040b0600180d049410514ac5c050049083c0c0d5020784110485800000d0142c15004266021a0049101805032043c444071080010040c2d00714120451969446100c4e16101d4584841c480d1150030010111905117070400c2c3c01503030341e00700080c0440d00640c00c3c80c2075510722100d094103840010341c4c010a1040c10030703c8041807503266 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 917619793 1250 917618543 917618573
    0x50d110f070c0b030108071403150c1b0a0803011e08070305031b0114180a1506050306070f0801090510120c0306061703030a0c030e3f1c0f020403 64
    0x2c0c1c01c0310041072004203141224122001e040090070724504094135124017a10350790601c0e6051140480320040480c615030410700c02da80141c00182c4642c055030f14200c0b4184080c1000b002900403441000016080d04207490544245264008810824080410f90250030307401c800301c0d5124510000003000b00c0040140081c3d030841046a0700900c402e40202c0c00d81d010510303104a9008031100094010300108401c08455020004039100568161604e101c0c40460300d01c403d804c15260401031203542410003020b6000084ca01e0680800c4143c4200107108600c107014903418140c8a6003c01c910200078106c02c000f41c403210400131141000d900c0d101902c8685444212141420600300041ca596035140b01c103a40800c4d003000d0361071940c550b01d0200040c205490b42c01c081c1940d50011003000740d41000307030444070054030b040044100c2441345401c0495070b00e00c0600150a09240c244076086070702d00180e9410140304210003600f800c6600e50f4001800050303032001102807020400006100418501c9a03c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 917621043 1250 917619793 917619803
    0x50313080321091e03040f0b03090106050607050a3003051f0503100209030a06020403050d02210712090302130f05090c01022a0a0b07140105060f01050d110f07 70
    0x20306440303801c0b010381201048591800e03641114426040c24221001c080c0b544800040a0324a050703224030310f11601c0780c0d41d40c00c018000341c404010050504401d11500c40074000480310107051600719650b040e52400030b060010071461881c0100d60b2058900000e10814010354007200d10400c001c132a0081c024070f41120244115100c04c0485481203480c0080e0350b05a80c400307409003aa00700c0d041100c101941c0400856601407242d581c040c0d002c00e48078800342c40518410b0020300121400721000900d01452a92403125101c1900342c41d0005030866003c50744500c0d40441c3d460f0283ea0118015100c046240c0d00280d009103c12011401c4040b085d8001c009440001c90b0400150b00c038802d500b559940841c18150150748008030210140740100180380800c0f40240d448007a901075900442c1601c4403a0744400700c4c4c1000400c402c01001107510941c140000684000c024a10f417020000740088443d07000281804400103603040c1c08680703a00814a9007890300b5070165603ca5000c00007450364415901568 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 917622293 1250 917621043 917621077
    0x307170a330b0306060607030905040903020102070210031e0906020912010c270e100f030503070308060d022b020405011e1d01060315050d0b0402010801080f190503130803 75
    0x481c0c8841d2054550b800d50180040c01d10355501400d0160541c09800b003603040c0070510500055950790b0380100010180300354005a11046944180440d400f81440b0140074141070001003044082804a8a01d0301c501a40010900b40180c1c2040f1000744241051141c0103501981c2003080b0300415000032000066a695800368032854a0305e603000c1a060b8070110b04400107034401000400082140c594104245d40143c051103903462442000d11681c41d401160b0300d40000c140c07101415005428243c0c0004250f49104c600700c8160300103030804940d414a01e01a00624a0490b00481c8200b0005138980e07025104100b956141c0c442c2c0100030542500b0840709100410020404c2848500c07089607003414010194066401c00e40c0940280ca6283d075040e91504000500080c00d6175000782d40034100b8009e4407141c526040a00004101540503040444198031042015420982c00207045d07030710031356447c0d810f02170500f41e2030054110310882d004c88242101d0ba030004102a20040700400c16400060080c030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 917623543 1250 917622293 917622383
    0x12111201020c0c0f03011e060801050609090d03201308010b0d08190c060218031606020a02010c0c050409150507020c010c2a09020a02010609020403020307170a 70
    0x20300381d01c01c160705044160042c1d80c07226001c0c00c0038608195030b04401000410340070900e04540980c151038928503040d20780c840c2020010302e0001e00c20350b5000b1405a881a010f49804030119580b00d9140e640c1ea8205951080c480c2c80003185d040d00c223010203030400842680c440d0a1084914261a207000701c014075460031000703000038640101c4450f05242c0c403441d224244207080109159950560460400303022081c1d40301c400145040c40200b60b1039214052070306000402d04245854881049800e5010b1140480b060050603000100800d0140d42445c1c400e0700000c0754500038030404940c1d8000d0ba0803a00b0714011000b00403004090040e0207000410400c026030300c0701400c990b56261020b400d404030702d40802c1c0402141407114000103100f15608800e441009140130318240c421903a11055105501040c84010310780e0a01940d00100500c03001582807a045800094179080c00d485403d001e41c0c100040c4040e06442486040320703258002400080e5401c0140040b0b0940321900000200010524851 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 917624793 1250 917623543 917623579
    0xf060504051f0818010b0301151518140102010b031c18030c03020d021804030809120c0d050309120f1806190e0103060e1006030623010e06041211 64
    0x100020b0002e5a030360490b107849581012407014101c29941c01c595403186c40c0c1d0710454030240200c02044442180c1c4d1400340341703403201860442035120307405d6080000001c0c0403014004218404800e0341c003030008940000a0b0000180d00616140307078103580500800000c0d07101c01109000c40e58100f5400e413a5440100070810b007805c2802c80342e00000f800004203100030b20250070100c0f056881644080c091400c1030403890468840a24211021000500c3d510f08000c0c5c00c8409110300c42c074040d4442d02440c100b0521031300458481043c00002c1040260200000e54003410400c1050301c00103a4048896484400d0b1104e0181c6030307c100410680c1c514540a030b10354500f090000c9a01011700c0d50307511440c506030640d040f114850041540c504164440342c002c9402040381410900500030380a0700e01c8120314104001e0300303a41d1640d000c0760b81c40641b070610300403288a45c991110300e1182440c181d10000c4e03007800000d802d40940d410050581c80c030701c480e00007003141000041d8403401017200d81d00035030080c075082 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 917625899 1106 917624793 917624839
    0xd180e0c040e090a020a060216050d08040506030a0b0a060e010503070c150c09210b0f04050a08030702031e0c0307020409060603050607020322140d05070f06050405 72
    0x132910071031070030892440c0140305a00140c0f01d0f8400301c081e2550070042d00d2007928090400408090100800202113034050310005008a0700c904040000d00f000302034803c0c009000380303401d59002c0340140c001e811140d12824140c0d58a8a141d03a104422140c007640000110381801255461458041003405544645965a900c2d08001ea2500050307904203c00d0700c04030034409110002c0880030449100c442d5a0210040d05814125200c6161092034103c3d040030103410300c8804018456040c1d400300044c41c03c510380c414103880c0303404407004000d200e108041c402d0302c0c264000c009980060a25400030180e00b0b006000004002c1d0b80c03a02e4043c2800c108452010041c0c000040741403c0c0c00d58180d250f40d10341d6041704851001e600341038900c4107080c00d40000714400c2c00d00316032030810000100300400240229200c88000b0725a0b805000c1c02981040c000c1311300c20403203200c00002d10451544 = true := by decide +kernel

theorem cover : BRFrame.Cov 917446043 917625899 := by
  have h0 := BRFrame.cov_init 917446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 917446043 ≤ n) (h2 : n < 917625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
