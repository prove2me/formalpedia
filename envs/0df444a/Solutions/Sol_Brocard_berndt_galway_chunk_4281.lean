-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4281
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:06:40.591862+00:00
-- url     : https://prove2.me/submissions/4d8210d7-c95f-4a01-9b8b-c2a7c3e4e167

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 769784172 ≤ n < 769964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 769785422 1250 769784172 769784177
    0x1e1e060b030606030319030b0a0512030a08011e0b1c11040e090a0c0b1b1906061a0306120106030507092906030106050c0f0714120c010c06090602120903090f01 70
    0x400c446440041c84e105072080101b510b0042045a100400310304100200c0c1c0001d50000e4032213024111440c0d0020007091414125511494107a9071488000e0340c0c1c81100e413403008444c21801d801c004142001d80038009a034824a04a02c0040c20622481d04450300811300c0050514041010005180152130f4136500c140b580002e045d640c001d0355291120b80c08c00d805600c00d808004144142042c2d12183c1d002207480d464001c0394070843c00c40080901500d465102160b00a0511324042078840c0c00d040706500c510742e40030b4801d007142c8034041001a040400084070032599640c03040007022440801400c40103007480d83e0001500c41910007515802842c4c1041e09869001d01c180703200603905ca94040b2411100d0b185070003a2240100c0240900308261511403ca4500c19050040303030401a0380802034500d40102d500e03203545408801159100d245401c03115020079003140a940119800340c00092425204400c0186010300c00381c2c45501c000302c16210345007240e2010622006c641410032092080207003d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 769786672 1250 769785422 769785427
    0x909050a05061513020a17070305060a240302071e0f0309150c020603090304080a05030c010c170c0717070303061e0e06102d020c09041e1e060b0306060303 68
    0x40c000c030b65604c03880c1903029a0030354005260701c00c030381c13180280020f140791030003980141e4204000000c01404003510700340c0c410f5071000f00008910035406084481e90340c0c40200b1180e503120344d4501b5402504a4003068440040110305150806041c0c80c000301d090b0b2040d146091252540d0600901c1d402541d0411441c01c1c070301e009101c4070a600315044404e510303811290a6982d6440d00c8a1785d0850066500c9030105214901c982ca0410201101170309000800d0700c001c0107080701d04002101c8101c00e088034600301000885c04500751003071203002003140e030f40602228002200c0004090340541d001113815000640c0d203403030a1200000c040e0703400b15440c4141d000030b1409401c6c08034240112030080e0100f8070aa10b8410300321402c80c0502c12811040500306800c1040c6400c0202500507049030096101c01802070820042c410710f0721501c164000c42d080a00140c8032800c5091070320318102901010703100100052100c1c00325100034405910000d100304030105400c41468141454240090041407082c0c105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 769787922 1250 769786672 769786711
    0x12060117040605250e030f030918040819020c03012a0305061311032a0712023c010605010c1e050313060e01080c03070e0a0909050a0506 60
    0x180c480c9500260007020001d8a9212108481c2115589100b480f51140c95a03002680385500405800700e618001c0c2d05442e00a111940c0c3e554032481035110380c0740d0105400b42c10000f51241e040b440c40d031003840b034503c1a04d030909003041900c4164000ba681c00060340580240c64480c01c00780a6900d155400000a200c55840c80000c00b100400d54a54041055520000591903548842c0780680c00c0c44030722405c11030b080d02461070f60f28641c0111441401b0000010b19000b0190704515042c4032090703240d181c1e505210803a0b4940c01c7c480d90b102213041c03c5206590380807007080c0c400040c541010480c1002d81c15120240c4d095105280f00da86104505645020400c2180340d0f089100c403400c080e8400301c40d03243c500340503140302d4000c1410040070300a4800481c043d003004640c40040c0095407803a407101c184c8901000011242c102044071907100c20442840450085801203100c020304060062020301c00c070b0303100e040d004119400b450064a25502c40e0030718905024041c0a5607401ca003d504014000c07084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 769789172 1250 769787922 769787957
    0x61e0d02190e04050c0d09030e1503011706070f0e04240f06020309030618160e0f0a2c010603021206100e040302070e0606040e0a0b0108071701050907020a0b0903120601 74
    0x154004d80c4046c40d25404441c040500c500c030302164250000b0034501a1844002491540d9042401164000c858040b24815032500c0040c1262280c0040d603a18227076085428000c945410402900c0c941181d101c0c00e2200e07011081501800d1000300040c0104c810350b18004901c02c2e94485039110005541041041440e16200400c40d00c0d80019401703080c103031446140003241e00e444400210041e01e0303800c001021238042c000f015030b217014640d2100143d14a4440c041110220344602c026042d1a02141c2c8066802ca5038110b02e9603140740196000040c45a9a034001c112611000350b04008190440720420441900308600000a000380c4003000a042c502950042d5482506000d8041a04044c80020701c80f5030314007007102c2c041c00540a0095190404c145101c02400b140100c04d4045080000010a810b10550340350003580661500707014203900e0a0103022100c1c8010388128114001c109200c00820300c104141d40c01484c00c600115a54040d494410480c0305002c1c4c282d604001d10400100000213 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 769790422 1250 769789172 769789177
    0x21e0a080325020715082a0f0a020a05150402150711040609020a020721020906040e011d0609030301060804231b0f04020405061e0d02190e04050c 64
    0x6500c1400396a4a403901d90310034941003411007004a00d00503203100306803210790101c0c0a0045800020032166600c00ca540240c2d440c41c4204c5003040001c480401c2c2807410485801e14030280707440920352619010201e0f040000e1a80841070b207d025034041b001d00b100300442040b804075000c00310740c0140311505041c0d002409000031440502941900440d1150611401107800354442e540104100034840c4d03075030451000b0750805180c0f0000341c000c0840000302620200131441012400d0b5030020482c045642c00c105111002030318140c4c00c1031b610504284846800d101d8a0541c4240030103d10003200095540303898420000c200340b0701d64000344010842c03960442c404e5500990f000115250184042107980d028080c0403161000a00c108103032985180050b40c1910400041620312405502d92842400164456803043c9038108000300001001c1d1540c0301c0c0010400450040e41030b2520210741c03000d0043c6d800c0180d90b024641d4245074003203032542d08440150b420b100145c1c0c05005501d0051503054103070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 769791672 1250 769790422 769790443
    0xf070e0634110d060e1b0918061603060f0303081f032102010b090c030109060b030415150e04061a0102011803110a0213020a02010506120703120908100507021e 70
    0x24502c49403d60104807881e00100d050380c500a08803904a140001c1c12100c6540e10a02903024030300300d81c045110411012019084412540d0061500d911400c4507050305c00c001502c2e007070405070765080105540c00c03d92890f8000f113010341d8030f10750740741401c4020f2000c442040010101c074580f01c0e401000007569803540c04840e074031100103d20312102e51107402da01402419040300c5e0702500300d60070030404440c0d200181d0f060741e02ca41801c00076180c46012907a5584030079036014044036400e41c1c10041303000158222003076001c16003201741e110f40e9441c070b004010f0380c00030b41c2c04a0707901c1e84901480c00c245800220b00300d00d100f001d1000340100307540402d030728005aa100d032010302040740e114800c84000c0c0041103141003055016050390028440084d0b15002034000c8000c0c60300650034080492214903018080500d008071450103803032240c0c0b44d80d4900508000c1a6000c0d400d010201d0700c0064070b00010700c2280c8140f80c12702030100c1d261501074002418015500e110002d0142400e4021460480c00500181071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 769792922 1250 769791672 769791679
    0x102040306151211062107090503071d07021f0207030206071718030906180316060f032007050d080121020f0d050601030c14040903080f070e063411 65
    0x8a5040c4011607110302c1191000c200701e102c0c01903042c41d030300c1b604c1d01c01510800c503560302c0d66a05900c407800c16880720914072a02480c960140f02d104441d40380000501d801c1206401140e281c404410011401c43d0f107400445400c5a60100c0e07940181501402034070b902500038508078001c0800e248401483c100c02400c40c0b100b41180d10058030410714204112811064014406a1070b8008080c0b00012400141203850281c007078441c2020b0411002c842c0d100583e070084d2190344043c0c400800440040109035111541303a400401d000c822821420000e05e0150f01460262014031401a4043c05011040c0d000c25001d083c0103e000302c03c880c00089154002e0b604451340510060000700007426010029800b425500a001c00082000702600c10700f8120b4aa84503000c0032410030340c0400c4103d9080c00d10107408a40c024000440d812400b0040d9940610385042043c05040f142020941d103410640d0f0100813880084201125841001c1030110300300701610810b01000c0c129541e03000703000205680c0600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 769794172 1250 769792922 769792943
    0x1b050d09140111180a14060a18030309140f0a090c03060b03010e01050a17070e09030c010606030f3e0d11091806090105090c0f03010801020403061512 66
    0x70021034400d60516416420000d1141d02c40006031007815611403005220008411003903100b00d0b05103e103001040390582c1a07030403450b01c0a0403d100032a4014800e00b4100710400d5400c003c0c154010107903c01440c081e65a1202e403a040011a01d05000a0200c0701c0c800e0803000c0c40c1d0240c0c1d40e0f4a8034018180c60502030041541a2008400e401030010360b006030441d00740100012809016005100d412910f045070b0300001e0300d9580380305503507054040800f080240c03c500400c0c044440da0501c00354002d210720045174503100c00600c0244c00c5540c15041280002d48621031108c844546000d64541126650803148111075075030b00810034a08950605501584004405200c1da040b00098030681402c41c501440305192000c40501181d01c82090300380b040221801030b00e44d8450001e021807003003401078007001e45a402d02c4208803507030350300034081810000d08011501010600d00701660080001d0800941c449003107103400310544880c0610030b03505990000c81001071212011060031015000401c002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 769795422 1250 769794172 769794191
    0xf1f0513080c07052106010e1308070309050402030901050a060f06020a060b060c0d020a230d12180c0f240804030e0402160c0801020307022d0607121b050d 68
    0x1420070809500c4540c1c000000c1807007903010600d607005c2e074800c20240c50540307a4a0784c0314003050510710800d40301242c0400c1c1c8000300800040c510f9005050050107820106020341c0d8900008083e40e10880f009203940c0d45400601410071000e0003244041c11a0094071041d450800344003d50300c103400000901941e1701d82043c0c130341545944040303403480401c0c0c106807440c00322491406035840180400884002e0154905070441a1000b0106aa41c5110300040c00c200350300408100ca40e141094410001d2603078a8498a07003295001700c0c458402c0e44141c0c0e0f0720107014600403210f1105164ad600010518083c880c60024136003102c00d00181000c11814010010b48031400c1c125080001c00440c26007252000419440c403880d411600c1c03100911400300502840d444072080c07800e0b40003e448003005a070000510340b840e000e80c0350b1410040d0404145c0040c66182a01000e85408001e441800208921009210b042d00b264080c0303d0401d400e4510144a0f0600c030b840c01811440344041c1c0c0155160f42e0002c90 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 769796672 1250 769795422 769795447
    0x103180c0803030405210f030405010609061e1d070c080405102c030c01030b040f020a03060501180e18151501020c0405010e01061b050f1f051308 64
    0x1156030308000c41900094444002075034a510a41c0c06440500c10300d96060081448210700e1a0a407840340016402c041203c101440d0030740002e40308480c0b41d520f951010400d02d036181314600060000c19a02c0b08400008600d06c000d803000c3e030300704900341840c0b0040e2543c844052109035400c000146407074890b09901d03080048050186801199218890740740660010303500c000205200803540c041c010001e601e401c4100e5640400608140d0076810208440c40290b010b80d10030307808810043c00c04920100c0148000b0200d134080010a40865681c031814405135900082c04e01501e0949414007070170a080400c8903840e944000d00079004005004c1015501c060140720070700448d1040e586141c020b0030040b241e8030800b00c109101d14018800c0c1030300500c1c1c91405009060403181d2070320b103400c400c2e42006003c88a8400003c0d5840c0500100b80c0c0400c0021000c0041c0d5500d40c101c0f5000d440741804414512482c4121000c03d85415820f0000f4041c3d007901d02c45086908582c81030003243d44010041c4039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 769797922 1250 769796672 769796711
    0x909010b090604270b03030712030c0c0501090b09010b0603090303041e0f0c05010809070612090302010605180a05010b091f12060b070c06050a020a030c06020d09060b1509010e0103 79
    0x41000e070220134401440107050521012803500550307018065502c2030010f0640ea4081c1110180c030b13051a42d100d45000d64000ea02c41c3c44000d54520303014035000099121503095840109049482a81c03000c20030212540070300c122030311000c04a590034a541000b4020310f070b482c0000f901c081c00005d20031100300c8035a000300c12403075001075002400074001c071110b0919161040e4680f08107808240d03a10700040c860b10000c1031034001c0d80c54607100c08413a42e040804030001040110000c4055660303071900401d480da1814803083c0c01140c0280604007600c1e0080c003c4066030410307403050540e140306016034027250740c4005940d21034281c0b0011260012009c03007000c071000344807400c02d0b201240c0742c118082146584c80c001010600d02500d04084c401c0d03661402124240304d0152820b0058129072004030009115000b000e030380600826015040c284140e07102001c8507084034044401943d01d1010721402d08100c00140f0000c00c04061301401c140c26000080c2c44000e1210700241059a20302e034440310f2600079400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 769799172 1250 769797922 769797929
    0xb0324011d040503040b0a260f0f060612061201151a040501091203030906020d091e02010806190f090c030b040e0c04020c010609020f09011223040336060201020909010b090604 77
    0x441c030011023000c0c852080032803041d2640e03400107800c14002070703c459804052a0041d103002e4203035850703e0303404d80580103145009410341e5800003070075419610218090065111826090001c40c40161520342c4403040d50440301c0b07214440c0342d4113000402c070a0b038100d094001100c58440d002155299140b030210000c0a0381640100213a102103941e04600c0c00300d510018109210314040c074400b00ea00e03261680032118007071009002454200008030300f424600c14103500c210400c03010341925500c50b004008890396640240c9865555840e19007a40c2d54075002d004100d43c0c0c00e8500b00100141c440407261940000c44149000c0d50b000180f0419005096003c50000c1c0115074003191101e01c01e0303e1490302948006038150008400c12102c10724106140708940708041d41c7c2c08042c000c0592a4204190180014010703011b1100040a5240030050b56003004800ca82100304c0381c0b0078140c0c0b446540d1078480142c014401310ba03c1805100401d40f10f00c0041819144903021326a20346492800040262043d0b40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 769800422 1250 769799172 769799207
    0x90303050a20151605071220010903031a040525020a020a0e0f0919062c0a15020f0d091704090203040b060d02030a060b0324011d040503040b0a 63
    0xd512203502c807403040f1680986002420307500c070b02c2410403045409004404002d000c0d102803080c80140280a4504440c4c1601c2c00400e40200282040c00d035402c490300d1000c294046620b079001c103800000300284401c200d10080f90100a0790401005580c024801040801070140b2803a1300e003000c6030700030000301c65541e03801000e5442c92910b0706591050484240c0f4030008410aa0022404101001c640310203207d141400304840e9601035102c501c06484c0402001c0c03d144454040c40464001c10394000071034070304040c0245080300c124580341c056095003907608141a0300c14808612100410030890b60540c10302c80010640084034100b100f10702e40c4000000000280c00038000581c50400c1e0045c40c4a1409188801c54036075803842884070046a068009500d900410b01d58030020360180e208204120000d0111a01940011280c29007541c90f030110300c9031070322180010811842c1440d4009426400c2c0340c90b04d415820613070f036080d43e00d02035030180d1a04484041100c0c55031903c00c007580da400b21a0903 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 769801672 1250 769800422 769800433
    0x10806190902120c04030b0a15090501080607021b0f2202120405010b060906030f04110306180f011104060c05010b0a0f0305010e1b04020a0c050604140d090303050a20 73
    0x1c050790340096212403040004800600005030030f20403808151001c49401840d0820180c0d10082c0c1c0c14018001022203110000c03111402042c480c0d260301c141c1703010b0148903005003890700f86280e02a1404520004520b807402003602c81580f186c85200c40c80482c21800c2c0c1d2400d03803105002c5d950030103103809403490540e414230100300e001c3d02c4a8a004d405000d45d0049008100b00e1460400b44080e91050481c5150080010008030701c00011200420380d01034004c04085141116030000070341805e0003a0b851043c100d603007405001c11404144190000c40008800030054040b046545040341e0141d40700704000c0c45900602c000603c08290025000c0d070390010a04200c0f551115a070101c00907c3c1d0100b913071b1561800840745104400000c664000c0f0b0100d00080706882920000c000c00395105a80d880100060800240d00084040201500861185071840080801d41e07040514224419210804001400e0401c10200e6001007c9590241603403038400c101844070320744421203104028080d00a03101d81d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 769802922 1250 769801672 769801679
    0x60f062b09030906120c0518031606021b1801141804050709060b0313110a0b0f070b0c030c090405040303240312050c07182a090e09060601080619 64
    0x240f01e00255042d5448491045204c030b80c802088440800d030540106504100c0451507946c0c4034030250442c18002c2c02c84041101c4c0f00007510305081a03901010250b4840a0015440d031a1641240c82808007a6084440c440441410301c2e004c039411322036002c1d41d100000031a5200e4a9400c080108030b4240550b007a228101840c0a503942c0141e0b00c10001480e01c0c0c550040342c002881d8084070b0060078440000700c0070078225101c0c0d01d094a142d01101d45e2120452000040c86200c44002e00b04281130307101d400d038883e08141043d1200c0d84008183c4c440410080040184001d581000d0b581000030644000541d55184c2c0380a4004001c4540c0d400d880c1e04864110115005004d0002030070390b0300c184408008200f582d4000d944602803004c050415411465080c0454083c00c610b06003840c008040102d4140710760310300081542142c0000c014445240301d4413000380c60b0070051900080240215414003840c0c0801043d80310034018002504002d10356010078140c2e59410042000b0800001000202d82d64 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 769804172 1250 769802922 769802927
    0x70204051008030a0903031805010f08090f100506040b03150408031b0f07060e19020d05070f0605070317010308030a020901020c09090c03011b0c03080910090804050405060f062b0903 80
    0x40921048000403140321a448128258208c2c401c12604183c54440f07181d0380c42d400540f41182c0040c0038045500c508003d804003c0703010400c8071102102e1801c0010b2500f8803c00744000d0307500560300d03140203607c80b1a2100e008010fa910107030380590802c902e10f442e0f03140d20070301580d240c184100c0040d030081e011842c4184030522038010710926106080800c5088511000309446900080c2000401c840c1d01742e513180981031800a6640317983c03198080c1e44100d070f01e81c01c40e604e04a5164010400061000c2210010543c001d103561040301824035007103001d5891640d030410707075200c0103000001d00d136000b01e084000c0364003c0203581c40c52040104120100d241c01c070401f6135035040d4080c04038402c0d0b00f000000d130307072001508140c0502c04165548564807070b00c41d61803e55600d5405802c842c7c140c81160003200303c00006202d07400040b031059036030603503031480d180800c8140c81014100c648100b01c03099494045071b83e03507000c5419000d00d2600c5500d02140380e41952840800d0030b03040c4204281840550301c20950b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 769805422 1250 769804172 769804187
    0x1303111c0b07050a090f031b080105060f0409020f10120f02180108060a080a0f0b010801020c07090b04140405030a1e120515060c0607091a070204051008030a 69
    0x1040d2204021015201000c0d4640c0c1040c00e0041d184510020200b00303458410b000030a048600d40c1844a00c9540d00c5030982e6071456564000c4c0c814440700301002540340c0c12000002d00800010f802404281002000610160100c11800384074a655042c035200710340381c419180c540315400a1001d0203010101d42c010b00b480300d040a401e81107a00c0c10203a03075a012280c3c400d0b035202c0c250140e02d51082c102c01d0b030f0055800c160003420099003d50406800078050004001001d6201d200c1c1d64140d141c203846140004620710180c00030038061b4018048805c48081c0041c450045403003800003c2481010f00d0041401402c080c3d0800c210181064200310034070030000700a00075046030341c1d200001000f203100881904140411071800041c0c0080c0e052441c80c140c0d4000700e400003843c182d529112850f00b40020307095406003201c2c40094111404201d0070903040010480104941e20080d01003550b0011140598403a60b20001d110b555114007091000c40c01c025454060142441100c3c0e442c420018041e00d101d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 769806672 1250 769805422 769805453
    0x501080a2d0b12070302040b032802030c0103060602060604050a0605030102070c180b0105041403100c08060a06050c07170f0123010b25030338030a03231303 69
    0x6a0a0582c1040e071420a1003440050350303030080103400f82c242035900300000f40107030500f5aa410721625034621000809002c0440407480c4200c804952800c0c07907c149410680c10942e0503051510305a0100181900428a1303a400305088030000b030550b45000520b0001e02c15508074175003662010a0103020002186011001c0c0c6980000c11034520080080403003c1e40e106425480c0044c030700384410882a040490781c5d2a21840c001d0546110030840d54281341100c84081841001814001c00d1047e54200202004e000e0101d514020b80b0349101d818165a03954614800c88281e0695940d80750120481031003042110b14001c0001d2006209401c0910021041e06007103c6401032075000004003100c107030b42142c1d281c54090806120800e03c3c0f130012407151398000c0003642450384841c00c0d1541007050104074070b0401620121220032021011841a42c10040344015001ea0300098029002c40c0c1c0106040b100240fa483c203011440d8070500d00310049000d03986058080c45d8110001008115a10344954102c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 769807922 1250 769806672 769806761
    0x218100f0902090d3503040204050612030a0c0215040f0f210213181203360302030d0e060a0f020a14090f0a120314130501080a 56
    0x15580c6600700c4008920801e0200d99114a454442100054250955862103905031909461400c000303e025104040300980c0401a00030010401c000c501d01031244540001e400c0e284541d20f1081c210700290f886c401c8000d40002d10110a50090441d074030078006940b03600c0395001ca183c90700da5a00c15060044141d000e108841542c66002059900d403400304148400413203001c00d54004402c0d020700c0300381540c24100080c01900d030286012403040c4180c503030501c40c0c413500e03605101c201225801070440d81841c1c4460f01c15803d26040070550403003d1441c002d020b042418460740c00c0e603113140683c558230070700e0030f02400c2c03600300803010141d9140803c81c5440740209071024070040c1c0b100400c1a04a01c01c144102012604094a9038070300d0f1031102c06000341800140c0311316290491100080c00a80c0a54840c811392150480500704040d4000c2d0f003660503840310f4030606d05115408503c007000c6c0810313010b414100040c600001d0b010005075080002852007040d4681c0600c01400600740d000341c000c0b41e00540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 769809172 1250 769807922 769807949
    0x80f040f030b061f0906050a1202160c090c140d090b0a09020109050609090a2417010c0c120e0d0b09010504050f0f0d031d0102030702150903160b04021810 68
    0xa20213100c000c0c1c00c0c0744040c41c1d4540e9111414203400743e5580d0086039025041184c1039034047c3d00d202c51231000304075000c880b04100c2c00c6c000c600e01e40030307000601c1500490308142c00d0a8003109901d8005004100c48400b04800e1502c0b074841c40c0404c001170041d030802605040c801400d100e1100883d44c400b10070a8006c0e0f84820f5101d031110309028151146804c081e810031401c2001844045040c0d10044111a00a500d20540d09001e04030a640b43c80719005510074050038403100460b503100341b00b17004035071000d414500054210790311900800c1000b032075001c0c2481207041c0111415528008034000041e841180601c113410030000303041c02058112000c480502c40c1ca000e200e055140003c00175020039040d0014100c8207503054040300640340340040380301c1d0b007025084051041002800a14800d0402d076000b4114042500b5003560011000303442c000c51a002004525503c20744401150607141e005203078a0030700e880c0c0d480071940c0318055840060b610041e40c414071540c0030014215008440045800341c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 769810422 1250 769809172 769809199
    0x131805010c030c0f08130b0c25020f150f210603150a0e0304080a03050c0d0e0f04110c07090203011701140103030806030f060f0402040f0203040f080f040f030b06 71
    0x181101c0e066441a00414402d59006820340d03c545c84842e07000a0041c0b00c802e030000350703985522210000740e400d036080703010104194008608036203046950141d0030350700301c1030301c011900400d07107104c0440326441c000c10b44e0049499490184208680104440b00480c6070356200000002e00c5002c10b61000130783d408c01041c00b1075054500010b00d0708420380c10004001c1c0b41d40f2a15402c80040074480355007800da010901c00021802c60511202412501070340340c00c0c0da680019541d840c20f04041684401c140191041a20398980b50742400f0100c00d80c064030000303814104248100494000c010111407244101d80c400314454015401460482e0301c1c840380324580d00b00440b070b401d003030340c0c107600c1d20311000c840100040001c0f80c0b14044040d040180541558410f440d450105400c1c1142140d4500a004445d409d01c001c41c2801d224020b15494280740c114110709142e500c0071589c60044001403c00f0901298201c098240c5400311380046c42d50b8011400c946903a46056080c4120071550301e407240e41d2446401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 769811672 1250 769810422 769810427
    0x180b01021f0203091e0a0302010606080702060406021303150605010e0109120803150310050105150307021b0102010b060a080a0e010228020a0f080705010501082a131805010c 76
    0x80c003040040e501ea1580e04180405160001c0d007000700b80303e85034440d00c90f0702c009078681038551140464082c0e0141002c0100b60601a0941d0b4442d40480300b0481203408208010303501217440398009501c41310250352042c003000b03600101012070b000501003041d0798400360b280b600280e1114085542c203807999aa40d4225000542c2e200c0558400c0c10030101d902c0016600141c44000116400540030001200c440b000e6030200b45019004132801c0f1210b6500c45c010710084c5070136040c0e4500c000c2424a1580345d464250030003929259034201e904008100b0b20b0745902c01da8002e40000015200181c440c644540710100000c007800c50555a06040c5483d08061201a10f01030085a41d20a0040300b100044402560141d03100d40040b00344500f140242242c0f02d0009502c4543c480c00c1602409101d6112071003824200c2c00c403401a8044001276200b440105d040c40c2040c2542e106000003408180d9104003c9008502c03107031034003001d5074511072603e40103800d80d40c03210401b00c0707440c2c0c0100300030460a000f401c400e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 769812922 1250 769811672 769811683
    0x31701080f161413180f03091a041e03120f030b06040e040206030406090f0b070806040606080601050f04080d05041a030708010306050604020c0604060f0e07050a0506071a01180b0102 80
    0x404000c03003a264000503050800c150302803041d40613424000342800c80c0b10300d840c0360a20301e95004c680c1010b006d9009030505902201d803801501400e03120180c41c00f80c039248a081807065201d40030510901042c210702c4219020aa41c00650308006075080d010b148000040a10f1116042403000c24548071001185041c03003401d80e01a07541181c02c6442945442d006c11000e500002c00c2119015107800301500082c40f0600500001d501c92500e000050600131400fa0060078024540d03805a4a002410072174243d01500d030540000e82070901c5549c0c0c40110320400a13603c900e40025600d0f11030440301545041d8484010004c480012200140c031151100451140d0f00c0242c81c101d001032140310040c80400d440703a00c056048903000700014a0710484011140c10705c1c1d41102c06451090b0b95400b040c2ca518114040d0203504068100508111401c20000450405003401000d000d1070000c02e0403401c0060102c4004401c2c051200741c1c2c244d039a034540c50800b0720480d0703015424043d820500610303c05d5000241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 769814172 1250 769812922 769812929
    0x150608151003080f040317040e070c0c030204021608130e090a0b16030204091401050a050a0b0f0702180f04021504080303060d03050906070b270d0c031701080f16 71
    0x2071850300c0c55030f19210815004501c806840c0202000000300003050704e6220840c0d0803600311107649440c54480b5011904400270105002d210007840d600b000a03564208035004d580c0d04803001038550740da403203422001401140700101490b10005052000c020ba040012084803403101220032255911040d0740d84030303811210020002000500850310710200c0d250000c1420740c81d44ac0040c201a9514503030b8003500c24580c0b4405003510584018001810302c03601740c6018180544541c9400744c41c00c10006c0300743c403680d10851400d1802240c09001c541d40c0c08511003a0f0710404036000d03a24103180e540c04000480546040f4465805014201d004100f0b24003618121355000019508594076a000d0044116040100320200710003000b2030100e65641030054030700d844c010860030405140040c68801420204000c0c600700101910702c1002e010030008010b1b410780f50518050002d05228030b002c0c1e640d1000c0d494881401c0c50f61000100c1c2c0000c0000c1c6c100490003040080307030160310b101d14007020000060301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 769815422 1250 769814172 769814191
    0xc051216211403130b1e04080318120706020609060901150b0903010e0607030c020c06070206070224030c030f06120717030f1b160b041202030a15060815 67
    0x34080c0049010700e00c0c2d080c10710b65501c064030b10740340d80f542c0c810140e0300da02c0d080003405940c08158007403800044040030901020b10f03c0c50500c2c150401003031301d95a0207001c0c400c91000142ca03e10561948031010460381d21b000c1a02107078402919030501a445007021940c0004a221351000a90142014041c1d811040a16070001043c141860200e04240e840ba0b600d168266480d0701c2c0540d00305108114080c0704400f550342c0003445860740900281406100e81c0102c4c031680041c0400405a03991500311403055604980c8142c5420340d4074007048070000d03100c144011084d008010040b09820000055100300303001d9200b0b14075942d40808005daa82e000412502450f0310044091101007401081414a01d0604044a061001136203d00d06141c2c0111403100205c2d030040c80e03016008804000d24504821080c240051241c03c041800e10315000b20f103c0c0303000ca00401507010056480034003025203503d4200d00c10110688020681d080549158441c42d4224071412840301e440707000540c062800b62060700c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 769816672 1250 769815422 769815479
    0x30b0601080c091509033f03010308120417040602030318031206040e030403050a0c0906080d0e100c02060d0501180b010804260d050907090b100c0c051216 68
    0x1a0955182e640003058059003500c501c13140c6040d1070b100460101f0300b420003070085046110800b8030040b071000c610b41c00c0c280b05580900060002030040400e8500000c1000180025a0398a007000c844c2000047c008860040d800540031440c251b01000640c4a000354000065000001030706465a078420000c46040b036040324008541d46140a800030341101d0a101d0032213061640301d44425080003500301d0111440c41160108100c141007900a5000074241324000d080b103a5140c1902800f44240d0040c0144969003c0d03854500c50350042018442c00360300984443c2c0c41e0700e80800410000c01d02030280d07500351032154000081c0080540100b440c3ca840607075621780151140e959450109513080b440c035545e803101075401c20341c00325842e0240030100000300f80400d050070010030f0282072003695080780d005582030036518151503d031841c040801401a00d03210a0b02c21181c2031841120700b01d9040b05600020b54000040c2025000034114901805803060903c0103a6660390b18119908002c811344815412 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 769817922 1250 769816672 769816699
    0x108060d030306090608031e27010210050f09010e0601060f0c0c030807080304060f0b210f07060302090906090601080c07030c17120f0603030f0a09030606030b0601080c09 75
    0x300300c103015440c82420085840e43c2c032043d040e01540c986403c900c40030350003c00c4c2107122036004070245500641d100000c9103003010b030b1490780100e81001c0c5100b4900401e82000c0d03c03401c0c0d1080007400002c1d0200c0703104004500704240706400411042d070301081c803036007443e101c017402080224042d4103c83c440d80f80c0c0c1c1da80841d081ca0560b061611720b802030780d180034181800004039480400902d2010f01c1454038030f50724606460040c0c1143d1204051204444c0340012007581d5840d4200c0803030682d0100300310407500e0f000c403000c2c443c5414508070b0005183e002c0d5202c000344017509500508082001100c511038103603281803c1c0500d0840417580310f400104a00c012941c02c24003840140f101c80e01a2400944080c03c0ba101e046034548000c02c00c001d180c0c2d00280c0c00d080d0440460354941c10500c8071811038510701300140000d503a0701983c0300206d02d481001801060090103654040011680b001050000340d0ba02d04002800d031130122042808a218240041c40d208040320440f00d440000078500c0e05a0f160 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 769819172 1250 769817922 769817929
    0xf080a14060d0213050c03040b010b030129072102010c02010e03041203111f052d07180308031806010b041203210b03010606051309090512120a1109010806 68
    0x80c102e07026a0822004070b20300d202c0c40e0140c0101c41c800c20305404a243c1d641014a4602c44401c4140e004008041e1300784014400305194500309200542443c4242c0840e85810480c106140300d00c0710000e01840d4014481440780081301c0c0e400040304916002001054980c0304140d00f07982c050b061a8800d41c008100600a0450000188400b85d00038070b4407071803905503000b03500d103091076403003600059403c0901006004245030040c582d100358022410322281681c02d0180c5000c0401d050080307540300d001c10001700910711900b00741001e80d40741c0307034141e4620b0b6581c04e28410640c0140c4580c0352551001c0c404040500000480c2812101d07481080b5140c10302d03107001148031070301031b842c11401c000300e42c503c2101d1100550100900c10801903c001400c0c00400c04160864803141c1c8100144401801041c94030100038150304203c03101d20201142041c502e281482c10040c0d800304c15140d11074085a00b10180c62000144d510480040744100440b000c000d0705101c103030203241c0355180003460380c2000500030b09 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 769820422 1250 769819172 769819189
    0x302060309150a020408100207080304030c060f060b090f0a030503120a0212091627050c07230111070f150b060d0207020109050f030d05160606060f080a1406 69
    0x66500150350001d4a00c02c0410b14100d4142c03640b40340c076070b00868180028201406507000007441e0725030452904090b59100395803400005e0000d07003841200d003400014840160800e03002c080110310108a12070712149292201d400501070a070013154000808a00c07400d24055810a80f07402030002e5081a022600c840003952004051081c0940c092280d1200c89060303408141c02030003101d0141501154016181441c40c0b02c0303500c8010342c0440307003000102482c400d100c00d000142c40e15102285980c0d0765460704500d480307914002070441084207814003151800103806510f04558178001d0000382c4400c1c00b0140e513070040350400780c0107000b612013020020702c182c00c02055044e402e02000c101c0605807000294660040194007043c140c00180c3d8108560b449079203580a0b004c201e039180302401d861004280d481203108241b01c103100d00001c08840d01c2c1100c158010045501030018000d13031381c0f0f0360780080002d01041c440350007141602e07010a100130141c2c0545900191132a10b541d2072030b030b620703810056000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 769821672 1250 769820422 769820431
    0x230f1002010b041a010809010b1e0105190c020306010e070203030705090f12100b030a080d05041b080109031b320a06150602071d0c04090f090b06010e090103020603 72
    0x540d41c0d80e00e000b03181d444900911101944007404900f030300c84240d0000d09009001408030049901d4240c1c80105a5602e41516201001c0000042400c910030401aa0703503226903100c1b000040303126203d1108070341c1d0207185903060620a8090700d1681e42d0354001c0c43c0c1d580c8015614400960000d0002072140352291014128208008281098400d00680824401308000f0541d03000d54015603c00b00760f06499020ba401c0c640300c02e400404590146449101c0c040c0201040e10300501c3d280c00c0800c06101c2204941402e840d4140319140d0150f0341e4a032018020090310f107089011850400d5a0100e80d200007243c0808584c01488144d82d6010312200e26001108001c28002c540e0060740300304080800800035003100700e00c20140020300441c000e6103042883d84a07400b040440d84492028403e003a58014458003401c41c240081c0880c0d260408048224000c5400030b00100d80790521020303104034981c12400180d8060001840f0646462004554848841c02e030160007031400c000410060a011000b50342c0f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 769822922 1250 769821672 769821677
    0x209040f020a0201050a2d0908040503030f0d050601090b090d0611070302070314030901210b10030f060501031808090d05070e0712020315100311040602010204230f10 73
    0x841500310048102d801421035a00141c0d03580007000080d110511601030f003101800c040481c90242e01c02440d000e001908001000a1b0312107410700104902c1206a0700500001030a59844401e41410700156400c00403880c07a04900300404248c440d4010701000301030756410b0b80041d16012010080c00350301c804440040350318a550710400540305000c07002070210030344203a01074107255145042030050030207001c07800c0a0315041001210034a03130300184085405250300c2e01d82c24103a40d0403240607004116800380c140c0c201c0c0f9080e064200b480c4e8582d000c8106a14500d40401200d0307110801182115901600c0780d803842c8039940000080b0342d40e04050a02c6060050116129071034907030315a820010f40ea84945050340c844d00c1480003041e003210406080d0007480c902142107182071501c40000401c0c824407103000d080c80e00c454000d02c038481d40000402d41003803401542d03190b07954040203000394040e04c946c2e4580c41341c5007480140550915900040b0500c001c003078207100346440b0100221070307503603062103000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 769824172 1250 769822922 769822931
    0x1d06090a030c270209030607110a020a030308071101060803220b07082104260712050315041e11070b0103030c0312090308150301060305060c031522020904 68
    0x59841d9500390098050088541d20201e8000e600341052603a180340300d441c140c010b000340145d030749001074407550049062400300450100321078260705106050301c0283d000000b4080110501d40c0180c401c85c00b9841d00ea43c0d09540c80e803200c6002d803c0752614000c407103c9030170400a1070170f0360344d2600541c000d00e040c514825104aa44646c6139819910004c0d049881300e6000c41c00b03100002c0c022031401d10340c030b0310825a45aa4034151365094881c0c4841440f0200301000303080544203180303c181c01e4880c407903444500380080308004800903103640c00803180c0b00c21354203801c92a0702007820103006001c00079002042e131700e200c6400810b200000e494290005e03000b4210a10002c004600d8410f1020300030360083d103d40c0039158150400404618240b030002d00024141400c1b0000603a02440d40d650040342c0f0104120300b0290100083d0140900e82c0c00500117114007418031149401000003140500d030800401c550202024091020300140103000300e0342d054031031a040f034215940f07400a1016039001400000e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 769825422 1250 769824172 769824179
    0x1c05060a091d0102040f0e010509010e0613020d0f05090c030c09040b0a150308030108120403121d030a1a06150a030203040204090f03050304060b190924150f1d06090a 73
    0x1c3c2203070040d52111100032515101040592009214140901015a0401d03100d40c14016100d0003500080d00e014050f48a500c0000103511301355042d1500002d0b0319105205801000134420050081518011954001d50700000120700d40059404030003207024141010b65a150748992a100000400c0b41c80300c5519540c142211190350461b95019601c130340f0803039451b5414002d01503e000d4602c00d00e00c8210400700000d00114028400c0b80040b02254908209804c030252001544000344070300131a054414050800c0820900c00501100103a4205040700140e50301003c124030401c2c40089054642d20400090300c82c02e10a400941c2d00500181012808480580c0c8040705010403400c19070000b1408000d1000b00425801004031038101100c0d40505000c00b440000804446d03407103004100759aa0906030100f040d26000300702d1041001b000d80742c80b1507440d0701070501ca0180d843e227000000d2640b20800c4401e40624010190344400022814803080d0b01005d0102c10341c440c1c0d405c240e02c90070040000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 769826672 1250 769825422 769825481
    0x40e2d030a0f05070c1701050f1e131e0b1302060d1a04050c07030e0f010c030c1a0f0f0a0e030a031d010c02070305060a02031b0325020c030706030515090c040b030c1c05060a09 77
    0x700802648039080a4115281441c0b00f500750090190314ec02c8000002c00c00141e03480500752003000035031400028042c800c411000c0c0c0e4031030440d9131080e0410300b0070301045281f0350580007030b1484d540280ca510903910444030810244046469000b80460041e03800308000c84c0c07207280940115442404c521503a540b211000c10034407001168101a510340c00010400c40100c950034080d00801c40c01000e0004100005440e5105e00913003034502b00301513448120408207004039001d50120074440008105036400c180009448034141d0106850138464000460b503c90a240300712441014210b840900ea5503a0714104c248540c0003410046064421041503842006628420519a9925001080c00e24910310070b0500340003060f448502030500d00310070810114004180426181d4080f903d8244940e80c18601c00e000e4042c940160441c0000481000362215640780100080311103900a9214000d079825918103903241200e04640101885004002c0680d69420280064640c1c04a883c42941105802d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 769827922 1250 769826672 769826693
    0x2120d0b01050c100504110102060601120f111309141332070602060106030608151b0408030a0318030e0f040b040e2d030a0f05070c1701050f1e13 64
    0x92460b466445042c041080245440b800607c00c0031b0000c1c280c6d526111380080c1c0440000c014580f81161103190480b00518a0b502249204040d80b4145844001105440403400501e00071220010b15242605680c84002955035105054440090178100a0355890051130500403500d41114080080307002d428401d500d01600b0142c51010081119030324015000b442d00606904c40c80c203151a105042c0030300c0c0c002041c141e851840c110403488041c0c48840c900401020008140b8030215000b04002c07490039008030003040040c030950f4050100719003044c40003000c0c1c01c840300001c0c04561608020401400c2440b4020140b800080000580c11120b20115041e104101c03400c04503500043c00884420550b0760800c17071603140c8d0315107011284030354003c2ca03036032403003002c14000c01c1c08000030328240014440c4c5c0813179000030391000c941001203a0700c801968094401c208400495400c000c00140f07041c0344404258401d403042d141c0f5081360680c9059035215080041c5c040103084284070007680200f00018030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 769829172 1250 769827922 769827943
    0x150b070f02090f0c0703031113080d14041404050402042403150204060905060309030705010c03020a030e0d0f0e191517070804031d0918010c02120d0b01050c 69
    0xd8a125011040c41081084200100840a801d01041c140070401900303405880790140c1c1070600007411810010b26601c1d5005100b4011504105402c0101e04140080781c11000b0074115141c4e40380e54014040341071428000e5001c5e884a003100070300c070710000749041c2d00200e410a0000e0700020b80d9020280c0411505410400400294408010f0400401ca02201240a00d00c04603c0860610303040810050044042d885450320500011001c58181da8061003203440b020750040003044940d848006c054081e40002100101003843c140702000d102102260166110742c086c0e5404014190207141942c0c841c004a51058108858542c1402c4408038034840c48050a51400d01d02c10203240044028000c90007801a4240c0400a50500002da80c001c3c40403500306070316007840201d40d9040c807010185c20180394501d59110000d0400d001d03044070b10b0503003100c0010001c0000e000141840005907a0791042401c40c81049100f006003003003440250f0321514510005250852400d604c816803e8a0141d400c00e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 769830422 1250 769829172 769829183
    0x10908130e0606090603040321050402010905011d1003060806090601031103120d3b060a0e0606130204051018171005040519140105090a0c0603150b07 66
    0x2540c2150511440d4910004000a402040403860080003040042c003641d2500c5015030008000310702018002d0340d0311081c212400c200d004441e81c10048d00f4000c0c04068030203a000c076100060103d100d502c01c0e91514140c500c1300c001c034017a1201032014000d06a8030701820104041c0c0d14500400d0f0f0410a1001c0d50040c01c808005080c254110308182c13a00c01100365155101e41d000350300081c80d0030701050503580b580c80ea4090005007a4820300e900050081ca092004049812109a035000d46881c00c0d006141c4280140c1158102d03640c040c6003008952910b400307035140d54080800112140313000d540404003001036840241c00c065881000c87d82c00003800501c2000319030744c0368600300641c2d00075207540020228100c0383e00310364a55850090701c1e4013a060151200c1a2a40001400e1000030401d09044840341d5a00311151090b80c24181112140401402d00341d50920000c01c2440c180020711550090b04951015416850104142d004114281c01e04c9150041c2120000d4056400c80103044224001c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 769831672 1250 769830422 769830427
    0x6010c08040510030203160306030b010905060d060204080f1501060e1201021e03161403010b03090f03040b0d0615020c1201061503090516030b01050d0305070b1609080616050a11010908 81
    0x2042d0001c0743d28547c090402c105480c0032010070100e0341041e0700c20704490315884002203540f6040040f8400c90005100504441e00020380050524800105c4204203001ea00a40f2040e020741c10900022042c2807044100143c5010341040507441d29025450a891160000601c3c10b0180c004036002000c0e001000c1c2c180150120820144244a0a030b00159185920b054407000c441d0b40326401c051301040c050000c04410110005051034003c0102c100c1303032105001180c1d05c031980e85100400300e0380020303110400c00d0b007811000500e591584565500314202d54001c0c2400e030300c07580309228408040f20f030603200640d00e8010000d80c640c0b1080225504000a98002c25200c60900b46245002e01c4440707249140082104108003140210200d103042d03410884040200e4072841c02c0484d100d008546020f031000752030105002c0260300689000c0e80e2414103468640c90b039503480324400c2d11446d048410500724002d016040e04064032078001001d02031801d0600d102020290389040b42180c620107012104031900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 769832922 1250 769831672 769831681
    0x30607050a032903121c0b06070501110d0b030307080904020304150501031101080708150616231504030c0f0f050a0c061206120b062e080a0e0606010c08040510030203 73
    0x3d00a400c91907800250861800315625980c02000031a0f0b010304200a81d29601c1f05c4c255038a01088540031600000240f02d14074607401010400d90051035a041d01c00d207040311007180340c1404025240b55036001032500b41040100700a100282d0b0008104440600704846002c04400341841464082c41c00f4010720114900c0113070014144a2009e400c110034414420300b00141e040d101c0d05d00040480c0c007941c4007511401c0c030200300302c031141d400d080060241c94000070820040ca01203200600e40303010001261180d4108040300100e09006840203000208140041c40c08148900e490340300d041d114480c41c0100c400203407030713003424038074401c408a4a20b803007060b003003180e81d5104004007001503a2603070801a180c5003004a400d00680310b140100308003c40d0303000602a5a4480c4003520848043c406174108c51400860703814040408040705000c00c142d5400304034200180c1c03040c4c940005a180040c0010303201c003070064804c6401290708540c0340c1020400401d55031a50341c0a103091202644003d6101e082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 769834172 1250 769832922 769832929
    0x31305040b0405010819060e0d0203130906030218130c08010506090709150c060b04020f07050f0a1505190e01020a1106131b0b072906030607050a0329 66
    0x181c0c0300d00c81c03081c1e0a150042c05183c10101e07441c02c9100704040c0b03521441c4c0f164500780c0b0103801000d450071690300855040180454002c002085c07201d4411003e8040030341c0f521402e2088910074000a5040100030000c01005c090150034660407261285080b0500c0b40c1030303940d1210f9004550041c44440c0d44420612441e42010070f009a002083c60030406100c6081c02d03410101710b005811407004000c41290804140700a560190031020400340c015552514486084031140d400074100711341074821840240c11011000c20710301d01c600d51060078404990fa6803802017011b0100034001c850b241c1030f15851520307841418419222080c81c900700260f1201c41000018010800c00e5010321200d8006004104d50f1010000f40b03203840707507400480c01c100d4101c9030580410111054010385802c0b100001c0b44024000c6940741c016649141e64040c02d805140e240c003036000700d0010742d800d5406031711840210b40c0b86401940a49652140ea1600245000303082030321045d1180e2201c0717000c12601e05610064810b0a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 769835422 1250 769834172 769834181
    0x60d1b0f180e03030c0f04031a061f0819020c060a0515040902030a121b0302070e060f15160c030605010608010608040f0320031206030c010e01021b0a0803130504 71
    0x140c28050401a072101c00c1c0b11a81c0301e00c8010090001c940d000501c2c0383c0c01e2500241941d01844d04a0b815508140c3c0ca0f24004020030f00079a801031054410120000451600c520000290907050740c1e0906d60303888400d81d80d000061181090702e8010707024060341940420402115201340c039501804a007604007414241d071542580c1072020b00a50800c513820380507071000654000030b1503020f05804840c8000c00c01c02c99406a1823117100c900c0c08040030102043c950f0010f45030080d45d0220042c0450ba4030385000b00800c80030303680616034000350103562a86043c180040503019071801543c411034885072039565a40d107400160030496280b81e0703980050040503441001075000d040d00b42041e64450405d07032a404510115040018100100c40188401d0300000d030100304807852003441200c0c0c54410204071040968400c0321090301034410702c00b50803c50341c0318494003155584180c001c0e040c140001e800320b0032502c000c0842e00d03400061003c40003c80c12001c00c003e00e0b80d50145980210f24604040c1000240d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 769836672 1250 769835422 769835459
    0x409060f1d030a0203030f151003140115080406050c0f0714060c040f14060405120a020910180b0f1207140d120804141c200303060d1b0f 60
    0x40e4400d11201c0f0701c00b42c00004484d00030340f50034160540d03985c030300e083d110410603420300140d00300340071414180056803d500202d080842030101c0205c16a02c0d0000b8140c101400001c080c0010a02c101103030124101d544825040300990301d06c81e01c0c0c4842c0c0c11001d5280d510411081b038841404000c1e81d0f040140507c032042e0440600c44d041c0703141514100850255440900813024089415840740400703544078030445000f05005440120f591140104058a6101c2208241d00441d910300001d00c1c50315043c1d6a8909498040411184040c40d80038407600800180d82c0e03072504450403030f07012801e507543c2101c07c109511103d0020320b141410400d80d04085070000144030b0051591000c142c00241088d20300250f001c03c079103054840341d0b07228100019915005400001c160081c410650010218038600c00c000c140d060b00c408400c4120f0400e50140741010024008141d0800d1000c034505240c90914201c4c642d0080c54080014021541c0000500310103900c070b011310b24031120303040011000965018030003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 769837922 1250 769836672 769836731
    0xf0c01090e0601141312081908040308161103030412020708010b0d08180a080309012606041e050907140414060f044a0a08090409060f 59
    0x10741c100140080e021480d4460f07880c51031074000c51044901c0d080c684120008040031411900c0f045800d00b4000341c9517000051180c20440018885201240a0b2800d54091a4107075180e42c1c2c15900e0000b0700702ca642e8508140d00420040306580001400d00b003028500460054000ca034040000361400b03858200d0a030f101038010390610040013299620091a01c0c4a1078005a17016a01c101d540c0c240840411000d0480b98020f82521010131840c90020140c0190002031300e42000d42602c42001c9480701110f80c81d1038404285c408005102d500b400d80100004001d0f030000b40001c00c9004d4a00416100110b9036900c455100090030006d020180001084031441990100107940d10205048c1d00d40340020501801010f9a00c100ca40e540c845a000841c01c18240480c0d48106c1c4091300d480030001040d40c4a510b06803001e03c9160008040c0040e00860000e0140084c402d00005030b640c0ca00c0c58200342e01303440d807042c0e036962100d021a103d4060005449604d1000081d01d600000031350030b801c25100030184c01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 769839172 1250 769837922 769837949
    0x6030f110108060907020a080a0509371a09040204030206160b1302130e0f0a1b170d0e01020a0c03050c0a090204061710080307121d0d140f0f0c0109 65
    0x40c0b550045070980446412058a0307075510108001034a5038404c2d040b0941d001503300050900b0440c02c0030001222160007801d0b0302d45100c20100000b04142c1c2c40c01011000b0303c000c007000d60501c40c4030f002071500201c050009402d1540c0c80e0001501d9801c4001e0040e0410083d43e454401c00040c4a142c0e94031100c0f048203c40f00c00d401d034021034401d80d03400107403600056450728900c81b0408204041c60700b0044400072140c10382c4152410680340b8103d600c01220b12040400c0201c0e811088440005c0050b0030345c40100b2403007034035800890380c00d110301c41c54606500400702d405002c21b141d00100c2002c1c0d40504010040c44c170201c001d11821101943c0301c034644601c1403000f0b0046580c0030084038200800d0050030021611100c04800c541d14072a4000e007410b110000c0e40d4003c120f0910545141408903071a00002c4c022030810904001101c81c0125500c4076250303103000000f031080700391501d01040c0141141d00300000400d102c0c0c03401c88411382855480c0c2c00070180f081c1e02e41c0d00000000c0500001240c0c1032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 769840422 1250 769839172 769839181
    0x32010504020f0901050a090803191107050d0b0408070b2403011109011d03030409060f0b070c05131e020c120702090103020603070c0602040605030a06080c0f040f06030f1101080609 79
    0x100540200383c00c80781082000203a108035035101c6d112500160200c1401c0e25500c00039400c18060030140e4032401c0000c05c6604d000340c4882e000202d0800200c41c0050440390704450260b44440c0c01c0303403004000700d41d080414060381020802c91448030744135549501c0d28500c401a900d15400d81369071203000d4144a0b03810140400c0581e007021045d20007d15085c04c0810300080d5003602d10900b070b5940d44e075241e01448003080006000d0002d030000310803540514445480f103030303c5d6101d510310340c49412030203400d4212081c401c004500b00030000d10401480340a0002e0740048410017034080d80c03007004618400c6034010985000d002801e0111a250810488849140c02925404224a4481484003074407c40010002030851070060640c0d00310302e94884401c41d59240c4403030001c0d06076001a591140342c54074043d0007041d00d0303c001070400c040010041c000800b10b080801004003038125034070011403154407010000300082e49604261156407140c14a90080200c64000514040005102a03c1000b1000030f02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 769841672 1250 769840422 769840447
    0xc0d032403150608060f060405010512071a04122006070c1503141612020703020c0f060c0111070b0c0f04140301062103020f070807060e043201050402 66
    0x2011258803200700504071903449442c1000f4019644404510300a50041080c04802d0b100340700d1140320111340812050741c0b26802d11a01080304c11044005510840e800e02001802c04000c03100d1010180040d860107440e00100c4060400002007120360300178100d065404003a10294900b00803909480003403d0650b5500c441441c08010305c6102004a540c603401903243c0d10a4000d0754100b000d440b80700030941000b03081c0f000091903003005000001c4072000312088440c0c46000312074130590590300074481c0721180f400b008240d14008105991084040056800c4070100f80164030351119114540d82d240e071564140019686002000801141804c118105100d030314442581c1c15610030075251940203d0071401300b0700410702e80e00700801c5802c5100b480c58040b9902c0c400011890306c26820346401095211419a0321412401006c01e50b41024006200e4244a180c10800b407803070080c4042484240003180c5600c1013042580301c182000807185c000196112070260030300400342135030118940085410b10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 769842922 1250 769841672 769841741
    0x5060a1b2a051506030d080a0c1806030e010506150f030c040906090204090b0420160b0703060302011d010507030305040203010219020c10080405030d0e03040b0c0d03 73
    0x48041c003415001c4007000c074411507400c601102001072060301c0c54040d4102555100316010007031114440e410002141814080340c00706100d2000e484184480d281d0b080305002505840400c0700400140d800c41214a0b584005184020091a20300280f40c2000c4203010b400d66100400d103034010f64513a41a02d80c0c1c541c201e42254a0200ca03500c501d900c90305c481301d04662510071176101c00281814510301094102d0280d00a02c201d0725900c00c100542c010070020700003550300009800000088186071070085210080040c081c5401c040003482c110f2880d5510201d24280545281001a03905c140038421541c025000744d11040650141052130504200000c12a00c21100c0c02402c0585403c00f003011518250199104010880413001010404400c029600d20034028128030529107400582c400d14011500903000366004409549420000600c04001c1c0c040f030743c2c003a10f481c80100701c0000d0b600c42c1127018003c160500b102520b001c0901c200020103492034414298149400d0354800120f8800c517915 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 769844172 1250 769842922 769842971
    0x90312040812030f181c020304050906040b030705040507050903060a0b0a0605040b030a0f020f19030b0f0306010b0a0e09070c030f08060609010f03060f0b0304050d080106021e0115030303020705060a 87
    0x3080c1041c13090070031406040c10303500c0100813603140b001a06c00352410340100140c0281c6005950143c41507607040c0c100020340301e400204a40580151209015504050700079a5004a080c00c4c91894814900b021071f1411208858070120141c0c0d581e0b2003e81850901d4000b00100ba4614015061904041c0f4030038151001804103c0b595a542811041508507901914160610069299142c450114941a06415800c00e0340c0029151803c91500c07440e01c4a03002490000181c0203200d03a80c20b0015200d9585d100c18140000e000c00040d1812107644c55041041c4210070340da84011101419150280c5007005016014090108500801c2042e86655043d90300c8074038241703802044500140010703001062103421070600c2c80d04012001c0f43e414121001140528440c404840c0302d0010460201d401d24070a014410068000f09011080040c00080c15604003c2c03090000038403103d28004000440603560080b004240c000c02c4000138007009001651384881c18000c24049000036016010140d042c0302c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 769845422 1250 769844172 769844191
    0xc050c0d060f14091c090b03010b090301050c13260109050319080f040b040f0c150908151b1621020c010807030221010308190905010503011a090312040812030f 70
    0x1040c0a901d1310071000c2e40300501f407220459a8a513101d11045a203a440a000c0314007c0d03007010301064840004008031207000100c80341a403051820461502c51200172108003402031164140e0f0100d403000284203013a01503202d0b80c01590760320740c01e030007440d00c2012648148007030001d02d5041007918030600701042d0b4081e40c015801c00c2c8590b142d103000d815020306400080c04035100310a010450214240d141c4440e0b1080d40c8401000750b580f03884460359011100b180610710b20700c81010400a40c110107201800e60b500c84240350400c118421a200d40307807111003090700c1410041c45440950292042070b0841c16600d480613003510310400001800400c0c01070100810141d0004440501111a0400900081c41407041c401c281d40d4034202501241c0041c001c400307500070b0100c1309844241c082d80403003003200c1043c0c407881e0842c0c1c642241420f442505501c106440b51040003061107540e4240011700760b0388440c040580d101c6060810301480c103080101d1340c0c58200010010b01851044034515550711000c1d01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 769846672 1250 769845422 769845463
    0x1050f0c28031803021612173402040b090709032d050a05060708010608070c060609140108010612030512091603030f0806040515010c050c0d060f1409 66
    0x3074040700101a424032015000000b1070700c2c0410540d001c40c44915003201e186101701456102e4001c1c7c0d10041030000001c0c821000880b4140c000e60f060b6029207107103407282c1e4000602031242d4071100001030f81c0304400c55903490501003007021031805104980d2201e10030760b01c002007407400301c1000e85240c04034000609401c0c08400300360280103102402441600303072038400c03d108210310f01d030035962054520381c01c41e003900407507001a1480f0300c9030a465049070b5950b9a00040341e16509000c3d100f140002d10140c1d28980c580742c01054036020f600078092900c01c85500c8100640c5820304c002c2c2159000e800c0811900340c0b4134082c402095126081d03d90800488014856503204c00e50300b980381c5240c140946400c0c414009000041c1608080c0e9400081d50a0b07c481c00e1650318201080300301c8404469081b103d100201941c411540314454001800c0e120b10111118511038000041d15040480780882d00765480f2555130005240c940103110229500b0015a20f03141061080c040e101c1c60480000c40300007031303034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 769847922 1250 769846672 769846747
    0x121308030a0b19060305180a0b010e09070b0a110f01060b040501050903150c070b09010b06030a090302070b0c0a02120a0c120804150804050118020a06050a030b060c01050f0c 76
    0xf0a02400b040e031002184200015503608801780c0503010490300b50207113005000c607030b00c09000081006032215600c0016034859a00f403d40d00c0100540142c01243c26100d100008980d10304404014180c1d00c4440d01c8403c0034000b0044a146400c10b9042c44801c544d040803810041d085002d81604c00b5507100342020b039240c0d625103011070314000001315000c2900440c24184205c1c2560300c0010b00341c050041000405c0d541d1140c04650030b0791021078500341c1040e0708000081d8045055407200d406c1a200344180c40d03515a503208160881d400000f03100100d03030826602c001c1140361000391041b1340e0304024050301d410260764896180c0c1040c0c43c480e030301c40301b00c2005600042101140c2100c000d454004000141003201480c01000b00004071801c9400d586058140300399400489085400250f00400180e4031030b0030700e0303070032206608030805220901d500c7d0320078403800d40c0d18080503012003c6e01c00000645807408940302c0c400008042c101e03110f100000c01210b0202d440701c4419521000f04a45da1001c211107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 769849172 1250 769847922 769847929
    0x7110f2107030e04060b070c091e050a0b03060f060406140d020609030f070909060501090902030c190807031b0b04060e010302180d0c050102120a0c0b101802121308030a0b 75
    0x181082c00707900c20700e07095010a10083c164090301100d8010002d8005040c1c9920f1002704a0701000051100400000e141c820b00030099000158058218140840c000309a007020030300e00601958100b0540055604000c1c2c034cc2414891400100131800201c121900340401040d54041422001390050000040003151503c4c10031820703036a8181082102e0400d6600e80e0354000514012a08403001400c1c0400019045224050030484039001809000d2406d80751040200790b00e000e00244a080e807000000041c4980d003807048000440c0a80035040310302c040c40b02c0100301030507a504054050101032106000c110351021054000f4442803c0040c0d8613103a03008040d411102400425600c5100800107404010b41004803504403102a000c89142c0491900c0781042400703441c0031034000a9202a6003000715640b4003100d0b820003005480941da060310340001485120307034a514948059000142c038107502d0b420907540e0781c0c082003e1200140800083c0c0c4e0300c0903184800380c504092240c035418011503d0f41e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 769850422 1250 769849172 769849187
    0x210e0f04060e1503010b2d0310020d050f0f1b030c0f070807050114010b0702040b0f0d0b010602120406090b28090602070b0c0304060f0210020307110f210703 69
    0x14400b0501d4040e031030200e40341991081c4092200d4029420036403007502908220442c0031010b180241c411543c0240301c0c0003003c0c03018009109a0b40340c481c01c0102034101400d407008002038824044041458503010006218410b0087c002c000d0b503000120030003249070a000c411a5121407294400c51380c0c0e48442c0070300001e0707004105982c8842700c1c00141120820540720010040e540c42080244910b40f4269884201110244504c11540c0020400c0c0b00052a20358448011520010718450b00300000c2c6001c10403c0c40004800c031a10503080005200c0d45404100c1210170310150700c24545001d08004005103a003d8601c6030603c085c1000c1680d0708034030141090409100c2050350b540102d94164040200012403511a1b030f40580601500031860b80054011034560701200d0006502d0030340b40800895491191104907802c5029502020860030039900003075000c0c20072a5540140c84400c20b2a40e810b0113039030290560254007800ca01c0101ea1200140e90340013a4003200e01c2c40e100c40c010b04042d03c644 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 769851672 1250 769850422 769850429
    0x1207020327090907050a0b0d060308040608220807112103041404050412081308040b090a051917030f19110d0c02060706090b1003210e0f0406 62
    0x400c031003000034020400e000d02081c842808a50000c1192688109661140c07190301585420400010702072003100c4031359004040c10340c00c641000503060359a0710307540a65001a00300b000000d507031405001d101384211850150b8500700301d04091400000d5505d580741481002c20045c101c0c034202481000683c0d99001142c868240b503844401c0310780101442644961141c00381070040d810070504138245040c03912a903840390382c0c40724a903c1c58201c3c5020589505034001c0600004c080109480c400280345000030300024a5501d0442d610340594004210308010160400c40c01507100c61080b2040116030800b0340211110040203e10041c0e081d4091411480380b4051086105000141c0744280703c69404204007400c0282d039041c010501c0c1054442e180d83c00362103c1000034229060b024054a0000000c2101500c40c2d00e002440d41d140b503564010450046410440c080350003a400c10034442d041b41031404004440036802c444898020018162281036a0400c0c004d0320303540300c80104c3d5200c981c4101c025 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 769852922 1250 769851672 769851697
    0x190b0703030507020f0a0812221103010528090c150e030d0806010503041401090606060c030f03020322020f0a1502070e01140919020f09011404080312070203 69
    0x1910600d08000d00070705015602d200041c420220440c05800011940001c03d80c1e000c10880d242400b05148107202c1c0c100a00715111003000d00b00d0001c0c2c0c501082c0c0746007001601c2511540300d000041400c141c21128024010140e4000c10040555031155902204582c081e0b041e00000354104a801d02c4001060503030804103403c90b070b1240c041210b90b001514182044005c404a9070f1480018104656244040c0d481c903010840900105000600c0c4840d40d003c0da4461200000e1445090740744d080030f4421130b0340700c4c40c0030540c405054410706500c003116282e00e00305401d0551450406510000384140c0380c0003d03881e0382207a01903104c219552004d42e1024007400400c5940d0194aa0300c9051441342401084800340c0b0881d400002e00f020000102c9040b1012987c001468140d2401400901c413402810315000c41c0259609000c4c80007984003178002d00080307604190b110101c150000d0044c07968030780039841c102c000744005c0092080001c01c441000c0d60141c0107000c2c03500c6101040e8590f000380c41c1070119 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 769854172 1250 769852922 769852927
    0xc050907050702210c13180305030403080f0103020a1202061303060507090909120c020f030703030509010201180b01030f0201051c020a140304023f0a0201020c010f0e190b 75
    0xa0306503110001c1c0075510f008a401c441c0e605a1203616603404c1280d182c142800c1d42003140c08841e9460709451100d48802c41580c0407503150300340d5024910700ca0300100110b000c203002105000506030300002865108000c00c9820000e5411500003414002c6603100700700da0307a014591018210b456040c01daa4414100d05c03e100c0c680c0c0e0716431400c01e010703040c110384003800a084600e00290a82550140041c8a0b4000020b6000d03c50011750841da4059200400d98005000c60840c1840740c604008a0005601a42d1500e4440515500080c251403519031401e620403912543c1c2400b007881d082d8018112a80051041d008503402e10040e00c0e10b004855400102407101100039406100d80e40003099829510742d80e0640c01c660700e90000a9078041660003940108800001c07558000d400c94140d2040f10680c000080003140406089140d90010710004006070084056101103507010490700c00c04100034240200030b00401301c001042d00100000e50b40c46045944000d84890b10340d0648100a0b04d0605042079 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 769855422 1250 769854172 769854181
    0x70e0a060503160617010e0a090305090904051510030512160203070f030c050108090d030b030c13140c120f100b0c030a0e0901120f021807020a2109120c0509 69
    0x60001c0c2807041308040340001c2d5021201100658690781614621944403986807030751907a1000420b98041c080341448806c101c2d480041d075a100c1c01c0da104a100300001c0060405101447c0d464400c064807903035005c8122a0b061000445c0443c050000400d20070b0200c1c2c40d0320390044942c140d010550f001135018011a40b0200300303101441000000d880c040c20700080e0059a034001101e400000311902c4120340c10210518104030310030b401920700c0040c020111240c0141030380001e8800c0e8001c1003100002e946e00e00c5210704126040708290390110000b1ba00c18244602614222003044004003a001e52001210004984d540c404000001805c5041072054480d455480400d030350b5445441d200010400c081100c890500e48007c515058441c4c8019001481520707a40d10692840001030490340403000800d920411080c0c042c4880c420100740e0f000b019070300a00d062039094969211510781e00100074a860300000c540042c1c8080131503c0d50040210250924107010b600c1d00800c2c1c12150740020400180b1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 769856672 1250 769855422 769855453
    0x31c09020d0b25090b0a182304090c0303080c16060e160308040501050711030610150207050a0509040317010602010506100e090c130b040e180609070e0a060503 70
    0xc0c81050146100480801803a04100100c4806814500004e40c504030a1250100104c041c101903000ca0a091548000b0004e08900562264100140203c910308071308806064198030204a01c03c02c0d1001c02244a0a0302e840c1e0078802d213804040c01703004401000c00d1500d2100001c4460502e503201a070100106149400c2015151081900d08507200d50050001070420341e00c000000c1340da01118072494246031a0065591340c010102c02c2d1402c100101c1110520346007404501d200f002c01d980300031455401c01c210320842c00b00c18012174003198441e1009010301e44500c10003805a03802100d503841c45641c1c0d840c084442c5440c104411a80703500050000130240d80541040e80106011a07580c640c0c0407483e8011242888210350320740d4459a2440422200e0714040c000300b115031518241840d800352240d00016042e40700794031601c1519020801c102500016514903006009075001038030190410440a0303540d03507854000d00215803103075001700e09251407030381c0070b80010800942500d89020700183d14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 769857922 1250 769856672 769856693
    0x60a1d070e010216030b1503010f0203090d081014130c080601140705070905090a021503041703040b04140102090a0807080601150207090216020904150c02070503031c09020d 76
    0x4032804614044521011580007140116507400c2281006100c03c1c038544814039221000342206030314601c000c00307202650f202805003200c2e030350000d07001695a0070961011442c0c4070510300c0756020002c4c0030080c8030003002c1d490120801c80b80d218200c2840075403a800043d40b1204483e141c030b0103070751070709000d856a260401c0c0003078401c0710241c039101540080c10a240159101e034100040c880d4020050034000011244d100c142c0040040c13041f9100900690701040030400325030303000110040044104403c01c8281e9044039200740c40182c2a504609181d41c503110b800d88081d100800b064401c0d0050048003109505840d1120401000e0340c420907603884074503032125128003520380c640c05030400104200162a80c01800c200e140d030b005204071032518400c90000e4100c501607201810140c28120003580e281032449014900601801085210410304030040702c0081e800b40e0155004140c042013195404020784600448040300ca400c000c5840c8003020080c408020003e40c0110f8100084051041e480f01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 769859172 1250 769857922 769857931
    0x90b04030b0a0c26041401020a080f090d050712271403010612020d060e010507031d0604020907030f0b031b0307080118081c0911010f03061a03060a1d 66
    0x2010070801c0c2c6144011242d465940c0940005408007140911400042c82d00484d031060066881506185504646e0703030a90b0b115905442c0007407000703014002c07001e5262419540009000008025101e088240500180251000a81000c0e500000c00c003116000d40105070029050781901811840310401003148002b842c0140f008440d1602045002070405103d031030103680c50241640000c074825030801070184004081110015100c03c6c640026401c24003c245c01003443d038401107401808515003007141c0d0b4800d01c11800c9540400184009619091811a000384492078045060519255060003900d04042c485405201c0e51010b58040703078a6003d034920f044000c6064903490350341c501c609403d13034081d0b0b0328103a441600319a03136000007220040205003603040b8481200900030951016412a45450780588a6042503101c40d80c507507034045007250112080e410104021405c29000003a00b0486160740780e904040040401c030700d0342d030b541240e400600210001ea07140d540e990422200150042e00d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 769860422 1250 769859172 769859191
    0x40e011e020f040506031b03090a0209071809020c010213030609030e0d08040513090f32061303020f030301030305090406090b090619080d1710120b0403090b04030b 72
    0x16a60090000364002ca8420707020074140c80d03051a00f0711080101940c0060211101c444810019014100403640a10b11400d10030300504582c0d03a0034018400d04000007400001009000c00000d4440e031343c40158401500c199401c0181c80d544244012402403141c40243e280916458000008000d20740c0c015080c810301c81c0e55542d50700c01450302404100c40034000001c0c4061414081801036050a80200d611114065004984000c194603902004044a01c3c240c4004551402d40014645071110701d800703130024003001c800e504180c0321845449030405021103040701d80040c90041450320030404072462484203410340c2c0e500c0d41c0d2403501511135400b00300c000b4010380c00d0410000d44002c00b84680a640000039240c01d42c0340d5142c00030480015014441c102c1d804c001c5600100d42c402c810032040203505101c0c3c0b521581d001007903800b4640d09000419003800c00c52000010b000300c40120408189650f40403640d10566102c3d854243e40d164001c2c0c00c40020b1a50105000090000c0c040345580182d2010307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 769861672 1250 769860422 769860461
    0x3020c130b0f01030605102604060b0f0619180b03010e04050c0f10030e0f1f0e0a020102210d05100513090c0b07170f1207090e0a02090d02040e01 64
    0x4800541c1a43d05c40d1062960005a0300e802c070000b80d000301b606503001500110101201c3c00d082c032440220f143d05a0f0165071040e03035048030302590705000b44d140000c804201c40080c10000e4050170350606444100b150701c00c000651080100362010700c032502d40175140c516080e5440750b84071807421003007070011a4143c81510407180c0900311030030700920100307410fa405805820f00d00c504400a502800d4605002c0c0814070030030105421401c4248200031030703c20b020b04488066020343d00c243e0243c844042c1031304056001a01c44100523070b000220241c102c03c07005812030881031400701d42d0460340185040104810704010410001c0070424800174280c0b00c0460f62414201181c1501008440b044040281400314000c001e200344500708001d00162071180360f403240502c0307044840c07012a0300010114040907102150b5410386502c2250484d0b80050745240c11702906e0b140001e002c21044000e00030180143c1c0c00140d1048a84680448100e81030300030f0400e004807040da04038176000b0301c85c18541e0380c1c402004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 769862922 1250 769861672 769861699
    0xb0a0602011413080d0515030a03030c2c0415030506010303052a060c09030f01020d0506100503090303041e0203030a020d09050103060807031403120405060a0609090b040f03020c130b 80
    0x1201e181c19240c0742c2084d80c0b0703801d019441588400400001e0001444c40c007070b0400c134400d40ea604102d400d24041c86660302162462119902410200c461131162001104d120380341907420010801c5000c003030710100ea011580324514084c1c4100302c1c2c2c00790800b03810790117010008800d00d908a4000d0482420039000c40503103000d01030b1500c490003100c2d07032026025000319011552020350b810142000a20003800e6604c207000d144101400ca07804400388020b500d071030344204151460283c101702d8681c0303103e0521500d58074000c5001034513440b000b00018444640045e1094402940743c122000066015044030b50381d00210001030b507521502640e070300004d004101c010995500c070b0301910045511060062566900b542c0d030b2aa60038240313111800c40740c0f00622503450f20060405640d4003c0d402000900302c54182500c41c1001d80d856604205405424101e80e40c00080703004c50240c2e805034110952202c00f100a2030200d00305030070000d0407640200540c050300c1034440c29034003030700c9161400c0b54002e010840b07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 769864172 1250 769862922 769862941
    0xb0402071e1b0305250f080705030c090402010210090620030a05090708070b210420010206040f02040b011e030b0306060d030203070813030c0f0602010f09050601180b0a06020114 78
    0x31207000040503508060010080d41411700e10281a2000c46690440c480f5222000e007420215194080c400c2580400b1040007142001e010a003144082030f200b60b9a1403406800203542c03407540100134022035a4074820750b014451240d000300c60030924110b40340c0c0001200002112280c01c01d641858001d80b800c80440c09031000001c00303400306c40c0303d4409440964a0300c1044c0c4195041410800744450fa4209080441440c1500441c403880c46440e4822008000d2103003510205400246641550712180900010695440703402c00340c594104c03400314114901d000100c031a48401d00c50301c001601422050b02c00560107420850040c0f03029011034241d6512070341000910350034a40c0c0500583c104000b21400f04424000800340710f9081c22489450540e60f0b0384924005185074098030307070341d00e0094060100f43c3d07081c09807400b03282104501b88902501e42d100d040c1c81c0c1106101d451000740910b0f0300b02c0300d0b404041d0014001454020401d040b290760fa128068040c01990007007030007a462980c0042d0b620300c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 769865422 1250 769864172 769864223
    0x40b070c0f0b13060513050d031104121202061503030706020c0c0d0b0118020304080d1d030a03021b030715050a06090e030d0b030a120c02130905010b0f030a0f060b0402071e 76
    0x83c7c01000910400001c4e5506a000b0504003400300e610310820480810542c0b840d060218801d07110b121402070940507003600a00f0410b018008144401c110a0148000d6a000080c0c60070309801500069407810010312603490010301508064000190190040900c90606103d90484842800000c5003818060843d0304920080718002c060180a006281d00800250300c64106120b411541103441c0c0340881c0760503e076404c260130100010350005044401170b4440f10681103200c002d04021420303c000c50303441018101c20511192282540c1d6000150a01019003080c0001c0504541c10444d1414010260742c032640b10400c0d040001c0c0c28101c4c10b103000c1c14001240280b0700e42064072000702100064080320088195101640e000c00c11035136020901d174551041608181c0f04a000003107241c004024049852600000a8801c1d084200060081403403140301610065201d0701c009003c07992035000a0081c010940e01801030101c43c1144048440d09941c1007140a000c0c008480030102c4c4250742c0d81c0e011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 769866672 1250 769865422 769865461
    0x10081f0c05040e0408090f0604150318020102032b0f020702120606011407030201090b0c0a080610050f0f0d0608100605060403080f09280f0806040b070c0f0b130605 72
    0x18981400100414440c0c4040c00c1800802020403007c094108001200340c1c00039046506024401d680340340f1040d4051248007007810fa080200071641c1c0858001039101c0c011002c2c0d032400d220581c3c819084011800c00700e0040860558020407501e801c01700700c200290840780c4128001c16525401201d0301d20001040c601c50501650b603240c12003034807120350715950041e0004605664950b09407200041c0014002881001c005604a46130300942100603c20705019000718040d01c2d0642c5001c80310b030b91050444000041c050101680ca15a00c9104c8549224000400c045240341180103e405400800c1099404242c3c170300c140003040d11a070030885184514030004120342010051210031045030409811803910003004035003080c1a04043c0036003211402401d0958044000e410300c4500004140310703001d811410300070320851809640300c45440703101820030000d101d21900060300300044090060b40c8a6400350212382c2d9400e0918100c00714803a012012942c140c108000038001e01c0c44609000001d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 769867922 1250 769866672 769866689
    0x1221090906120a060c0507060b040501140607050a020d0303050108101109010c0807020a080607110111070b101805060a2112050d14041703040f080310081f0c0504 71
    0x1c0d00c8140070081d600d103a950000d40d06000b0005400085a680e21800c07203103507280d0b1116a0313101e0782450001c0444101100440c41180b030b180040c0010f80d0b03040e07110910907805545c1a0ba49002d01c0c10907520b051501440254007440003500c1008055258010038125410078040315034540030010002e065035800a4195078085c0b00b03004a00856100301c1400b1981405035001c42d2a00c1e0300f40c2c000c6060303030015400514442e40040248216264807071041c551201c4810020032062601c1c00104000c2c0c40b407120040c00040d07030040441e08400e07181e12820010504400487d580c076400c004403001418040b2078042c460110b0507000074109140c0d01030300400c1c0351540c0300d403840b0f80c909681d212000c040300c00341002003000502c030301c0e00304480038445e0000211a26803404820301d0b06107424080000310041c1c2034590107060050100280c5d180301e0f00400f2551050926450b69200400d000c01c0c820742d6407060b08030f8842c00d0020389201690f4242500e281c90704440c06d200050a403c800d54242c425445491507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 769869172 1250 769867922 769867939
    0xb090609030319020c0604031701050402270f10020a290403180f080105060a120206030c0c0a0228080325020a05030d0203030717060f010503090c122109 67
    0x2101c441c111203210f240b28555801401d150a0350300c80340c070b0420300b03c800301c0104a00f111f50f541500b8000c02c010740140402c403402d500e080409020b80300b8130503140a401c0c000c49030b06280d1801c0c56440c011401607a03040582110300c03035140135100a55503001c1d004282da640070341303142c0588142215000740d1401c0200d8210b108454481da80c0071550a001d04601011160850101041d18121341d06d1000040000100104281c10040c0410003004440d510121141c2c21030842080144c0b00ca4054a501450b4032001607101d110050040e810a4030740c0d03100941c400610310010718003001068140c03d0100c1910402c1c8947d0791188100c5035280700300a600382e403c2c44180c0f400300c4019140f01c0068003051000c1d01c12542c10f03a03034801117494185072401c0c0300e0268101108010403250300241c5100d010784140d0301140181014000b0400c24015410260b040206c00400a135000104000d406203032200640300301c0f45007552000d800c0e144d40241e00c000e8100300c030b044842c1c494140703501e042c0c94560310000c2c005d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 769870422 1250 769869172 769869181
    0x3060906010809010908030a0608010f0b0d02091b0f0c1005040b060d080d09050c011115060603130f050607020d050301032024031b030405210d180b0906090303 70
    0x403101c0b4002824100b0541d02c072800c14001460940c06540240303000c1c40082203582c1007461103030a5400c2c541071100b003185000034040d20f41da500794841c410a60151084d1a042c7c44d0002c0241c044105010352501c5258002685002689048010070140f445182a18010440c5011410a0715400d50700a03144090980114545150070071414100a1244096518010481c1250419108802003d590581000c5004005135030460005060b024151000d448800010358403440c0c2c800000d011640208400700000d24100f030500d0305401400d800140142e11042c0a1506595910040b150b034401400b803050680e40e41c9010340d0540e41aa0f5200290789400350001c6170700080f500091614560050f0040740b00801aa8000b59426407103030101ca804d552840c12144075a082e942900400c00ea1190410401000c101d002c00e00d41040555000309000d20285010000300318002e94220002d003a1400c420582c0d500710342640032008a100d4090700d00d80c0d030b0701ea514054480380120340e0750070b00d03400400028 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 769871672 1250 769870422 769870427
    0x4050f15120307050609060103020103060509010e041205041d01062003030a0902010e090a06141002300a0c0c0503010204080a06050a02040312082703071104060509040b010f0b0306090601 82
    0x341d40c0e451501d0899040c402103480710b030b140c00429608004d0640001c0b00610035540e140c01494083c060130340d12012207514000000e0b078080d400400c06010b43c012111706040b2103110300d044800828043c0c804691600c0c4011007600294428071810001c41c49212410300d800301d01c100d020a0342881003000d1401c664880e084400580a500400ca040003403208003d400c0e40e030b4011740305000d42d1107800b00207002c0d070a11660380450514074001c0c0788605c00c1011140b44141c0e0000f01085001150340ba0400841c0030b034100c4000f80940700c6408134600300041050200654440c0c0401c80017070040e02507401495584003810301b01d10442c000e003805074001030424000724030943c001c1030308403942050040c0340a949448090b031445004001c0310015182000380580b00d4041c841c1c602131a03030f00f9800e000350340d40369842482c0d8a110710b2000402c020710041840402c1e0b40d403580420000d1501030807001c0741d4035061a2000303080409010350810590100070101c2e4820020ac02d50340b103014090182c07045500d592005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 769872922 1250 769871672 769871689
    0x3060c08150a0b07021912121404030f020112110904110f091905040606050d0506040c1d010c05100b100206060306060103050a0209040c1d030c0f09040311061504050f15 74
    0x81e030300100b00c031404140d141e021450420047c41414003a00c1ca07000549070910b060700b89002c10f0710811141d0140115102400c03021281129445041d0358030710711880c80180d807940e030510440a00a171511020b01b0598242c50005e0601080440c0d0400c0440f0107110010340030b000300440580030200c203000b0030600e41440f003000400c0c8008a5040304280c4e50743e40c00034050720a140c110100041001c103541242100038020290404011101404802e643c103034000c0046484011018101c0c00c1e044000c9100e90050502c410425041426070310f01c0b024a1a45c0c070081c182d0000c1c00da01411800030900040c600c040349081c02200c0040203080d03240c031110b0046028000180c1514050f0360300300030300d43e00350765544602c0e152400c503500c0700d9120080ca0054070446401c1e07c454503010b600001145100d55582081c1c000040c070302180d40b4030036901c842c14202c4040b890032030300c0443e074490002805070301d01040c80020201b80c4111424081981e60600e00765103240b00351030000c40b0501e0125541350a207042d200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 769874172 1250 769872922 769872937
    0x312020c0a0b07031d0f0a121e0201060504050a1404022413060f18051e1221131509120b4003140417190f0807170403060c08150a0b 58
    0x3010200122700136145180600007a800c2c0300580e544000401a5050a0141d9540151140360420610740328214062568400800c001d20510322403002180440d401e40342820018414104662541901c0c1080300001c81107001d8403012400024104a01a101d07403041c0040c4050300001951162a0209110210301110084288065003c1800140b6200d05d01c0781c0101000317540081c404900015811400e1000815000d00802d00412003180410070182c00c0001f150800c0c100b014214400f0303082161010460740000c454458486551403e0101885002d03020741201000d1041c001100c1c2d00c402040c08882d400512980e5200c00310342c00680707003142c1488201c3d0207414002c09412402c420207006034015081103c2c030742003030070100d0201d4408010001445089d45c0c90300070040c0c84d644031402c07180000c95004151210000d002004c00415a00045043e01c96480f0a07480d16124542400035068175581a00001c1d00d0000056900c408a01000b146240103407035400140e040ca050513070f0640c4070700d9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 769875422 1250 769874172 769874177
    0x324040201050415030b010e031c2d0504060224070e032d120a090b03151008220206030718050a03061b0504030312020c0a0b07031d0f0a12 61
    0xc000349113410360748040d1031041d41c5e035000a404600840050561300c5000e034607070300030b5000b40c4121740f058201c4003018010348401e0924015501030140c07001310300294201072030f100304030154503441144c1d00a0301400c00e655464095540640d80c80040074000030034822108a0421110701140d0042c0c05110500d00014020341503820003903d1424206140304140c200042c807605018100240e26400e104840d014114000b002c1d01d40020802c00030507004150103079001d00e480c0000801c60303621003c002403580d03da0240a02d1703042604860b000e81408c0088640340b84031401d06500c03180b22071100b91385040043c0d0046c0329a00b0b5885200c030440320b41d400f201000003411034a03000400c49030b44401101c0000c43c45070768042001182c88460700903a8109414840c00c0c03080c1400b0910029400a6117407402d46207c0c280140c58211401080345440a4010054180d4402d00148401c4603810b80014280f042000005e074031005d40031104030758460343c2e180303402560f410000104001500384120440c0443c0300c0d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 769876672 1250 769875422 769875427
    0x10807031d06010512071404021b150a06090b09011701020d090f0c06020610060e0d0f030908010c020c1c05010e16030b010b09010c030305040303021c0e0606032404020105 75
    0x4000c00380002201d62104254401d900410042c6841483c48001c0d0201c01e01a161483c54019030080036401c4552180c440d40e00403e0340700520600080d001841c040002c1115003090520451003c00001541e040d2a071a0501c140454045502d0140c0e0405040c041c0012800303a00c0d003084004400210851003c0380e54003007000f070005841d01d0113a00c10060040100400702089490070b100300da0f580c1e41c404d10039034021008100911b10005224801c03200311b03051407103000d849500051201190880000c000f070758220365800c00e02da40500c107541510580c0e0000c0292280214050380d541c0381c00707400705910400030309601179a101e074100000c14041c404d20020610000d0640d0186c00c007480ca0528501d6003022a608000b07000000444034018908114520325110719540020400e00141001905068507035010404040c400d070304907104a11070100c80c1040c0300c5c005400c1c0c0b01400d51008500c0c498031a000c00f007184c91402151980442461000303014403401c6000383c030344c1030000c0144168140a020b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 769877922 1250 769876672 769876691
    0x7090b1911070e091b011b080d0c081006031e02180d1203050a09171e0a0c0501050a0216021318030e041d031c061d04030206010605030609040201080703 67
    0x400c14030019003d0700404004600d0b05804040c40c0a00f00140385403140b80384a02c0507002d90f040840328030918810110414000802e05101303201c1c2c41035401d404505d40c54103000100d03540d40030001d03e00900302849002c1403039a40b0311049007034540c0941450030484012030448201d032050b50041c0042c0c8422204003489a81c0f140c00a140d4000510b01a036107540c50074039940398503034544145584905c82c050708012000e03498444400c1c00181081e2080c141100058040c200c128068000c601c1c007035018180c6035504803100f00207000f103007170b4541203072150300308400b18145a02c9230096400722010034070354010000c00e5808012841000303882000300d07103070b50f00324400a45000c0e48500031000e00075104c9404405400c03080c041103030ba042840b20100e00c0340811400c0c4800d4003004848806410300f04400804040c0d0503000c00903d02e0b80d01064035043d64940e04440d922045e03240c00d1046000303800f910410ba0382d0f03c8c030580b201d110840300c1a07031100007440002d00540c020804d0325040340d041c4c900060070000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 769879172 1250 769877922 769877957
    0x130c0e100c0f060603031704030c0f05010f050709050312031605091504120b090307020d0201030522050d0806091003061517060402040b060f18030c0d08030a0507090b19 74
    0x110400241d41098466606205142c0c00034081c80b0f46903c1000d07c65a20715094a000709408a100e500410f603c041c82d0040303007400002d40002034091885101000141440c03100540604082d100c0c250181c05040989507004443c5001d8034800d901c650080380b0214602e00048a00780e1040c0e55030b5a10400d4104038507884140c08014001400304040c20501d0340480d420000c0401000914910700c0340c4c801c122040c016141c15400400c9030340e0a080205842d1a40c00c40e089001780041100d48080c050342640c141032080004010312851107a45541b003003074403000300b40010020304490300390710800d000904000080755a809001c80001402c20a02e1494446541d03482034120841c04070703580e901103c140819441d2500c507400080d041251007914103403500448000384e0040c07103500540001681c0c844c280700c0d10240171020079414010801c000714591858065801d0308282d42d40d40d905880d0800142016010b44991816a111860640d04000601000e100c00d000202d0581c0100b040c20030001d1140b02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 769880422 1250 769879172 769879193
    0x20705120a35040320030c1e0a0504060305071a040b03070302130801022a0c0301140a240e3303120f0a1214070806130c0e100c 56
    0x240040760146a9280000384600e01284091400b00100000c02c42080000c80c1202a02c50310004d00042c140351042d178000290400c0700b07104015401c2003880d401c03400c42c51215691f00d140b0480c00c440c2103100503124420300040702e5403800010841c3c1d0180d88180541e4007031a02c002c038040682d10400d80751036121015000f03503410941d80720000c02d4010400410345e14241a080c13001d401d00500031800c05100010312602824403d021440400552960312042c1905008031380c11520060b00a10a41d000e801d6120b0401c0411100445103a01e0015800213009154901468461034520829201c904107003803040401c0010381b4001e40c2000070740d0b000000078004003000030760015541102d868070f2409000d040c144481034151803120f4208120401c403202e101000c0e503000190902e444405a400e0701005001441c44444043c0715242120410001a41c060b1005104490a503a0f00b62010703d00c0c4020009d854916894801288000705521030a0904c00b103c60031001c00c604e045904c076904d41d200e409150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 769881672 1250 769880422 769880453
    0x31704080405040c2d021c03020f030c1308010c39030203131212030902061b03130b0315010f170c0a1103040612020a050405040e0714030706020705120a 67
    0x3411030310b44138915018a4101c042c003e03080314080c001170400e00320300948565002100386800346c2d9001e1944011446035055890235818901d0042e9607043c00c10f40c800071900703c015a541c81d0401d03c0d10202d2101d0f0103000b0240404c8060703c0ea802c0d030301c9011015469003c030a051402c3c80c15102090450541c140b00d2a40c140702d030080d00510b80c5c841c0415009038940d41690810340c400310244148800195140b18900c80d00c168521380000d40c46d201c0e1000824900c19401541a0880b0300c0380c008001400c01f200400150041480455142d983c9200705045d90200b200c4003c440181c50502e204654021030750301c03c40a00502d0b05109800e01c04010508224003903425001542d004107031900c2c0d8030303001021200038220001c001c0d410310f8900b540c0101400c4042258084941c1c012628800c40c50281083d100030741001002031001d07584003c801581e4292a10501c03400120007083c00c00d460070041507600c165502d580c0905045030030002409400010500510380038443c00a480020900c080c1024112 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 769882922 1250 769881672 769881677
    0xf0617060f0306310302030405041d0d0e030c040c1704030504050d0819174c0b1e03180a0507240905100207030605090307140604031704080405040c 65
    0x90001c14601c81c0c480b0910446400d41d003501c03110000005c603400205550455104440210312411034030624034544410404d0035885205a520006000703030440d801a051013402c0d0200c440f550b03181420001900c854594240100c0c1e0911800f048644401c05c500798890301a0a01c81d182c5a600e8001c24504000c540301135601c0700001c0341102015400305880c01c0c01c07407460b19100c00c440c480301d940c5038050340020f4100782c1144040300309000c004210990a080c080e61080d01a00d54180480210280020380349451240e20184a000300c2c800c0302a505880c84480384200c0221007860000c0200b88d07641c0301a1000707c8550f0401c00009440340c081100c1c0350424451006000780a2900301100785c2d140009038000240c000003060404035a9000d0741c600304480d0221807894135203e0301e900a0b42000c0f110340000c1c0c209820b0000b044840f100000060101d1f51144602c083d034091802c0003541c5030382040d200100000c00502562810354003601155821a01455a0340c1c83c00740e0ba000050112071812040750007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 769884172 1250 769882922 769882951
    0x130803161103010501080c061e03181c1b020d020a0f051008160c0f0c0b1e0403020906090415050f010306050919080307181e0f0617060f0306 62
    0x4011200a041c0301405082c0d000380180e5041803141905e800382c0c0814140680404544031301d5414039404002050320407244202c0e90ba0402e14040d0350a9000550018401c0c803c5000e0b60701c60044103c403a580d604415a900441000b030500440311013681200b060b41c0c00500b8144400150f0b4555140200400c40007007003a41d86071030300c2c0030b000302030402d8248181030180680030000400007018900f501101d55141106051000386001120080c020030050103180299801081041482c002020b62450f610385021480441d0143c0400510690100941240e80200401c0303107420540c01254005100e1a41d2401203210518a84101c6904a68101c1807100c018010000c3c0001d510480f0340000041c00504242444039044a9034150420710043c096400000096031440c8a0a100e801880443ca03208500c0b41d07440b109081101e00d410b0300ca9100d0001c1c0e420014500324140d00390800c0318420346642c0e021901c581c803102c1e01c18400401c1c043c0c00c00c880414101c2c4565041c40300d18070030503c03203280c1038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 769885422 1250 769884172 769884217
    0xc090905011214070e040b040c090207030305100807061425050a0c0905060906010f12020705071805041505040501020702090406020307080901060f3b04031d09060402130803 76
    0x6042c01c210640c1542c3c02204041c041d4007038030b42484d680030742c0011000080e81c82c8ca20b0000101d01d00c41e80800115480030451504041d415008240240c503d0908000f0b02d0780c0f9489039a0300c9101a01c100710224400c04200e2007400103c0010700000d461500d030389101c459070b00c010818060303004102100d15030880d1071180b040241038488a0041e00c42000200241e04c1c24902164840d0009440796040c822042e200654491017030042c0c1c580c80b0710350f202c10341d02d42c00a0700d000c80da10700301130003040070051000034110741d601202e120741d5100e40d402052920308112100a40402000c016100303035400e5400300050400f40c3ca5071203850b4066403180b9001a528684240700410b428400707001a00d5903410301004210064589000708155144c070b04c190400c42500610301000d00c9003640854441c000c2421104100d9480064414411802900c0301081c0c403400f00d503465621540da8805a610851702d1001c1030407410541d000d42015110b20140440040d2100c1800740b464028413000d00c401c1d001074000300c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 769886672 1250 769885422 769885433
    0x100e011103160212130303030234050c06130608250809010c09060f05091c030e0102060705090a06080406020c01050f09070b070b0103020f190803130501170403030c0909050112 77
    0x4e035080420000028101009400943c0b030040781444042c040540210f145400c120340d11301c0945610903400302c480f0800a2200b5814043d0300280f0041d42c036801600b42c211047e05214088a502c0b08220004071070443c00d002c6d055449200290102c0720036880d501410112401da1304500940b60001c2d1600762032441c1500c462070035204410468001c00001c2c0d8403c002c80741d0484400d5401410038104640c4940c0040302150255499118003402c0111009d210001e141e040b82c007111410340f00b03a00340d0315240d0b100801543e00303215040200c1d810411f40c1c1300c1000800e102e000d8091300700c1e1144e000540360a00e0194101c0c2910340680f2003143c05503c410520036180003c120000050400c0798206040c140c003a01c07100b005010520019000d0000c01402584558600601941e40013188030707000982074580ca50b141c1c1c0ca8200103100c0c104400041c030003245940c000c5201c1140d1520a04060080307940b40e80c4d0440290840540c803100b0306c0b42d0b0b03110110701d610301400782c14040e1840801c3c851520480d424076 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 769887922 1250 769886672 769886683
    0x9040501050303281b080712173420010917030603030c030301080a11040501050607030f05190809160b1806091c0507080c03100e0111031602 62
    0x9503210b0351040000800c014a0004c10126850b080b10710340c2d08084203224161248074401043da6240383d5042040c1c010080204054030341d0718066040c90001e42c08502080d0741103610004507400c3c1070050302c0001e4800b1083c250000c005070b000d03040d001042c00958071404c0000b07507000024020401854130f852114003150510100c90104000031b01ca0102030791212030810b500c044e410841c0c440000006130840d1010012507200011900c201c90740c135a55003907000d4650400c3c050440e51000f240c00d0710803803454907019950685000a12a502d00449a07400761340560074a2052400e1142c24850b1309404800303140c60b902803c406444041d003a05e08141102d080490160710f07115403580882043c07000c40c483c00305442240203020300e0806403101240000307000e03010700321209601100c0c00305c810b6140c2d82c0c0f600310340090a03c44c1085a16254440a1280e00c03000c80707114003034040e44154a5a10740000a41010385045091000007030407000030050103185520884544400071a03503800c041d81180e04124 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 769889172 1250 769887922 769887929
    0x307140a02090c0a05180315010b2508160f0206031003021207150503070507060f021b010902011202130f06020a0c060c1509050f0d090f09020f03010e101a09040501 72
    0xd552038030740200b030058410b011b41c180c0c50078044500d0000b00240d131001c20031001070303102d0403c0001c455a0f65003c1c1c2c49860327010b20700540c810724900c1440c96468003021900ea00d4141e21800a50404031841c9d03040d81c2002c074a03541030301c45820740d0070a980513840e038000440c020102c606215507e5800d50041c44020703444112075440603400000c041040854880c030300d6000603003070f20f41195031fa04c1d0040e049440f400382c0380300a002d06140c555010791030902e5900400b803400810209000d0440600701d11401c84603000d4019001c2021651140c140854550040c01514443e110360b84100d500d070f024903079803014039821110259200720660740c2440501c80840006088500d420354904030396a6402d180c40c16500c2081075590345904440e02004402d0003080b2440b840c41d022590703618040c00005040212601c601034140b01c1403240410040802e0003140c002d40550040240303182d28004a8415200008294600c566060300000c10201c080310070312241d0303404442c40a03448007140390811040314010307070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 769890422 1250 769889172 769889191
    0x3c061803370504080601090905030d020c0d0e01180e1003080310050a050d080d020a11011418030901020a0809040b0a0b030108060708041a061504090e010501050d0812090307140a0209 80
    0x7104104c0c00c000044c0c0281580d18091010907086018601546036000302004105074a0012800c6800100e002454940c4100a80e4038000c0c04a100d0780191350400e080c61441c41c03000202c000c140083c1d00341421640c0c0041d030202e0f082d030116540340c850741d5450304207640b29a8101e041410801c858504a010007010b0841100e0a80064056a90701e40452107a0501955640d03000f01e0a071480900940c01590b003030803032a0080c44400760706035002e41c0c441021a603104800ca42d020412190b400000107413040d034203068008040203550754586a03429088009001d40c401d46400950714a5100c01e8041c00041070501c600c65101d504103501c007418001d0082c419030421207044200800b0501c401c2c100f100c2c2c00b040c58040b0f8056110386010425103080000e00e2600c041c0c0004001581e1100b591000081120900c000c01481e601e410810a88402e542405480d0392024000c1c1005000c2c0351115940102c54002124507013103583c0c1d1805002d950306145050240c121001c0f60b800e6050200303425902c9203030034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 769891672 1250 769890422 769890427
    0x60b040f020906160f020916080c0c190f05150411010e0105090405040f08030115080f090303070f031e060302120a03210209033c0618033705 62
    0x44021900b02d000f101340740b5140081c0160350005000101c4181d80300c20340c0107081000c00380340401100d5184040d540c010300c0000c0c00000040c0800c100c44007950400c481900141014400110740000d0b0700031501e03003c0e0751120107020000c1c0094001c1028070310035400089c0b8500b0754641414103252490068000d5810300184004c0d00b450350303134400d049030403e44085400003255119420500240d410790203005240040c000000b19603014840ca41c004007071425a01e1030027582e070303e544500d072001041d80d030115503500c280013090f0b40340d014a070401400000e80c41d00041c80c0f00c1a00c501100704c61806100a100c2d0750b102418401c2d0304000e440a806203400600600004050341e0b0028503c0da4084228001d007800c00e20790300c3e6071240c0b0b50116100810028210340c0c0c1c52070701400043e401401194203200200841701d80319800b81030f48013505110040d04001d001d8940c0d1740424200b00d40360032070610b402c0d400100680545116030400c2c0207480000305019005862035480e450000400039800081404400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 769892922 1250 769891672 769891687
    0xf15090c091109120717010204030b0403080402031005040b0601140a021f02070b010311030f420a15050114070213060b1b060c09030c09180a060b040f02 67
    0xa40c60036021650501400141031810101d9a44240a075405096000d041071010545815000444400380e035030151610b078524203400c0031517080b40319920006114206070340025010a00500800341e0060014041d0740050701007104001c01c0b038904990840346000c01c0018410075581c41000d030460f408419510514042c10b14a001e944d88521440d02d87d080b8070b03040300344500780c01c154055402d880d0b4000304155455031a850503000040024003200c1c00b900c90941c400200000c000f4000c14100b1150002c084148130b400c43c04101246402440341203160328a00e01107400c886004958421117403018000b80d440c0c1c820700410706515050744910304021562600102c440c0742031045840850381120110004401c4920071006846254046014803101113410000d10440b070224420300e1011000f0303600260b0742c85444100d18099250710903090742c000b400d04c002c00e092192520ba045040a04104143d107041100c17103152000d0401c049512903155043c0e04e0a40c10503000d295501591020150b0a0a0700e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 769894172 1250 769892922 769892933
    0xe0108060904020d050f01181a061e0418050a05011407050d0504050f0d0210050105040207170703030f0c1115010b310603061e0f05060d02090303070f1509 68
    0x4058000f03440743c90080d0110003000b008100c0c80c000e00408000074031440c2c038100003015800c41c0650b02502c2c0c0d2241603110700e4030054004030709403003508010500c08050820600d0308040240046132160456035581048800c0030b4080304021b0701c5031184005000d500c2e4203280150035a80c074000b240c080c808200b414040626004410b03202d5401d10621300050070780d51401c0c011703d0300d82c6400e610841070062000c4c02c500705a022032441901c00c14984180004c4e41e8a40c240800ca10076054040d2031108400199031404110754003c00c42680a4a0042005240f440501046909121208011a84503484203114040a02280b0048850003000c0c14040d0704d01201200c40b4400c01c85400e81100403001d44000c06407015180c449040c100041d424a0251a41000f50061885000e2503030b00c44140e2403144000c0015510398415104501c00c0d12410300d15000900515800101d40700010680070711001815441c00c001401e0018010400710803034801ca4101501180740e15a1129201420302c08900003060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 769895422 1250 769894172 769894189
    0x20a2c040b010513090b07050309070e010506031503150c03150904211b08180907120c200606120d081303050d091b21020f01050403080c07060e010806 66
    0x10780682d244801050384e048404020424800000c052500800c1804a00c0380d02030051841900e05008580e4015110700300d40407454000d1042650180003003002608290360b20749402c5d03c40700080c088a490702903407000c0c4046850215000102d68201004108410303c000381412404441950340d540d490416480b04590400e1100543c5000c8070a40d10110314188104032040c81e006d075450790b140c4c584940b85040d003095408030316001031842d0705c020b80c3c082c0c0349070286609000b05801c0d295009240c0030200f64002504084c0101010700c8100d900111711082e100700e480076500e81520181c0701620700031040114800105244500c258456084501441e8100c19500e4102c03802201c120b602c1d11181ca0708440f144250001d402d1002e04250220b02000894034980340d0700d018418103402e940d902c60f401e40c1c9560705880400220044588110390160a00064290b401035042c5429454a82c80c0d44504a003588048842c408030350142030b04100b010340c004555808101c00f40b820700740604000c0300050300030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 769896672 1250 769895422 769895429
    0x21204022706040b030c0a09020a03320c1c020702121614061b0c0f09061e041b020d120603020a060e010c0507080a1b0806010b0f07020a2c040b01 64
    0x9680d07544e040035156400700600040414003d00c032204a03900c4051040282d00010f00308808a818101c0189a01c5014140e004141c00c803008103102c40308100b180c0009521010f416101407080400800c003540c4282000786a5642c0002c6c80560756440c50b1062020b0b0311494501160580c102202c0c280303034400312081c0340b011540513141145401c0c14040c0002c601780304540407420100441e5404954251000c5116003242408554404035000c220707040c80301030b16003140c11640c0a00b40102c800c560f90501c41401080d0701018000140b41411200d8104440504a074030b000940d0200d4601110617900c40300006003140b103031781d0501c58a49190f02299501016005403401c3c851211800545030b48581c0d81407106980180032034807410380d2140b04d00d440e10b02c0743c00103843d05883d444030a403180c40540414800c5031118001400c190b0300e44030140c0031542155005036100381007084458090780c0e4007115000a03190004081c046440c00120b05040180010b1b000d0303024602e0f9900b000085064601124110b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 769897922 1250 769896672 769896679
    0xb01090213060f0314240409081c0902060f1b0712110105070b0c0d0606081012020d050a030f030f0b0307180b031b01171027021204022706 61
    0x254044040c11380260211004185250070300300e040242600ba48405240c0c40f9030440034031684008000c05100a40c1c6d403081e4058003d000402481007001e89061003510101d03003201000564560b075034000340070b650245007100540c0c07001140350306c5c070504400c1050703860380b49181c02070010b42d151082c0d00942e1a0030031409031001c1c0c4505185442d50b40a842200c00c100e03400380003801d5610b8080c0d02031403540c011002044246180050210740c0f1401001858000c2e41c9131a005407035546019007417002c42260300800c90308020a45a800300040080009400c0188a40c0b03980f001c0b11000180101181d0382b03000e505c541e4a00b482d810400a07100410a40300f51a00303003a03120449100000c070303280541040320403903800d4820b1000354201c0d2403c5440c00c41c0d21000981e00c14051107400a281c540081041e59007007031f907020502c01044150101c0010003240c1294100450070040c05d004034500300c0e001500d841d28102c1000701044110b1424001107254502c8280c9154081d03180d46199000c401c81c0140f80500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 769899172 1250 769897922 769897937
    0xa0201031a0d060e0712030504150302040b0703050301080d0503011d06151c1d060f040f120804050c0306090316152904050105061c0905010510030b0109021306 70
    0x4400403024001c46610401500c460082c5a0742c1c50410024000c5515540c0706001c2e450022441080003a075809220390550303185801c09007011405001804910700c00000e00d50708000009443c0c02c644c000e41140c501030b88403079440f5031420100c41d0400020303484110800004100501100d082c1809040a41040b2450130300c181c1d6490000c07541c915064400c00d02905404070309110140d20003c803c110805c240802071144054141210242c1d1000303540050550b0011300004a14460821205500a009000d588114501c3e600d90201c0101307001c4001c400500c05a0402c801e01108110601419400384d004200502d840b1503056168019503d4880740c2040c18820340c414050a8501420b14052040c0100121840c92a80c468181000113013903120201d080e010140320b103000e101d00ca048940c05028145007590421080d0383c41c820071050b240c0030640da0304005002c2542442824400c519005068020358114181251850b505034002c0805500411902c12003802c1400c5810031200c080c00c2000303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 769900422 1250 769899172 769899191
    0xe030910080a06050310151e0302010c0f0f08090102061b04090e1c05090a0f0b0301210c090501050f04020705070506071a09011e0209090103150f0e1b01110a020103 72
    0xc001e01a01c0d4400d945c14415100348240c20421980110740000001c0d68488250769a84600401412000d08003401030004400c10400b42d40076000308490b045c858018050440c2c0d0304d640303c0c280428074060544001d54041406040d80d44c04101280d08044011203411503500320008415191049000f000c60781a01c50440e80c80c0c10300104407403160001c0703103010400a204490002842134000002d49485500407540000302040700c0500700741900e5003602001d00c1c580c01c01504809218200302d00c006041c000c0200c14002c1010b00d80183c0c0a00f20b0510081282d5251204121003e20082d150502c5070340704000ba44009000007405000f00e94090360070980310740c1a030030102001c42420620784400d035510b100300700c0d0840c419805892400d5408010000c0c82d0f00200c1603004030300540e0000c1d40c1040720f04e40144045001d032103a0a00d1002c20480c04201e1354424001c00054070501003070401b070341d0b20500f8400d001a02150342c18480c8402882c2c28007a04030900400b650329003a00c0d6001c0d042c1541c2c0ca0890 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 769901672 1250 769900422 769900441
    0xc0201090204110a03180b070f0c15090506060a0b0315030f160602150c0d1d0109060b150a0503010608130b0f0403030c020f030a05090307270e03091008 67
    0x90003640040041000d02501010810700340d00002d569000a4680480e402045040d4032401d8200d035000f6001d0721250351142d01c107885084a0403204010f104d5000c00f0780d00010b40d007441066091050720408207a203491460628078050b00a4151481005066030a008000080081d03941c44084482001441c90345400400c2c180000c4010322a036501402402440040d40300e0380034000c1300c0c1c19508513401240001c8035030100940580f0005800507040016800b019455040f2a06500000403201910b4041206a60840c1d50121b01260709035101e80d41c8144600d0320310918220590148405440c05075000d10040c22884140a5141403014083c003050000d090800304000c0c603603010960b903005003428402c0c0038100c20103c07000c034002400d0032501c0c451036102041803501021203800071814102d101c8819a44c540210416540600c0b6412000401c15120401c100c0ca000000714900c0780c0d00321140300c9500381c2c1d01006107041036a10801612041d074440e8109040c00b60a689000740d82c130749540052 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 769902922 1250 769901672 769901681
    0xf1b0d050f1e07050304181503110f031f0f0e061b07020306190e07081207031e0810061409060d0902040c02010e191203051801090c0e0c0304020d02040c0201 69
    0x2c141841c00d0220f5810704215000000340107840c1c071403644410580c000b101c844182c4507c8030038611480b10358001000007074114910030001d04401041c60040744c003004003007131501140203113000301c903040104000f00380c3c0480d1103928a140122074041c8903c05110914507650314016149904210781c03000a103106d40310400030341e14416070040585201e410024285400c01441007080f5142914007131a030203005c1c03000100002207420301d10140004038048114030307481c0e401002081c2c00340301220b8032503580300001004101003410152240000c0341007451800080c025907410003024048500328030540c0003180070917920041c10481d04690780d1032080601c4c030b0107402028802504141070100c00713840d09406400543c0144440b0007140c2c0309a0f2082c1b034650081d000120050041c445112010040c544243c000fa680324130007200c003080c03507005080d03440d085940e5844261194842d0351824001e04807140c6106d81c000f02d400c4001419814280c002070f00041302050000e04c940d95440d0542140c174000e400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 769904172 1250 769902922 769902967
    0x50603100e1803040b03040b06060c10020f0c011817040608060904170a02010c0e0d0f020d03021c0f0206010902040e060d0c0f0909060b04140a050406060b0f1b0d050f 73
    0x1a280c5131651a15111003a40003590201e541103050400640141082800d849501e81d040c00240b912001a00001c0000c0d440201c1319940790408100607040303010240241c0480a8021829500101f00380c100b00c030386041035407414491a2000c2108201070ba502010761034210004030345e2181161614608101c1400c18129540f140c01c4001c2001d6101c43e40651000f1000c3c07c080e1542c05d14041042d08001000e00700c0030009005c110302102080260600c980e4802000e886401281c9001e100840503403204081d98a03200005291842d0074182641c1c103000b01030040039820000d6082a0a200144400060040c03019014440c40c1003604148107095008800030464190681c00e55a00e440440021700740c50385081e60441d040c014002d03406d061610401f5400d54640403a41c0c880c2c0c4036104c1c2d030343c0900704c050010b540c82c540f10500404c003140c0400042620715a0704007000e9442c800301c074030300f440304141c00003c60311600b00089149030b8035000011100e000b038130348183c140d6503030402142c10702030b407030461 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 769905422 1250 769904172 769904221
    0xf16020a020409200102120f0708070203010527010b1e180709061d01020303040213020705100f0c0905090106030c110303090a1b0b18010201020928050603100e 70
    0x100300d0040c8040004026607204182d020305510310281c4c001a0b0781c6040b40303155040040800c20422005600b540e0181c641d00d4490300c19203103049445d40020b425070301d065034a0b1b00c001103403151b500126001003181007004041d003030003402411350640005a0b8041495920b10144a480301940143d50700d8031002c02d1a903905010200c2c02c2d0501d154002d02c42c0544e80038000200d440001c907020301007860704c0482c4103000140d00840ca9540e45a090040702a10000c94601c40d43d001d00640c07000880c2170040e82c1d0310889031034000074051500c403104010f5403603c118000a004c0b0741603040c0702030340b5460501c606407551414046080652100b0445648040304505105170001000344051070300041602c1d175030b10340580004200407014694a4190230080d200c1c01145203020021340e04000c9020010780711040c014000181001480e10110318100701032602801d81c8c800000e040d039000d450b0759040c080941030560b503403425890600d9030144c2420142c010103c0114109000030103008402454034001c40080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 769906672 1250 769905422 769905431
    0x16031b0e030124080c030a2307090e0d1b0f0210020a1a012402030d09030e06030f09010f180803040203010e070806090106051c020d110a0f090f050f16020a0204 70
    0x9038400b5100030701801113114070701560030b0b074042614000400c0c2c1d500c150844140c2000b601c01040300c1c0004a10210a0141c80c040d1090004001c11a84505c0403503030843c2d00580700a001c4c207240104141522941c1d0051412844031f49070204001c0344143c116940d054a40008245584100740d1501c0c80d0300c00004c1c485100c0540000514030007074a070b14103e50244481c42420441d121080d07020008440e0f2143c0182d0050010010760480c0790000c404040c000e0038150035100005011600c66803007281d40300304a6100c0e0040c0100124240705010440c102c60004028543c001401186860354540c0043d0001502001040942d0340a520044041104108031030060355034444e01d9031100004c0740c440306254a461400510790401001c652507910300d6900242c8108015820015000048802a200e050b9002c0c001c40e00c0303480380324105e40605000002542c21303900c0e111220307041d241c541040c484024202010700401c2c01004950039000460406944035828521808904d800a0004042e520a061 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 769907922 1250 769906672 769906721
    0x1504061116021323040f170324060d0213120506100e19051b03070c020a080a020d020904151121011a090a12080316031b0e0301 56
    0x81540d400d81d4401d80e50b4806404100401c0c4045640080040707a0705210345896182100d10039000550140c42200010b20030003041d2a03503545280e014403140b8040100105021241d1b82504260300c03052501c80703190800041400200b01540190040c13840c00c0c6802080d2119100161441000a4950400c010a0541d1941000b0703a49801c1607590075100f2401c40008509442c09111191050b052031100e802e04041d902c0081f40140001000c81006002c2041d0381b100034008000294000c11031543c1e281c1b031444441c010031410140382c4d4005001c5502c42d144400046c0c031448238108026404803003602c82c990311403c0464000080100030700b829450152415107100400000d464909180705c148020111954500101c01001f07005140700c15a403d896480413022000090004e02d101501902403956100340c54402c03404800000c588602c004010002942202c0d1030018591806150600c900700000791640c000070354400c001002c12024261090243c0c0b806d410050320300035040a6a48544403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 769909172 1250 769907922 769907947
    0x7050405012c06070302010b090103050f01230705210c0304060e030a141b070b03181605040f091a060a0803090a050f01021926040815040611 62
    0x5000d058042203919007007880080b40402c140c800c0b50311071030301d0780e5001a0010800c03c094106200440c01c5640300c0408185545070400218001c61040006043c00d007001818982910841d01c140b00ca80310070050b920311040503a4641c9a04080349040040c1c2d13450f102c1c41c259040d604103503028a4040501000c0c01000f4165200851041d17005440030400ca15600e243c4586030712407001440c0014812200854051170700d0002081c80074020700c40740039100c041000243c244a2030b9800040e400d240401003100c13050800d65000c5071a00764102034115100e10008d020707400c0c8070a0103818000d69a038801d40c5c0b020802688840c041940002004c99107031080c8010321100c0c102103070005e00440202c20005507207980002591102c90008001040c0c0504140600003990040881c46045105202840d000c041d072050f901107142c2d00403403140300c0404005d04541085d1034100d904850440080008000010000c909100300101481c2110440c0d00c582c10f00c80083c2c02e80c2e111034603900900186a5200d0b02e03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 769910422 1250 769909172 769909177
    0x5120106020d230904050a0204050a060309020f0a0e010603050907090504060b031c091710090302030c010b220c090510121a15030a0f0207060b12010c05040b0f040b030705 75
    0x5903505070110f4142d6220346100460300c03920603a0341005004201580c5415008254003000c032000050038166540e0010311810800d03480038002c20740c0d4100314000d60400200e4408407280640e03441078a1480d04c041c021503a10144100002c00d0359620202e450080d090003054014005008c0a10079801c0606008006100c2429098440c0c45500030441144000f6000940e058600f03856206841d403400d142c400700d48423050071300044c601407200100700300305c003602c01c281200d8040c1e8000c2d5299080c08a4090031204c403021000e00c00d000c082c08020019005148503884035103295000305007849030220984054116800c90746d4009400029a41c1c0eaa610071130f507072080c0308503140c144a0144a0b50350400188c0c02c1140c03003500010209245901c4200103c001c0d90002c3e541c6c0720001e0307485003500e8203108980000c2e100b101c40d2501ca030f04542c5549007039100103d84054000c020400c40a48140103441c0303224920a5154810303012400c1c2440c2d840c4802650018455003c10310f07940e1034210b0001744941d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 769911672 1250 769910422 769910443
    0x40f050a3f0203041203020109150509060f04110d030c050d110c040605060a0503061c0b070f110601031106120c04210c0501030513060905060114010f0e0f010512010602 74
    0x105451911082040011141d8544030000781c01952030142400000c0414074550401a0203542d00d86914600060750b8079451046000d881e00c00181034244030000d2420020050410010790b0780701c400740004100c0d0151b80000c18442200e010361001c0091809071207210078884007400c41d00400981204040c1c004900301c222010010030345d83c0c00c642c1e2804100449540340509a00300c0c1003070100d005c02034011402540c100720002c01141c220210741e141c564156152420485034003080c0018042c1d0550080c40b080080340710303420440741d403156664070142c2e80c110520000d090540c00c030440d64002d8950004690702080008148481746c6032800b001003182c1e01601c1005860001c1d0100c10b000074000003000070b5415800044d07035a8043c0380600460207043d0280110340014201212000041e1080c80358410562081d000740101c1d40c5000d4001c000d00d01822103071414040f005071070b0503003142d222800c001c1c00d070421540c00c45621502c07401243c9038050960401902102d174400420900d4001480c507004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 769912922 1250 769911672 769911743
    0x4050a02012705061b0f03040810060501210e0a0c03110a0b030a05090c3303010b0405150903151504021305010c020d05060c0901110a0506040f050a 65
    0x14400b250b80c400300069000090b26010000a04040c800e51403e44010009103464031058000c040d41e414000b03003003044070341184140341d000040400c51810140f10120190b10510700800c2031900c2c060000c1e1850054907801084801d4031120850340b0240c0b544889201e950b0f00c0f044443c042c0d01c510305004040c525000540380200c180300305038000d06e0800f648100351155014090b0854480306400e02c0603010181000c080c0c4c0c01480c00a40d140d8841c028100d034034840c210043c4006490b4021528800d507070307045002094500c10401030094511110841f412a081501c921080c0c0d030034050302c42154011200308a0303040c02002c407943c0c6159054401c1d580035003055040a0503031003907201000304a21550242140384511031104010719030182c0b0310070240310f0016058103080a42da0750b6040c01c08808842140503203002142241031541d12016a44000d00020300810102410351105a502c800041008000c851001d0b450070400c0010f0150380240c079403001e81d01c049005240c5051070501e4910310701901c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 769914172 1250 769912922 769912937
    0x11202040603060305070e091507110d0c0b101505220f230d060c111623030a0f0201051e0702090f130314040e0901020301080f0a0308150a0504020304050a0201 70
    0x10964031400f8007234001d06e0240002c00740c003440b030038101201000080044c02800703d0b420141112500a018102d4081007036519052103140c6894074020341040070b8840c400903010139406000302d00c108050b004182070b0fa418400d441e01c503c144211031040a4256002c00420343c8000050100f142003001d10645210361a9042d0400118403088554900c074240b00d58000031018150000c9106507002c250728036002c0c500810204c641c00011841e0500100c4404802c1038201810801b20087c01d0402c1140c484a10703000201c00c0d20500081d5803488814006840b40c0d00c221344180031a03028104a07282c40d8007540c0310b15808502403040c16100c0d0882e0500742d000302160310015803aa00c2d140b500d51b228014100c01d0b1010b40d0340c1d980b812100a000100502140b15081001240ea03c0e05180b40511030110796001596940c1001ea40c1810020301074081101d035070000d003c1c00e00184d00312400c550300440b1688a40c400b075030004001440f000c429400107401500c00000e001c140107011074000d02060003a2141340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 769915422 1250 769914172 769914179
    0x70305070803130302060d09051e060907061413150201050108010c110d081b07200108040c090b0f0d030e090c0408190203100608030c010e1203060d0201120204060306030507 76
    0x540702c0c803e140042d8042400d100c024001440d04002801d040d61009500060031840c580d5414a4600c00e28400341a2803404101c0030521f1004212080d03200400300f014080e69480c0440c00b074524030149250803207189012a13004480204901c603c0018041d100c1d0324000c40c044524040e0080c070080c000c03006d00e54204400d4841050040305254248d1441e0001820311070001082140c01c00c90180aa40030000c01c00700303490400c0d0884000d0700485000f21388050f10300e46c80d40e40a840342ca014041c1a0b050005810420001c12524142c030b200312640c04c0008030b022002d0360700155110014108441e8071146016031801859803002a00b0001c590549215005480d0840304000c03e00840c03084005950000708604081048181c40201c0c0e184040d0403507504c10446080d03641542d81c45d4001d40c0095001040c14412803200b4050a41c41021401c05442000c1400c115101c1718440185810f0040c03101c5907541c0116482a42c00303940041c01018219100d40d1140301c000c010b004e55100999040c8035104010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 769916672 1250 769915422 769915439
    0x300303012c1003020f010e1f030f090203032704110a0e010c110409031101050403080714090315092b0306090e0601060311071203050f010e0621010e0a0507030507 71
    0x10307070050186400512490f4656800c0007007000341e1000985c104030402609040c40d4072203148502d06040350000600e82a02940c0300103044a901500445100342000300b030002585010044420b8042421100c80300610100c00103c0248540c105203900140f800d0141e010041c41c4d80041c06e0a02440c0e500c0f0b82c00d1204400044410310b0f0000d03805001d1300741c4002144818a460b0b840440c100b842410800d0442e41c0030030f205070031940125400c0d004999410108012591f000c0a004140742410040c00e040c1845c0340042a91000140c1d00c0300138202c454000708909a404102070161240318a103860500f64a0301d02a03a561700440e124040441c1c105800842d10711424024000c55200250081242d60b29041d0218007610200011030b8050780d0401c00400481c6814800042030a5030362801724150600c50450243d00405a010607a050113203020302007a55600150035000144005450b50401c03404445034ec0100051140b19401c1c2c13141140d45010042c0c003185440480e4010003d442413141daa0621 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 769917922 1250 769916672 769916759
    0x203040c0b0901080711010f1a0a061d0409080903011a090703020c0c040902061e03150a060c0b0903130e10090b010203041710020a0c0c090b30030301 66
    0x4490124148600080660f441b808804051002d03400000c100c444028111904403203422074500d50243e2a50004402810030b51a090028003041c60320f8034030004024104800200303080c070468401c3e621003040034144a5441c05440702805d004008120351b13800708100901406003a08200c2c0580860700001d40c605002c2d10039aa1107145203400740124456440400008161303c6004a82c086414444051401751044a280d00003d508609580c2ca0030a1030250f0b001c00c00c0d28000d1413251030440c4091041692100b801e8a1310f07036011441016984405007200c3c04c60166000e08482000d031480000b590203640540f1500400c1c60901c1280c2d603030707101c600c07800c259000641407078056807041104211032008800c0c40900710b200c1070180c40c40f03142641c0c10141607030b00002911000929401e60f5005108460b50031070010074518100b000701c00540c00c0420a1408006c59031180400300b418030000803080c5100070a110009041943c0e543d41e141c1241468039500349100c40c1c040340a40e1652030308415140c05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 769919172 1250 769917922 769917937
    0x140702060108010527070b030c03091002040f03031809020a05071703100303080c2104200a050d0204060b0f070c15090902030403170103080903010c0819020714060a0203040c0b 77
    0xc80d1200304881303109200500c2d05c1c10f00080481d20440e200041d42d801e90102440c01520321000d4140d40c1d0505548031490304082404c019032044c03042000f005041c0c0560803038004c0b290306003441400da002c14844000312140c0703544907a407150300010351040c601c3d0f4048000c0c01c0c0c881c441c40c02441e1545000148003941e0108035080b03030703500c001c9800c03e00c04030340079800c20707644510721a0446103000350103141098503c8681e441c523005203049509000401c11031140e0081a014102c902420130451a40000d00f0380d15184120fa000b07c582e65440c00039500c490304044082c0400c032440c1503035503200c40520085a44404000e90303100304404000325642400120a41c6451065916624024105071201000b580060011001c0c00000d2158004561016007080d0007507000c0c1400c0c60710380d002d541c02e040c25582c180c49408100040b10040115203045180004a0360010303440050325800903180a40114031400d0340146c803842008100008442250019407203944501d043c1201a695540b480d0540e0042c0b82 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 769920422 1250 769919172 769919191
    0x150f110f0610140a270e010c0809010c2012041509120b0f19050414070803090604170a08070b0a0605040204030308040b0916030f0b060102070503190c091407020601080105 75
    0x3608001014465104101105140817910760100441048100701c1c2c104000c480740c540d44031310301102d84a03000b0080c0e03a403100103000244607845a45100800094001c24102204480e0b8201240391300c204112000da50707074160f900386542d0ba45940c2440011032490000000107028010046082c0c42c03501d1142c0c1206502c0040c0c0d48241c0c07110111074240c85002000c0c022140e00e08028511216460b00566001300c0c09260800f08410480c072746a03080c880d09030041100d56008014005068440301c08072401c41c0d090200c121240552044a913080c0800850080c04551010550300140120104005d00a0900f007404202c80c030b03907c00c04d100c1039004503c030140100d000f090020700071540782079109a2152508003502c0403000601040d804100340d030b400541d031002d07550180d0801c00610b0341e6119046a401d00050000b28a4640000d170703a0713500181e0160300300c814200746601f00401002508068446c509041c490100409807103030f00c0100031160360b4010301c11840000341c0040184112806440b514 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 769921672 1250 769920422 769920439
    0x30d09050a090b04022a16050f0105030426030106030e0d1409030a060606031a0d08030402011103090d060903030f1505040209061209030306031501150f110f061014 72
    0x10000b50007030840191050300700d902048151078402e500301155800071110043c0840c000718680e205450302050146184015040714402e020755a2000c0c000c0c00d0481e02464016620760300d5182018104802f07042448240d4070040402040f0100380010318141c0d00f0f5981e04110050200007082c0d0f882d2300e05010784c0c1c0130800180307000744404e00c2e00009028802000d41110084142a41c46008664131688000000303950b8841000307050b0354603114010701c5d18084409804024558903880524800a80020305200496100081402003401030f980c400100a1050380c1c8001c00e814120050304914001300d00091500440501000991044268070b080c411181c2003468202002d0000a40c010365101e0341c0024184035803500c02d801d96002d20310030b45082c00515145d041c51418180b070604000c0800f14158601001800612000450640030741c50714981400a000030341c600307980d6501d2800f9100128051040703070182c604000503485010ba100503000c0d45c1d00f40d82d198044401014280313225540100c80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 769922922 1250 769921672 769921679
    0x16021c12110303072f072304020301080d2d090603050a05090618011103010306140f0910051b0a0309050d0e0a050f0114070b10151215080a0c05030d09050a 68
    0x40081400c0e0310060464070700e80c84680139044524292a540c0002c030501f00e460140007520042c1d0105040c156010303142541594184007140c0d44030342c054030750071080055003d0800c80d04100071220000c0000402007064072081c5000e00204109128007c41b00840e040802140740d84c1054403400b4891b80b4604068581c03503d40203010f40350070008120b10384413507403140c0c0c400407076085400c000c60085114ce4000562401d031b00f000c840c002d510040540489803615000c110780c4840210703541c003c01e1802c2e01d0004107551521001d50aa029000820040c00d4000c0744d900001074050344161803d0303000f00116940d1600e2000c00300c943c1444240503a4001080312400c000384e0400c1c80b40c44080940504005006d12610714444505030020541602d071000000244114080c40700d0004001d0003c45981400b180300280014140c0c203040c101000010760340d041100714500400c480c3c00050140c82c0141c0e0009030084c01c10822078001409014442d0048050141c400750050f15100100c07100a01290f4601d481d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 769924172 1250 769922922 769922957
    0x30222030b04020118090e0309030c0105030f071b0f060b090114030d120e0105040f11010309172a07060311040305070b0a02030903012d05060616021c1211030307 71
    0x1702004030902e1005451004100c40845000d618116040300e8010b41d11092840105494172064103160307814804200180611a0310504035103510280350304090b59a0b40d03548491a031201400c000c05031000c607101e03000c0c404100003a00032502c8070310120740300f030800c0c4d0f02c80d5100b1441954001109a05074002c0ca80c1d1180300780036556140340c002d8040400500e0383c4110f0543c41c00d540c403c540844a05421114000070271420186100582d4001c0c60304110740403c1e64ac0340700340c0c4103000c50040c0c11040d01140d040088002e000300d2080e99205004070039414618061034682ea41131a02505000c64101150341c0305820255082c0c40491760814014950039140c0b240300b1409a000a18030400c40c04200031443c829202401500440f5200c00d40e1310410b0380214a01500c0e00903d400d00503082400c02c01031003500d035242000c2d030788440c1140507901c3d41412603100156042c0c2c044d10100502d0003075a40ba900520107050103004114503552210300c04e440544ac00c00e522440211002000304501c80c200c1d030503854 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 769925422 1250 769924172 769924187
    0x50a030b12190201050d05070c1a1b09030c04140109060b070b04020f0a0b120a061e140609120c090702030a020303010e060a0306090606050f0f130506011707030222030b040201 77
    0x3d0040c14981c0c03904201c000d49800380e03041104c80101007450000304108002e4014a21100c20f08940304004c0381e800c0c2007410b112030314000b124010002d040410701085950b03003031006541c0d0010042040181038071103e15108007410034401c864900d8501100010940080390413100c3c6a6481414454a0b42c2e466081010341c01140701c04503049108030001044400c00c1d0002481c040c44945404403c80c501031084c03030242e4400360004c82143e0004c03910080740503080303d003105c11b0362400c48801425010800c0400c4050143c00d022a6120b4040d101e074080301c140105181e451003030b0aa071489565612039200740e03540d1140340f110b040140c0c0104010002d89201c205c038160040e40c0202024481d0b41c0d41e07103400702500ca1029007904c8144d52844c08000740d180503021070350614000e032001c202c00d40c00c1900103101100d00701c125440340c5440c0e10006280d6840703004c504207110035426110000d82810140180250090240d030303450080d0b0f2100960201030b0070503840c42100d0780544c080c10ba50f034541d801141c405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 769926672 1250 769925422 769925473
    0xa090f27020d020903060a0b0f0d050a02040e1c0c05010c0e090a0b010504030b1f051903080c0a0212030c0727021e03070e011b230c10050a030b12 64
    0x940d00380102c1c0d2903903409100250084031400c0c000305a07060840e040009440c08107241c188580702074045c0c1cae0b00040001c603082c4070032070b011100065500340340703c101c40c24110030200b0600c0081800420781030940e00003e000000e207020720020003007030f48040402d640c4600c906445aa01c0070810707001411084054000c6c15004406141160074650750340e8801d0980728050b1481e0b941040351424110b503500030100c400c1d000307020458681c1e40f03110340d8240c0841d5101c00d600020382840000941006208070400540790b070709a01603ea85030420130898529181c1d0420700c41402d5034042c04000149503820441868404424080c80061555540450000039804288120000c020f11340000c0c407044605001345215101c240c1f50380380c0065104000529000d2054000c0941440300008180800d20700c400541084010280c500307009054a007545140105c4004200e034030907000c070038002426502401408401c0a10f4606100c03840c210742c104480158001d00b00d401d181d00c80130709190202c50310241d0003000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 769927922 1250 769926672 769926697
    0x180304030f030917070b0d09050f0d0203041a040503030906071a01030809130e070e070c05010c12050a0e1c0c150501051503100605070c0b0a090f2702 66
    0x41540d69a80d0000040a0040c141c0110b601c201c400c01100510200a4031260003407009081804d081a10702482030060fa022071401ca99900410020014104024134000326040210b40180410640c002d41d40c0c0d000b03001c1d8286001c0403080c42c494503040182610207540008001e181402d8200c0e0500c8015001072000b9145075008025014802c3c4900c520107020714000c883c0c01d540c0b029035400380030042c04d040c0c03419000c1c2c910f8041000001c80c00800c040003900c0304c0011125154071181e9007110348018020001d00627507c3c01d001ca2528640201d80c9140b0703240004814001552840100c40441d034180294002d203410148101ea00e01c03012010648004582c0c0c14161310b01031068941500d1200380c2d02c00c80581c50340c1c441c0140000d1804a0300310301c44030740c070034145031440c03034010541090104544200c4081c0180880e020b005c201000803244050040c5041c81a11009400f2004040b030a461180c401d10703441c040008203c841000174558a4088920a104502c080740c05c250340081d8000c10403400c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 769929172 1250 769927922 769927927
    0xa02030408090904110301060803040302280b120106030b090f070e040213080a020301060902071a090a0f12080a020a05090613050a08060a151404020c0c0907050a080c121803 76
    0x10341d0b5400743d410340110302407441c04005d0002d22062600710351a5800c0707250745074400d1004100599a1002010840c02031070030b6203522a41c4540e900c040b260b039682000c843d00e500440c3c04030440845044040c103c9096613403d21a80c20340304140540c03000140c68404c11201c006001a40081c02400c1ea9080782030054030041c60007000040f1109410060f41101d01590481c920420641c40e09010b4070003d4410507808510306031483da64a01c21070000c0203d50119132081001030031035001804490041034010507902c160313a0907840c00d0481c07e294030140f440403400d40004601040302600c2643c2c0150380c5511420301d040101c03030410131a60094442904c500b175142c4004511603e400e05104000c0a00c00d0050085080641203041526001101400c01074211081003185a10124840c4120801580c00607590813542c000c990070140864040c0390029500014000826400b000826aa800e15652110540c440d0204e0412612540800850500201010038221206420107010300e0f030071801201d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 769930422 1250 769929172 769929187
    0x5160b0a031a150c0c0907050702100c02060414010f02010c080106030e0c060c0708060a11090411161203112113060f060f0b1615020403150f0b01080903030a02030408 73
    0x5032a910700f0350700c4015a100100b92901414000c0042c103080680442d05003d0354503095000030580d00409501a1040801111490925000300034058a05070003800c100d50741c1c0d451b0600c00101c00d0800c1c403c14000b409802d0b000c502c2a01c10f10500c00003a14990f203904c8076900c0c140b4101c0207800e101508011074080c803419a0b00a0380c3c2c40d0000c0401e144180040d010b1240f80c21481400c0400007440820b41a081c090508144200e540480e200694203d0b8006510541000400341a000d00d0b41c0145041c0154a4202d0511039000d60196030a801c642c1c052000342550000c50445004e11030780e40d0389084200400c041807583c503020305584151900d00c11a2960100d40322041520b40300c071280c4001c1da41e101c01c180b000044d1840340030082c0108115540c0b5241a90400e07015141020780c001c0c01101900d4400c0c2042403081e012039000b1030b00521104081501c101c3e42000810f443c8007003203c59881c052400c0010b5010300750140c4900e448001850543d41c40c407900e070b4060b50005108468002003041900f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 769931672 1250 769930422 769930429
    0x210b04060b210a06060506070f15110c01090506070c021302070609020a091b08040b060108040507090c090e0a0501060822141e1f0f0905030a0c05160b0a031a 69
    0x5440344090002d1680c2c030030f00e0070020102c07529504458000d0b00b040152101082807403141c070707840030390003110301c0c882e0344070801d150b0000c0025901318022410001100f51030320300f054001030303a031a01940c2541d031180c0f07030340c003098400e06514400203403c488400e048886401595003d0f1441030b00440c0045041c8015900280d01070100b60091980c441c0d44254120303109841d254a2300c00d181003030801950a0405e0703251114030f1b0f04000d007030f40d0401c01c030300000504010050129030001c00503000c0c14004600d1040c0050306035809401200c4440120300001040320031140034441c12207120380c90b11407598440d280d4070000008000c09000d4100012096800001c2c0d000d002000080a5407000d0800003070304858503840040ea50034130303a00692092203a140b0310600740d81044000c0084c9000001c0c0ca031450b2401d03030041c1c80300c03600140090101090212299030812034070042130f0310840941300140314410f40501e9140075070041104030042404101c200c0c0340aa8420300000c8090031600042e1311090002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 769932922 1250 769931672 769931719
    0xf130e01030b151f0c1205251131090506100f0b0702031c020a03170403050304150b04090311070503010905030d021308070f210b04060b 60
    0x46241615010040042c0301c500c0c1d90350703604408801c030003180400e035610008248918500b004000d5000d0114180b0003240655401d5000550040504078a40c98041b005421600180100d440070001d00d8840308540601c0904981c240e42d02404940000000070b0a0240205000034001400000d4100c81c9141040284032030740100c0c00420089555007040c54001d0800300050402c04e07500d641c400003031100c80500b4250000350350700c0c1044561129400e00000c0d19112008c0d03000c92034903030398451410307030240d000c83d240710b0041c004d072103001088400d9600d06001c00003c542c0607001541c14404075000600c1d00c141400e44020150004c40e907010100002011582c82010440c042614210600104034080c030940c001440103c0080081600f503480e95520380c0304006c14a40d000b40e00280c1280840c2c044240800501820b008451846469141d03400040480d80241441105074a044040011150102d1074a96600820700f042c55112030f81d0342000303000f100f611640d104803ea00c1e010a803d00404a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 769934172 1250 769932922 769932929
    0x3040f141908060105040c03150b0309150f04050705010503040503030a090204060905090c0a0801020a080a0905011d0f0624011d060d090b0f06150c070b04030302211e0f13 75
    0xe0f01465141c801044125072215803454203260070000032000f50240b44104804403036206401690b13075940d480e945420300b881c82418a40c050809800e104c000c4100010180c842e0f440303003045544c01030b10ce0006580601003118018020f82c07080001031045205504040700003031018002247e1551220300c100180d441c1147c04140380da00100c511070842c40e0583c014402400554021441c01c81022001000020001c5c00b60012503101d03140203040140075803014200160071513a4000c60301c4080740e0301c0d469060920520295201e810085018096151254242c4c8260010b001e00d0202a1500540d420824050552011001c80301412070545421004000d0041218000196600c41d86040f00c05000c02030008400702c0000010450140c0760103944250400500003060385440c0e6111380207180400c250040a55414003140000415400045016030301c0707521100180c03800310bc066007400500600c840f40080c80c5140c2548034980c00c190703000340641080c01c1c1001e4901000341180c103000000f030341d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 769935422 1250 769934172 769934189
    0x30f170f16050f0706111e04140a120b190c02010915060303020c1504030204020406120c11070924080f120717181302030a0b0303040f1419 61
    0x1010010a00c407560700680e80180380d800c2c510700b0900c0c4046015410301038010000c1100e0780c1d03203031514600315469066565a48809410003040c05550700e07410b005030854424030210002c6c480b1210a18641380b2090011f81b001040d0250760914251141c2055803405011005004805d0862441e0381a25024441c1512200c0d000400c6202c0306291111400c2d0f003416890041c1440d007402800040d602203a45462008100e800381441c0c5919503c411161260307500095000344000390000303031140c1203980c2c07402c8140c882c1800c21840d03024010640700d070b809403a100c1105030030440050000c001c141e07101080b0412080001140c0d4040f0140342146905140c0181b900c0e54000c2503401c3c600d44d0100511303818085910348080c123201c00c5581d041c610410003656422801390119408c1001003484520154010006101003003c40e0503c800c140250320a4503103000950420101c3d40d11070400100719030440b00504180c000f8030303150040e20010320190100e40d503030200011001c4665400000805c170080c00610703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 769936672 1250 769935422 769935451
    0x20d02090403270e0f07050f1c0f0c080a050703091a06100212070305180904032007060c02061b0f1f09030f080613090804141804030f17 60
    0x1001800f42c40000d0001420295905100910451064601e840d4101180ca440540d658a4005041e12240114610042c0050001c608004103568000080700103440d020000c01490b120f40189601351038040790003d0200b011036010405e4a1002d078441a400041807034001805441ca94500750418120710741c0c0d00100c404142440391070f2030114641c0c1401d07007550004200303404403254202040e00a001d0090140400131540c468811000300050060f0000141100314928040c50090004c42c00320083e00d140089420714003580343c50002d0504140c0301b0540383c0901c111903641c03c0110a41c882c81c1608100b01103010781003001300040180c500c0c100040000b400c400d0a04c00003034202d0026007440c440c0c149041c45202400b00360010822803000f2803900c1c140100e07558820100d40c20f0164403031102c84c0c06180000741010f00c000079016006031010b10a402c0c14505440c030801c4039110045699503144d1036640302084c0020b0043c00803850085d07241c2807041c0306010910041000c440210b42c241407003640b4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 769937922 1250 769936672 769936697
    0xb03100b0306070e0315040201030f0e0318190e040809030307030f0806031c050a021501090f0f060b190e04021303211d031c0e0108010603050c070609020d02090403 72
    0x740419580f15001c1e01c1d114800312104000260b4603280c2c82d02d003000424054001c14103691103500020324a504104007404207048892809940354059140d8002c081c2840498444a2800f8401c02d000e449160b611016070a040004032101842c000d041203518000c02c1008288030b8a0500c09062041d0003a143c1d0b025020001e0800b415030580103002c10300c00d8002c107141d05e000070000c410101c12132802d03180441d00c804145405910740003075441400c40d14414240006003108050b0000121400041814000e90b50076035080420b46180d806603038040f4a091003803808161180d21408540c5d01c242c603100c001103044c80082012a40b101d40341071000e5a8074001401409484402c400c51844011081c4491f000c00c590000c1c40300040002c000394a500c2075603580e11a5404000c41e00003100001c1c1494100d040d17405010301241c0c3c41740325550201d0080c1c00005000c44c024843e4611503040828214609407060740c41c0c00003405a15400c81e07000400012600168441c012502c2c0700d40e11075120555844038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 769939172 1250 769937922 769937929
    0x10302010908060c0a0302030606160c0519150e03100903052701020a020402090406030b1303020c01180b03220b040b0c07050318030a0f050d0306090b0d150b03100b 72
    0x1242c01450709a4000d4052110651111080b1012444580b400584a40321200000c0c0c0724801c41038a40329a460f03a0280b40c3c28000d401031548121001190242044036000c09406a5a21a0700c203450055054960404102c0e019468038082c0003401000e0359070b0000c91540c0b160440d444890142d0000c1d0380401e868078100366255110380004c01d65a05110010501c90000b90703190700f40d15000340110340100b810f1031035456503045440034580c0540251490301d0020700d00020841026030603401441071015903172195000d010140c42048c2452101e0300c02600f40214004160300103081040d9041c0b1103140312400b071288401d081011482100d40f6181030510707051075006110098000e0403000c2c41000b100002840c008101c820320016058030300014001c42c40000c1c01d0102031000903180c403a417110710804000010075000041c50481d00e00300015510313100400129014600d2a607017002d80c0c660200081000c004641c0c010100401c00440d1170b40492002c80c4c24003401d0100c4402d402e40b0741c01d0440380d034907 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 769940422 1250 769939172 769939187
    0xa0506151206041a0a06020318010e01080112051c030e060105040b01121503051603032307061a03030f0403230d08040512130618151215080601030201 66
    0x200c0810440e08029030160307a0040c0c0322002c2c1c038031486036960703000f4a821406079420508203480d00420740d000550351000c0c040e4890348004035119141c900310020440c03640c003caa4200b020041a0b4032065071381e00305190786202c0c4200785d000342e403d482110140c501004e080480e4014aa0266030302050b18240d40503001c1c83d1010603004030f840b0f1070424000d8140c80c0d80c00000092400a500000324080c2c0c03242d0048104a101c541010304035000d4540071495011a0980840c110b80c4a5a14107401e1190340840d03e207000d60400c00c4c1c0140420403c201c0303000c01c24681120088480105214600c500e0007000a0300d10b900044103640c40039070120f0b0070400d00841a40302134150f02c03c84145030303a050f1000c0050ba00c500c0c1400001040c0b2104001040900004102c105690480b4041c541d03558440307000f810a40444500c030b13420001c0c020000b44010011050300050486601080c520039210481c035094500868000045d061541d0b648030440141c2c40d000c031240300901c0008007504103541103000042403003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 769941672 1250 769940422 769940449
    0xd050a1106061f0908150906090a0f02040b0f0904034409030708160b010b191103130906090b15030720012d1a091008060a0506 56
    0x1030300300c10100451620740a150f40350f50402504801a1090b5000d02a0303500c0803a500100340383d00c2240304030800c182c44c40c0710580c000d400b81001c89215075035001d081a0f4410f640c00e00281402d01140d0300b40300500f0305401044180000078454140b078140c0c60041107000004423002c2c1c00058944200d0303e02c050400e1258442c10b004009940b01d052105600c11816402c1307083e001c00304001070000078980c1e140a10980344540e40c0918072070360381c00803200f81c600450b440c13001c2540ca820401d00005004884602240c0800102c41c100082c0b07807040341d0094901e55110582039070310380000c002c114608040c80a02c04050610054005503241c2000461b1040b10000720f80c3c01e0103480c5144203c2000c10611080e00c5c4d00400341d10380444680e50703000d41c507004112a0004000390f0360814250341165440d0b003d500305030416104440e006482c4800001081c0c80318540244203104846544001d03078100808000d038040408614000807a076030740d00f07031450705c001128001034070355880c82440082e291442007001030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 769942922 1250 769941672 769941707
    0x60108010801200705011e15052d0a170601090b1002070e0a060f0602030d0c1809020d021204140f060f0109020a36090507020a0b0403030207050d050a 66
    0x50040220f03070404442d101c542906071110300071424404102e000d400c40c45400003844001449000305040c40b002421580c0c4100021301c07080c150109182c2080301c4c950310100c29840d01c60042200c4602d0700912000101c1d0100e8100c1e03040d920100342d00c480440c540a80034000c20042c130481d03141c03910b264103d405081c10b10f84141443c1e01162070036036000030103d05a441052924216032100560180100300580c402c410313030030f03c0c0c0328005a240e4020005e0240307100095810300c5407020388942224000382902004850000300138050261000540c098600e807080d00030010320785442045015100070003101c0c11603003d454135402496054090168904c9131498400402e503c5c00c281c5c060b4258420b05018400d1600d60100b000002640700b0000e030b040844000441400e415030034038905802c4401340c00c15010015184c1400200381e40c00d40b00d014030070340c0a607000c2e00540e61107586e00d1401860190080d800c25400b840000c3c0461030030320181c2039141d810784455035580c0200c0701c00b4106900d08800a0354 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 769944172 1250 769942922 769942931
    0x323070b030606091009120b040b10030203030a0c02030307060906090c14090f060d0c081c051c150305070b09040c02210a050c0303090102040503011b0c080313080a08060108010801 79
    0x142c8071103007a6019540221030340b01740c10311800001c82d00d241141d4410700d6400021b0340f07100e0600220314841c0303001740d00810300d00e201540c5a100c00b1150031800c0c40f0094055004211211080c0d03c42c2d5144850b04d803008040e05c0c94481e107a21960b0568040080c1510080d40c1d60020760100190f1020f10001410600c1c210001c5c0440d20000811040c00180140c14504c0105c00040c090f50344c0c14002003803242e0099450314410b840303c084e01c0e612507803600c60710030040140082c16016805001602d5411403021808508018401d01c0074014006401441031043e8040b0000702c0040c80038002e5001034086005c400b0380b5401c0b45010002a51081100b032415504107007020070680f03030b000700c114010408002c034440c3d8403c24248100c645116001031050240408014440b40c1c01041d0000c0084410850007404210b9080304445504d8042c1c046e0200407c1c850403080300064095000b8603440b00a0030508010400103881d4801903610038185540050046802c021483da0440215405815241e00800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 769945422 1250 769944172 769944181
    0x90f0a0e0a0b0406180c111207230d0309150501051f11030406020601080c0402400b1c0506030d050702190b031902120a020c070323070b03 61
    0x300501014080700c62150300c484000c6410380b5941c01140040c003282a440b2054040d0328150402051540f56440014181c0314007000d10136400a0075000c06c05051202c01d1401e0301690b18440c0c2c010703020301e24283c120010b0f0401000b0500038401400c008480c2d4034040365140c1640341c06800c00c880416418616841d000050140351220781c08400c0202c200d110b03071503040040c0340b000d807080b01204541040900c00082c0102e021907004c2a41412030303450504480e20700e02c03074204200c10b9004511321041d501700d40350700c0f0b501c1d581a40100c04403540307003001c40707800d51420642850103158406c0e00803500114000036040650300c4100b55101c52a00401d074100520700300680000c4c0c440b125118020200507005c42c0c550306540e10f000c100b0b40080c6000102007940343e030320794440792030b60411a00780380b149025815100704250315008070303904004501510030540d030310400444000c0d0001c0c0303040c00091103901408000541040c0000c41c56035101c0001081c1e41100560700e62410a0301d8211000c011400e00512 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 769946672 1250 769945422 769945439
    0xb010e040f0303200316031b0f1d03031215100807030c0504150c03110f060402060c0a1407080709060b071113020403080a110a0c05090705091302090f0a 67
    0x3440c00d0303070b454540030482e1800714266100b51510000302c1184c2034000002d0140e078103403a000b551b24052041e10180455288a41c24045110031940910003080c00c3c440b094420b284182a0a9101500c0780c20504a4420010119140d50032880940f5800384060040c040074040440d145001c581084608a900d03607a40c9100600007900907007800d09050300c4280c941940ca000d081620b001e440c8200c007803400d81c51500001040742400340380235008110400c10920080c41d02081c4d9802556105000b411140c030756a00b484020342c4046855412401211503035000038410032016000d46045200030700540d0304001d90641040d40c2c550000d030049107032400c104550392020040d110010340000601c00c1e9039030180040742d40e20a8000820b4842807001a000c030401c41c80c00080c03c02002140c0d604414031503070f2001d0030303904d00c000300f0003415030f07480c281c001c001da40707131010141c8d500ca0001d141850500710f80a0105500400e5806001310458010032000708a042c401040c901041c001c50b06620000c1c60301498 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 769947922 1250 769946672 769946693
    0x30318031327020c10051308120402010e090403031a030321040602040b1303060b12061603020c0706080108010f0c1413050627030303090312090f070f030b010e04 71
    0x100c1d1111902201c4a000642507080d510808000d200003e43d40d511640c920f05486200c0503180c0d0412926040100d2420251500a00492a440860306140408030380d151070840304003c00c12810041d001079142c0c0b0a490b881481030041d8465180841e218201820515821164081d0755019034010302056101c510781502c0658400c0048040c600c440d1180e050070381c042d10407908101003d1800180102e08102d03400e1030401203c0c040c180c00c1000d2080c400400c18510040d071443c02e100d0f80150041a80c20451030360380c00781d02030035050041c50225640c1660b428a040c0d9404000070030000001000405801e0140300d03805042c3e41c1c1d007041416002e80f0050118003450501c4403142e403010507807412040c50000f01e0405000010000d40d142c2030010800480207003801c2e041c160f102c1d00651202e003e818008183ca0080540401940c100030003604000c01008004040f144d15100388540001c000100b840f0050141500d00e4035041100e086080c000c441d0501a4801c2c20400016410400403070384a00c070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 769949172 1250 769947922 769947929
    0x13112110030b04050a060905060901050c16240f200a090e070c08030117101e020f090604080109031e0207050105030c12071805040603112106090303180313 68
    0x410520b440f5418040d2504d00341c0400103000340d2411400c401448400035a4920842150000b031040750b0f00c100d044440e50140b100c01500c041c40b08480080000c083c81d81d400d0301c850720008e2190840705503c000c0f0099039407110812955564800031448030001000b414040084444162860100302d1400140498844d10410207a242104d0100e801329204070240000a13030440300007a12075031100700b98946015000020501c52041300d840e4940710400e80a9501c0200e035800003041c40c481d0542070000654800306010310000c40401c207500850f641e1304060800b4000b4000001401071a80c41c002d0300031030f558140c900300c0c007034006034079640c0d6940028104290750007880d0503500c0391a21004600640140b00310080e22420b0201007100c0580d0040c0b1100c0c003000c1404481c1002507440050104035400c50201800c03840031380741820f4260421b03c0038403d1280420410541c42203003440850f0410000303540e2641650000030500c044982041d550621921002000e90b240803183c00480e901448a0320 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 769950422 1250 769949172 769949183
    0x20060c070303200d021e1b01030c1101020f040501030b0924010903050f0a060c030204060e041d0d05040510030c080f10270c09231311211003 62
    0x144005041d000040c0100000c0d07101d600f03d40d00c1c4491144c0207505c4d440c41c001a81c00040480707020301c0d282540004c21006001241d03404c80c1b1403141ca00011000343c100f624840c407e1011079801501091800d100400703158030740030035460711a0b040c0800101540c04041e10349100c4d213030300400d00c02d01600306010005000d2070f001d817086041d05814010381c1e40f01490b03803020f072140c000c4081d10010600c000c514024113902c900c80030015481303040c3c0c0c00d03022805640203042c0012140c59030440b090a20350b014070105201118841c03050079500704520300e0082c2c00d072400000954049020011418180f50300301c60302d00941414054558508002001400d0060038820041c02c2000861a40781541550102601c0c1c10070440718040b4486a481c07514285003125440e04524010303005466a204407414001c3d5045001c2840004121420310f14421002c0ea40f00b5a00401c040e04107000c00c012441550b840c40e8030b1050542c0c840130ba1101d04103401c404c000d02c40394249002c00802c140304070f0003124201940d40c800c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 769951672 1250 769950422 769950437
    0x203090616060b040203041a0f15011821170708030f1312030e0c2b150614010f180b070807080c010b1c02032d0a20060c070303 56
    0x20b0070034501030120070502981051001061205000b110951040c0c00d201c0317102008000d4448902981d040d071000c84010b40c0340341c44491407a0040d80304003001c0c00c0c10005859000e240301d40341c5c4141e100501850283c0070059020004a50800c5640d916210340501e40c080c900381070140a854002c1d1600c0000c003103503011b54020002599085111440c7c845040d0401020b8001c00c000020280080140710f821001030f219640e10700c0503d1828802614542028004031700380f1013210040c00e1b403080c4482808540000c0640d00022981c1d00611451000300102d4201c0ca4607402a100090300c004d180c000c1c1c58003004401205048800002d1611038101d41c250162103903a030400341080d1103140203001c1c000f010400009001010100150020780941d0002c44001ca4142c2060040585080d21500001c0d0160811a0309419104e010350b0711907407240c40c00e10220f515141e494073b100e00300081c801301118001c481c114503a4800c1c030100b01150b074901d42a108580b41001a00200ea0781c0d85280c80001c0411010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 769952922 1250 769951672 769951717
    0x25080d1e1103070311130305061005150702010e0a1d10060302120c2b02040f06110d05130e0703050a0e0a02060d05040303060f0b030613020f090405101a040801050702030906 76
    0x5d0030200c408081c00758031616249500c0346441c5450f120103076155200c1824501c07000ca410702d030070500c0711840311907012500d140c5820f071f500540c0d5030407a4502e0154008041c0400040d603081d2118000006800c245600c0c11902d0002050740300a0b2454000104040c07040c072140a09415422006402c005981026600d819070001c2050000c000c040341c20b88140c140130380c08000903903141c01078802e807402c0300341011555032200c608a800b07480b080c1c09030000354041d65011307145502520040070455000306048403200d4a0780f46645401c0003d95250000a544608018000c002071040003200f18140c00a4041320000790000f81c0300740580149030200c15907500202d800c140c0240e000c1001041d003280e80d02001d80c3e4445659009810072500103005181940c15901e0040c907510840d503864411040081c1041680c006000c010300d40101603012604041e08042240c100715242030300e0801599441c1740d038480c00c000d02c187c00c2d540080c120a0075581f00f848400000e64910003901c1160040007100c4038000e10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 769954172 1250 769952922 769952951
    0x100c06020408120403050f060c040b030a060b0316090e012601180c0609050f0108041b030501020d0b01092405030c13060801030201020105060901030825080d1e11030703 74
    0x1031a400b4000300d200390481c080b501050180074200b120b00440c25210141101c80141d80c44510844007645901400c000a0180740e4140300510f030000030344040050b9058883c0c01d2100c5551051710703041490281c00c214002055880f9070341d2406407440640b1032034103503d465550980441c0311322504403442148004000c4480d001d44c001c0941c00080035140d0a61b82003070500c2c0e400100c0a004000c00a01c02031001310301030800c501c04c1315140340c041e9105003007a80c443c1c5482540c84c224007840820029821400004103009001414680c3c001440000f103003681100003416180081c1d00900c05a00f00740c20b540d121070807894500420900904045540ba42c80a40702d030b51511803000d01090103020864045600781e48050240d0580b03200380c0003003045031035010800810240034803000b81a92002c003c1080c90710445440303649100700b45480a680903203c1c0d6681d142a40007201c4c541c00d43c0c3d83d0380d801981034081c1000f980000b0001e4031020400c100b00e084854503179100042440c030a164079401c2d00286150b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 769955422 1250 769954172 769954177
    0x50f0c0c030d110609030c1b0409170405040c030501080a06020c240f0105010815100e1302030a0501061107050f0604031b0e1e011a0f0a02100c0c02100c0602 69
    0x80c0080c195240b4201c00c610280c1182e40410740140d50b480384000080a00c54000b048036414982e0b01c1c003c01514a611014404505408040d260019103d00320100047d014540b00b49400c0c02510405444a013080248400c031905a10800c1c20541000c0040002039004201103407125040040540e540400c103d2980c0340400d00b00441c4000c9241c00318203c001c227441c00b282401088510000d0150766604c1004513030045054490745200e001d42003901101c2d02c1c040740300e141d241c00d050070101070428143c00040c001004641120215940000030003003810341c0342c07003442e000d82068100034186401d0315843c20f0b510b1610380100ca00800d440021804d19650348001e680007158458583c01408070303c090a090041154850504064806004188441a080350313404d51a03800f0b084c01c0050782e19180074800c0303180358401d035504c1460b020071500400f0b0503040004d007001c0b11950010001d810b9000003038012034103039100b402c040000482d035800069031441805240d69141d0b00d083c1408081a040c03010091 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 769956672 1250 769955422 769955443
    0xe160b13030b010b09010206070f050306040c09080106120506070201090c09110d0903051e0a0c1b080f0d020d180e04050c0a090903080609010e01122901180606050f0c 73
    0x1500c002e000040c6080d941d1006018204007039003628000d03124590107940850380501c01c04040364003031000901d02d080c0340e030000031705a0369817404058103a41c1c1c02009003100d0351500301d6003076148141900014410200442c6070410240c0c0300030000d101954031461003981060107020320751030f00ca1001180c0d2414071400c1d102c0c8100005020012000c040c54094003507881000e803410080a100c03582c0d00d1102c850000e032440083e0a032582d1880340010703500c80d0b0707a5a030030190070807081070b050001080e005820010840e40400310710082c131100400d054040c2c41d01c4d041050703803c100240c000038910520b020301b0070603041b03542d07840c458072440d29a450040e0505400101c02034000b04100c3c0b0000f0740c0700085c0c0102d028180a030720307107841e180c4900c4240039806409004281134241418010041075206080600b0b09500410001000c001c024503035036510741504030b94030782e1814544014000c854000510001c00c3ca0406810041c00345000710151090040d00c2440d945080c0105180c11141410300001050303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 769957922 1250 769956672 769956683
    0x1e0106080d090e0609041104090c030c0e09210415020309180a0c081003020d021201020a050901110a03081f12050601140d03020c06070804150804060e160b1303 70
    0x2844401031008151070000d205032a100f400740c6000c55040c2c24580e0485000f542c010703881c0c082040f18581800003400581c2000c85105221040c000003160701c00b200100500b1407540079407024100609e10a2420070114020750b40700031112030040c81c0059100c2150122040f05c0440c04c40100100c1c410703421400b4900c0180d810000b921140151b52490155042c4070751040038082045901101040300c201d032044403001428041b803807040c00946418445404e02d24801480c852542c0141d004150980e08202040c0c000300b0404241c508066810004010980c42100010007c15889403002085050f014112030301c68400c04d0070401801150342c218202800440102200300c0a081ca0030507074410091290a01080014024000c140b03054054800740039095801000840464000c22850741d1004c2c00c2100c07400c1d03080200060103c401982a0f90304440c0b07807508001c0f8942424a101910040400c03c852608800440f10341d11207900d0910081e0741101c0b00140d215102141c030000f141501d900003a00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 769959172 1250 769957922 769957933
    0xc0f1215070e06130611011e11071407030501050f1303080a02090607150b1c080d142508091b0d050a0804091113140a0e1006031a031e010608 62
    0x560840354040e1504035181603880c1031b0100e041c078440034221103c101c10404214100d150141d6030066640080810703030b0220940d0340c5048801c0e9201c1801d400405940d0341c0d035802285c010420f00c0b80a00c640d50b4030205809d201c0d405840c02051510030444209070013420300c07500c0000320368134060b01e23270603240d609178050500717580c0d001a800c1c90b64595584071110a215410404c1c4c444003070a1242c6c41600f48000c5801580d40304d80d003030fa20b000c03440e0000440f807018190b8842c40070426051030040709000704e4a0b030a0801800c0b0200c56541110161a085681441954014043c0c0140f00103100c0c1c034045030703041040081101d2000003a00060511401514600c1a20001c40a00034224010030442d0b104100c100144000406401b1060203003009010702c00f002c41d10104a190709031000c40d410701c0001408000d040740c4550440e400708030300751141407010200e10b00502046815108004050660103614411407e440000a035a601c00c003030032401c816214050765550041c2504800c0240001605546 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 769960422 1250 769959172 769959187
    0xf030b06062b0905010b03030c030412081204060b01080901090b01050f0a03060f1d010603020d03051b010608210c06040f020102030c01020a051309152102030a050c0f1215070e06 78
    0x28080d000303c1d18142c03015442c0541064079494000125403461103181c01850405150204078094450250307400e40300b5146c10001c0b05401d80800400d1486144a47c000040b05c4034954001415030b5001406100c550b071510300d6123008120520045c504444080303824901800c103100110300c42240c1d59000402003800c00c071380c01c0350b80030082c0c012045c1885042003001e01c90940f0040304d8241c60081c03002940101c100206103020030310900080c2807032005480341185041640e5100c40c2169601e40c080ca00d02e40208800c0e00781041001003107032010000d100c1d100d04128480606685808014200a01c010050a558421a4024419290012503500085441c2d4040d400050895400b00d07030508031410010b00d0214007450030307100344201005501803c2d050203003080f84218017400d81a0100d100031070480840c41c016a01000b840380010310600180449509940602c2884500d0f02d00c16846414820041001c2e0b01000406034011400d8140c0b481c40c81d203801406882e260165544036030062000039042 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 769961672 1250 769960422 769960507
    0x40b090c0f0d1b030c1803060c140d140109090b0c07020111150f0c0a3c050d050c09030604030c1b0608060a1a16060b06041d010f030b0606 61
    0x50000d2105070304c0034440380c03001c600111103980549000c1c50a030f401d0028181302240c1036522142540e00d1178184280030a4060108030031b0380d00719504020203261148148040d640c0b03440d10041c01420b112606114103081c960b100c882c0d0100003400c3e440304450102d03841c41503a1280d03000c19403000c10b20341594254071100d05c103060950421a8242c10030403003d00800d0200a00c241202c044044581d9401e040e00d603400098419810400244c40d000c0b041030842c08540320410b128024080043e0300d803141d641c103261500d1f0081d100000c28100c5100d00c240500a0143c90121390355a20a6061030458010704161800c0120300b8601007402d000010807400104045402143c81800b0b42003c8640c1c0021a5440417015021003d540d40c00c104114180240f442010001d559420840c2c4503800204041d0203500c04100c07107800c80ea0009008880d06085030001140d40c0401034050b1050b1202c030b10362a4107540341d9840b42c03400580b03054011100024480e503464161201504100d5074801441c48081004119 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 769962922 1250 769961672 769961711
    0x906050906092811010e09090708010609060501090b0f0d020703080103031209170c010207150221010608131a0702060709210321091a06040b090c0f0d 66
    0x28901c0b4890071143d844403408066100e002d8841c40c1d008102ca100030340d910040e420f03951010082c1882500744490486554641c0d90381c0c070600c1203500800c007151606070300c9401c3d910560f0001d02d0b00c51074000b06100740c0c0d038441082c13016100c64000d100d68544082114000794820380c411050304520100c1c8400400d58030452040c1224001d589035001400f48920300e01c111400706400030041f0840c90503913501c0846407006800c5110100e400141807a401d5203a4004105582c0c42c54007082e0740c00240404840101c480fa450410200c00300c09070b03c0e60500501900640001d00807036000b0418075440c40070800a00c12501c1c2c40381410304080500d00f03240340041d40d07e603004c5d14008c021540d1080c020602e0003440c4102c952442011041001202042d10706031000c40c403c1c120b602182d50345031a629000402c03402003131201c61003402d00e140000703d06003400b408450098070f40740c0f1039810200c0904460340c070b1032219a0400055420a95104013154030800c00c1e100f001c2003050014180200c1d003000c801001c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 769964028 1106 769962922 769962931
    0x16030807020f100e120c07050103111606060302040501141f050c06090a23060613150605030a0f050408030a09170f0307110f030a120906050906 63
    0x250541089183e200c1d206650392a81d9844180343c1040040c9040f8409200c426401d03c2e04100c2110385621443c0700e0b8604240d00ca0802c07030b81c0101003034101d64030003000711000005080d6a140580180a10b880180e00c103600d018000100d025450b0b8001c003003000001c10003c02607402081040b91803505603203e00410030240206908074200300160b80c0030380d109200919075001c0c5860700f0418070900d0f00c9203241c0245c442c124860030410000b0020b401080031215000b030440071001240080582c1c205d51a80400004000598070b50000c00440c01450780000501c024929100140107a072801c2d03900811903a810400030320031010540c03004405910401d4944031500d00024005400e4021054000c4c0205001050100e040d40101030610310365000302c0a0a14a0080202c0c140c50f0301481c402c03d414040305c09080000c009241d8800050380350301c140100b084d41852110155145e10484 = true := by decide +kernel

theorem cover : BRFrame.Cov 769784172 769964028 := by
  have h0 := BRFrame.cov_init 769784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 769784172 ≤ n) (h2 : n < 769964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
