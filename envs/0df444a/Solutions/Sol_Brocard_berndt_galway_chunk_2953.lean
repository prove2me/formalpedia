-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2953
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:13:52.750988+00:00
-- url     : https://prove2.me/submissions/19ec844d-cc3d-4f24-8fd6-95b6adf9d1fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 530935251 ≤ n < 531115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 530936501 1250 530935251 530935267
    0x90c0702040f2d051501021b0301092109060507150507050f0c071a0c1f0204181d030307170402060712020a0c06021501030f020d1712060301060b16050f0a08 69
    0x5613100202607658002042d00030041990700091107904200501200400c500140c0d004640100013899000c1e00b40e84030320005c84a0fa02c800241c2e403100030703200c2d6030b01c3d014a6169482076649104488005042045000305100e010340240e00140c2c00c03000134545580303065a2000e07941e290340c000e029005242d4110f0b00c0100300141d021025001c0d0561005c4850303040804501d9600d486008048000380070030304c07018481040103402e0341210080e00c440c5624100c414a0044a43c008101c03450070080503408403c0e402c0504070000040e130b480781e07e141c0d03189100401c02c1240022621800b91040ba08840144080e1000696038440240351641650041101c200d10b0700302407044090030740c00401590014072106080c58500d034a2681541d4000308040c03d4070f01d282c03008ca000c510151034080d0862071141c0c140014400500d0090011840d01c42c0e603260161604800c00d4201c4240d4801d10810050810103000a500c82c2214a21024023420aaa070b00d44200783c141307800c117801180100d07641c4900042d001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 530937751 1250 530936501 530936591
    0x10020c070e060405070203070308091005070e031e030a0c02041b0f1d011403070c0b0c0a0e12070323060406091509020a06081f0320090c0702040f 64
    0x10b82c0300700111001e021131305110201940741d1060003c040e080001400c0081c030011010483e2800701e1500d80020412460032480c0201030102c851a418400d0090248032600d500048550b800260076000156180c0716441405803600007070386600702e8000d519989010212668a5007100e081e0303884d0303203c1442d11070140100800b4010400030740401008284030388425a60f0000084c00617002d6801d40c117540c0d44405405580341a01a0b100502200c071020030811640c42d094064560f80b012b50b26550b0964210501700320a501c2e000001384034603400039600300040b89040c000c0c2c01c86c1200420894001c0c0c00c4003440340c2e0030700c01c00711400d0301c3c41d80d1142c0d5182e00f0411a45004296110711440c10071601010b5400540900d80c0d40c0329203c2000f0141000c60002107030b020f01c05036402e952f036507500f468582ea898907948403a42014602c82c4034040c0d0b8010100c40c00c0c1217103094030541028031402e16051081d802c0100a1030080307404100709568001d081c3c08034036210740d0007004043c460703c690b13145c0c401503803e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 530939001 1250 530937751 530937779
    0x606090c090e0c040b07060f0509010902030d09031a0a110a0305060109050f01080a0e03190804051212041e0209010b180a15030504050a08030c04081c140306010210020c07 75
    0x40450050410030003803050081810b03941511030440f0115580c0d81b407401d010340640301143c0c0c40b10141b07182c070302807009104c0154481b4a802c0d209600340c860010030007a06568519a51001520300c90100510890303140c0c041c00041d43c0000e600000041c0c600381c092481d9500d401c000400c1c0d020a80c0d402c1031002540c0c020742c010740202411a5101c1540540c40002451804042e007016000c68131070b5600d01e0840018000d885401304a078000f81a40ac1085000801204003030750192014040d4140c3d0034031111281c0c0890b85d08650351a903888180d100c0b5900c40104c1c894540c02c100900317a001c0c40700001139440b0342d0428001e0004c02e44803520f440b254044c02980ba4100c4c0d411a10984800504000c441255009415030840c1428002807550310746c10040d003071864114004008800c00002c000c04684058094400d552690381112104001242084c0c0309a00c05101203003c030740103513640d650f94503034400115480941032059403080d610684403241683c1090000c00c449410048083c40b41300c15010300c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 530940251 1250 530939001 530939009
    0x14040b120a0e012003130212010b0103150f0302190e01090e0c0f0f04090218072012030a0915110c010c14041707180c09050907140c0a0606090c09 64
    0x200540395441c5802c000048000344400d0314103070017100080452544c80c183c000780c9500545061800c0c004042828020807440103c513010910300120b400128001003001402e441d18451002c410038256002c1141550180a125a107009088804071b805040d541d0401d000303022a03e400f05482c0e0102c54070f41e060070301440c1c032207001d580c01590003149542c540700810789420b0103840000d07501080d400401c0310400345c07075040441e101004003881611540100c2061184c1ca4041d0305900390580e6481040e104c8146d00f450013500507060001c144120720395407001102a210340041500043c1e0f50454400340c0e0204421418480c1c0301080445001c0400e000c0c0c000d1030b0b0224038000b90500c040f540a845240100d001c0c03400d008540c5c1c03e41d4000c945003040310f4405001c2d08040341c1c54111040d4149805410890b00001c0094030003e030008050a0002010303000b6003c1d92110818032003060030310909500942c0d18030b0710a1140000c400081a00d9100d402d002d0940c000c008551240300c0c04014091559070341c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 530941501 1250 530940251 530940253
    0xb160c030806040f0204030605040503130e070828150f141c0f050a11180103020d110114041d06030304030302150c04180b150309070614040b120a0e 65
    0x592000254024011988104125400542070003024244d40081c02107400052040b0301d0503082c8828000000080c01d400040d11540c5403031551118041101043c05550840100c2d40090218141070305900f400d440300405403c00789040404d03101180c040d82c106280f841c040180c50709080c0071030902c4480703942c0503200c1d1061040705620b491010a202088421402e19041235034a40941006464440d50314065000701c2207032119100c03820b01000780102503004074450010f9030742c2180849041000c10741200d80003402196030549545420495100851049040000422202c004c040f0303080080c0005d8004e0403201c25002d06668401c00183c540030b0902c502c01ea00a210420010740d00141d11640e03071030040142c01c40c03601e40b0940108140159040b0300d085000e00241c0000c01c4001c0c1e0b11219110704100e444c1c40701e0300311449500c1c125100c00d841a24064100b542d091068a010b404000c01e80c80c1507100c69450070f940c5100607040c4d074100400d0b4480255100090020719030070b5004015000d80c20170 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 530942751 1250 530941501 530941517
    0xc06030e0c2b02040e0624010806010c06090614010605130f0e06150c1f140f0a1a040c09080d0504060c0b0702160803031e150f030a0f0b16 61
    0x100d98145841c5640d54600720002c2581c51000440d152030b0480c05d040c4640030106d030014144048150074140e146540110001450141101d00398404c80b4520f00070241038580d8016900d0a84540700a40076609050b11182c0e15070464400e41c5d01e8000940c4e00802e45c595505465058828603a403001645900441c1c1603600040140414610b01c800607800c44401c030f6001000c000303880e01c03115890007640c041500341c1c094a4242082c86020030031220806201d45800c0008420780c228141a00b202aa20461050781c01d100050004030b00e64420140c80a0240307402d4100e01003040050151070440c4440e1000541c1e0700c0003000020700800c040d00c54064681800b901b01411b09000801035601004050036601001c0049000280240546900645100095a10b09407074045503983d0354015141c0040d400080101c1c41010716070000b050b0b019024410f049003188038030b1401c101c04000d0099040d6810300a20444000003052003981e56030700e520420100103580b512a070098100c080450302c00701400861 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 530944001 1250 530942751 530942779
    0x50402030108061f0f12020a080d080a0b120106030807061803020d0c0c0314070e070c051b0f090415050703050c1b0f0a1109070306080d08040f0c06030e0c 68
    0x4075549910500340203010b80303a40c14a0240c0b500c1e00041c2d6010344180d4400c00000f040c1c0c843e003005904580e47c02aa0650741da907582e00e00255803440b00404400002d20302c10b001c00e601d50704075008000001c00060400b100030701900c00790750840b00a035100326a0312500213000c0f410002c046c050701c3c1084411482c0c0980d00022900c000e501c81c4074002c0b0360300c20815604220310030001c000821340701940c1c01000c5140540c140b405403665070001c901a16400400c8940040d6500f4490042021003d0f40100640032090701c0001c4420204482c07403a21b58822405100d00704203480b075001c9540b299006050101c050a88666041e0071030304d0140c000f90402d0301301020891800e0071501103541c5104102041092200590440c500305000700c5404e4000740a841c00039020701608400e2a000b9980c129014400c035120710800790100c0b856445000740319000b010300815400d01500d041c541c424022200304001c400c580d0760b0340e00800f4098200d1030200b50380d034150701c4401004000381201c070350068804008645103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 530945251 1250 530944001 530944003
    0xb0102030c03040303080a0227130b01020d11071e03030e0108060d02091003051f0615020604080c0a0c03210e030615120105070e090907060912110a0308040f050402030108 75
    0x584c2c040a4240452140465542052a4111950301c00d08410001c501c02c110008581c502140c600644d2050090310210341e18607003248920514240160000c100740101c100081e5a0015001d50b540440d00030000d00003068101c0000b03041da490740d03040c1b0a83c0180e0070340c980504007001c0c0e0a040342c1041030304010844691070f441e1131612840c1d0110350b0441c2d1f56440803c1c00191410759000180280a03410030520811078100d82d2240407240c02d8000d20615846012030341040c0c030f01c100f011005901803070106020611048c02441d01291034800d49298140640b12804044516401180e000540381350b09040217140460700c01c440b182d03034580407003031040140c0003030341da8040580501034003000300910144a681c1c030820300503030008040080c4044e16141c0000b5000b21880040b0b00d0048080744000307410f84101040a03001d640160321075041a500f0280030f8010070305548411240184016249002d603a2032002d444000c5200f41d20180d07840c0c0c1000d10801c240201a130025004a005100520031303500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 530946501 1250 530945251 530945257
    0x9050901061106010611031c0e0705030f0a0209091c0c031e0f05030702070509010b0a02010c05131514030f100b0a050d0b0d020a090501060f05070b1308041502030d0b0102030c03 78
    0x491b1070300c900f0035804101903030304511500b41480020a50301c032100c003103103c841d00001407000c03816007503e400c155103809243e207079032080c181000329420100070600140390501c1300c00d0700500c0080c00c0ba19641c8009200305001c01e00306400001213090b884080f0200b69115040caa00d0b00c0c107010111202c2c10261101801084040c4182d205104000c800100054230070000c3d4402060018082d2980e569a0008025135a015040c403e0040d420052100843d501603000c840b01002c0c2540c030a8019450728210300140240d0180c0700c82084070b0740d03003003903880c20300900035600500e46068500001d0a1541c050300d4140400d901003502420180459044681c2200c1039814119111002281e60102d00c0e00044d000907010350003d6000c3d803004c00109401120350300240c140c904503199182c00701c00300d03003045d5810300843c80000e001c80181e01c0040c500001ca0100001220722940482d82802d403070340e0a00c1645004200400016400801c802c000007000b406510020035017030000d5440c00c1e8211121941713902c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 530947751 1250 530946501 530946509
    0x170a060f09080909190f021b010c1209030203070b0f0610090503030d0203060a05040e062e0603090f0c06170c0705030a180801020706090303140c16050c0307060905090106110601 78
    0x440200040d8080030700e5044030440d401512041010450b1a21b2140003908170313490351091421100704182d060074051203802140b2009865804527510180343c120081c15103000200d0031400140440b60010b94400c607000c0c00f5102c2e4a85516407880c1c110140b20380070b054860340c2c0c0e041122555040105480210850b800e0110980002d641e81d55a14089804501582d0085410a1408521806c04840410301c00e004021003800d0341c980034580c40c1c04108401910180c080c52a031101010000d0900030f1303000844c000d03c10b8840c05c4185105464030101b90510f40e201c100810120303510144074000d024900d903802014040120700704465a19865030328021600e0207130138006071032211000440c040440d0801400148020365661180b031030f2500207091200c40403008607003040341012180da2161065841001d80703130102410641c44070500c1c0d4100000040507146805041d100014544041c890034007d070066484903c4800d10b07007420310001000c1648500d04002c102c0a00408207034010031024115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 530949001 1250 530947751 530947759
    0x61b0807030213050d0c061419052a0f0f19021011010e07050a05040b030d0f090e01090203250c380106110a08071506170a060f090809 59
    0x142000103403c820074005604400d03444002c8000c401e04010420341c504090310f613942c2c0d4109140208584101d820301481a030b408880044001c03140c070b69031080015254112203c0394040008141c4605107098110701c41210540d904640c10000800780700304906140114000020140841d14018150201c3d030350450003840384601c1e0030034034074140c403d407000344844440310020080c1c0480313514075640c2c4500f1485810701135400c0200c0040d00d46020700c5101c41141025000d8031002a0305401100d101d20304054074024011030b40380115a41164041c1c0074040c012034040103a980c20520561256401000c40000110107408003440701a40c0c450287e04c202a80103000a84038060742d4101300300e404070f081d101000d840350301400f03e40c8940b40491041c125003103501ca4500561450140315114260980d0207444075078208108000500c040b40403042c800b54844000480780d031640c9490400200e07030382c0c0c00090f40d4002880201803100070710865402000c1e00c0c8040008540c550342d520014012407855500c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 530950251 1250 530949001 530949007
    0x604031703071e030902030705120618070b070302010906110313080307031e1e0204140f040e01050106080403030b09010509040b0405010905060910360507080a0c03061b08070302 78
    0x9008003c10701c3c4001c000d00442c940006001030080c014150042c0a92080c03048000029071801c11154440f1000450070107414950780d0040d906281c00e80b1405600399a10480e0000120b00ca409000342c125240309a0002c242c1008a06160050725031010082991003810020320052003945541c0303107051a405542141c0740c0d80c0d00001a001445052504110071f15903041404150b00964002000110000f04c20b0f12424543c1c1c0029040340506d0050000214400742400c4a03072919460b6681500002480440c030418091240303801d450080c1c1c00b40300030408260a000800d50940140b092050042d125250550b2400002600451015001900500e0b000c0e01041c01d2003030030341218108540080c03ca901d24240074940075518407a0701800001c0914045d03105040c1000305500010100740524041c205204111100d4428085694110340394815070000280710802880244896401094800c0c5546e140d0305100c020354280d00d51212107140e4000468103425001072041d6008103891a0050f1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 530951501 1250 530950251 530950261
    0x32a09031519050c0703020f0a03050d1104180e0f01090c1505070f0302030a122003180105011202010905060c060a1a09010902131221091203030903020c0604031703 72
    0x403401d10340c542d0010b5400c1a04001a0703120560003040c204d84a58221903c0d540c03200c8c052a180c045401c0010b001400c208001c02171800285c0000741201c599143e448d14295464051400415060010036205521521607095401082c4120080209414009d01412030265662506440503020704440c4038070103500c0c044543c0c4500150350a183e4400024103101d281803c02a54036001401f0702c100181540000700400b00c5079000e4912110440019080b120341ca075403d641060304010f0014840c1c840701240e41c3c20109007402214001c00211001ca0350360740311070000405a14a54101700d0250004000d078500b0740d80c001070681e6012100c41000111004032103600c7c028484100b5156902103006030010880300120340c01040c1288544500350795242d075580321500407400b24400500200c0b406407011714541040c100a010141085c07520b40003036920761011408819100500380c00180e0b80c0d800a60426030100310746016000f0407541c05040501c1c42d0b5036070210114201c080c184821012012038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 530952751 1250 530951501 530951521
    0x504061208030103080a12022701030608100b0d02181501110c01031e020d0b2103030c0a0915050703020f0105360601030308100e1b07030c0503032a090315 68
    0x8001541c41042596181c2c140484109418841c20009c840d0021418105000b58000c0c4550070031103070503002800303060302c00100050092201ca036100b60030203d416110780050b41c0303c0106c3c0c81d4448401610305002d00305803106802d4042c0700001d650500540d0a04c1c042c915500181d00e031308401c001d20340803d00310420940c80c114200c021743c3d032064a500104810340003401682100119031801c3c0d666541c2001217050001100c2200682ca0416802c04c2000c507402c101c03074030024808000b142c1010a0110707524516204058614103008bc002000030039000c0406905015115940300820700a120074100511140b054900038985607004000079000315482101c0c10b034020803400300c294241c1d007007580d4034280940707a804111030112500130844404291658003215480c010121124680c004c0303000c502c11240382d54080b10302174080c000600181c0000840c100005c600ca2134840004900700c000d140c81c006041454085c900080090501a803550381c0c4001030303026096520002060601d888400e88a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 530954001 1250 530952751 530952767
    0xe0d0f120c06020a03061a04142e0c0b4015050106020d0c03050a030e0316080c07120203190318150f08061e030123010504061208030103080a 62
    0x80400b0b0010031188411030b01a4011b0045078989a01440440d6035584480c0c80391290f0300812118038040c40c0c10740810306102c80c28180002142c1e207107003601c1c080c07000f0030341540900345c0c40c51b00016030305000e80e01000081303170425400030350440105144050720103110412010050403921620000b1401858100e00f141452181030342004150400354a00518403024210901501015100344014100b005201c0ea02d03040e00315801d80d40c0d0f0b42c00c00d0a40c07142200030f49441c14103080c2c0c2d84010301054400780e01242030900f8061086454070303655000c003441c040c00c008040d84192990904a0b100340b003d030301c004c100145912002c041c070460000d510324055825845050506a215030303031070000728400d1a0105202104259500c1c0d010f200205041c0c05c45500100702c5103190400707600d241c0380e0140180c1d400342e41145080180080381e03900862018501c40c000304000061403d041d08010400c0d805d051080c00007400b103450401d01c2c0d0308043d8481032194441880024448400000c8131840b030303440386802d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 530955251 1250 530954001 530954003
    0x203130606081c05030705030c03040303110a0f14090303040513091b05011206061b052415040203010e040b070c150207030807031517010902040203160e0d0f120c 71
    0x20401000d40c40d00c0b0490f40d40d900a250b1401c0481039001d4100310107000d002501d1190f422a40c513145150f640f01c8201d51780350005403045090544074101c0c035502e940070030003801c98683c1030703600c81c0c0c21201c817440020b1a9040c8101c54a01c01a000c2148265645011040300d040c4d40c030603160340320412644d005401c010045608041c00c9242040e4000c640740990440341400c4030b209030394030024215421644012100d4034410300011a600c6c09040001041c0c11840702c4c3d485004001341e480e241c00d10071800c2220f041115800300d5052940d400c20407541c1c11409000613115007514210700310760600e0b080901c242c2000d40090309030110040058940351050f82081e042961280c060030000d460b816600006e904a020100d0203d84c0060010f50350612038400c504682c1400d580100d81c8038544480e07010810046000c584a03552901940e0340962a1800298015030400c110700744440c2c03440e8001000312000100140c8940b00302c40300704000c1400039054445e004e4210403074a0340703800e0980d000c1c0c0b880084840 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 530956501 1250 530955251 530955263
    0x24050d0f060c02060106120204061b020a092c010203090303010b0c1f02030405101a1212031005030f0c152529090604170408070b0702270604020313 65
    0x1441282e80354046109812114580c489004007069040c0110036406175001d5070300000c00c9840c20a401035a02d0704481d08032400a0202041c0a4603030102c1815648420010b85807807c045881c146612848241154540c00c500021821400e2003160135031a44018420406600b0002c9030140348101e0620036505108005e0700510514402c960b03044029400880f0144c1c0c85025104c3c000881d0b04030307401107584c141c2006194a05010444013003113100c0120194002c19440b034050981826030501e0011800380c43c14060b02030003a03150078101450400909082c0d02c0b03e4014145a100f80c2c8c0300d16000c4017090018004c120f0304e81d1202403001c41545602000d51074091003a80044060256112010080c428000200b40184040c0b80040600c04002d130380703040f02e9601c202d0005011644e2950840703003180c49011114a0b09560740074040ca4000703103402580032003900085c841e086103810150156920340c14484091440d014008030f106600004042c180116000000207101e10350421540d0030060340700d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 530957751 1250 530956501 530956511
    0x5153a060602010f0501082b030902041505120f0c040209060d0207031d01020c090c0307030603020604350a020d050c0d11030c06160f0c0902030f060424050d0f06 71
    0x107000034043c01280c030740002d103907140c0400458a041c0200b8282252800b92035121409070141080c0042507003820301e94010140ea401d484001a580c0d0701440e0f200c4000da40d40424403074106010410660f8074226480c0c8030f9071000070a210744110214650306101011500182c1320b2000b00b0200381e461080715200707043e040c8005030031000c05402c04030782c80b405400a03840454004541005991380c001c0d00c0d46d103d50200110001a01d050088002961701900070301d40822030319900c1d4082443c60300240c1125a6503018030b1180080c1c4c0c0c00200512035001504440d2440c034414890f4003940300d82c09200060300801c105046201441710802a4186440d00900003103080501c40c100031504200991580c1d120707000e0340395030010b6464440150b40c480302c80040465403406507a5601e000c4100030300f00403a007070040003100160002d01c034030103184030352401301e5902c0942c0b800c0420401207852110001e49601c082d10904c1c80780801d841003d205441098411b1003080d61142400740d030102007920b00030809400c1ca = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 530959001 1250 530957751 530957759
    0xb130203151305211e04050402031914221109010602010902040f060e060d110603040f0201021501080601060f0203040305070f060909090812070302121005153a06 71
    0x5158182d032510b001c0e00c15260080030400078041304010721007010036003050503c05030b240f0103010043c120a008111030318500e025a540702040a03600100d40791503100402c0c003001c00c0300c1c446a000b0040004190040b00c208bd1410020032000c40301012004d0a09a03440f0403403004214400607085004800142041c486694610f40240a0510603000302d01603810840302681c94885409044147c941d035401444580d0341d00c1042c40b602211603c0c0540340c65150b15601c000544656000714010742c059400d202800c0307254000a4900ba00341e40c82401388000303441c0100908040400c000c1d0540d2114074140d203100829400c104e1650065030008bc03e00d0041c00800186204400205030444555031144014140e036245040200c507481e100c003501d00c00d8200701c4030202d086420412a8402c503141001800d00141da96100c2d44440c0464805030100c119070070a021501d45502c0400c0d4103885140001d00c0c014410071042c100d18180c94800d10003c103c00c103000d85418121412540c8002100000c120032541d07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 530960251 1250 530959001 530959021
    0x1d0a06050d0b1503060103111603030c170a050a1a0904030f03110c01020a02061f210b040609021f0e040b060f0d2007050303190e01181401090b13020315 67
    0x416240039012078540b8007240800a82c210560f20003000751040309e03402051507103080e801742c0700f030382c0e41b402c10040440744400200706070541c000d000d40140355000400740b6205c5004000c0b96079a40000d1103040a601591419558030740364190f00aa15103080c0340c60714004142640502000e00e1040070071900400c072400c0d034070b8055019049030300c0e00340d080f0b411a440c4c4007010f45108550700f9001c0ca2040082105211050842903440620b61a45100c240078081c0c6441d20705448206a804546241d1203048003403d41c501000400c040e0201301001c280300001d5020b02070b2160500311703d03d0340541e845011040301540c0310015503089100060321141d6480083d4a030380010b142107901203101e0b81a442c01c440b481c0a22005550340c05034000011455a116060700c45d040c010014120070310b1a8890402d0403e0040038055003248a6641c05030750902049841e200c2c400300414584002182c2c0341c404007001282404e003a40350410035030b410103a49c00074140080307401c18140000c6860003c80c0f81e0705201070062 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 530961501 1250 530960251 530960257
    0x903120315050a1d070c03050a030905100c0203130605030106120506030a0b0403053a0f0b120102040509010b03100e0403020a0c150f0f23091f1d0a06050d0b15 70
    0x1032100e4a51205580e006026201034150f041b010740052406c2c800b000f482c41c040c1e402001803901a004071682503812207807800030748020001410050f00082094001340000c40c0c0700d04054451802d010303007190704101009024405280c090b5002c0e40c1c5800c08100951030a2013041603030307500500300d00e1141c0340c1800c000c0c02660103404407007525100c02c07665410f40b8a6400402c0415549280322400b100e041c2d0510360003074890324288040c2c150340c440e0404100e60f0b50204c0081480c8400c030015803240d150030100002c0c0f03101613200518201e410000c0040d880750a8011384181d84040110b0030980d251401c040385005c1036240014880081c0c8400424200011010120788504e5940c178149041d0600d0412508006002484c102207490001441d004282c001e444141c4400c0001071241018002c1780011345400c0d05080c8610b80c10b03494040d403000b095100a1011409010510310709030440c40b00041aa214202d01c103400400602007140942240d00342c20000c4844c4006000c619008a51404031400b54 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 530962751 1250 530961501 530961539
    0xd081f080a030e120f0303040b15090406060f060912020d0f08070b1803090f121515010201050702120717160507080c010306060905060a050c030406120c0903120315050a 74
    0x68100c1d00b00c9100c0e62400100c501460207070101550548d1200e070b0b01c03c03107000d1000e8002290b0036480d8000c000103865080115100f140a00000f040441c9001d0341c0c202100c0c1e45070040b4081010414042c060031201c0c0301030080079581902d43c41d200503000e044c402241080620001c01c0c00100269880074400e2010101d40031314000c42c02a9406084524081e913030748124004240c0003c04114428680e15148607504043c0b4a01c0d01914000c540070717924a0b90b00d82d1704865000082c2800e0800c2125560309200b032960112850004020140004400310182c2c003440600a040089148441500039500020341e04030a0400e00074103112010762405607222803050140070b80764403403c62102c4a9620038001d07030003151050b40701c1616241c146000c0c8200c40e0321513054201484070400800c2903c0c03c0c00c0004200800c0e05a5441020303805100d400c80554240d5804141000b500c11401e10215075098201e54401c0c505040005048101c01d6841d20445010350055a001c0580707a00003500c20b4903511010001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 530964001 1250 530962751 530962759
    0x2121315030b0f220c110d1107050f090c03071b06021e090a06030906180b01030c051008010509070e100e040b09010e0c0d0204121101110d081f080a030e 67
    0x2040c0d250051004c8009110010b040898501540324660242d650048200c100c0901d0030015000b441e5941a10b80304010f480718000803528981c400d8002018001c100180208980e5042d01d2900140081c3c60703040b0140220030b1030700b030010205201c02d01600090650881c00f980c10350148075603080440081d08a10030440300007020080340e1440c001c1d1700080310441740001f0004000d29050000403001055031280884000b907a0320300700c16020320a20000200c152103080e01e802650b0651410030042c50075980054040c1d05840400b41e0415040600c0d40c0c1034840039900303c426680c956004a62420040c80700d1038020300109400300d2243d921204c0e070408810152803c1c810305030704d0070501c10140001d1282544220302a0007244004211710001e144044009d007000d400c0c503407503401da501072b61070b04c03c0d048581c151103071002c240315600403858034580300c2c1c0e000c00342c074070598602d1024020240040c680c4000c076047c1031140c0c0c00000344500c030602404000080300c14929161038040e080516003800e407481 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 530965251 1250 530964001 530964019
    0xc0b1b06010602340806040309060206090a0f03021c03271a04150e06060f010201050603071523040503160f1a09030a03032a02121315030b 61
    0x810980099554122010b42e401059400290600d0140100710400003c11402d00300c000740751012500522a03010700310a501030191403c0c0780c40e01a2807410b86600020954000304108000e121f000f29040d500c454200804e10300d0114103190403410034000c600c1c0e18041d524080c3c00e4811095166112030060000700f9a03081c1c1d652014904280004403d00000309040c0010b07104040500c0c0c1c444031950081c1c446c410340150075907485414000d6401c0c4c0405000c02e644186e08025540c40c0c14003820036180f0003800200107604010001c26160f03030701c0d4040d10412a2020f280c00101d9481b46500c41800f2414141d041c8098003040480b400c603a01c6441180c0c406d00c285c40f00c103403008807a0500c980c1251140100d41020138a40801483c0300394a0340c0092012050910101d000c0c0d40b07092041e5200d5074400d86c0c000484010281100c00400040810500d030b00300070142012038680c0008074824421558028035484030748101c105800c400b96a0000f10306040d152900015107030b09900184c076004d07000c50350307510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 530966501 1250 530965251 530965297
    0xc100c02030403020904140106180e1009022125030b0a0e0d0f0302070f0302010510090c090e09010e070b1c0c120b0a08010501180f0207050d050c01090c0b 68
    0x41c0d28000c43c00040d60110b4504080740004101c445c5620000c4161000410903a503500c01d0f5078440c8214511101441c1d895010142580905000c1001011000182001304000a802107031000c1403480c3c41820410090b41010002c850410649400080c00c4126124002c0c075840c860156422912049414210b40404100c00e80c50350300401002000c0c540c0141803500b0601030407148002c44032001000e0690801c2610702140c074031448800c0345400385d00003051508101d136100c0b0000f00030b80c0c011450240380442800d46180d00913003000850710401d10b600e50035200c48012600410600781c4500d001e100d06c03280050800d6802d00038164004030105501131140104000b0400e8503d6802c0301c000103005540001c002d400c490b4000181c0040c00383c000509551140341043c02c6403c207811001c8056410903400c80c0012a5001e01500e280c20002c055080c41c12990b9881d91700c0382030701030000a001001c2080540c0079400d40c01612400e401000002000b541d545584c803041e40450482d1030340d4500e050303101c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 530967751 1250 530966501 530966503
    0x50a0e040210200616180501020c0f041e0902190f05091905090102090a0b07020a031412161401090f0204020c0708120901080609040b13020d0204020c100c02 69
    0x140300303507006030a2480711031032500203e411180c1c0da04a4881424a002c034201030090800441c0d120710407036440614039103102c0b40f0182101d1215078217171305942c00103c818030041c0d03404500403c4402d81134455000c84005900014050201c500602410f10b81901c000c510107406ca41007544c03802d000f91010030034502d8816442d00007080030701075031140010402082045040c82c8110650007080c001c0c18401201074218035005850054070b64145581d004240046245072084e135a40052911143d50f9240c0302545d03003c038150711501d1001030003880d04040800c40840062000c01c130180711244002c2d5403459000080c1100b0a000356055440d0f150300508140c5000c0b0502c45c0d450242c1d000801c03d01c4125841d802c100207548a01e501da503050081c4400001c1c1007804001001130b501121000701c4e1540c0c0040c000422144006080074403402e05e00084c48089070a1141c000d80200611a280610201900106110103204139009421500c009100c0313600440116041c003c0800004007800075214070f8400f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 530969001 1250 530967751 530967779
    0x70b010b1e030c1b0d20030f0a0c020904030e0108130b1303020a050a080a03060b09061602060d140901050f0622180b04020f010203040812130302030604120206060406060915090b13050a 81
    0x6c10710a5004001c00c080c2c94030040050b042d0b5131418500b8050b40c008560200d56424801e07101240462140d0708001140e603041010203600001081c9918030400803600d455510b610040d204640c800342e518864801c0c14030074090744900a4101c42100c0100e2080d26040d80c1540c840c062850010b4a445070109140c1000003c890b0344900080040d428129880d02c0803414002148080342d22100800c018050010180500151228105600c903001d1409400e5503003511001825409015a420b0030001e6658030600c01d41100c1e001c542a0486494510341210004c00c0c0014829083d03444000d241c404104d00130000500c142d00c02e60b80840c200d2007140040e070380c0b4001d0b0300a111190f040b03a1a002d400c1c0c10000094079030145040c1c810f008450707898020038203001c000d0b0b4050721000c01c40c14450040c070390100a0742d80c10130344c20349042210703e1030010020b10410b414081e1380301c10070400159040d11441b81c1c01900140c81d00345682d40d5030f0100031054010780c0b14144101c5006d00d00002002030208441045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 530970251 1250 530969001 530969057
    0x601090b041406042a020a030e030a1a0921040510020a0308010b0702040603020d03022b02030406050a11010e0106091a0a0e041511070b010b1e030c1b0d 67
    0xc89515515020b040201a09450600c17486880c40c201d400300c80c040c2c100f81140392101c8140c021302902c4d80789080043c911418502d49038004c2d071103200804006090403450010040450b036001042c1d8590b80c4550b41003040801c41c207a1040303010303000e450f0264407410040040302c5084442d00403454842e001a23880d41c0f0221400b0307001c100349000400c000b14400e4020680b03e84000e00020b6280c0d100d60014044190b40b01007500103a1214501800c6807002000b805001d10442040103e0820440d80003980c900c901c2c0901c0040100110360450143e014000074480ca0361008024480d080c07000007030b107000348024401c80c59041e0604040042e03600c0d00140700f40300118098070500c81c0ca41007003540f503111500035000712842100001d60341400c000c148150480e0228442c011980ea280341c0c2414001040c060300824200704040100f810000c4440034600c4d80c111b02400c1035526692090b0b10b01016018035000030380d990034003804c440c00d4000040b40c2c10340300d0b14030368440401070b990403038408452095000b2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 530971501 1250 530970251 530970281
    0x3051006030f02070c140f0d0b0106030b010905030114040b150123040e04080702030624012016082104062307080d0609110702150c0604050601090b04 66
    0x10040c0003041c800e0300510110300d01c070341c0d01625181c00c03079540f0700c0b640100da40103800070700d0070140e00d0600d0301e0403d11340d220a02e0308803081030700460951a4242101e0040c411841810390307801031000c8a034000c005400060100800801221041e48480000d45404a0301156180c408000080301885481441007900c503040c0d403000284001d200420002d0b0403e6007030b08200800c1403000207940c80918013039502c9140300b004a961a281c4500c145171412001816922841007040200111450750103505000c0e02e00919081d0565918031318800c25101d251101c9034400c0c022240107003c041c51601d848000c440342403084491080c80d40c1c0302050381d5030484185a00841c4100030403c480b601c6219900303880e0100103840c4005501c04403a001e0641e0005074200d501001c0810a030643d0b60452183c01c3c01000c103120244080340241400b400c041c429424001e00c00d18020f03c02c01040c1e02e80c0d40584182c0d4030507034212003050400707041c80d55407880709202d211b07803490410b1007180550906000708000c841180d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 530972751 1250 530971501 530971531
    0x6030105060603070c0f0606031b080f0703020f1e060c030a11150c0d06180605090906062b081b060c040302060703120e0a08091507050604080702190311100305 70
    0x56146d80806000203000c1d2900c0761140c401001003440d841100d42285031103528140341c185040d811900b0012003040554040d00304400410158640c4804044928402c80d8001c0b4005220f003010900700440200c131031303000f81c4042000265090008010b008030030007901d41400c10001181c500380c1e108038440942201d00d1401005c19555500500544411800344002103549511004280020661030407081c3c038881d101c4008200c0c5080c980390036508440180041c01c40d5250000c0400c034148c1760800300c2915103031140c002c01d252149910020324065400079480d40e0b500940542414555000103c51a15001d1900461410501e250498003140e60150505040410545050380d062200002c0d480580d40c031424684007844003400148070151280809a894007108401c2c041c81501011800e50484001c0006c0030124100207516540654002000f0384e55012500c081203050b540d01903820384507840032710080208a036916060420308010f403250681140103120032420b0f541c096410224043c511 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 530974001 1250 530972751 530972753
    0xe0a080901030c020a060903020a02010305091605060c0a200f0a03050d03020904060b13140102010605010909050402060f07260307050702011404050307090f0f021201063506030105060603070c 84
    0x794009a02e08101c0d0b006071560b0521517101d01c01030391f0311031008500507040110250115030b094898660081a080001d20100c0b102c14401c0e582e0780c00074011710303108000c0490340b0010011b0030045440c0180c0d0012a580100c400f00001c4070a60b0910031441c0d105d41440240c400e864245015803d0840b030f044002445220b910300b00980003503201300c00c2c168202e52509004611a05440d000f41700407104444100861840d040c0c1d4540c002c2c1a07c440141164148101000030341c0c2d1050048007989e40100b000107490719184001581032040d515884088000440d6590500c121070390310003c00020b00c05285009110460542c526100c00c4030f100c404150300340f009070099445015101c58040b40025007030301d0252564002445c00b2140c0e84020041501d500e141501c1140d240643d00301c60f520004198240b21000024408551050040c841080921921100d403420400001c0344500300740224849594400e00349031051401c00c9070114001d6080001142c202e0418104913480342c009031b61440c5013500702d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 530975251 1250 530974001 530974007
    0xa030203040c15020c0306010501020607091802252a0b0d0f020d02070c05030a02010504060f050f21071d0409050111120108070e0c040905060d170a030e0a080901 71
    0x40038005944030724440340040f070340b10300b0072100c40342e0000f694004040c203c1480e0100361404105811007811900008207104600c0d1b0454200001d03680c860304201141328070b000614009000c0c00f52034000200007980d0307103014101e001c500c020500707001e0402d100642c158140c42030060008482140072244015004010046010700a400342c0011450b000c1194041c090002c03059810105039030240310b6002503c4410822201900b0004103030a4001c0e01701c0c8082c940010b049806070344685030034031692040c0168054415030858442500c1000b500781c507090140d115910340d1650101c2c41e44d5041e2090003181c03000d40640c55540901d516140f24101014140040c040988040c2380700701c0d890340d00c405080a04c3d0741e43c0d9029001400440001c07401940c5095a40b44c034011255024840f282d10b4041404542281c0904413800d4552039400801c40d520b034500410b01600b60008007400207841d000d0f41800042c4000c0007011200c000303540a0000d110f64000715911b651003d10001e000d81010041380c2c0c1d003540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 530976501 1250 530975251 530975257
    0x1103060907050a12110a03061d060411040b011106010b030a0609051006050c0304051203030a29041d01050a0c090503010c0207050d0c170f060a020c0639190c02060a0302 74
    0x40300e0b45e1884684d0700450046070142c030a940080b25526144c15140c180503046c00303201d480028840d0000c10141c02d1a4481c41c1840400e920000c0c0650780340d43c003100b9180d00804403121034020700d408941c46036948a00c1e0064a81056480e041010b003000ca00150290040c05141e0081c680d07111110030f04c03850710308191220346c0301d44440f501a000600000603a90303281c8242e001c10803c0840a95030303030310389012040c040310a814060016280701511040801d095a10201020310041d2070028040c4c240c0c2201e4082440c940c02c1c0c82549600301010040c190300341c0d40101180820075112051510340b900200750907101e0380d81d89900103922041b0200718601d0403503403000a0ac0e0180290415464440b6800d405403660b0000c1080254440100c13190780103010040140d0000780080118140b0500303500203521420058007086181d03a83c0d8150020b6400c0c20407407510241c001800703203000d250304060901400d8000350004849402035440d605030050280b1040904a40c2c010003552030512500d100750000c1d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 530977751 1250 530976501 530976503
    0x2070c0e1f1d0a06090c02070305010509031608160210030f0c08071205132108100e0601081f06030911092502010f050a050103061506021b0105161103060907050a12 72
    0x2135111800059281180d00c41d0b104a0146503000e012503a05505026003503c0002c0c102034120b81c002c110921044840e8600842030a5110020b90783d01e01007081d48000e2040354107800395024440714002041e00780c040d4400500c5515204040c4404080d900050394414402c4070003c01040044407805e0000e5115031003d94070120074090030514031a40c3d16a400510189a02c89800386001400222420b8101d41042e5008101c42e080c81d0759a820002d07031032055580a0711082c184910301c0c000c100c895a2201c1542d20340502407000000c40c80d42d441000b80034101074079082d80c05c800c00101034801c0d42084804c03242b107000c99031b140044144e451280645010624280c00f021550303111094a161280c278010b80c3c1c094150a0b0010450307504504201c0300316180d13008541840161040708000c8140c011400c80a1103100c1d580e4060900d450707400699592103540d40d1414091f18964028003001a09a00405240401d90442c0c41039070300c1d4411159500440d00400d64410500b99040240b5540088441491 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 530979001 1250 530977751 530977771
    0x8130201020a1703070212040f030b09031605030d0b0103140f18030a09060e0f180c13030609110d0f0210030e1902010e010c032102070c0e1f1d 63
    0xd0b4000e515000364807258150509043d40001040c0b01c5070ba581004200c03801981c080005d40f60034135020411021001600c801004840300c0800142d00441c01d0003a5002286010f90300c0c035800c007180c80d008d52244d01858450592614120580b02e06521030310502c800b2003100c0d194401240c8482c04070440c40c0900a2400070380030034880408804c01d17402c0c0060155000e6640b030f03074040360b400e001000e000c0c0c43d100d601c0b1501603039600340d04400c6e030f6440e84507144240f9480341c01c3c0800d039103568001c040a403080d001d4800c522403403503500004000081d40b01001c4940140d01c1d400040d80d5403030800c045a5100c400180c000701c82105030a000d840c00004005c0b1882603418005680001030199504081e40d5641213081d40d10f001000c0d00c2917503080282440085000d00e0710b261041499030b00a440d161100d0101007403a000ca40c86c009046000390704480310306030003011005d1403a98a01001c40032945c12941c080c05024003200c8601810868070100040d80c030800301000d05480104903840303201344010084d00c10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 530980251 1250 530979001 530979013
    0x9060d080f070b010501033b0f010e06040203300a030b0d0302010b10080c0d05191104060314040201050f030a14010803070c0b1810020c13020c010e010b010813020102 73
    0x540c81c1c400d0080102034801d007014a00b03985048005401c40312042c0c401100308091000300081600d518940b00011440800c807400164009a013803450309811782440300c075641c170b0300d1040f84100100007800c0344164400c904031070100315499031400880c50319603a0301c51805c00004e900302c0c0b07204401d400f50074900c0700d601d00003507000501c40005c0d40b080962032041e00540d5407640107200b9420800056183c2030410b0034103c01c030341420b0a9500b0103104191000c0281c9660300e020404e80600034288182503500d252052004210b42c0307a40049a030700511400020a00e011400400104200392691042d1b030142c550ba414803540007203200e03980e480100304180142d9a14201e60200d002008194040c052900c02141c580c9094504100524600d402080004034107000000a46c1c0402001444808040d54242c980c1c0030030140a91404484141840d48241920701900d032941f61a8058000d60508800078014080c04000302e0b82200c40c0044400c2c00241c4840000d04618071541da2070161034030602c100c540e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 530981501 1250 530980251 530980267
    0x6050f0f03011205012306040903020a12030e0706020d0503130f0c0803090f01020325020a0e0a02030402040b010c0f2306010e090d0f050d0f1e1506090509060d08 71
    0x40c650344260803002e402c60000c00b108090010034804d04003100c0410451030684640c1240e401c1405800400701441161602140000c161080c004850b405504c0140c400080170b00303900150241c02c5002c6410108e01c104400040c4039071002401246449141e20b907a4910748506200d00710b0404121030685203000c0e20b00c1030354002001125041c0040c040c04001e03584a0241c0e40400c07030004640d11042e81154424070220705108130340b42500030350320843e4000003012a01031000c50701304001d5600c903240c6180e40780204105204903800841c81544200c1e420080f00d4000d40040d0f0308000c07140b03005003a01070010700460000d400c0040759809035146418103140ea1b004000050314112098201d81c0074000e440702404803106c01046500052050b40c00c101081800104000700140a6404144420740d00d44900b034045101c42d5001941040012484d40401d040c0c024046000d02180a4000081c41022a000400900ca95107860540308010400e0405490343c00030043c9041c3c1900f800d031021482001007030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 530982751 1250 530981501 530981527
    0x91303031d030d0c080c090307140d0b0a0903090501080903090d140f011d0106080d030207081317060a0506031f1103040c0314060103120f090803040602070e06030c010906050f 77
    0x4440300f0245140414080203640c001405054090180040d0120034404078506980108010041e150420000400500d1140c00a1903d50f203000c0d010300742c0300754003041c0008405180c114403000f0b030080c0c9a0419a44c0c0e104011521003c0c2201c01d450301e500140300b40da01614160440704e402d01e001315501d0103010030b00d003130041c01c0c1001014140510780d07551007009100303040900c410303800380342c0300340200401c91406240c40d407a01d0410805804043e400200c01d4100030100041d41c0c520b80d1294014004503407503680b007410040c01013a00b40300314801c01c00080c101c072810b0b0154910912020740503041c40c40b82c00c1c030740c1c107550030000302c03036261198880100f42a04960b5901542c42180500c413100103075807031410400c1b40c1d034542c00c0c4c0980706074000d03000610219060380e45040c8000c20524080d80010030090080b209890b1b2a00180241d0100080010780300fa8006641c0055070b076100c0180c9081e4840b5810117548180d400000d0780845d030a450b00304095030040e40a4100688401c81e0303540f03403441c0320b081d032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 530984001 1250 530982751 530982757
    0x90e060d1e0213020409180c0605070804080318040f0c0e010e011218020111030403050303040209041a010b032d0c0f0408010e1b04090f02090712050f070e091303031d03 74
    0x440f5070f0301007802c201041050013810000e0481c468480401203986d21806070140c9203024000500c000062840100100c0c0401c4400801e442c000781c9842d071b41801841540c1c50000140d043c40b941c103201c85506000f01c5446070000500d807030344038075080c918410b0041d0b034084604408141880003140d502e0003c40e406d402800e4250100107900a0302c40c1062001506000000300c02c804039610501003800001c00000031603801c6a01100c00290036a1a881c0c191a09010612400ca13001c50400000480004a20244d0f000311000d400d40003141e1910241004458030400c43c0d09421100300d1701207440444400000d185107258110420300d05070f1140f000321b0130368541c080b184140b07621404000c1460074450341d40e0000720000f1941485003c000b074031a030510f108114030103031181040c44085a00c1a0080c280075800141d150000c1c030961400050011107003c04542e800049000018605400d24107901102d100740100c00149c840c41d00140c40c1200205904100301305015504425134240032010005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 530985251 1250 530984001 530984029
    0x40b04090c03030801080a030806060306060f0a090f091a0904140a0b0403030c050406121e0908041a1c020306030106270e0c131509110307090e060d1e02 67
    0x603407060386140340c010040da40c16400708401e500460326081c0020303407202545c1e0300504115119901e1341c54440002d442481169021040749600040c0c4d194030302d40021480c0c00319801118807425940d80d8840e2070090360360008001d281c01214850f070081d03a24140d400260054021284000442c2d0202c095070710304a0100c1c000d03105440c0080c02c0004040d414012801d14070068500b050515241c400050640c421212060b200e207510b50500a582c11070860710202c103d4500001407002a10702d0820107482e90003802030b0f001040003042201d20b480b07541411103074680d42035600141506c4210340b014000b0740002e48603503819500e03080001410500d195103544e441551102441d00702c1511104201281c00d00c03144002c5039009186510841c1da40c00005100c05030410750041082840d003401c1d107541d00301c103420007803116141c88241140891120040c40c8905600d4407413215003900d80440c028543c600b2640d045e13100032414800703000030711b15106025004540c20007820071440316a0020b03803c0d40c2e05001c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 530986501 1250 530985251 530985263
    0x705010905060109050618010b070f050712111504061b05120903100509060a090305090d050c09090304260307021206090d05070c090b06160b01061409130b040b0409 72
    0x5011300710b05882000c1d04900c0860b504c5180c50a4020583c014030014030407603250702c002280380c006204d040d00316503405941c804256003001e525841d0889521350076480a403040b041c60285802e031802c0c032188284808008408450401d86416401c41c0d03500d5803009045985002c0710b4444002403c10401d50400140e6403612507241e0f00c50605041c903010ba0748408040d000e04101c1400035900c2c01186068020003030600101c0d103183c0600382902c89103d41891b0a4000c0781d0340184005201010403a8100170034100c0300c841268a544041c0b6a5034000c5001324609e0036a030140e0a00c0140c0040590100c2c0704800b01580e040603001d07000100061254a9040c04a80001c010400b011030284024005003400e410090b05100e010740b103a034100d4205009002e02540e075a11500526035550701170300c1c403140c1c001d40810f50b000401c0c901001088400c0c031481e808030311140da00f03560481c90641511070b0403002038000d80071182d220440c50060002200d9040d0042d640340c0881d20692201e018400510303020380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 530987751 1250 530986501 530986513
    0x20c030408011a0f1f0810170c0315010e160e1e030601080106060e06070f0b09031207030903210b0a0905091c05041e051f030605060a0509150705010905 67
    0xf01804400440c3e00c1100b44500c540203400290b01c46022030860550038a0301c0c2110703556a41030000c100c090303100c5e002a80a50554400545141c00000d10341d010810184e098510300c420940d46403425050a00442025070300070000940c81c05a1080c04180b050503500c1c1c03188001b421500803582c00b0045030940c0b804040c042a400142d82001c01180b40102203210017001500e2030198014502c040c03c2c2040e500c5240c0004a030020b10000c21000541c4541092062f0143c0c201603c411341d90b0b44c00310a8100082d03d1460008200f03602a03c40c0d0443e86405483e0303108803140f04103003041d07024070f01481c02415039550307a042c3c8810744510700721002034521001c00107040e0400040003843c0c5000301e0500d051070390f98441220115903001080d42e0454103c80d4207a800c030801c403020814404565040701e600005070070324502d4410710008a900082d091038904100250300d9200340120b5206400814001c01e80c01c00001c1c05904291400980120107803020074201801a40c429080d07880c031039001d44142e4448 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 530989001 1250 530987751 530987801
    0xa0507021e0102030d0902040e0105090307031e0e0d0501150621020301030201140706060506070c1706040b0c0a091e06020d030b130506030c040507020f10090b0109020c03040801 78
    0x100d00c41007050101c1081d6890704420340c0380000c0d03a9100c0d0f04100019a41c40c1c080e030f00e085444035007103e103410441d81c000340700500d81356843c50f54982100300d099000a400310017650440107811101150010b590760380c6100c02d04035205000e0034207000728084501d50350315240c041ea0944d4440c241c0d0007030161542c841062016148540e102003022202c003401d054410401040140c0e00880c42c00ca88201c02c0740015110403450030309100605141e8000d540000000030510b0810148250540590780744aa00e8003803090b682c90740a0b983d035002c44004140c1c4a030030300400c0000e0f0821000d4a2660031038640042155140d180308982c01c00c0c1d042110b414501490010f0000781c2d018490b886400c855841c0400002c0c09480004899181c12280c8105160340c80021070a151814400c1e6000114060018041400d003850000c2da916100d241255480c00348020032a094007840c018001c40c4c641240c0d841c0416420100782a0003940000038a10780e52004001c001a541401e000d501e480c91451070b0203d140c1044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 530990251 1250 530989001 530989009
    0x2030d0806100215060f030f0712140604050606060921060103060501080609030412030306051801030605150a0509060d020a08010c1e0f200304030b150907020628020a050702 76
    0x190324588250b40042c80884d010501c4040303910303401038040b920f0500c0c80c0d00000101e824500507200d00d618a0240800c049107030168000440300d214810a000d121805010008540301c500c02da5008109422003004100c0c54a44040900030300e100c01495132219010344000a00c103050761011701e20312500964010014003a80713100d014010700c00000989801d1907e005042d4681c0724501403080e540d03401c07082c0b40050510a81c8140080d04018160664030660002e4450300c8600c00d1204076245801c00300010b50500010f0400c881001016201c007494030b0800c030070844443d074010072a94105082d20b501d80096940c42540350010b1101000000309801c0d1030704000e098403600301040001180701001c0051069000090312005813051505689290001020300100415140044054800403030301209100c16070380b8480c000d540c8154590100c038480e4052060407801110b41c1005030304080700107090502c4482840401071070301820303c120249002081e00890f00480c240c1d5002420104031340c011410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 530991501 1250 530990251 530990269
    0x40f0c1707020109080a120f02070f0c150e15070204290d020d0b07020f0d031e060302030c130e01050a0902010e01020106241e0507020a0b090105030106080c0702030d0806 75
    0x1007036200034401c614050b19001882d00c10000d601040000170644901742604941c4001140c3c050032200359a82c84c418104840707207100d000010f8407041013507000000c5411044000801ca00e00a85800c1842440c20702044519004012168041d040400160005a45034810702d041d411700440391490091504003aa404011030842d001e00400140c020700000d6030705c00446441c4254042c5402c042c030740d1622030807803c1441c102d19045080c403030244448415030705034102000da011200c5c10660460170480c034803001c3c0c0d05140700c040d426408c500000e001c14140a4030002409400c560042001d5a254922901715079045606052980d03490040e00c04560380091028083d407402d1000344101c80c06d28030b0309180581403504426500c110b403c01d559a06005100e901e8040c4890014121400c1901501030716961091504034800c2d0000c08002c11210ba00505880c2c2203107040e902c0a09607805d00748141e8041402030040f5103501e0060042e440107076020485008451300c07030750301d001300e60411070180107a5203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 530992751 1250 530991501 530991511
    0x3080115050c060406020901110a030504080d1805040522260a0f27090605010305100e0a0207020a05061c4208060c040810230402040f0c17 61
    0x904000760001c5200000b01990800d1704010016a242003910041c2d13030720a5000d020005c40d006080b001c0c2c05254001c40500112002a406d4075130092001e0b2084801407000c00b100607114141c0d050500850819911003070f40030000c40914050444200142101c1c0400b4010850f80f071003107403803401c0444804215452340c220094000500b8507010b590701421480c0c40e29070b01e0041045a0501c1705c1c1800003684a00009038140202c4481962290041c4001e0550b9004a5000c80e0800340402e0729260101c0e0903108030703044c050380204682c41d21611000079600819050341c0c08842e00a01040a50781d04005014102d84403c0c0903840d002e080c0d10072410760f4516200d0f8103040703114840c1c40419000c08001c1c1d600b200341e507160404a1502004078032000f25450703042520144125810007183c4800c880080050381c811100301c4500603649d0781d0000a90b0110707a282d690025414002e00c90031307801d5030007047e00079100500104030781030020502021600706c1040400090540103e01d04401580480141c0007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 530994001 1250 530992751 530992757
    0xc010906090501050d200a09030b0106080103051f0b130b04110f0a230c060106170c0409090c0509090a0c0f03021807120507110d0201200a021903080115 67
    0x315182c000041c1642c099a130310001056140c0d8040340c45480140c480c510303100d02d59000c441c2c1311a4031280050100b5003a002c2140c0c050002400030031034a02070410075048952250082800e0030610881032024140844400c200c43d17107030403204403240d41e400200340000d4036801c1c0001e031910012081000380c0d0440410450480c104200704050140c104089418a00c01803d112402d0801c01d08261303021400d01081a00c424000300f50078681410105082d4121100c80e51940c10140800501d600c4804003510b004900d08000c00c020801051690409903040b070090b420364400959407000300b00c02450407034000806400c4041d16074200009020300001901002210b1070300786045602140d0490704407090141c0b0060210001003800d80324041c090f400d417101e51010700c910309160a020b0844502c1c240952540d0041084100e503e510500c03540800c03e200d0b508400c0503d1074420070500a52003008080214020001c100c0c020302146200404464405c0c4ea4085141d8505004012061142e440354010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 530995251 1250 530994001 530994017
    0x8060c0c1c0e091e07090303020c060c0a1401051014090f061309210905030705280306020405090a0207030e130f0213050a0b0304080a0810180506040e07120b07140c0c010906 76
    0x8c41d600051085141b0816124213a8800541c0d006600d01428854020f01c411f0000010403e40380040d00118007a43c42201075008a5489000901d0b04a401d0310300703190840f5004000032415001442c1079900508050704144841100201580c01d540c42c44101340e40211001c155a1225050b400d0000e144071858604482940d0405000a4071122548a0b103031250307200142640142452040301c18000f100c89442c210265501d150000180d0800e100b890b01ca040d0500c00101c1108850088945e0994581d03160417100304218104100048480b01040d4440c0ea9165089034011043c4010135a8144880740300080034a00420810151080d0700b00c0f107510507050003804005034500f01a42d060349800e0030b0080d03190361160800070740800240d0007283e143e140d110800c5122100d80c0e10484c02640160340a00c00d0420942c80259950040c0c460500f56840d0050b0140100f5030340102541c0103850f40c6840780c0071815484ca00407490f004112880026001241d100b48a50381104400e00100782e1810904c0d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 530996501 1250 530995251 530995253
    0x7110c01140d0f02090d03020f0c0f18040303181a0c0708190e0a03121403090706030e1c050307031406060711010905061308060c0c1c0e091e070903 65
    0x414014480940549a2603404100c0e00e40c4894040e43c005810140c003140003401b05050080d5105004180180b00d4001c02490004030300708100e00c0302c0f40b644045d140c482c424041110318100c0d15401030041c1d0426517142d42c0410f0148032062245171050044110000089001103210b8183d0345c041e0518071150810820000050700394010742d4001c84c50b140e1036410160b510141550403d000404155100140b5000403040000700352441b07035050425940c00c00f200070700241441c050300c403d540e0b1030036603841001d04101203407190b0010b0503440d004c4001c0e202c690600070114a6400240d180740d4020030004401c120b10240d252107850728540c0d014080303103d5400c0c2140802c150388125140a4014a03840548071807507401280c84000a00b0702814190f95081442c1c250900a0324900400f5060302955000c22200100c03041551248640c20020b030a202d107228900a00f0342d904003001c0d006004103410203000301c1c5c0ea41e00046110724040006007034480ca42098101901e00c004100300140080352a043c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 530997751 1250 530996501 530996537
    0x1080903071a0c1309020d0b0f030705130609020c06040510020415050702180c1314060a1b080d0213060305160f0e090c04030302060601170a09020a0e07110c01 70
    0x10002c14280181030a6900d40902030340080c4190480600c80200c4400f0001d24a0400e600500c4409503035581000200c488508006442c004601e8030341d0305a10070501441203140c0490805000c604c442e0380003a0a80d80d4859000c280d81000083c03030002d420000c208030a00c1814040c030305180101482c1103103400c1c107000019003005a0340f07001c003042200110303400c1c0840d101c2c54945152030f00000911026458006065076840d400000744001d00d519800340000d03284c81201708184848001000300d42000c40c07082c000c07201112403e2941100b20302c0000603902080b60140140010464504096074070400054008140ba20507480360301003500d44010054100c070020b241c441d510800385040e0900f02c18407102115a00c1082100e9a030200c848014400b07501e810034000c2c81201d10035000c0c5c41d150380e0350740011750710798aa8000c600c11404200d000260320041c1a4000564a03100801d4496042d84500800030003800484032800454205000380c0242c010801103608868000d01c0e0a46800d0341c00302007a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 530999001 1250 530997751 530997773
    0x40e040b0c090301051021030e0405040503070c03050c1f020a03030b0102030c070807030b10060f1404030b13050114060303090f03011103190608120913060306050a09020108090307 79
    0x18110101640101d0024075003030007141c00011004000b40020300300080905a2601c80d40f040301c5454140400b802e46d401c02811141440350b0301074880381500b15880702404041d2800800c220783e9808100a1100000c0004100d60099800360340107107045129101402a030070040440090f458412603045445560300140320110581e25140114017240310b0801030b4990f0080e0880c80c01a402380c2c12000c1788826000400780200d900032540f10205444120039001c203403406018200000301a6442050414011480c15010080c070f440b01e0303842d003540c0e9103820038100c44c05c1c2da100d48011341c0780c0c424206001d001d00990242c01600c180c0e030061410850002640c03481062081c81c01003556104042c0b00740c0d001e51002429600000400c0e607a4a06807080c100e244190050401c04546840404039503400300140207054503400345c005918180f82d08042200180d030299008403520745801d00400056440c0c01010b001d4512004003249150081c4005000c071180103095200d0341d071041c00001c0c0402c03c10f03154 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 531000251 1250 530999001 530999003
    0x14010b0418120c060f02091302092107030803010f0501120b09191503030e010f0305090705010305181c030e16030204021b03210c13060f050904060305010b15040e04 72
    0x1103520682042c002600c0070307801e80c08064101854840c180c419885503030010700782000d044030112201100b0a40d02012401140000d5070000c10248002c6600344a84d0b0503a1489000f02c001c81d84040d5580d17860301c9007907200f40c00000002c81d8111080040f0750304658207901e603e020440602003407500d900418418500281401c944181d07040c070481d49001d056100d0200500043e10404409890b424003411552002d001070b030000316015a07090085100b071203000c2c000c1035080050b04220380307810300440141001074000310106854030101c0d503045a0802418215405010f14800c8500c0040c81c080d0480c2d500550031460341c1c1114003a103079005c01000d00700c4d0035644c0c11980185c40d6409241d80b05820602c80c0301c401c029100c00150b03c2090300b00b540144041003041d0b80f12400310b0387e503400101003900a60f100c9414200080700c043c880240a5120918603014a2a00e1400c2c15905070004041e16840c4e441603456941d03a64203040c031420705600c2c82082400c1046002d281510301103444502d8400244 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 531001501 1250 531000251 531000263
    0x100501140a0e090c100c1a1f060203070602130801050709060306140916030b060a1107091103070f111906060603090f06020a0c0c1e05040c02030414060c030714010b0418 74
    0xc0c41c03001c600400100c218290000c10b04449003201f181c1c50300c0440801d03160f000d02ca07042d101400050410341d044070001e450582d4041c50402e08213a4800029400080040e0700d2240713040d83c0407035500030034420581314048a41e03a295009140ca00090b007225141d030030518080e901101031a01c941c0f90158000c3d04622003400214154582640c02c400501032040059400304000820131145a40a811905030b00b22600c1500d00d85644e80039020110352103104d810075524018000141014024602c90340c400005081c03c01c082020165030b1800c00c0120000c500295540ba08000c051140303912480010b49654202080714030206e460f401d015445000009042c10303000a910b000d15446031604100c040d23030050081b46582c0d00c405820403410720010304104000c05107000041e141c0703080e00a00030104040d4019616003414240000d00c00c4650040c078a40001c01000082800e0008100414199000d4150341c0c3c00c4034030840045007983c5210566030f00c141e0130110303e0402d1502201003020b00da94044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 531002751 1250 531001501 531001519
    0x4050d021302130b0c0708150a0e0c09092b0e130b190602010e011a2103160302070e01030503030a0b01021e060901110f03060d0203100501140a0e090c 66
    0x710070002a2290b80724503415400719410000b000b80500700a0181c010590040c0c8000039115201d2a03524032403480c04812100340e1402088581140385e21540c60a4100000d8600380844040400c072a00e01c15100d1001a901240846007500601c45074040c0c0c41010042918522490a41c010b03d4110ba01c07014a2003032040c05d1501055401ca42d0040004040103407130120034903081c2000c81e4140060f4898007000d5400c2c031800d0301e0b5810042c400e84580281c5104004450044a002e00c0b0303001d40075620b8440c404034034203000034103070030104060321207010a0901c0c0000881185002424070f44980d1180484480c4100140300245000c801d0300c0d440000d20b0350000d964652400102d240000c41300100c1080e500c114400b41d9044000b19503544034414440003446020103a00c5a542540700f040d0500d5080382090000c10050f00d019400c0c0300045000504031003030300c50509840d10890b9030a0b0b00a08407005a903024a1050a04425800080c00d89100301d5045140c5481601e4a42001d59080c0c4c0c4078134249 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 531004001 1250 531002751 531002779
    0x50603070e0f040605250f090b040b282106050603070f0f020c15090609061602010807030e030d240b22050114031e090615030304050d02 60
    0x2088410001e01006041d101281000c028482440e80c1c00e6600752059820800040c2211000d540900749200310452105070040c9180400c84000203a4607120040104041c80041c00c602424064409000302e4440c01d980c90900c5c0c00404520754140c07110054003034141e034200800941282142060080c2c0ca81c441052007065080d03240100a19007203980d020034080240801190701c11006d420702079241d215518a01c101c500f090383c1e140c200031480d581c4404000485880c04281c0c1001d0300c0d201202418a604001001c4005003007030304085a041c03100304074165590103643e4400e070f03c10303040401c2d4201002028110284d0320f07124030403008c5200c1d200d0344034120359035510160080d51014910502d5126400da40311904202c4540c00202e241080c05060f03c242040c042505880c0c01c200d4405846219210620010001c0316802c010000c01028002664a402e1455041d03401841042480003600c5c062030100d02c00d00032480040480360083c0e00900081c0111f403214501d410106804803031146e529211 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 531005251 1250 531004001 531004003
    0x140919080a030b180103081b1b210d0507060f02090f0d0c031403040501031b050406080a061509090513170c01020f04090c08131e0203160e0a0b0405060d06050603 71
    0x41c090b82c00d810300244d100001c288070f0b004e0f0107800c49048401c50105040c0fa0358113000e58544450752107808201134510010030515114460710b19154640b00990071a0340c2c40c010382d509120004000350081040010684e0401200d8450604062040c1b481182000300c8140403501013580350502c14060006440a0028421440d00c554015948200403610fa052107400780390f200cae0460300c500d0340820704060301400c0001c2c164500b01d41064241c1d46081c00c0503e070613400c403440000a401402096541ea10108000b0410701031207103c011151076031002c16140c07140c40403c45400512070348072441c426180d140055518103090359180d601c48801922440380440341c40c02440380c141c4854402000040005180d07a0640110071013000c582c44503841951022611221000c40c3c1d000201080402d420401c04100c00700f00e00c026890015085034116014100008903c01e000d40140c00242094010040c5150450141b010401026241800035041400100d0400c4180070340040031251244006100790310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 531006501 1250 531005251 531005269
    0x50324010311040f0929060d0813080d05040f050301150302060309100e010b01020c010215041b09090309080c040e15071403040c2303150703020409140919080a030b 72
    0xd03110000704400c040d18076184486c1040100702c035074940b10340d4142c0c0324000c0c1c2c001040e9214541c090181c07c0c501180e90750303c501f02e070300400d010b540a0114110200c2c01d0b29003002141001500c03922420764850400707d040300c2c6a030640c1d11441c4203030b04203080710b22015011042e000c00c42c0d6050390300c56140d8550f101054200141160044200f51404011145140c0c0c1500a1041d448003070f000d41e00e07284400c000490300e419200070310006801003440418000703114500c07031000c442c5410400002c65034441e40348105a501c054020780004220303040c1400050014401d0b542096001c540030458215000e0400d40c4035442d858240401645070390005080c5401040c0110360103022038806507980c0707000c0c90840c0c003c5802c0d028081e401c80c1c56400a601084400d20b860044400040003461071204012940110040c002c2c00081010707020301c0001410400c0d030181740c0008000e201921300034540406e0481c0b9164a43c05000790071072a01c40f0410101d00301d0022241c3c042c1c050300d004182c0c5a079003004905015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 531007751 1250 531006501 531006521
    0xf241008030d1a1507061802010c11060f031905011e060806130204121205130b0a0c2108060303120105091305120a12050c041202130c020705032401031104 68
    0x100102d0214040e40d11308010000a031050400704881140c4d01e88000000d000c2071002030201f0b01c0400c084000c0781c010407a450480320b00424603841c0c9140c1e400c41c004190426180da1100042e0703903c02103110540c6008190140080600503d07023061410b1a001e03000205110700740500000c2c00204519031180e4100b07500070400072005541d581c0e40d40031708003010111740005689014929102c003800070710460454450b11205000744810381d042c1600610300d0b902070540001840004c0c00e51400060591301361920184c0310100c1111710860300d101c05000404000d10f100d109820812034402e1000182c1061030569006940d407900c0d0b680e401004001160084002401900c03d0540c00302c0c04004210050010005c42c0d614503299070302c41c1d401e0405035001a6090104036109100c10312030310003641c03500c1d00d486000810140c215004040080c0c121755501009200580011600f44914101045070110054000004c0e00740030441310075400c00650107000042c15419000c4000e10b4036a511340002c8c0c160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 531009001 1250 531007751 531007759
    0x20a020907020a050d030b01211806020324100e030708060c090f0f09190605150901021203040309060810080d0c0c090c1d030f241008030d1a 62
    0x50704018401940e254a0003108851038032802e100c0305001e6219000f80c0d80a8001a11074801980080b41540814400c0c1054410740590301c074481265482d900b072400c03c00d030f4002c850051340da0411070400380031405000900c0094880301c050145403078a4840700b5006900080c502075a603e6103c000103814170003168401a601c1c400c01c81409a0b103949440100301041d0110b0b072440c00402c3c0c41c4184400388443c182c2550303100542c3c0b40001c0208038402113800c240c2e00c0c01100040c016449000086044944984034905c204000c0f4200015503010000c144982c80201c081e141103282541e40104101c819004138800c01c5100404501030302100c6030721401815504040c2c40400c0200d4000030010880c100003507031102c004c5400040d240702e00d072180f01d2800d02e440e91105900015115080003881f017010420f600351045e256404413051040c010000c15081c0002c0228000e8804150415084e82c09003c0f1b078009801d03c0c0c0108080e003800004c480c05880d02c00e5010034100d0142c1c00e50f042c1140c260400c9600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 531010251 1250 531009001 531009019
    0x308012702070515191a130e03090a0611060114100309050c040612050d0305220804090501080a061109010c14070302120a021f02060106110102070f03080f06030a11010f020a02 77
    0x800d10403c440b8401400c3c805041203046d80341d40010340d081c424480751913001502d10092081c00c04281d0071540170034080d05c085900c0c1c1807200000c20061200c0c2e9000e00001011800040004038083c044503005001007442c0e0a29103000900090442615021100600d55110400400c1080078000424519030040c010042d2954440202a1448600304201c49500400c50328031980c0b4003900c162402821440c88121300706024460540c1600c5140200f502c0648080c44002171191039030144034060511440500100c041a18002c42560310340c03148400750002c00d00c080c0303802c1d07640800540b0201d80c2211f81d0b81c2c0c482c8100900345041010715080039401400880060840e050009240f42182e8420ba03844181c000107806c10040040c1c1c8544031a0068000340d0041100a118007855040711905600062419420ba0b494460705e405290341100400c4c9881b00300106240100c00455102e041a0041c00144d010360750341026211604c0c00290500c0b02c050380100c0c540d8420050011401c0c1c1c045e24400da = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 531011501 1250 531010251 531010261
    0xc25110d110a1511121602010e03120c070801020a0206070c0206160b0717130803041b121a06010206012312011406031209090403050913090308012702070515 69
    0xc8a4043c0d40c500b0008141c3c000c00d000c00340403002030541e00424480301e44c6401c0c401c0301d010952800665210607810040c500d0080036040e07134140444008600302c103810941c0c88401030049402c00b05240d100c00d205920500c20780a40c66000300d8000d512208619000800c50020310000301a070154501c0010341202000501007042940080c15010b14045e4440406107038541041d008283c4088419105d620580320b440400074000340046c5410034421400d20b40700811074034130f048030a50258043d841b00000a01c9450501c00e880c03201181540f03450744000c40d589400c80c00070355194030602c24600a08405032411740c81000e01d011442c548540203042c00b003043c4040114030f020780420034400e0001c0c0345120101d1414500040c0d002100604018100d003042081070070171203003500013441076090280c100046200e5640f0502c2900184254500004065080381801480c128050308444942800ca400780d49401841e8888a44043c03100100580d0f1007120b0719259081071030b0390088045044036101489 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 531012751 1250 531011501 531011519
    0x71b24090b13140d020a030f050a0506040308060a0e0408030f090106080f010f0f06030f140703021f020f0601210f0803130611120610090503060c25110d110a 69
    0x4012035400d60000e003241501d0300c080200000b0071304c0000b54448080324040000566010a121409014400b07840140540b600d13000e0031701104550440004283c442041214540003a40d007010b00205c01400c0214a8075035211101c80c40054005411000c0038070025422071801d400034805002180207403403841c0906030701c2501900004554010702c0e405c04d03208000280107407155500b225007020060a07541455110300203441c6505c10141d4490244110100160302c50008003080c9900400101e0381035a40100001d041c81c0c004034140c940d80c0c0041004000b240302421740d400d41200f040300040a0302c985032404085c0941c00a0004110080100c20803940c030a886d50040580781c011502485130740941c00c14a0803906c0750001c146040084000415541e0510484e03111305403405003030502400341c440300003d07d03040d41140d001c000d4000011b0f044410500e011800030b80e04a10001c2000c0d4030409994001551868144d498014160191400241f0003290041e02c000807001d041c92041c0c0e42c840c8040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 531014001 1250 531012751 531012787
    0xc08041119080706030e0c030c010f050a1223130308062829030412080a0f0614030c1e0103020f13061706180105120304030215071b24090b 61
    0x98061f02032401100d03024100440c1d2004504c8050f560455071200703001040e91030b038010b90b4441d0f00b003080708020034140c0c149030710564180301c01c200707038002201c0c0506070428204100181f0100c66131410408580c0040c2d00021207541049040741d42074031100915140d6110b0941c80c04407101c03406032004002910000142c2e0695112141c1903403404004141d130307010f110301c1c0b000380c1d4010401c40d102105101024403801b22150480300c65075005c03d200803040501000d443c070981280c0346d1040040c1000c6503d240030031010740614001c1e101d50b19400400031b5141e00c070100c400500b80c1031540004112001500d150202c1d00000440c40c849030840c0d40310302c2c004054600042c508402c100441011828600d040c0340d020002019070b403040d0501d6030810062003440f504129640245220520021005a070f600000d00f00303145030003040948880c040e049c100c070070303034100300e030402480c5540c1d00d00340210514040031070981c054260301c01c0b100101060044601d00b40c158442c079000e22000c699410a25800410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 531015251 1250 531014001 531014021
    0x6070f0224010e06010c200414341b0507050907020304060f0314192c0c0402031e06180408070c060203040510030509010213030f03030c0804111908070603 68
    0xf900790641d00c14005543c1001e510b98080c0004824103154904032600d80e141828145002d040490b0101980c64a00b11080d01a24228000e22070300000340140244a0490603000e40140942d048440105501516264403a401a5080401c40308000240b00c0e08021070303001002c018001e40d9441c03400040084d1643c000b0b00880d40022240144221614400e010301c00070620703040000c00944d01e404d4903403500c1211501034180a42d4840e0030042c42c1d0041010f80c4241c2c5034008203007520702c084140c181030501101c5001c0510481c418414071048007840a940301a004201300c6010003900ea0070001540310008002c0300d80002c96144c100003c00c50044040d2070003500c1445c0c421a07131615070609907202e004070b0159a4010015032419412076200e900900e400c032044500040c6402c6500214150440150300180c0f0010312030040d00081680c1882aa1080780407858401840e003016519240800c1c00300542c184500d518408580e41a45200c26010082c01000220b039526035645201030003610034003131 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 531016501 1250 531015251 531015269
    0x405010509070e060f15130501090e010e072717011a030316110405041b08030307050906071110080604060b07170319090803161106070f022401 63
    0x1c500304000004031241903515800441e5500d07900c460a000201000400302684a240040b40b0f8408030312010060904003800300020784040d050200143c80350003d44d211101a03d04140100b103a80c0c096142190442e6407454800403502c00c10750303c2e400c0005402c1403400241e000502c0041c007a81c051240350705820181c0c00034880b142d18180417400300c03031003c0c94041c0c05800401c03041158409a035400700c0b1045c0f043c4460700c03a41607804007003401c98104580407640001610280144034055010034001460301100841c41e5242c00000206540600c404844c020400401e40da41000254500d10050140241c80caa9041405401c01000c403401a6485070280d0b14103000412540c03103903c01c5034142900901c030030341356080c80c04036030845e43c1c4000c2c000b030200e05e0581c90f800c12041c0a80201304100340070300c00c225100d04000103110310030181c010f8210140034903050741848201010454a40c0401541010400b24800b020b06a007403021000d40d1942540150802100e0766480000050580340000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 531017751 1250 531016501 531016511
    0xf05040e0a11011412130506180d050a14030709050405090c030a110d0210050a0905090402010c023307110306070c0b0702070e07030b010212040b04030b2a03040501 72
    0x94200d46440700342034090300700b42000103491000e50065400c0102c1c03804c0d111056140802d03012084001140540d4440d1400502c044a2000c0c400204443d5030030113880c20b400b0380f440075201c2c07016580303004424802c014000c0c042200c01145000741d9030303101d00380101b1280355170742d1400c3c00004006160500071988518a0440440c1606a0014440800d44000760003011010400d40350102400d04d01c4444540c8821190380400058888031010200721070281c58481d01c4202850015016407004d400090148003844200b10150307034041c1042c0309250b015582640250b40c1d0384440180208001003001c80c0e0401030f403088403c04042e100401c1164020880f030092003403000c040644420f0305172110f100107880c9a10400100ba954150305400100c41e0045900f0281e980448010001080f00c40d0310200381d460721010303041e50b01030100d00b000d804041c0f202440e00b030500d100f0490901035404050700040108001448105030817241c0060318518844900003511010b006010990003150121000c0d4200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 531019001 1250 531017751 531017771
    0x406180b030d031a0402070c05120a03020f0c0d06051801061d01090207020108160201091a01090b030a0b07030c0509060d050603100504020a0605030c0702130b030d020f1504080708040f0504 83
    0xd119150316220788511308280b0310b030b40c03008200294002100c25601f0902076000060b56564401000301c0f40700c5a0000703803194402c80d04020341090010145a1199004650340004a541d4034900e241103e500000000302d07521a00246407031010801c1c2d034010f5941c41e111002c10b10003031b08040703000b4030740180948144a0780c0b0780803000c060303014800c8001d0126120030086500c056941880c0190925548000a501081c1f5150110001d540c4034005500752048401030120704001e02926607075503c02d800a01881c0403a40d642070081d44010581d4040595032215202d406118a040b02c0f80c0c040010840c80d01d5844140d40e480040c00300b0b44186200340b040040030011850340e03006540c4955002031441c1c0c2d055140c640262803170342c402480c01030403441c00c218480040e5203c400100d00d80d41c004c0e200007426000e1030700b81482c180d2060300c034400755031144481c040e40307600014a0800851401d600c031485a125132500440340c1c060100300403c0b02d0b43c0440c0c00718400100040c10b40481d081203a090001d0824 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 531020251 1250 531019001 531019007
    0x19051e0d2405010c0215040e0a05060402070302060f060a0b0d0518060709060309080f03040b011814012d080102090306160503060d0212030412061d15060406180b030d 73
    0x24499104055001c1007020491580502e07090b40c0c0071800079082440c40540440303441902c1d072082e04095000740503042800000c0686204a9900440a2f09e04514080342924041e580e41001888040c041011030001381c041e454010001d0020041011403503151106800c034035015140440e02d150320200c0958512112500001d13445004005584550300068102a0210302601c0002402c0e41c1703000c801c01c4124468aa945c3c02036104074040d41652059504012800401a5a41214a01450410b08020b004451080460703044400c08114910014452608075050002160101c070000c0c161000028000300190001d1500403012429203c03607580305003249801c050140550000a1030501c00290213050000c54891224001001d00c0d00c1d628905140d01d180d64401e42080d05440c440e070410000b003044600500b102c1c0c8418004e0041c443c5003040555681e00400384401c0450440e45000c902941ca859014001404450001482621003208403a014215003c6072900074400d46d103502c10400e00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 531021501 1250 531020251 531020291
    0x30d1d0114040306111306110d0315170709110c01050708282a0212040e04020d0609050102130e06090c043c05090c0304050319051e0d 59
    0x1c52001128102821030b12040002d2900070241c0351004010400c401d01004420320f60303c0101000c0d511480c024120345d08007030510a1004101c801d03d4180003409402086104208090744d024008101849841e00b070518501512640910308203444e103641c1210801d10f980081202d501008003c6c40540c4820104540421040758001e0114230542075a00014011466241280342d803450301081c141403000b00400d8046404208420100302c011072a001544c05000100000c68407214142c02e091900b062a450351500030002031150101005010409c0000c0d4040f0300425040802192501440c01280350445424055012241440382c0041c18502e42018007030321038190b5101c2ca9041c6032502d085000340442c2c80020501980b9028985105881c007240310681070900d600d010011140382c002442240b44001d80f00d13405a001c10020400880d50000c02c403040402c80e14001c411146541d40304940c980500008100010000101e41c682111454040d0000f004070500410a4030001b248a604100f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 531022751 1250 531021501 531021527
    0x91a0306100c1a1816060e0a0308090d1b0e1803090d0b0903070b09030d0501050a030c060f050d0e07060f0c20031507090603140103050a1b05030d1d01 66
    0x1a600700304010212003000c10355508028844e12030a2800400031046080c46401241c080c101012880104059a440701074100580c0054030f90b00d05c0107095440300c4a1910441c900780d4021204454403008015168203101146016040d035491901d44404a240d04810165034040c42d800c00320541d004941c001004a40704080000d0542c43c1c000401c1e030700c2483d010740040c00c0e00703291f0100b0f020400c0406c2c1d9404102d8841c01807100596650391480c80c2d0381080300c0301a048075001c4e8206e00c20034000030f0012481401030304c1c0e90342000000b00c018020f0803105442070200344d020040c00d0145030500c1640004901040d070b01242c87e4910b00c0400c80c0700c01c6802d0820510003815034203086403a0310400d824a075030001c414002034142d641580b03440c0d04020100030709a07032080020380c00460401580c1d52510904145414000c1005115403540e1185983c82481e07031409002401c030010f10440c0320071800b01103401040054243c0d800034032110000b0700071543d0b5400d038401503c0c032440c201c221503202d420000004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 531024001 1250 531022751 531022763
    0x64608010b071b120305070204050f010821130e0912090f01030b0612070809070f14060918011e050604030206030117010e011a01020f070b04060f091a0306100c 70
    0x1200d42c444100c110b141d0303c112104407650950108080600503403090206000741c551a66800c11f61060004880006120040f000104401400128000300300c42c0300c141070b0082c00452074500c22045403494821340c50091440c8900c190f0025504117590b00c840d202c1c0029000740c40c0c1d40c1ea41008604120710030010190341c0400300f01121801d035030003a40204080e8501600031400d0004115078000720000603105403000c655600104108010104000e0000c0d2014070304600f02c03140350160b807802855032540c500d440b615001c503140710941c8400702000300e160b114244082995940c0d4076001103411216424204003a025100465217003401001c0b81c0840b64040c1585107183e05e00032160480018404601229541795004801e84000900a510b0b40e201039044080c0c02c1c107811070002e481d00c01c0d0302c483d00300c0701d411840007000780075000c505a07001c44000f400c00300402c44030104100c030310041542020848901003210310019403c0400510300c1024191001c40e4144145407044c0c49a0400080007401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 531025251 1250 531024001 531024007
    0x1207031d0409050c060c01060905100e18060703330503070503031c05130b0a0209040b0409050a03080613021206030c0604080a1e02030d030c0315060e064608010b 71
    0x1540c18205e0050041e804c010000241140e1602e490f18282e42c8140c403040e01c1d07010500c40500044030038a0b407a9420190145c3c0440040340316841060721541e00410039018140c0c2c0321030070b603108080310110014407038204041d018010180b26030380312108402d000d01c50003032050f608041018140041140e0541410421b03046204080a286102525005014280505107010224005142010001d0040c1000800961a02d8401e0180000c580b100401d1610640c10001c0c0400410804590030442d05c0d09480c00d881155102c8022881e525510800c0c640840d01c001030301d0108100d40080d1a009801c11001d42d048440000d007080b2460280380159072803600001c84032800078025599030300c0c4d1068501d00044450520303070006030a000900c141100440d0b1100101001e41d0303498441e40c100e4081480700c2d44a130a0500780c000302990420954580174500004a4421451240c540045282221481d2000da00f040141d0b00c0b81d001124102802c154001c045080c2c0110301501015060756a15280e0b541 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 531026501 1250 531025251 531025273
    0xd09030b010312030b0a030308160e0d0609170a020105060a0503010e0303070516121710080a1103010906090f060509010c050708090409021018050303040302030d0f021207031d040905 80
    0xf4500420076001e074145560f440c0013101a48588070000025402621440480c1c41d01d81c0700d51940c2207102942c0d0040081c228000c0c407032035440c10f29a4240b6034102000140142c014038041c14400020031004009800c08540c401005074150042803007520700381e0f58104e0b01d907034803400c0c18281e4010402481c40d13900203100040d941480343c00584110080c011201511204a4941d07000320804c408620b0000b543c4d03082d0500410318410040790300108032500400f007c034030b0240310710748403021507400408042184804454941e825045442d9960f0450740400031403090385005501d860043c0c9003112001e00301400a8030410043c86001c00c0158a500c07490300d0200281e5480195900400c22103034001c0d0303942d4a141c00342c0c81d50100b0001000c040d444e46c2c6600034181d40e40021400d05075010782c0c42a8030421041c00103031800710700320a000e0403034102a038441e02504816424507901840100002a011803200c0505030301c540101c03010b0000f140104000710000050005480d201400580b03980d0005210356 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 531027751 1250 531026501 531026513
    0x12020a081317040e0108011b050313080706110a0206070f09171615140c030a140408060901090c060e0f100908030d02130e3606180d09030b0103 63
    0x407a03030a215401c0c0c1d60360040c112102c2503403600241c00840f008a504001885007800c244a01100d44455402046000e0640703039000700180b00081c401d14040300348401d40410030050a0680b8003603940007000b481198415040c1803090f400c0b03007400c04014031800740403071010380c0075150382d5100b2002135841c9024241040f03849440039550622210240c8036449040c43c080450f800144003034400c280e80c41c1454a00351030000c281c20341602001c180d15208102240741c0c000000f00300ca5100840e814420254120b441660400340115805501140a903808002c41883c040d485146c1c40f51140001140080e00d940c003c465900b215078480b07401a202c0e42004541d4501050f612007410361a2404446640e10f03096079070304680040c04404080d507000f01e40c01801501400400002d01a43d54143c00c5a00e00094403540b0046400d20f49110300100020210ba069215410366056940f024200e80742420001e17580030220341410800300342c41c010b20f4a0b16084521403030119040720b0b00b01e00a05500d9086841310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 531029001 1250 531027751 531027781
    0x2003060d080d0e0d0e0303181306050907020102040306051605071704120f0c080f03030c0702040609060627080c0609030f0607170619030609030e040e030a12020a08 72
    0x980d901070050001c0c15a0741c9403400340c41e03041c0320f1010240c200715880c88000382c4200d8060a48074440c1d003080c0030754068030500010300014550700329a4103c241105819000081c681d980145420003416820403404540540042003101d00c2746030f007044581c0d203110503c21318101d4481020300140042001c3c801003000d01a140c0c3d41107070324042940c40d003581c603513501555828031300040303422404a205e04010300c428040040014400e00b4054201c04914256094032403000a080114140c0c002c110002503440326031141001c3c108420080209a0306c0b500f0103403118425000044503155901d00000308104030b12400c0b000c07165404010004042840104a01504003246c10740e0144104c07208122900410018503014203099212080f0800100d45001c020840042007a401b5100050440350000c420010b080101e030740010000039200070510301101c03c0d0340c000b00d001c1e500605100e1280030084e40880108000c450755140d801004070000241c10503805010030900204a00c24001151600d0200c51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 531030251 1250 531029001 531029003
    0xf160804080307090e150102060a020711012d080411100210020d140f0402100306030302070b07060b0d03120b0301050c0f1605061303030c020a0b0415020c03040b0c012003060d 77
    0x2203004d001e9122201d01c0c14821086444c00074074009010303071411030358041c4410703074228401c0c0c5003d6140c01c0701da0b294404a459403d0b0814104107a400c1e07401341108050b0710440750b0040300c40b00c46072031080801000300b1000007520305940041603803424042c00c0c81e04000e0400e2618841d0042c0c64030300c4089503107800941100d900c1704003068030f0b00e20001500d10b0140d50548100008000801f403401c103401404030204c80d0340307581010300d0300c0d2113814000b0070340000d0042c3c00c17200b000e90426510101071078104003405500700001d400c0960112a0010544c1201c02440064038409080080080e1601054207959080c0d4440d4041101006440300900050f4024440741c000507004240c000d1441e036455142040464001040604801241c405c060b0b01d4041c944c1884038500c010142c0c092070362034800b204400644000e01e024148120070300c44900076019140c55035000c03001e6070b03101c950303480071020f9503401408a9040c035484e10800507050ba1203000c01c0c108400030301c5692030035942d4800520002d8400150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 531031501 1250 531030251 531030257
    0x818070b03150307090609110f0d09030e180610030218211f150e071d06040303031e020403122303090d1709030d0504020d020901030b0f160804080307 66
    0xd402c203003a10f0811085008000c94407002400e00c2c5030101e08001c5035001e66400c90014070401543c4c42e0540341d1000c0d40c42c400403950001444581900d07003540c200702980f0007142c001e55404003401102c007011030075500c01c01d000e0320514500c100d1010308800b20700c542001a1100445600030f000386040c40707200d0791881e160340036004812114428041745040a002c08285041014005000489806020b003440d038580e80f01901c04841d0410507111454800241170310200080e0400c0b603032600c01e000c030740001d140002a0401c1d50351354032400c005000d055034043c480010803180380f00401c41034a45c402c980480b0b4214105101280e8025070850f1000c000001140d224604052000c40c06400a4011400380c5890780c0249401030102d04040d00c0840112444c0c001203a140c404c102030302c123001c0111064405d0090340007a407640c42d440001c0d505080003030040d4100c083c100007c010006c0740d6085a01840c104500d86c425a40c43c050cc50035a41c00e5480c000d00007804840100f00014000e402441d044010b40c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 531032751 1250 531031501 531031531
    0xe100507060f020c0708150c0703081b0307020a02190b03040f080f040f1404060e0a0207031416020a14060f03070507051209191203050901050c0f0d0818070b03 70
    0x10403140c003680c124500c0b1380f400d41c1144001700000c5100300108955601d00c01283d0555241061058015000e44440542400707410b5001a64041c0c0107805c101d507800320706104646038102140c0c002d41d6588240b2007280a00e890440080e07119600cdc21080d4211101505071500c0c0d5900c40e5070340c10300c4490008084580060910510456180c824042c0c00900300b482007400724075141c41076504076141201360042c041c038038010b8280003001a000f02d8a40c0001c1914000d030b40c400d1030b0314085600c2607615a10110040300890304a51180004441e03031940c074000c940c03656002c1c1c1c0f00e50041010001c0e00d401e641c0d0100c01001107a000c000920080cad6808185810601d00301b00164880c01c1c00c0065003014403680800c009503010396407414a40c0c0d89000f20741a10702c001000d080c803d0039079a484a8110107414040c010440311050707803060049035484809601541c540882d103401c0141e0303e40c001c8060b600822210b80008440c800300328544040031082000500441d4900150041c6692014010314845c40000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 531034001 1250 531032751 531032771
    0x1009030501060816090b01020d030b010e06070c081c0e090406090f0f200a050402090a21021311160c0801060803190e01050a140409060305060411010e10050706 70
    0xa21900c4018040b1101605156100b0104803980d1364854004030085482c103034613503095036400141441e00103034900f03000070301000100040c1c0700c100140010503400301d00011400c0420510350851000c60724000704450b441c1842c59003510400ca0700000410010344040003a218614142c0502500540100c90000b1500f001c0c5e1100ba003408007509007580d6482c600d480d083c081201100000a05100071405e0201101d54800004d114090390303c900c5220f00d40104410916a8911703801c1d00c01880b007060b46049004d481000b0084a0b82c00c0c8600342d03c564040c0080000340d0140780910031441c2a80111140381041c1c0f0418045140e21084042e10001000380010036801801d10529001d03014040007562911708004d0b10540c084d18901c90102040344001202f082c0785d0308002500c0801c2490b00705a140c140d941c24010714035004552281e205241412000001d0244c00700e03030140218033034180c04803107080703500040d2810320b04001c000d6006007807080020080d07407045000e0549a07229140c042150385803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 531035251 1250 531034001 531034003
    0x8032a012f04180203040c0503070501140c010b040e0a031101091a07020a050f0a0209010f12300f030c081611030d050906010509130b0c0c0f06010603060f1202030c10090305 76
    0xd0102d5458500e900105100a010520f42e80c80c00422341200148515801c00000a000540d0940c00f105194404503502c212042e0039080600030a00141c410840b0f401100d90140c1d68508005090b000314403601070400e100e05042c0151000b41d50000d0a9001e0304034020401d411801c8020070450840c000d00070030800003181880343c5c607014140400100007c2d102c50041010902e0180d1140c080110484000c200c10f2080003000140079170003216104200c200120048a500c0c2e501203030007040b020725000f07040c41d43d401c546520000013040e82c00b080381003003002c000da821580554044120f2030404800c43c00c5280b00d4444201001d2811023640d081800f80a034160a941059a038114a60081d0005011900740a59100da000704412040b001103006603c0700040102c01600c024070842e030000d1003140c000c008109044070f0703c0a1030101c0f00300b907a41e0307a0028001c2840340030305281d82511910000e140f03205004405492134004001d0300c500e5100c0c0080020403000c0ea0048414010021000004190 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 531036501 1250 531035251 531035279
    0x10f0203070c0e100603020301030b180a080a1e18180b041b020c0d1a04081b0c131e02071a01270225080408032a012f04 53
    0xd0722900011682007003900c0c0035404e00706400c104201441407004101140760303080000d42000791002c40d11183c94841c4480d41c100800043c01030002c5c24001390b1400303900d0313000802c00ca0b01c000d81c00111040d140441c001b113070312901126690713003414016502406a1000145503010306c01c500c0700000744000582c00810141d17980644400380303e44401e910301c1e48098040c17005078542c0404548108a07604c2c50755400a85030100c2c4c1008228203025400142040b940c0030494a003006a00100d800c101007010b90f090f0349014185082e40a414a0002802d99400030b00442080b0207644440c102c03005240d8414500940100c0e1050384c0400c07969034040e840107481003c00e40a414a015060450b88c0202050302000d50032504803100e0030710401c826080050f11100115000c0141294407009a546050040b81c1d80140c1e049588580000980c039880500038041c4002d0b8815041d4494285600403c241401c03a87c00c1d1114101c2032001d9140c1c001c8010064000d800f0540c5401e0701a810703d6118480002410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 531037751 1250 531036501 531036509
    0x2041701060302090906010e010b030a020d050a0b1e0a03060b030a060e060106020d08060f1c02030106060c03090f08030301120c0308030106080a0e121923090114041202010f0203070c 80
    0xa59141002e00c154242191002d52182e0b0710b400400b0994542800d28802590501c10310300350300c3e408804070348281d1040e0103c6080fa45242c900380498101000d206000740780c44800203216584d140e4142e244d404901c080040c24060040401417146e2031038545002508154110729858095180d00300c2c0081d01912a0340402e01005009003c10742c14110040e00d099018102182072081d018200040e40d602c010039950310b035200f503445d00404020a5240f650300621640000e505508000011411503808a02200c119010b96250b00110f651182c400124140034003400e28503810800050007c484001c043d01855485082d9801105680f41c031040c8050b002a00200c000580031000c3c048a0f150302d028000d01c40e01614094145043c894218024a01c222800c0310b00c9000088010a40c3e0f078011010840042d0311002031200d61580c05610210a03444200301c14040fa85100d018001d0000141c1590161400c2c02058121071441d03400542d40d105e04401101c045201c108248170000387c020f01280010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 531039001 1250 531037751 531037753
    0xb01020c1005030412030603172109010b1c0b01030f021207141e0d061d030f03010509070804030e010513080d080702190c0e0c04051c060b010c2103020417 68
    0xd044c240381c03030304500025600320410541006010310201e0060915091010035003146c41d40d540a41103014074908920491090b004072440e020800c031007206401c451540c04040340c080d10b2407961400e00100e5031002d500b001e407007190f0319001032000800b1076a0569560780002e12a03c0914840b041e0300d40b405890b41c000d184064501e0070459120700b010000d00c1c9081d181030340d48040d040541000701e0664030a507032020340b4048e01d8800844090008403002a084d01c0190252130762000125440c28040d48207105040c0120803190014100074441e00c005070045a15070780d40007403141e0364001154550080e2454030700d080c98055000440e070b04100441c080d032400e90740ba140d0081ca0078820103814140c400d0015542e01d026035040f80300150752080c1c20000c1e24415000304101e81c44608000800703005a030070098100040716000816030140040c00144030f845400e06202d000b40190046804c21003008004012a50000a050102d40d0010100c10700d40c0071481d0060510383c2d18000044100309529880d102c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 531040251 1250 531039001 531039007
    0x8070210051908090607030f060503011a0f01030b03060c0a142d03070203161505090703060609090c150c06230f060105190e09240d030e01030b01020c1005 68
    0x10503403180c508801440d601e0914660302c4ca00300319010f13240c18004180e5020146d88001c2080410b601d0391000e40a4100900204484c031200214003c0d0200c1c601c540702c0c0308034101942d0060703562083c000c030380c0c000300003401070030080d01d0381074494805402c5504043d06200c0e100b0921070482c1130920181c04c1015170040064401c403200d05959842c503111a21076484040d003042081070710354001044606441c400d80e81c1812030941402c1c040170340708200000b90300700c500700803e01881800c00113040d400d6a00455007045a69551010041103524111006085000140c1d04114200c00b800300c8900c01140e41c18282c107039502c190b8807170041f030342070740248160200381500c0030115410000702c07107038400034581e10000c06d800c08400107091070003120390540341301c9a00208950103502c100301d602c4001d0f8010349401e56a0030444030005101c6005000101e42000005110031103140c1190903079020350701a00c444100842e0b60b07004601510050343d107181588501c0c0030940300ea454050148048622036686c40351 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 531041501 1250 531040251 531040267
    0x5031e030f091204211b1e1401050706020d320402030c090702030c0f06162f121204121103030105090a060902160c0501030603030512040807021005 65
    0xc84810060700c0440701e07a00051072614150344101c12242a503074140940d0f02d044081144140e17020380141c2c001429000b50440c6600850680e001d4001078515045084410b03851f41450949800040d11031416148000c215440c00d80d40603c00801c909806014098608014214010192001e20800c041c640d1700d000300c1000c526000300ca4102000e1218007020219050980009a030341c161070262603c02c0580f07501040e108c500030000c403646501060207945018152060b401c0e1259011100242c1d84401d55140000b1103100e221006034012000c104c05d03ca00b034407803401d12910320f50983c41410300d109a0b03248901a0351f000e0041c18590a420140c0d043c0ba140a1074641880041014074005110110070410f603560004410760341929400c0c0c4035906d041e660400044058041c2d94020002c02d440052140d1049490ba420700c01024054458070061a58980c011000c80b03400e44005400540c0a104052100d00168081034109016000c02803d00c0816000106d2814610513a0b2012840000b0815 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 531042751 1250 531041501 531041521
    0xc030c07140607170c01090c060906020c0a15080712020d06050a0509100b07030309020901031b0b0412060207050a08040b130f0608040201050903070e01091a060403030c0f05031e03 79
    0x801e00800035200030f418852036645400c140b400142e51070010a1000c0742100d80001d0940c86140219003100c4138031295941e07008080c0041e0480d014010060103652000300321070a0101005007141c07200301800c031140e4091a0102c42080001e0841010040754900d00440f400309030000c3c000c107140e002e030005051840d20042150081640d131103e4054001c603003c01c4002c1e807083c80f8000444d1050703202c0e6030b075030b8000d032034200e0081c444840300941c8194850004001c0c000c15403000e42100300e612402c11052038507400090381501443c402e11201c3d00703089000a0014126801500400e4410000c803100b110179566968510740103034004500e4404041100122034120043c00402481e00080e178403151402c0400041003004001d01c040e05114002803185c1094030200840002080b00e2251102c0b0344d40c6407412040505003044201c407401521600c01c200500d0700740c080b20102c0758945c40b8110303002010380d5a03020302e68007030505407881e0001380880496001c504a031400b90114aa1a10740c0d039282842040f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 531044001 1250 531042751 531042779
    0x10906090b03120322050102120601030e06251101020d021c050907090b1f110d020705180c1e0a080c130905090a0204111809070914060c030c07 63
    0x1c1c038440d9100c0d20a555000248104a075000b080390100300c1014021000303941003d082081d0028141e40c0700003452410302440b44407483c040d820036a070500c400c0003040401c07036440b4419101c40c151594070040d00d804a64a03d961004a0700c0e0700e00300040d4103855040308a003240c00003180b81004680000e00c06201c0002400e85c80e141540783c400070412814072a00303960382d9005030301480d1100c590b10f8041144950b40d02009900710002c942529180c1c0412010003400f160a0185042061040c420b0001038140045204401e40d00c0203010100200c0e81c00c0c1c0017002498000c0c20041400c1020800c00241036900d00a481180038400700c126a036585950000b0803010000340380c03050550090212014008542141c0c5048034041880454243c861b41c0146003030480c02d040080d0710502d040ba042000486000c083c190701c5d028201c0754941d1908820511000031000c58452000a01404c0e0903c044400303ca00484003442c0a040d450600c10301c8915140703958400f20b02e0541c16071182c14204258800c807110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 531045251 1250 531044001 531044021
    0xa0c030b1509010e070e061b0a1b0302060702040c030213031416051309110d0323030603060a05101205100c030b0a032028120b010509060d0b01090609 66
    0xc0701215858070850911124011341044100b00034800303030000955920003235561403403900180030b15200400042a607500c1422100700e42c40350900270b8020740b25900c1d103002003c1765009440a40341607096400c1100902c042d0252906041e8244403101050205ca14803d02941c810b0342d1002d40764192500884c0751600d02252400313030f006206000c1c481c0d80c41e00000082c8800700307204040b40c04400c0340b4041186400f51550150084d103405c0c803c0060503448031411000d030072041400740e416503411001c1c3c901d5210032208030390140d000c03001040503000d4076030003154019070039000da81d221600d03411008039125510f0003d844039404030710705803080707540fa01c08d81d002c8403143e04007080b103d0400c0011404003082c3d41f0004d40044a4540180e0b2645000d64003c6a00d480080c42c5e251015010340b90180740c02201041d86400070885400402d803503000320851600c0c43d81107854005d441e0b217880200b0502c50401007246400c421002c242100080d4001703101e5010385032840b00403448505040b2514111030803110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 531046501 1250 531045251 531045259
    0xc06060306012304090506090a06140f040f060b0604170105090c130c11030a02030a0f0f0c12030902040c030f0b09010e070f0c0c08150109200306030a0c030b15 70
    0x401688441c0040c001c0700180000d05440c0c00c0402c03d00050007480c0c4410050801d0054100300090740b080811074003c039500c184000c0103107140c0d5807010b800701c82040318580c800354411004100887c4011442c202c0306031181e100800d1074a5440c000c2181c1c2c0d00035501c60303010045031040050540c0c40a0140300e6010030703140000e1480150050000c1c540b81c2c0200e0003804400d50b160840341c0c0b040e2042422015048810040325510084510001d503030b0752022640e071002900e050040c10350148101c0c41c5002001c09992012000310b01520744405004203520b822082c5641c0305130101c01030301c039805104d1070140141c5000130440030210614cc00d50314620a8035115804110050211420400f8460780000f0a450050a50280004140c1d0030b030400e0754010b80716602c01d84000800c1c0340d00103002010b10341c01001805031a640d511103041038030720032061902c0d603003400000c0303010400414000d1640b004005040b40c440b019641c0711300143c5201e135002621020241c00403ca25400c40740c51010114a0a903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 531047751 1250 531046501 531046513
    0xb070605150d111011150a14070e060f0c0118020a0602010c02120309011d0706030b01110c010c05070918050105060306040c0911091e1002030f070305030406110406050c060603 77
    0x90b44000d64044061251407150035250044100c0c4ca00c5214483e100c0341e8044211694440043c1550071045000c5914030300d0a81040c001e400b408046e00354550085029880e5010050208000c2000f150801c840441c0003c40c140140c9070100f00034064107071801000b5401c4410034885005000c0c074026250001c000356070400480017211640011151990f8854580c00c54494481c45215400b6065032001408a5410380b60380c5074503a000403030000f0072500140c404001e00e1200c000151192001c4950350740d8182c1011003403a80c40d500030358104e50b003188100b040d2040c15860344802421207085028400305149604075200c1044001d11070140c21010840040545242903176451501d00350600901d070110362a0360a40041c5045042500e01050000301201800812010900c900c085080000c5d0310440401e003074a201c9900100032100d6940886261358a0071100340c500796550341c0050022690f440d81c1c1c8240c01e0811390898041e0020707240c00c0e0b850950301d662040d512454042c010f05500c1c4240c11078 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 531049001 1250 531047751 531047753
    0x9020c011506170c040512030325080103061509150306180206070222140702150603120c0f120c0610080c10021903030b10110607180b070605150d 64
    0x10411105502c01806201c3e180b658500c40c01500c0c5010310740c0b00542001c42001580c044500100103503108941aa6040c4e4882050140e402d0401000c2001080483d122200500108440d5000144a43e60543c50b4409142d0707034a00f04000c941e00c03004001003000850341c042c03041141c1409120f0020482d03154802403180c0a4001511901c19420300a01c104000e4510682450186461030314078030354264100514001c000d40e4170400103048031907000501400c0061407070603100c072606a0040074003400030624030802c11501900c551280503000d00d284500ea0748000e070007104001d03120614107051096500c0b10b0002100c540382003c042d02541c1d901c42040c8050006580025070004001c0e0704403a019001154444103905181d05186e401c0300601654035001c8c1415019000404140070a964003460340f82d0304a0101ea0040603070040000a801020207d4102445aa4002001010b52002c2c104050381d80b1505001c580c0240401c982494403441000b1215014105d4680080000e941c0740b07070301c9651 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 531050251 1250 531049001 531049007
    0x18030301050307120302070305060423031204080a031e0c08012112030b090a0c0207120519050c13140601050703020a20040c0801050f0a2102030a06020409020c011506 73
    0x12a0140c4d070044107482c000340003450b2007000b4010096401c2000e0303685508190404409410340402d1502c0c10518413050f4404070f1400000b00c0c2c1c00803c802d6160911a252660381c01240e80c03001080c1001c050301c400e0b007242e0144110030400c49015521000095002910b4409042200705030312090304207601e1260410b02400c6032000700400c0da03201141101c1003887c0c0d001030b001064a900400e0b0002c032801304010100e18298001446a0060b40840c0c0c11107580d80034000700b4080581c8020400c0d000008803002c1c0000b00c08914020500c02c005603140c00858070003080302d01480b55640c400e043d440d010307660402c04e084004d240d0480390a1a040b46807100c00c0c0c60103591281034010081c0100c14850341c01d56956a0540d5000b02200300070814001d03521040e200410b229402e02945214110050010f901468440100002c03200c110b43c10105110102c820301c07c0c0c20310b40c40701c1030341c25010390080c000c0050540d03c0100003030800c0040050710f07002801080e40c00c40b280d040c40c00885180c0c9ea40103000c0650 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 531051501 1250 531050251 531050263
    0x6030509210a0c15020c0a031e1b021507081b0d090b160204110c101802010503090c0d0b0412090e0c0708090a0b0403210503060405060102011404030503180303010503 73
    0x200d2424410b0303900300e403440e10200c5a410448944d4030030744041a0104540800b00d09105a00e010340ea81201440c800b061051100302007075900b4000c140484800100d45100210110341c0b140010003070300c1c0e02d040005036220140c4c4050340444084c0310000b2120f4800c1401a003130f180710819a0020560781100c0540035106049238080c0b480484000304e452894440b62100000200707901030300520201ca04403c4003081c540042d143d040881c0070329818650001000e11840410b0a842d802d140d80303404680c0c00555a90b8000761030030882d402159a51101a01c9800011301642e11540202c0031518050500b011029110300350002003040c801010040c6007441c6c1c01c00c9801103540c000843d51600e083c42e10001c50310a0201151f00a074015a00141c52701580c40503001316401803482003444600c0c5214103520b8504540420007050062001c240070381015030004e544044c040c00005486280450709170141d10b02100c0c224000745000040101207490011440d2081da9060000c5065506290001c0e485003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 531052751 1250 531051501 531051517
    0x3130308030415110a0e0f030d080106090b0705031e0d1505120307050c041e060308090f010c0c0306050604020c0307240b01090b03040503120a050109060506090102100e0c0a0603050921 81
    0x100f200301081d98070780e6071809007c240500040031241e80078080140500000c10034814079001c1a000340001a41212007400c651155a0100266241c041009064000342a080424241000c0b09000350b4020070600e03c191200c178140036504e03009691500c3d04002a00c903100c0031407402da410a00000d8001540080c0850040c4000c890225500c010002e04801c03029034034103d0a02c090811000105105078040240080601500c1040900860a0065488912004000300b04020611080011403510350105400440040001d8070f0f0005062000303186400c100000da908401c0d100021140c61018100140c034510140c00030700401c001040040c101041c248644844d28400200040400800748100c92668500d1820b150b00c90800603c202c009000902820f05c103149040004681c03441d005050325241c8005074010214010401d000c03501800d6a640b1103206846107141080b920b0707607070503d00406017803603580020f00f614140090070700e00b805401022109814800e44c61049480540c211200c0c0c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 531054001 1250 531052751 531052757
    0x1106191e1b0c0f022110050609060a030f14030712050a03270b040f0b07020f0606060310051002010906020d1a06091f02030c0105040305041d1005040b010203130308030415110a 77
    0x58840b01c000300d45c000103d01911841e010341a0020080b4071250b1199000d070300141c80ea1079140d5640e030180144210030b800081c0c81c4000d0002d0315000102080320611401100d10207481c1802415a42d02c0122031581a56801003040414112459503042c480e00606152080760704902814116815100e030f0b400800c0a403c2d039034060300180501c1211382c0c0e41c100d600c1d4005c00c0480503180c0810020340343d140c1b00c5003110303660160300040f54141c50300c1d00503240200380400807440d50307078503200402c44001c4c024444a0255500d880070070020440d03501c06810080701040d80814080760044613900c000140c00c80741482904c061000301c0c5103485405c00d40614519001d10900710705c04424007a4614066224008080c1d82460b0802c400c05a11101510072100d20980541078032a042082c0c00d00c1c11811605c00c04416181c0d40b040115182c01d402c11a02c451040c0181c03450440081107002400e01ca542040e145404004103200c2046810410280200e0b4401c0080002e042007603004a118410409c0200030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 531055251 1250 531054001 531054019
    0x50d09020609060c301b0c090a0209010f03060e0406020306120607021b030a0201080c0d14161803050c130b1c030f1106191e1b0c0f02 59
    0x1151034a404503400c4450041c0321988550542c400d450351244214a565012000d11220a1458013110049a03600034007101d241d0500412520301d10f8406c24031002d5050703520400c902c03034659444103485503000e00c1c2050000340c0c0d2010340170000341442c103100c20000105417a12104000b686a40804030381c1160703100d8005603694503141c000030ba603200c0040261245020726014405440e0b000100e020a02c03801007003040c02480b26400f059120494600064041801a0001200400403e0040042c051940d030000344020307040b0440c1242210031100100500001c040d9103100b190022448481e21410f01000078100d0300b165203e40d12854030b41100d030f00401c407503e05018200305235008004c100501400d511010a450600480400c9042d0010340102e404008104e402511621a80c042e21107401c0090800341c07a07944851004412401842c0e00c8580e8440039034203072404501300400d00d00030720800070800c8001c514850502807504041e440c140310f00b19280c0303400101980b06044c030042e0115440300d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 531056501 1250 531055251 531055253
    0x609050d05070b03130813050108060d020f0f12240a020c070608090312070f0809210715110406080903090939070c0801051e0403090305161e0303050d09 67
    0xb5106000d031760040068030003180b24066051920940d500312842680c1d1001d142d20f5030002d1000780310b00a0ac0103900503680760351007100c0c0c0c1000060300050207006450b14101c00a10000e850400a44c1100411141c072120548004080c0c0354606a400107903000e0f04600e8650102c500c213550780e9282c81a1002d011551000402581091054030004200d4610658052916803330080040d070000c203089001c50400f0002c00d4001c6d0307001035680c1013200020924400588083e041c11042d81241100311340240414001c1c5a19504500030140300f403a039181b800342c6407810000d0140031100000c00310304a680c0203012001c02c82e600c4400b52a00b1140d100d04090034842882908024034030381d840c2c0120041c950200c11318000911200400d246405449a0b81070241c8900328182611815590b8001c105005c0a8030510405410b8031039800911905002c52820b03a40d0b950141030440002d410780902100c0d240400100181c11801030b000140d9010881029045030350141940c05030003042440030360f8030241e501c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 531057751 1250 531056501 531056521
    0xf0607140d02130e100b09010c0606081501030506070206160806040e060709050f040203060a06081003151401080d0804030f0509041107060b0306071202090121060609050d05070b03 79
    0x18080c04081c040035903640340744003442510011148108801e4030700b00c500146000240c69030000540c3c0790707102c4040c5000034400045880640c40c1d24152003080d59030800240b542c1c4200846441580201c244182c20340c91400d000741402030091a410640d04902c00b001515101918080300000b17007820003100381d0703d4440101e00104000d000e200054440c080600040b250004840c50031a50200d414908402044040c481a800140c4020b80c11500782da10600c2920700882904d54000c3c00c4001d500c03d82641c0345c4583c1528411524401c40840d9500c0e10308c02c2100c150700545014150303c000400300d40b00b400764010000030b8000e00c05010010580d40b90310300c803846001268441d0360000e10a01c900e882c180300742d46d010341c002441250040e141200c601e04d142004140188260050384562050500402d2808007070342c0500302c1503040250500245c905102d000041d03088500301020f000400c2401c01501510821054100314400c0070501484400038400007200d03c29600c400d08040c0d200c0c0c69000701c01c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 531059001 1250 531057751 531057757
    0xb06180a050406021c14010b131a0702030d03240b1c0b040e030903100b0a1401050904090303051b03011a070515040b0f07091503090c090e01020d0b030f060714 70
    0x80d0750480385d404845001c114054000c241da0228407105903070702d03036a202c0329841c0c18424031030320802c050a050000c1003256484800c010800510140711440d208055000030300385010446540f003c240c3d95102180107503128000c19042c0005a00225a134500b85101d408003802141da00b40d00086605010804103010f5800c082d0145000ac1d00612100e000b0240491712500110300840c0a0300c01c1045040c41c140d580e010390a10500050524502c081c10003240d004200c829140181c14070804201108594440d40304114146000396400116402c06010031042c4201511450960f0001400103201c0da46030344d06802492800070106503030700c154615102c2c0c00c241c403584040d07980004000c1044148140003031003a104140d100710185071559030329410744204066004021040050302414010a800303075000c41503d81c004c21040586070340d18500c0d0303003c1d0750490a807100300d039401080e1054400710b5409505a0583c003100030b8902914201c02c1e255850000601407c2005111160f01d44115007120407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 531060251 1250 531059001 531059017
    0x5090d0e090612030a03020a0e100e12010e030a0302040914060907180f120c1706010314160b040503010c080c030a0b060d1812050705070308090111190b06180a05040602 74
    0x2600e1700c0350f446400c003400a41000b02000d0204110081d017854600d440301b14041404019207a003408100401d05020000034a8080405103640c1c4a40750340d4410350400141400d01d00341d6501598841c1091703824015100d06400c034888010600d0f05100301a0390f0342c030304070390700140514044144600138012204060242d511464003684903d002140c0000c40140c1c149440e80605a182c0f6601e0341d03200240c07030003141e032002c16109030040030042c000101c50241c0d040b04d11030240100c641c01031808000c0101c9000607441119076140000d0100100d04081c004c5404195050038483d51501d0400140e9181c6d220040410300c040e0780c7d07504180410343d103402c20795026000780c42c1d040180b007040c5890044140d0742c040c03069904070803d00220b82900c0c4a0411541f03103c1d0300c4070243c01c1c0d451a5645032307a0140c000000305814400f0410b0084600401004001c1007006040300c00f408481c8542007200a01c0f201506050041141ca0494102d40242000c403d070415044400025596150b00300303c4028094900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 531061501 1250 531060251 531060253
    0x150f11060718030c1d060603100b090414070807080c0412120302040b1b070b0702030c04050702071502010912030510030312180b040c0512100509030408010c050a0305090d0e090612 79
    0x14000c902c25111103881c900120326407817150101d8407a20208445400100d9003080220b44100080c095030100c44050860160040c00c00302e41c15500c44001d030311142c4200d5004001a50386070070010f40ca0360251302640c01c60360b14090945070904010305200c11031807030301c2c0c045c2c6950322100040ca00d4510a5040760300806110403a25112400030703002000e038442c0d44d00c0f5401c40c2d100b00b9801107400c2ca4500110b0354a00d9004005204884190040c0400b41c6001820107056000310a00003c0c00d5507142055000013159a0000400c4075040c500783c40500c480007060010940b5001c10440840008448002500d4050400c0740c041d090407000e100c05030036894070601c8404400c40141007002000307914039000d00c0c424180d0700106034458090010304400c001c0e415005a00c429481651141c0703d500c00c0d500003011000b41c07450617403680c440e0303820342d604048604001a07000405401b0343c0d505104107034000251001a042c40c801c441d100800c070005042c9464412540b040c0800c006d030369088900c01000d44124 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 531062751 1250 531061501 531061523
    0xe010f091e031e050f0c0607020913080d020903011521110402040f090c020a03090b070f050d020a03090b03010e0a1e0e01020c07050103060305150718150f1106071803 73
    0x50480032000f42a0302c0704032414802e4848006205c04003003282d0101d00d10107015182046c0e4035408004e406040038014034036001085100d0404a18240300400860314486000340e0750b207660006250844d100404144117482c00c440c420312280d644207804040d1425040022a44601c45050110186810074003681d03005100080000320021510040d000315001010200801582c1c528240d8071802003020003000203005030350a0085810002c090420a03015403106000c468090341c45a1801401125400140c1c2c44200c3d07120805034800b001350b024080c0c4604490840d49828400310b00c0d010060121507030961906d80b45007608031500340341c1d0780c0411b2601041c0050f8414111460007940a42c62005107800b070707581c1c0480e02e94000d004682c1103036840b0000f041e195200d00002d0f0151ba401038103110401494032440038003145210803400180c4001031001900544900e009000404545e0408092003022001080b015a000c500990b00c02d4090034a05480503000840c0790a58160740c0005006960704 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 531064001 1250 531062751 531062783
    0x103020a05220914131403120c030a0501050d0302060601030914031614011107020405060409080d0506010f03050c0d0b03100e010f05090307020603070c0804090f0c0e010f091e03 78
    0x301c410408448071500b0130400f10241320380c2058019000c480140b05202a00b0401d00001e1400070801648407403041640c0c02c0490351019881a108140e503000d000a03408804d10801180e030388038003401440c0c2114040201c034101d40d8080e40b140d000030040c40c117060355020900140103034998207144c00c80408064030b94a2507000c8402c03100480030001501c0003030501180743c40e0804144141441c0c0401c501c049424048154208000782500516840d0480e441e0410400010000009050b00441861002c01c552407e8000140004c40c4030301c1c5202054145028800c2e08145001150550040f504010444150060100c4e18101042141211851406010401c0c1703071810b40c04400310002c001410300003030719a80802e035924011440083c4d4006030410208000e140689c00b04503071a48146d10090a082c0d8421f02102265224820564aa902c1c0c040c01245250b108140d143c55000034200b80c00b04150760000144441800e0041d1041111440003550742031800c0103e181c02564070420907540c0d2441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 531065251 1250 531064001 531064057
    0x1140c1528062d050d12030c1b080706111306200706110a020d120210090b010501050706020f041215020309060a0b01180303090f230103020a05 63
    0x4000e20701c40c1c815848002080c1c6071459801903008450003082002e4000604007078143c0541100c02103443c0f80e8681ca42c00096540343d021080d110540215421075034001805000380540c1c0e501040707881000725004040d51b000b000d07000001800e603080038246844003100e14040004000e03e280e24400504041140d290110b00c400107801503c21585d0303070b8642da40c517520384440c50f02c242c0320008095401c00e0f2400d0020724810a050201418042d04540c088035140e000314408a204100603100c102c8034103048000182c04220142030314110705000c1010100c01c1d107690011540c1070091038100040001d5410a224164040d80c4030030028801055407250390b41c501c0801001040c0d411102d14000907455a180101403003a030f8401c2e080700e0050481a80ca00c007000d4000d100360208107061241203250b8081c200040d680d400083c40c170a44501030b08508050894070000c68941c06051720031b201030000c5c05051501d1601c01c80140d003c1c200541c4030060300034144c480740964000b07000304c1d460a2081e81e0a1640d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 531066501 1250 531065251 531065281
    0x60c0711130b120703051b03150a1505030a0309090e0313090204030507060804150b0105070b071206080c0d020d022b11010f020c0d0c180509010b010306030201140c15 73
    0x2000701d5800e1150407030001003541352400c0317201c040c00341d4018106c2400560b42c802110000c5100007025280e1b4a0160500f5a141c03200c00d8a480b0b04140e0307500048128826030098070000780c101140105411001e668009100e90011301800e0461a150407500464202c04c20681d070202c502d482503e0300e100e0302c42d000c05009400c94402a107552060b14000600b0a00803886540519084905809a00030510f0b108001e0101d83c2c640a040143c104000d4000c15482980c0c940218900c0d51030408009158919100f0b440058100b16076580003298410031070b6550845454071350382d0685200c0390840c020300020300c220303106c0d80d003a54032091000a0056a4003d5840798006544641c0b00e15040200042c01103490004900224026a10031a401541d520300050846034851003444504102c41e15841401000400d649101854503200c80a0054200c0280204692000700b071030304000040ca9600002c00c02c0520201da25840345001440c20300100050142011003c143c6540740c40c20b0a00b46008080c86e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 531067751 1250 531066501 531066521
    0x3140910110601090b060f0901170c0304140309033007050322140d1716020102070801020a1407050c1e0405060d0c05061303020d030e01080c0408060c071113 69
    0x1c09114004185031134140b08000d000003019009034104426040124001d034000e00d880f90500000c480d50000c0c2041000190f0300c030786000881c142c1c0b44e0a0903d42000841070071503501400b500140100c0c82c042d240055080b00216604900545907800782c14a41120801500180d01c9000d0001c0d0350b17030074008008001c152680081006040c0c801c8070001070400800e050050307820300d411148043c4494a010540a11840d0141c1103c00200424402020065020044009504e0300701d4116000b5581c041c0300140003850100025494800403010062600e080c1e11062180b103a07000c80e82d1014490100101d002255000d0000280c0e4104c400c400ca401e007401d0040c141c820307400c0c10002032a07410708400d0141c1d01c5520454180149d41884100402c94105c084600034154522600002680c0d8000341d500e080d50203078541c2201150402d000400940c0b0003030103843d0007034081008000ca800c1c0002c026078003d141c0306459440301c41e585030540341c0300404000e03198001c140c00c40c8180300c401c413580860409 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 531069001 1250 531067751 531067753
    0x4050607020d091a030403020c0406140a09020c0d0c240615170103020616050114040b100608040b070c0515060301060609030f081b0d030c02070e130314091011 70
    0x1c2c801c0310700403507482d400784c01111031000d201010707440e07050b800b0f40c051a000303031090040e6820303000c007140860300b290001d500c60703140518248902e444070b085c00103000b0b0103032440301010341c6000c201b6110b0a55a48103980786408119880811400f84000014044850109022201040b0744602201c401602c02c50040302020342000000a0b140d0b0b000b44c15901042d0903072102e00070340d61318503000c1200c0d0380c2108010191080e860000b841c0021000c1c401c80d000400301ca04412900c0c10681024260020001c4c1ba0b00032240b4190010322040350450065a4059400110020550354900c130448408a20803002016481210322203102380c454240c42030f109201c140c0c0200030b06030b0740b8036046406d5026480050f02c5101205100c5012424640050003507503d00340c040c241c0140f00b20002c52600c00c07084078240c00280e4600c03a015100d0307070520400006004021180c0503608043c1103920043c0c186240c018244442c10f29080c044203051001d40e02600001001203094503200000980041500c014400d00d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 531070251 1250 531069001 531069013
    0x903071709131a100207080613020d140114090d083102060702060408030304110405150907020a02040c0504050a0e100b0c0a2003100606020c0607030e06030405060702 73
    0x40d294141090701c000050051007801c55180c0507007604001d0409101c4140b480f120340007402d18035141d060016860010740e07402000507e11303241c0b0329818940b0103814a007190300ca03c0481005a958060b9450981c0c4d000394006003042e038058101ca00624010354110344401c408400c020003032002041c2c9001215403910782c2d6a480c1e8a1300714031151140c3d0902445442c40001c21a01101e0b8020030020704050310203084039203040304640010b8210b82140c0c0c0203000d00e5000008120030040c4001e060704444409071010b11140c2062100d41090040c55540e05000d44064800544040c0c82080302c03030b01003034024200b000742d08850040207250ba4400d00402d0b0281034900750000d50209003d0503a0b22030207100c1f004c0c134000d600380940384681e03510214218205126901c000c00208100d51400c8105038500c51614075000c00c0901410f060090303250703881c08414640f00081281c3ea030089103106c106002211255600d181c0b80c0350a88554465400103038000201000304020010700090040c041c4669400700c0314 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 531071501 1250 531070251 531070283
    0x5010f0602061803180607020a080c010906020f0604110613030c05040e070f120c08070603020d110307080703020c0a06020d150509040f031206170a12030221070215090307 75
    0xf4410307020b02034001c0e03943d00401515034442e00188030310b640030200600c0c2e6868582c5640002da100d600580088100da004198414042d603002014074000341110b001401071511501c0b0b1490311810024005030038003184c11000c441039034680c400c444010482920b1000000c0e280d080c03612600c0b07030701d01826000c0c0b441c061442c80844400601181152903050342d11040320700b401307199013121606034400c4511102c0844042003518042c0161800351a09640068454080a000509583d0b00c1e032403010b1140410414054515441414294003085905002d60340e64140785a55180140c0d400e005400284040f85c0211442299080320500c0139000e101074060382c1c0c641041060300101994010042107080101c500002d0003a40d00c00120440504c000800030fa071a6003aa40e078500054101d02c1c1500200564002c120407080c0c0c424034042c0324038045040220401e00003080b0b40341e1200f00840c2d00d00c0000003802d020300c01c02944404840e40350354019a410f0900301150b0340e400148088900c205540ca04107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 531072751 1250 531071501 531071521
    0xc020f011a03030306060a0309080d051b0708090114041203050306040e24070302130305060f0108030a1209050a0c18060e2205120a11010b040b0d030f03020d05010f060206 75
    0x81c140024059403541d1a004100189684581072200a040d21010740d4008520010042c00c1803030440b0710302060516166604017010300715640c0c00804128244111400319510f40140e81022a00b800c0a80204102d01542e50090003143d011110302c0c1e20280160003055400805503014040035542400550303101454035468429680303200c0c6000c99101c5101e6800f100d0044440d40164880c200186040401942c2480690f0181c009403031aa02ca40300380301481185c080468010003a842c003850800a0f085001481d000b02c603180c1c120784648543c4203d050003c141704036528181d04c81803001015031303100c02e0a40309500000400303c10500e005e600103401411002a10300c924901c0310044440c5c40e003482c880c9441182907905030740d2885440b4022a04040c84402040c142c03155858103410100301846d00e600f560b110144080c0a98100303c0001c0c0d8a40b142c460140f660769140c140342c1d00000c2200070440c001d0041c03040080c0301a00300000003034818400c14046041d506903a09582e090b5031603900c82 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 531074001 1250 531072751 531072791
    0x8010207050604020618040501060504031101030b0919060b0a020a150207030504030b0c0d09080318010603050307022413090c080f0402060f0c0609011b02120301030b10090c020f01 79
    0x1d01079402140004005191150040c00040d403031021201c410820b68000c41e0888070245c000c0310200d5030009003482400055200c0030044d0f0024a0300b8003044104130301180036180e0280c14a40c1203048100c00711f440441c0c0c0d404c048098401a0503842c0c03031f0348071110000c3d034807010020150f41613007a40c14500b100170500d0084590042d0161100e6281c949150303222025100300a0a1410725803060156403500070b0b80d03020f02101c1c4c5016003111516410402c6085540d01e2222959034016850241b04000048020040d40c04094040f219024040d4035815428041d206583c4800e1900e40c0001c2c0c0e1070300c000d00304420300080d40e02d40d2208116200348403005a4420000b0b60301d201103800085c00080051811400502607032126200303150600281c85122451300906950600c02039468611018100a030b0f0800c0c810848000c1c80100342940000f420010b0b188018040a00b22101c03060000b0243c2c40b1000c0ca006c0103143e40c400800c01104048030080d256034420301c100c00c842d400c0241d40c1400c0c84405d41c034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 531075251 1250 531074001 531074003
    0x9030708180414131106040501090e07050c150a0609181202120a05071205071a060a0e07110601150f08060d0219061101090f0201080411100908060108010207 69
    0x400c500e4007540d006030580c40e40040e6212948151522049601203c15000050090300441d075002444107207072502e0344881d081030300350601405040c0410401a03074000208021a80100254281038942c0d050845541c81031409860240c4100143c0c0c902444a0944445c455030b048913040101030b0b19421908180e61080a980070246600041c050200f40111190303034900c00c03d401212842d064512290b1150303000907580101141c000300701c203801d10803c828049801001840c100d0314102165480e0791000d0034030a0001c00210f2400300003141a00c5078449400640211491004645030051006000c10300d12100009280180c1c1c000003a114100035005407082155100d1815070031804d00201c0308400010103883d4000b6610440c80c0c09030700d44c0500c004201101c020101056807c210703000e88001003008a582403a8940032074000810042035880d14074a509203441c5445440f02e00b1b29130003210f0030303011096000f1070b5070010503040d81d00322400c0d1080306da21005480c1281e90320070085080303000c0c40c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 531076501 1250 531075251 531075263
    0xf0605100509010309060c0c02010318030203030c1312140c010305060f1002070509160f02031227060a05072003040312021606050715022701030b090a090b090307 71
    0xd240880a402140a80034809040c90005420542900c030f41d0f00380c0d10601031100200b0142c1505006659150144451040d50100c0c1d40c602c184140c0e4000b0b58900c40242075154212002c03412500160307914050038028410000c0c1c804a041950030032601c0464920754402c1c05109441c00c0c5010355000f8083c2c10310824005160a8103080d441050104151291521408502400340b01250030313030b41e440b02d03640180700e00500b48041d02005080604008034202d48002590f005004026401c8520114036a0201c8030310f689801564200122030781400120b041843c1600816040050f0740f607590303201c20300c107041c1ea51310401c00c00c20380c805035010071240c158100c0e000d130801c12081c8040340304440410a000700f03500c11100f0850b0800e9050400403d640c0045000410018070a0144141200c01e00c1c00352440140c01c500e4501c4135884d0a10703900f02c0d0b032580440d0654580034240390740e000e58001007881c01301600301041c52510140d054000c010030102100c0b03c14108002c9840d02800000755100664480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 531077751 1250 531076501 531076519
    0xa050405060d021504050406030b0105090c130b090f030d0305090105100308070b1e01060206070e120a15150e01030507080a021813020d1b1401020c0103021e07080d0f0605 75
    0x1070248a400c1055070030104c00e03164104000a401d4642d80315890086000b65404030031541000c04008030400c02805025403030100b0300842040b84944c02440c42150415618690303901c0d86071001c541c400c81e180320203d600d400303007010308203200c3c2d0075030080340c403481000300204410340c0d40c5041e5021541144c040a8520301b418040c03980000c04824401d608484407034003050740a180900c40748000103098228000681010050041d807a41100c2005c000510488898a142406190700359603901045005004148100494030022440d68400c0422002e0540388800c1651101c071200c54841c07003807004031030360301c15048006140240480d4900200341d00802d0760441c1035071614280841c0c17001074a41252006401c040c200182c0c0c0d041541811329101e900b01d1a140c1000707031070310306440049510096001d401003003400c909aa021400c200004000d00300141c5810100340402e801c0207900030326101c0c0c00360006148040c0300c01d0b000a0208175214000500030400070000d50410f07102c0c2c0e4841d82d60040040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 531079001 1250 531077751 531077753
    0x7060f0c0203030409090533060607060b040509030403051015030f05070e15040c0e0109230604090605090a11070204020307050c0714011106010f0506070f05060f060a050405060d 78
    0x340c40c4000d10500050450381041e85440001c0d048683d0410112156801010202c007801803191b108145824240d4500f00100b150072414201c0200007884580305000001da80400c000030b41c3d1009a0190000d0010080d030700d82280c4542e0307285d2081c04259034601c21142250f031646428012030240100407c51124090b10350303500d1083e8000f8101003202e00f806094801328a03400741c413060303600ca2000300c68000f0034400c901d01800111841c0c0c51040c0104040103a0302d580310b0340c10150620859440341842c10103580316040d07410b840c0208850441d80002c0024000903911540e030070071025198222400382e900c1c2c4031160300c1000c80d44219019072803e00180050405803909501841d809a031506002d850b0040041c41541401c0054104801d0a070959140403088d507030020039400d240030100001c048039418518501c0104080c3c2c81640c0c41000002160800c002c804402040e409034000c007140c4030750078405100f10207100308403000ca0140717949a03030025481c078089c01031900800f0041c20180b100096 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 531080251 1250 531079001 531079007
    0x20f15090319140f09131a06090109081203040c08030a2307080712021c08131a042001050f09040906110c01090210080732040810060807060f 62
    0x9241d00441400750400c11800c02c00d5010f0018811005038040542e0349580c0d0030304000c0300d5540c0d91390824651b480c040102500342c0460b0480d00070410101c0704d4507214801d420040f900031403d0f2704203070f845000c1c118245081c40c1e14000918042d501c00c0100381d075125161440f807a524000c9a944c02e001880b0180c080b4426079030107800401c0130041c10000741c074000c0780e0707240e81b0900d0b440078900f2202c41c0c11a06c00d00d1112a41070188024039004491503800d03440d0102d10040005101401c1c1c071100e060071140b084104840e1030790024129500702d441d91041d150900b81320200d01c5c441041d2101030f091f00181c2429035031242003160401e140c55081c40e400c1c6484041848020f00c0c411808460032a51045240c000e903070b540c405840e10030700e0100045600500d0784103202460070341d610217074148000c3c0018844110740285045007041c60819243e00200880c0c11560000110303010104001500000d012a8520011500780201680d0502c10300010384c2d2540a20399500e2a03101da00c000075000086e080b0160300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 531081501 1250 531080251 531080287
    0xa09050610020d08240d11030708240901020421120206010303080a02091908010c02150130081303051c090612090b09031c0c090506070302100606020f150903 69
    0x8210691a800c8402e0400f00c6c054012020040d5401d04040300e0151032031808100714800340020401419810103902901707d0801803594141590001d12000296094025130684009042080110340d41c1000c0c24003242500c0318403802070f80e0710a40044410003446c0001303041070407a0b84c1507450b01e403250b49829204000f9008821403e41c41464a007982403c0d07200c00c50404090070a031000000c2d081c0100c000646440598a000c0e00c0042c18803004010901303000304c0344001c070f4031081501c00504c0455440500108441540103104c0031001c0740d1a88204040d5407490181c81c850000c50b400001302c0e01c101c800b40d5040e6403e010015041c06e6050040d94400c58801c0c140303103c3c24001040401d21a5108000c9003011a0080c0469002046c1d55510f0141171021300110030b4030403000c1090300a1000000d22020315400380c0da015032030000c0d80f9001c052080022003107105020b0000c20515454120081d01c170003e41b40020114410031080e0f031000400c03481e485000d600e51200451170000c400821452041c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 531082751 1250 531081501 531081541
    0x509040c2d110703020a030201261603050601080402030606040e031b010c0806180f100b070b060f060c0a0b04050109210207060c022103090a09050610020d08 69
    0x40400414080c58421a0900c0ca098081c400490034008444010081c4514160540c04603183d02140f41040945c4a04946806032034082c07030b210404907607800400854040c2e0400940700c94582c20304000c0c5078014416200050501d0755401d100a4940000448034164156406989500304101054640c0707403170750180c0315960802050360306003003180340c48061600c0000c00c2c0c1c10982e5101c0003d820f005030311070760a69100d14121221001502031405158020000602040724030346c031171000c40e00402400c0718100003840c00060042d641c21061904030200081030701c01a0182c1c8079020400104c0c0340040507500c2c3d005a400c0180707909034250b2100d4103142d501400a5444d075503a02c011902003000541d07041401c090305041c60303100045d03881000340750070b020b0790000003042501604c050050f501c0c241098011086c0401100c9405514186c40707086100b0301c81c2907613101506400010700c070000c5812162107403004a564007285154003600341d0f2200207003200c40c0d000409440014070984006005110a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 531084001 1250 531082751 531082757
    0x712050601210605030d110307060b0a050d11150903120d0b0a0e16080403080c0a0e10030606120203220501060807030b0405010c140307051b190c150509040c 69
    0x24554016042c8608031456050040003034903035a09200310306081101d913560322228a8040200e025400c14542c0302e009011000740070903180c641c45000c80c1e9610281c1ca015084c010942c00c22158113107040500511603606150095200303500f115454240d80040d520301a10103000b90200800c0a2008550707548040f140014051369124001d000e5124481140702400c0b0601c2d0010381d41c146024103208818402e5504001c1044c1e000c00c000002e50300801c40b5400c403100340807043e114551050140c0700c541841d00b4580e00a404d460081001e0313545500044122092038465a0708000c0c011029401d07032004803800301410300b1115101030f060b4517074896088200d0042000180241c3c490041c10b080581c071342d10665626116030b0510060103000e10928800d49070f0340c1810b0001500025202d07040f808000d10b00d00c1401004901c2c0324208084180c844d8204681d80c0c107407140d0084407910103c038884207860a503510722252201203050741607040c0c05050405e540c1c0f51281058180c1080001403c040b031044410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 531085251 1250 531084001 531084017
    0x120e01050f03090c01110c030705010f201e03090f09180703050703060b010305070804030e0a0315050702010c05040305070e10030f0f060b0307050f0405100b040311030d03050712050601 81
    0x54800725005035000700300940c05012030281e108001841c840a1102c1c002168000440c521136656001450f04102c840c2030070268043c8048500079610302d030400c40341e90350300c0f81c4181410301d0002c400302d03008200326450f918010b40c000d0290141c07647c900a00c40c2d940d400c5000b140109405103001005650702001c2004103030380d5a4629aa594203009540e80103d0f81544481000d00c10401030780a007816500342840c00304980d140040b070060050b2030240000c1c0c10701110040c46040343c0c503048841005550011a0f200c0d000c095284444010402160741c80015460011a410310922841c03c8a0490b60860300a100060401205c0c1c0300600002d410031308030034a0004004002881d5150304001d25000b441034016010300750401506030b96800510720b10a800c81803003448943c1e2101801d40c2c0c0381e1700076030700001c07117a0b03079010244160030954001015038540403e00008202d0701c4400080c00071410340036160b8090301004150261841a661500451840703078422000d036019a124030b40c000414948650 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 531086501 1250 531085251 531085267
    0x4050403093b1008030c010209180f060f040e49110304050d050a11031c03020702060706110406120507120e01092406150e060a11030f0301090e010504120e0105 70
    0x81781d5407002c18400d00594010921380000d2411020841c04100c0c7c90244c41c103246070464105d6003141c0c0c01440e240c803c44c50500001c02588a5030b220180b114140c1089940d00b00c01c085580c0000c0580c01054400750000010443d42040071490466503095200701d02ca0500484640907601081c94846050f002d110070b000024295580c8801c40c41640c1c018009003c0e0103541d4244081d01400c80c015941c000e40c40b10000b40d4000010440c5c440780c413545403800607211311551000541c02c3c0b02e00c04001d0320307044c1000705c41556180c2d10700051007150102e8852241c0401010f0311a0240e0368200c81100c0401c0e5082c0d840302d00600141c11503401c07003444c100009101445640c030026410740440380d90700a8090190b2001c00004c4611585d0090498844100c0d6409103111004100760b180102c3e0301d000d1070000c10307200f016901a4004800c180707914425a51a40c88842248886420034440c40304064140300c00601c00c604103110313140c01181c0010481c054001e41c0c420030380300b01d0850202a070402a040021305 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 531087751 1250 531086501 531086503
    0x11a010206041419110f0f01080601140c011a090a0c08070f030f0f05010602070803090f0607052a01080a0b031515120a060b090705030a15030204050403093b1008 71
    0x8211803082480d81c0c80c0401100c06e021346c856a6020040c0100c000c407080000f203030b8200c1405a880417023481e054101039a40c82c4445424000c07031035900a0740d03080c03214401601d0380040304850880b205554421a40c1d5400ca030074000d4604a00e50079010841d0000814549889a1240342280946040c0440c0c0842120051012540c0c0d250b0b45009069481340184419030303041c804900102207000c02141446040e8001444800d00040d1440c4102c80c00100103041107400d0201c005100380301c0f178003000d580c0d09050580501362444458240068090030000c1c203ca0458496a071100a0190007440000c034002c10b4142c68081c0642406100000b034400c819007030360303460b01942d00d46890a0182c51105204d19040c01074668000e2814480c80c00760080110f0301d07902c40103495000920b9403000c5000d071480c20701c80c0301c2d11201e5000030707400909083c10032003859001104041252003015050461070340101d20940b07008181030014502c1500c2c01030040b0130360407000046810070b42030b223810f01d0030795034500b821 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 531089001 1250 531087751 531087793
    0x7050708120a0207053a0203190201140109050a0b0a080d0f021024090b01080a0906060f0b03091c02032a0d020d110712020402070f02041a03011a0102060414 69
    0x280c0c0d40007042d40d0f4246c2c4101e042030034131100840315141d0300e074401c903c40c000394490140910b440381c40e85000b41070380742c214400d42200d10600100002c400e8256110940300f0b000d840e0849004041c281000106d1b04281800580f072001c540c2d41002409080c1e003410011a20740d84076042e800d085104900c00c1444981d481e2081c0c4e40219140c140105503512880800340190082d031344040c6400780b6000c025a81640c0090507035500c100040000984180307589040001010260064012030440000c04900d84260f000254007034072000040765020001c0d007401c004403041c0c02c0345050060b00180001118400703c1c00903802001c44500858000c41522106d4500c0c203007a0448903801640010700c1151999001402480040150b0000e01030700390800072584064908280002d0241c0d80c00141402440b054541100e0f032568014001d00180307d017a1000290401c01d00e82e0180300b54681900107132005a024195607404506030058003485c1e94941303c0902206c0105c0c07130403050380260301003030102090200a07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 531090251 1250 531089001 531089023
    0x8040e1308273f03364516020604240f15060306060201060311060702010203041203230306130203090c06041203030507050708120a020705 61
    0x11072400142c0546503010000c4000340c624024400d2041071603010b8000680840d03035015854810404200c3c42c0c104110194410561011134000415059920541144000c1c82c81c1180c000748500c8081180342c9220060204442c41d90014002d9102114022144814244005c4d116016454941c0c813030040c40c3c000c04907088640c16244107500700240c2e1045150318880c8000d00344000e280c02c1ca03003517450f07580e030384803000100c1030001d0f44001d201c620712401e03049405100b800e8002882142ca02c0761250000c554503010380c0001c0707403c006011804901c144548411246c004521000703209546040c05903a500280043e41180405c10001c0380c145404541519601d1090390f070850700c1c14140800504184910380d12580018080041c018035035100d002040d84202d100f4001030752920340829007403030103030400b01c3c140d0400300c046030006100700c100c00e02289550098805018641d1210411145841502c00003045050280207604e803440d800c4249a6126102c1c084c01464007856441d4946801e41410f2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 531091501 1250 531090251 531090277
    0x90603040c0f0b0a0c11040207060c080f070e150c071a121b030f071e0201150b070f03080703090602120907091a0f060409110414010c08040e1308 64
    0x40801c00c000040c0c0c0c00302d00a051003040141003025015004000200e800c1e0046c0402c094001380f6904c940c0d8960481c4c0c090780d1b114008000007a20002c014265800483d164881082d003070700043d2205e0b0042c003000c402101c2c014800e100300825a02140243c0c0c021a2900d0620312500b240402c2800c41e90383c1c001c1e8224810340c6555121640da01000c3e0b841140100102040026444a009895520f02c1600e030015442201d24140b07940742c40c0200ca04059a0180f00c03d001c03144d5062a1a141d01940f01114014520108100f640d403a01841500c0380b04180006001116140c04035000c42d104180941d00b1420506e00415a0016a10b402003a608401e0803010030340941d40a201d041c081c2000700b4030003801403000071310071100d6408000032240011004580100d180610610940e51007400b03c402808000c5405c0108066520842040c3d401c50300420f80c0100d80c3c40f03400702a56003e0300c0d0030040194061070043c41d040c20480c0c008120100036090402c1c1c4600e4000d044002010f21000d0401d54120308 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 531092751 1250 531091501 531091523
    0xa02060108010c0314040b060d06021602030c0d03140a180b09030d020d090b0a05090d0b06150301120314270a0b03010b030c0f130303020619050f07031109060304 71
    0x91036440c00c43d040d103024102414549001e13150500320403c14164030036003158518405070750324404070b40003013584600203102074400034140300c0c680c3c007007103803890014000e41c11600c0b0020718605100b000380444002502144121503555407401981000706601041481c00040070401d40c8401d40d0288038540040b4680c2e031021a00380828282000b036042480002d00c01401418176403540a0550101030081c070003905400541c0c1d41400380901e003196501a00500000790441c0d641c20491650b910985026102c2e40218a0061114041d0070650303041c0c0c1c00ca02050750720603105a405551030b000803401000342c020148000181d00401116014010002200d41d01002e00c49a04020a15030309402c5600001020720044c8901c400300000d985e405100420407a035504010501c040c01c0b0b005821081007240b8110301c001c010141e021a10b140603140b80320003070340d01000216641040d00c008807203140c0e03080e400c800000e100724403a4000f010780c0001d28480760320344204180440c905900407101590713240388030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 531094001 1250 531092751 531092759
    0x708120708240a060f03090c0e01050f030a031710170601031203062612031f09050601021b0f030a0b0f07050c151f08150606030106091206020f0a020601 67
    0x180d400602c040000000058510146000144066120300520040144002e540c240311402a44007501030f6800212400c0d145036160301c814401c0b0001d000d1140101c204003440c50407420300050b40904583d05403a20307403072440d000711600380048004200c0c031800340c010480050f943c5034107038402907910742110141030150706508042140c80c0c1c142c103010f0209842c1c00401c00c50005815424019100c003245083c1d4482c2031039000070315100c1c44510300b000c2020008180207080640580d01562002c07020100d0f02e40590341d03e0f1443c01c0312021542e0601503081b00700c00030900c02036000c100c0d28540c2d0091542001c000802c0100f40780038401c880445810340c465040c8640f526200c15550340c012018502a484e002c10410030a807288001444880101d9203e004a40740154203912440182030034901078010540c0c49007466502c0035210403207001c0c103140c10041442400c0540803a030580740c0c3d945402c4400c0d49014680c8a491492101c1907680d00d6007806500d8a0204000080c52041455030040000f5414 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 531095251 1250 531094001 531094021
    0x60e01050708090c030c011d09090f061b1803071701020a020c270702010b030d0905131406011d0301020415120501031109070309150c030f18080708120708 68
    0x20180001001d5885413a103801c6a41d800103c0801000c003c1c078180120240d550109070320902c0347c2d404240d1000b1030008003ca0f072500050001903142940e403c58103581c4400100c140c2c0009051b07800180c2960410080080200f181d40034000741ca40a0308a6141317556510b850007680d000780301985000d940001c0d06c2c9051707075410001041c3c880c2040741c07400076038426662030703104400060404192070500c050004800074000e5200303100300308010b03050314900c0d0103000780208105a503000f2240300740c18101d2202240341c0c0c03500c194036091301d40562a4145441b0400191440110b00d44030041d05e910588801c0307480c2d1000e00290008203110042c0e10020a1030301c0018003003a1500c01d0a500c060710b0600101701140d07403089070801c20740c026120201c1e503031104002280507240000d80070300032607003079207150400912a62207848820a1503078200426200503d00728103590f6140300801c800d080006e0507801145035000100361441c13052480c0c3e8a01012980003a02c0280d085a6213400708050104001039600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 531096501 1250 531095251 531095267
    0x13020d060902090d0605070c080301030b1012031220040b0a020105010506160611040506030411030f3007150606022b0e0105130e100e090a0303020304020d060e010507 73
    0x280c118802d40c141001c200116440e122440c00180c02d8070f0322000460702640c0940c1041d05040e8100d4400742d07a03507850341803c0c110700714150341151529900c8000064112400301403130540c55810f6540c21442042020441d015002c0120444c61070011601034801c501c41e00380040004045a441280d101c070028000039085950590000b80544020041c88171881400d103103607039229601000001e0b15201411040600380103941203250840000428401030200d0001a40070840f402c030100c80b800c0d400744071002c5c1c9134003021035070100d18002c940120001c02d00c40f184d0300c8400c820f1501091304203181c62721080c0340c0901d02d0100310400d90341c406091010a07818840e410701100000d400c41c0584196020412484c1074861010041080003551810720b03a101d00201c880d55003500f6618840c003502c1c3c604804a400054401003030014440b98006aa102010100c0344a1151100500300101e0562030a80282d44024400ca0b4020400d080d41070000c0d00c148107250f64154890000216031810745c8002c2c05200c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 531097751 1250 531096501 531096509
    0x312021b0c0102011e050c090409030503060301150b1c090503070c15030b0d08090f12011a0d05070b07060e07060c0317060306180f010c02340504020c0a0213020d06 72
    0x1906154421a0001013820040202172002034001807941d5034542800e01400f410903925445800c0020a109040e44103000c1c5000307150480080000c1c207501c1e4242c10b5007620900c5004041c04061000c141c40788044000d1300da86915040b80420031f00c04540c1c81600719407000c101142c003082e00c04000c1c003034100110400000b13440c0301d0408001583c0a040003602414100c83c0082c148900041c441d8440e4440b540f20074480c2c203000e44000c2c0c2561010780c80d1800b03040c000340c87c20100c1ca01e00e11650114600300c0e203100200c0303800074003500d0340310b05011440c4000d07401402c00740c90761903c50302d40c0c10810404001170f00c01000f0550325401c890340d0300d02d002000c0d4055400740b00c0c0181640014440c0a580115a250700550242c888503080b50203140f055003401d00380310410000f9444d01c4144002c554002c100155491b0341c00908600504a00e40c048100d0321101010248600f00c0000074405400c1075401800090699021540030064950014a9000c03215040c6110341e0b40204d00c4824003641da02824000d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 531099001 1250 531097751 531097753
    0x70606060206011512050402010203270315040803040f0c030b0a061a120c03270c10020a0c05010813120207092012040c0e041a130812040312021b0c0102 67
    0xd4002490000c1c60418208540410181d5586c04681168020800c070b07008a07112030980d4a200010351400c80030900f1080646004e80a01d6001e452401d1286001c04d00c49c030f074090305a900395140d6031240503840c03000c000100d4540c9900c580200210341040e1030940314001c0030310301080c100d003410440c0350014009550050340c0708051012410507000c0744d21069000701d400344490389070f544c2d0104401640640400f0100c42c415188440380031442c000c81d03401540d03003040d188400c1080329948200d030740d1020701c3e00240007510f0b60001804507620483c1e40f2900501c80d9201c455401c0b080b40c440b074101d071424850400150384040c5040010380340e24001c6414402c001c92081a0913400000d44070180d00c81e0b0303900120340303a0840e00000c08105d550381115010303101c02e030509905850b003881d000003405154000780e40c10a9045c0c00143d0550040302012040e06d9005215a00b40103c503108036001203401303442141030110122052404504500c06000c07006503503d084803800e40700030361942c1013a8441040d9411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 531100251 1250 531099001 531099029
    0x5090103020303031b1917010608010e0a05090114181519021309051003140303010b0a0c020a090c0e27190207050706080a1404030e0f0a05030307060606020601 70
    0x7581d000700c1540c1d80401c61000341441103403103c080078514800e03003080d403140070141603646203001d900411440498122041209250340c03070717800030340d0000c00900c91505081c20040000d03d200010f604601d0b048200000007069008880d6548026070303d0444480380d01c5c00002000307800d4048200150000d65050b01c0c10064641040e403030500921000681203008a0740000b11001400c48085541000385461081000941440d5541c101080c140b84800d0702c81d800b030040409413000011086034121003140c0c2c442031520300401810388503000e441c041070717921038028000042c82c182940940c0603213550541e102403800c90904100803003441c0440d03c084155071200e1160540b2542d12442d250440044002c40c101414840700d00b0002e4814000020683e0261581c005121504111041d0182011031002d0010740551b40f008a010807080b1800341c00100c1004c149541814056413000d41d0201c0030740741c03012883e1150301203842e40e0300402c0c0803120140d031131700c08004840c0c2c1800003d0140c074003d482c0c104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 531101501 1250 531100251 531100253
    0x405031b01060e3d062601270c120506130614131a0105070c080d0c03030b0108070206152707031508030a030c030b100201060f06030b01120e01020c1203040c05090103 73
    0x1000c641ea0059000340301300c1b030f60100c085802500c00d003c1c0099007030194444960b1079084290903007488004040062000002c0211070100d1070040038203079981e1b80c0c1c880c4041c0046040b00d2024040141589410401100701003c1c1103440b4014440509010001d003450301e185a01442903000303040031203041851070801e43c100840860080b140905030240307040c5440700102c0c24603030354100300e030742c0314110601c0740b40c4110072241d4200113240b803030713600a4070104000340c3d94100545020708211a2000183c10040000d4100701501900244030440940704031812514141580603140044080000c4541c2000800803010b52501540044075410149510850b142c41031090340c03401402c41d40003d240c0c44602c80b02d0322500c81c1c0d000e0400b15000402c946146c2c0301d8800701038020315003401285102c0c41005004210a4004d005000d210103041e594454900c9000c092007000704004918504695020811100c8000d03080124540c3c01c02c8070032009940c0d00b070a150149581d1402e43c0890300039040341e00100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 531102751 1250 531101501 531101611
    0x203061f0b0c0f07060c051204030503312304060305150604230a0608030c0304091503080a08010806070c110d03090f0f080c090405031b01060e 63
    0x301160740100e20207032900782460803507080c0b41c54445469140d114001000504e036900050307880ea41400f61085d1168440800902c0d40320b440303503001c05050ba600030044a00f05101c03d0301d04200d00c1130412405112001e191a58400c48506980003030078040c0514070015070900d840c15404d042c1d0780c0444041005620f990b41300d9407154200303400c610004207041d002a200b03032196041035950b0f1101c2d5111407002c468035044500446001c0d556145528500030011594000010882d041c20301208000c6050034600424503020f09240000c5800300640d5200c000002a40d42c00034000500c0c0d00e0322248030319070502c0c1440d0302e0103000601c1c803010006202d18035004107600000141142c50151103000b5010031608041e982c1c2130483c1c2c00000c00309882000007540b558551480415a010b5606071180c114204040100c3c4000940d4007501c02e4008019a4010103c0088001800881407001040070f0742d41d80b0f10054281c00c102d50741f902e10400041d1010100c00c2008a04c000e002100300403107450f4100003591 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 531104001 1250 531102751 531102811
    0x60903070c180902030d0503010e0702070e010b0703090e070f1d06030c09040b0a03050f010e1c08220c05090f041104110d050c0403020906240d1803030504020306 71
    0x5400e51540c4000014508883e00107881c0150050211580d00c000b0510003401230f0700174030031900785014800201f9504e900c046419002c031014400501c1e616424010311400551120508406002c042100000c000600034160b0703105024075100c5000545403802c0c0500f40f551120900700d4548140c9841c00715a5840400307498000c40640c0c04a602c4140a4001c01e0007094410340d881e0384000f0603a400010040c0029400c4035500000740280711050280b603a0a550f000030144034090408400445440944240724880c0c0c880c2c000030380144d07030720006000088020140728040e10002a21a8113015a013050065a5081100000000e1251400342c460300d822840c0280218802c0e80c80340d20380d4695400d240e0565070b94a59a01d81000b040c140510030b284951b200384012801105030100140c82c614040b1031040b8400041c4840c0c002e040419003212070300381d100700390180390256034913190140340c13180a141c0c9017094800e0701c0000d110f0509004040c684076000746400740248803c0c00c403990a034026080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 531105251 1250 531104001 531104009
    0xc1d0c040e070e0402191e0c29131205281103041e06050405060d200703050c010b04060b0d090618051606020309060405101101110c060903070c 63
    0x40aa03079440300101154180100204203900a00100386009080c5110501c0142031030b0940ba1a892100902207183e00e18003445640c3d4049141050ba40010420020980c1e500c02011030344022010a030915030044260161480030041c082d111051007000708046044a000015042050800300450707115100b8042940356542e10707540c0c580a081d02c00380205032480c5980da0700020b0302e80f01c41d01c1300a5844443e28900307691070011951000025860300640c1203605441005e09098a0082090340b00b00c050480c1c0d028542ca0340d038940e100706460305c035484060201d182c82035540d01d941e2640b40105074203540c103140c1070070300c00e40ca4070000f00032086207002199801303016001c000c02e4210081c20f06000600d400c5940002c0620131041c00c0081080106107203c0d8220810f1150000e241c45203070890344ca024082046410220800040c0060701e044282c4500c01300c03c2d4500001c512015007100b07429590400f82940041d03201186000d410f03141401103591007200342000714113112082c3c98000001449203d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 531106501 1250 531105251 531105269
    0x20901050f12010e010903030b0a0b070f0503090d030f030e0708060a15080f0a15050c040506030c09120c0418080304080903030d0221011e050f0d0501090c1d0c04 71
    0x400c1c40d0003a102d1410220340103000c08000c1102090140c0058040c1281c22412000a442c081c004c10140c41d046082c40c003602c00f2008030742d0404559555401d00940c0c0c00301c090300c0f103101c1401043e8584d1b660100486039648a82d94180014041c5000903050b035003004900c0c041508420014080103500144942d800700304040d02161041210002180e220394541040107140a402a11016100300142018100c2c1c45104d400e40307641721070326041040741e5040c1c0c0e0003030070990104010002441c0c40000303076402c2803150f0700d0f141c0f41410810000f42c96800c510255101d41c0c001c000c0c981814a007900c182c5084083c00c03a01601160510740d0340310024800180024408079001c50b0368449501d0800542d181d608100c1d90456441130450b000a01c24081c060110400310480400072a484040030b00e03040181c003d0809012441c0c1c00c02c801c00800ca007511254a4210244440d9040426424000c04031004d004101ea010003500700080d182800c0440b000480342010a0303030900040e030a4800854084070740d104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 531107751 1250 531106501 531106519
    0x7020f03060403021c17010803120c1303020f0a08010906090b070c05030f07030903020d03120f0e2a1801170f2e0603030f08150a0e041719020f06010302090105 70
    0x241c11b0b600900803000e03480c502c4201750300100b42588000018403070107000700c0000300207030b07281c0246e0009031242c0041e0b1408007a0140f010070050600d0501824850001003020b508103484c0c51050b802c445078204c098465985880009003030040c0e441c0c0c01034200101c2e00c0e108140010791340b03500c1d03940d100708149403141d5503000500300d05052140c5d01640145500a0002600e008107050040040c0700c0d0046000780740746062810000402c8900c228485000b01c1000341140c4204403100406048801101c001802085800c0c1c1590343d4920000c2c40070003c070703410140c440d9410281c4448882c080c0d5688998030f80d101442501403074078002030348a2024800c140140340e90540c0d10240381500c10b070340d012010300d41c14508040209508000b2100c0404185d90319400140e58118070482d840c01107600290304408582c41c02d1140984081e9030560281c001d00c48956402d460010f0500d9035480f07400c0140f1110800c1072402800c0703506003c0e50a9501c00e410040a0650440e000954031080601c076440c842c2040c1c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 531109001 1250 531107751 531107803
    0x3010902040606020a0506070f0e060a2304080f010209092410031a0a050603160c170406090b090a23032a031b040504030c08040b07020f0306040302 65
    0x250040004240d001d0030600007660385007800707540e8129000003154180107960000300070700d00c91103584035454507590382d4040d141c0e002401d01040c0c0d8001c540071801c1003120b03030340300c26413001401655024248405849984520304a0715034105041406100c00990040141700721682d6660421a0044610000b05c514103034022a50b00d03500400d8684550011034200c1c1c0901700d560181e014407440c1c40f05107020000e407110f800401080c001507000c0c19a200750300340045204507084002c3d03400c082ca9a820248203044a0b030302c46040030400c2d10b1480300c800b00c001500303100103a031107020f1400030b003000c04944d070911100c0f03130018000052500843c40141350f42c0440c01c91003010320003251742c0381c0c4012f0f081e5002001050f09022050628904150f182c082d00701c4840120300740021201120104211485d072200c043d10208030103041c001c0c10640400c00d100b001100880c2203000104000c122401815a0b554139902c140200003e030a202281700750401820440803c9d004203401c1003c8500050101d200c10013 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 531110251 1250 531109001 531109003
    0xc040603031224052106070903021c030f121508030c16030f0b0a0209060d05010609080a030e0904050c0a0e2703070b0a1d0309030105181507090e0a291e03 68
    0xb0305c141c40b002a10503030b0144070301990030020307d205890083d00c0d03c00700c420240001d0180c10520f080010000380781100c501074000d01c035500300601d91010b01d4004c0741400c070b0040f8201c4403403c0703034011440c5a0800103030110a4001042821400303041c14400d9102145142c6a0004034011710360040d0807242c8a10015003040003a50403a4041c110007031400340c0380c2c0d00010640004150074014440840c041c07040c0401c4181001941d020020340c1566100030300c004010900c9485131001c2c00072116032044500c1814240d4442003000007030b10040940200318605034002c3d0321100d9400b0031201130300b00305103d01403a1000c040f049442036504100e101e891a2a00d54005000304039400c9101e00300c8030070b00c2c140007540c40e0210040c420724808400a10558940f1310042810802903d4507609540c4002d45144944448140e140c0c0e00506604140001c41d0b5030b40050715016000f2500c0d005c00c4c643d40c40382c000c030071112409903040143c0101d01c40c00480401c40003003200c1d00f240480d0b10ba1007400d0341d0300500c02560 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 531111501 1250 531110251 531110299
    0x6041a0904060c090b0708071202030f0708302220130f061a13050d1103060a09142109030102070f03020a0b010b0f1602030c04060303122405 62
    0x1294008170f40da5001c0c1810705000303941105400711030f10341398031070a942000d100006641c1c41c1440701c21000e00c2e0a18540d28100795610002e2070892000740200c06035040303459040000e032520540341ca9411300d0f141c0008000d8504440ea98158070780125001c45c400800e911001c5144003036030340c400052080341204008cc4001410010404025082080242d11000b02e604170004441a0405101803820101202800360107010000c1101901490041000380381c00c11210020902580f186011980d5410200c0e007405000c440003614151242c90a00401c1484c8620142d29041600588850312461a00c55010900a0302544045101203005c6146a5083d0b0465400700e90090000c0010000c030b1030065141c0070130071340c1900c0b40301e9401c0c00014026500800c039494811118446450300300b140c1e803210303420044800180d030035101e841c0d0411410f80b5544a400f000d103000c7d84441c00c007a5106140b035800d50b2040c3c1184408102c0d40140113600c03196040350301080d581e044410142c90600c3d4428542907079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 531112751 1250 531111501 531111509
    0xf0509041b05041404110a050924030105181302012102070b06030d090308071e050312090607090617040314040f030302100b1c151406041a0904060c09 66
    0x5007540264440164000c0024022603280b00c008080d0307604d4541c1080211041c0a500c0318550f00d00700448110144560300a280402d0000d00d504000300c0c440c11460760342c10a2410030b01c0c2c5618004014071652410101c02c0c03040700103001441c1e180e86070041c2080400c9048460082c18048400340303c20268603821800e180320303807081c24110342721101800d04040c2d4801c151403160007401405c0f0113000892042c00140240d0b500a459145001136541d1950b0070361060070020881c58105c025200001380c0d0034030090801102c0d94010303003200d0420010190400c4005041d00c000d02c000004108017054024110188944241074075401d1580c90717003410303204580b1101c45100080c0300010081030101031040f41d401a24007a600300c6904003a940501002ca6404204259012441034803400002c1241400c5424452244117516146142c24443c8410360705404c1685159880f03c0c800c001c49401c0c107100e5068400d0304e0310101c00220f0030102c0807c5034805e0282002c1d01702a11031494448007401184500010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 531114001 1250 531112751 531112781
    0x39020405180a06021b161502160b070309060801151d041803081e0c0a02010608010e03070209090d050406110a120c020909060f010b0c010f0606090f060c030f050904 72
    0xa060b0b19000c0020750000080c0085c0b82a8103000311480d40c00022000f11485280d002c056006c1e0424409080944108000c10218800d104680d98650080d0156030010500d803130683d03846180314030b0081c1004001d50840010021446d0040162100044007090801e420b820405555800c486c03c0704c1c0310300c42c1c0400c542e03005810400c0039144a54507602c1d4000a90003542d4160300358580314004400d100303481904d0300103600e0f000c022440c101e90b15401000040c20700d000004009580d20042c03400d440454000d032040d50400b02d062000d5081c060740899008002d04c5c0600325034814a6409005030080d401074104001640214403488002003042d20001600400582c000115004000b4407118900e5003c034002d0011401103840980c1c0040c060b8044c443e0281c0c3d841103682000300c86c24098105180a0140e59200c55070760f180040305108080140881e0ba94038a4038608200f0302c0380d03c66080e54802c8007080b07581d000c0032002c1380d44a040660890943d05d0b00b2640c92000301e000401400220440283c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 531115107 1106 531114001 531114013
    0x30b010b0a020613050307110f090103121407020a0b1b070e0a110313031b15020901020f03031905270c010e0a1d091504033902040518 59
    0x48d140010745115034000c0342d040051140c1c20280e001b520f8030261070030140d28941d0b0146103c4040d01c0300010103480e0080d25800f103260150743d8401c0039804040451b1010303103005a52002c031854500c88048852080d1241110b0f40d164106440fa18035403440e0000c1c111020f482d00003520f10881e5521202c0041d48141d403400c4d900c8138541401c2001d0300c283c0c441e502002607a01208000c40504100700140c03203121510001e07180484d40d10028000c0d030700c00d1082151078400d086400707403030042c1c040021039103440e07100300107a50f07002002080e001d109601b445c110003000700003840181c1000990300d00e0045071014040c000c3c00c40b120300500114052a119500303070f80c55500f0b25070f60442c0300c010448100344c604501415400d2030a8034120001211852a2244d00012440e00b403081c0030058510381940c4a04050344910605542d4000d0040c0d40781d1b4001110a690a02080c0e9403107501d0058481c = true := by decide +kernel

theorem cover : BRFrame.Cov 530935251 531115107 := by
  have h0 := BRFrame.cov_init 530935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 530935251 ≤ n) (h2 : n < 531115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
