-- Prove2me | solution 1 for CKLaneA3X.TMd.add_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:51:04.736089+00:00
-- url     : https://prove2.me/submissions/aedb5d8a-e55b-48e1-a1a9-fbba4653b927

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_enclosure
import Definitions.Def_A3X_Step028_first_chain

open CKLaneA3X



/-!
# CKLaneA3X.Poly — exact sparse polynomials for the high-u Taylor-model checker

Three-level representation (all kernel-evaluable via `List.rec`; no well-founded recursion):
* `LPoly` : Laurent polynomial in `L` (intended `L = log 2`): list of `(c, q)` meaning `q * L^c`.
* `SPoly` : polynomial in `σ` with `LPoly` coefficients: list of `(b, l)` meaning `σ^b * l`.
* `TPoly` : dense polynomial in `t` with `SPoly` coefficients: `[s₀, s₁, …]` means `s₀ + t*(s₁ + t*(…))`.

Only `eval`-soundness matters for the checker; sortedness is used for compactness but never for
soundness.
-/

namespace CKLaneA3X





/-! ## LPoly -/



theorem LPoly.eval_nil (L : ℝ) : LPoly.eval L [] = 0 := rfl
theorem LPoly.eval_cons (L : ℝ) (m : ℤ × ℚ) (l : LPoly) :
    LPoly.eval L (m :: l) = (m.2 : ℝ) * L ^ m.1 + LPoly.eval L l := rfl



theorem LPoly.add_nil (l2 : LPoly) : LPoly.add [] l2 = l2 := rfl
theorem LPoly.add_cons_nil (m1 : ℤ × ℚ) (t1 : LPoly) : LPoly.add (m1 :: t1) [] = m1 :: t1 := rfl
theorem LPoly.add_cons_cons (m1 m2 : ℤ × ℚ) (t1 t2 : LPoly) :
    LPoly.add (m1 :: t1) (m2 :: t2) =
      if m1.1 < m2.1 then m1 :: LPoly.add t1 (m2 :: t2)
      else if m2.1 < m1.1 then m2 :: LPoly.add (m1 :: t1) t2
      else if m1.2 + m2.2 = 0 then LPoly.add t1 t2 else (m1.1, m1.2 + m2.2) :: LPoly.add t1 t2 :=
  rfl

theorem LPoly.eval_add (L : ℝ) (hL : L ≠ 0) (l1 l2 : LPoly) :
    LPoly.eval L (LPoly.add l1 l2) = LPoly.eval L l1 + LPoly.eval L l2 := by
  induction l1 generalizing l2 with
  | nil => simp [LPoly.add_nil, LPoly.eval_nil]
  | cons m1 t1 ih1 =>
    induction l2 with
    | nil => simp [LPoly.add_cons_nil, LPoly.eval_nil]
    | cons m2 t2 ih2 =>
      rw [LPoly.add_cons_cons]
      split_ifs with h1 h2 h3
      · rw [LPoly.eval_cons, ih1, LPoly.eval_cons, LPoly.eval_cons]; ring
      · rw [LPoly.eval_cons, ih2]; simp only [LPoly.eval_cons]; ring
      · have he : m1.1 = m2.1 := by omega
        rw [ih1, LPoly.eval_cons, LPoly.eval_cons, he]
        have : ((m1.2 : ℝ) + (m2.2 : ℝ)) = 0 := by exact_mod_cast h3
        linear_combination (-(L ^ m2.1)) * this
      · have he : m1.1 = m2.1 := by omega
        rw [LPoly.eval_cons, ih1, LPoly.eval_cons, LPoly.eval_cons, he]
        push_cast; ring













/-! ## SPoly -/



theorem SPoly.eval_nil (σ L : ℝ) : SPoly.eval σ L [] = 0 := rfl
theorem SPoly.eval_cons (σ L : ℝ) (m : ℕ × LPoly) (s : SPoly) :
    SPoly.eval σ L (m :: s) = σ ^ m.1 * LPoly.eval L m.2 + SPoly.eval σ L s := rfl



theorem SPoly.add_nil (s2 : SPoly) : SPoly.add [] s2 = s2 := rfl
theorem SPoly.add_cons_nil (m1 : ℕ × LPoly) (t1 : SPoly) : SPoly.add (m1 :: t1) [] = m1 :: t1 := rfl
theorem SPoly.add_cons_cons (m1 m2 : ℕ × LPoly) (t1 t2 : SPoly) :
    SPoly.add (m1 :: t1) (m2 :: t2) =
      if m1.1 < m2.1 then m1 :: SPoly.add t1 (m2 :: t2)
      else if m2.1 < m1.1 then m2 :: SPoly.add (m1 :: t1) t2
      else if LPoly.add m1.2 m2.2 = [] then SPoly.add t1 t2
      else (m1.1, LPoly.add m1.2 m2.2) :: SPoly.add t1 t2 :=
  rfl

theorem SPoly.eval_add (σ L : ℝ) (hL : L ≠ 0) (s1 s2 : SPoly) :
    SPoly.eval σ L (SPoly.add s1 s2) = SPoly.eval σ L s1 + SPoly.eval σ L s2 := by
  induction s1 generalizing s2 with
  | nil => simp [SPoly.add_nil, SPoly.eval_nil]
  | cons m1 t1 ih1 =>
    induction s2 with
    | nil => simp [SPoly.add_cons_nil, SPoly.eval_nil]
    | cons m2 t2 ih2 =>
      rw [SPoly.add_cons_cons]
      split_ifs with h1 h2 h3
      · rw [SPoly.eval_cons, ih1, SPoly.eval_cons, SPoly.eval_cons]; ring
      · rw [SPoly.eval_cons, ih2]; simp only [SPoly.eval_cons]; ring
      · have he : m1.1 = m2.1 := by omega
        have hz : LPoly.eval L (LPoly.add m1.2 m2.2) = 0 := by rw [h3]; rfl
        rw [LPoly.eval_add L hL] at hz
        rw [ih1, SPoly.eval_cons, SPoly.eval_cons, he]
        linear_combination (-(σ ^ m2.1)) * hz
      · have he : m1.1 = m2.1 := by omega
        rw [SPoly.eval_cons, ih1, SPoly.eval_cons, SPoly.eval_cons, LPoly.eval_add L hL, he]
        ring













/-! ## TPoly (dense in t) -/



theorem TPoly.eval_nil (t σ L : ℝ) : TPoly.eval t σ L [] = 0 := rfl
theorem TPoly.eval_cons (t σ L : ℝ) (s : SPoly) (P : TPoly) :
    TPoly.eval t σ L (s :: P) = SPoly.eval σ L s + t * TPoly.eval t σ L P := rfl



theorem TPoly.add_nil (P2 : TPoly) : TPoly.add [] P2 = P2 := rfl
theorem TPoly.add_cons_nil (s1 : SPoly) (t1 : TPoly) : TPoly.add (s1 :: t1) [] = s1 :: t1 := rfl
theorem TPoly.add_cons_cons (s1 s2 : SPoly) (t1 t2 : TPoly) :
    TPoly.add (s1 :: t1) (s2 :: t2) = SPoly.add s1 s2 :: TPoly.add t1 t2 := rfl

theorem TPoly.eval_add (t σ L : ℝ) (hL : L ≠ 0) (P1 P2 : TPoly) :
    TPoly.eval t σ L (TPoly.add P1 P2) = TPoly.eval t σ L P1 + TPoly.eval t σ L P2 := by
  induction P1 generalizing P2 with
  | nil => simp [TPoly.add_nil, TPoly.eval_nil]
  | cons s1 t1 ih =>
    cases P2 with
    | nil => simp [TPoly.add_cons_nil, TPoly.eval_nil]
    | cons s2 t2 =>
      rw [TPoly.add_cons_cons, TPoly.eval_cons, TPoly.eval_cons, TPoly.eval_cons, ih,
        SPoly.eval_add σ L hL]
      ring






















end CKLaneA3X



/-!
# CKLaneA3X.TM — Taylor-model enclosures in `t` over the high-u domain

Domain: `0 < t ≤ 7/50`, `0 < ρ < 1`; polynomials are evaluated at `σ = ρ - 1/2`, `L = log 2`.
`Encl f P r n` : `|f t ρ - P(t, ρ-1/2, log 2)| ≤ r * t^n` on the domain.
-/

namespace CKLaneA3X

















theorem pow_le_T_pow {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) {a n : ℕ} (han : n ≤ a) :
    t ^ a ≤ (Tq : ℝ) ^ (a - n) * t ^ n := by
  have : t ^ a = t ^ (a - n) * t ^ n := by rw [← pow_add]; congr 1; omega
  rw [this]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht _) (pow_nonneg ht0 _)

/-- lowering the order -/
theorem Encl.lower {f : ℝ → ℝ → ℝ} {P : TPoly} {r r' : ℚ} {n k : ℕ}
    (h : Encl f P r n) (hk : k ≤ n) (hr0 : 0 ≤ r) (hr : r * Tq ^ (n - k) ≤ r') : Encl f P r' k := by
  intro t ρ hd
  have h1 := h t ρ hd
  have h2 := pow_le_T_pow hd.1.le hd.2.1 hk
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr' : (r : ℝ) * (Tq : ℝ) ^ (n - k) ≤ r' := by exact_mod_cast hr
  calc |f t ρ - ev P t ρ| ≤ r * t ^ n := h1
    _ ≤ r * ((Tq : ℝ) ^ (n - k) * t ^ k) := mul_le_mul_of_nonneg_left h2 hr0'
    _ = (r * (Tq : ℝ) ^ (n - k)) * t ^ k := by ring
    _ ≤ r' * t ^ k := mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _)

theorem Encl.add {f g : ℝ → ℝ → ℝ} {P Q R : TPoly} {r s r' : ℚ} {n : ℕ}
    (hf : Encl f P r n) (hg : Encl g Q s n) (hR : TPoly.add P Q = R) (hr : r + s ≤ r') :
    Encl (fun t ρ => f t ρ + g t ρ) R r' n := by
  intro t ρ hd
  have h1 := hf t ρ hd; have h2 := hg t ρ hd
  have hL : Real.log 2 ≠ 0 := by positivity
  have he : ev R t ρ = ev P t ρ + ev Q t ρ := by
    rw [← hR]; unfold ev; exact TPoly.eval_add _ _ _ hL _ _
  rw [he]
  have hr' : ((r : ℝ) + s) ≤ r' := by exact_mod_cast hr
  calc |f t ρ + g t ρ - (ev P t ρ + ev Q t ρ)|
      = |(f t ρ - ev P t ρ) + (g t ρ - ev Q t ρ)| := by ring_nf
    _ ≤ |f t ρ - ev P t ρ| + |g t ρ - ev Q t ρ| := abs_add_le _ _
    _ ≤ r * t ^ n + s * t ^ n := add_le_add h1 h2
    _ = ((r : ℝ) + s) * t ^ n := by ring
    _ ≤ r' * t ^ n := mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _)



/-! ## zero prefix (valuation) -/







/-! ## truncated product soundness -/













/-! ## division by t, truncation -/





end CKLaneA3X



/-!
# CKLaneA3X.TMFun — functional Taylor-model operations (kernel-evaluable) with soundness

A `TMd` is `(P, r, n)`.  `Good f d` := `Encl f d.P d.r d.n ∧ 0 ≤ d.r`.
All remainders are rounded up to multiples of `2^-40` (`rup`) to keep rationals small.
-/

namespace CKLaneA3X







theorem le_rup (x : ℚ) : x ≤ rup x := by
  unfold rup
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _













theorem Tq_nonneg : (0 : ℚ) ≤ Tq := by norm_num [Tq]





theorem _root_.solution {f g : ℝ → ℝ → ℝ} {a b : TMd} (ha : Good f a) (hb : Good g b) :
    Good (fun t ρ => f t ρ + g t ρ) (TMd.add a b) := by
  have hT := Tq_nonneg
  have h1 : Encl f a.P (a.r * Tq ^ (a.n - min a.n b.n)) (min a.n b.n) :=
    Encl.lower ha.1 (min_le_left _ _) ha.2 (le_refl _)
  have h2 : Encl g b.P (b.r * Tq ^ (b.n - min a.n b.n)) (min a.n b.n) :=
    Encl.lower hb.1 (min_le_right _ _) hb.2 (le_refl _)
  refine ⟨Encl.add h1 h2 rfl (le_rup _), ?_⟩
  refine le_trans ?_ (le_rup _)
  have := ha.2; have := hb.2
  positivity













/-! ## Horner evaluation of a rational polynomial at a TM -/












/-! ## magnitude of a TM-enclosed function -/



end CKLaneA3X
