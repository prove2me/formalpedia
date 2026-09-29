-- Prove2me | solution 1 for CKLaneA3X.TMd.scale_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:51:14.044136+00:00
-- url     : https://prove2.me/submissions/acd88cad-551c-46e6-bf44-ebfca99dfb95

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



















theorem LPoly.eval_scale (L : ℝ) (q : ℚ) (l : LPoly) :
    LPoly.eval L (LPoly.scale q l) = (q : ℝ) * LPoly.eval L l := by
  induction l with
  | nil => simp [LPoly.scale, LPoly.eval_nil]
  | cons m t ih =>
    show (((q * m.2 : ℚ)) : ℝ) * L ^ m.1 + LPoly.eval L (LPoly.scale q t) = _
    rw [ih, LPoly.eval_cons]; push_cast; ring

/-! ## SPoly -/



theorem SPoly.eval_nil (σ L : ℝ) : SPoly.eval σ L [] = 0 := rfl
theorem SPoly.eval_cons (σ L : ℝ) (m : ℕ × LPoly) (s : SPoly) :
    SPoly.eval σ L (m :: s) = σ ^ m.1 * LPoly.eval L m.2 + SPoly.eval σ L s := rfl



















theorem SPoly.eval_scale (σ L : ℝ) (q : ℚ) (s : SPoly) :
    SPoly.eval σ L (SPoly.scale q s) = (q : ℝ) * SPoly.eval σ L s := by
  induction s with
  | nil => simp [SPoly.scale, SPoly.eval_nil]
  | cons m t ih =>
    show σ ^ m.1 * LPoly.eval L (LPoly.scale q m.2) + SPoly.eval σ L (SPoly.scale q t) = _
    rw [ih, LPoly.eval_scale, SPoly.eval_cons]; ring

/-! ## TPoly (dense in t) -/



theorem TPoly.eval_nil (t σ L : ℝ) : TPoly.eval t σ L [] = 0 := rfl
theorem TPoly.eval_cons (t σ L : ℝ) (s : SPoly) (P : TPoly) :
    TPoly.eval t σ L (s :: P) = SPoly.eval σ L s + t * TPoly.eval t σ L P := rfl











theorem TPoly.eval_scale (t σ L : ℝ) (q : ℚ) (P : TPoly) :
    TPoly.eval t σ L (TPoly.scale q P) = (q : ℝ) * TPoly.eval t σ L P := by
  induction P with
  | nil => simp [TPoly.scale, TPoly.eval_nil]
  | cons s P ih =>
    show SPoly.eval σ L (SPoly.scale q s) + t * TPoly.eval t σ L (TPoly.scale q P) = _
    rw [ih, SPoly.eval_scale, TPoly.eval_cons]; ring


















end CKLaneA3X



/-!
# CKLaneA3X.TM — Taylor-model enclosures in `t` over the high-u domain

Domain: `0 < t ≤ 7/50`, `0 < ρ < 1`; polynomials are evaluated at `σ = ρ - 1/2`, `L = log 2`.
`Encl f P r n` : `|f t ρ - P(t, ρ-1/2, log 2)| ≤ r * t^n` on the domain.
-/

namespace CKLaneA3X























theorem Encl.scale {f : ℝ → ℝ → ℝ} {P R : TPoly} {r r' : ℚ} {n : ℕ} (c : ℚ)
    (hf : Encl f P r n) (hR : TPoly.scale c P = R) (hr : |c| * r ≤ r') :
    Encl (fun t ρ => (c : ℝ) * f t ρ) R r' n := by
  intro t ρ hd
  have h1 := hf t ρ hd
  have he : ev R t ρ = (c : ℝ) * ev P t ρ := by
    rw [← hR]; unfold ev; exact TPoly.eval_scale _ _ _ _ _
  rw [he, ← mul_sub, abs_mul]
  have hr' : (|(c : ℝ)| * r) ≤ r' := by exact_mod_cast (by simpa [Rat.cast_abs] using hr)
  calc |(c : ℝ)| * |f t ρ - ev P t ρ| ≤ |(c : ℝ)| * (r * t ^ n) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (|(c : ℝ)| * r) * t ^ n := by ring
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























theorem _root_.solution {f : ℝ → ℝ → ℝ} {a : TMd} (ha : Good f a) (c : ℚ) :
    Good (fun t ρ => (c : ℝ) * f t ρ) (TMd.scale c a) := by
  refine ⟨Encl.scale c ha.1 rfl (le_rup _), ?_⟩
  refine le_trans ?_ (le_rup _)
  have := ha.2
  positivity









/-! ## Horner evaluation of a rational polynomial at a TM -/












/-! ## magnitude of a TM-enclosed function -/



end CKLaneA3X
