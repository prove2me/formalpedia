-- Prove2me | solution 1 for AvramDividend.Classical.cstar_optimal_barrier_of_interior_gap_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:19:56.110011+00:00
-- url     : https://prove2.me/submissions/cdb9a142-362f-46d7-aa72-569679a308f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_finite_attained_of_interior_gap_and_tail
import Theorems.Thm_AvramDividend_Classical_cstar_barrier_compare_of_attained_positive_minimal

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcontDeriv : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : 0 < a) (hgap : deriv W a < deriv W 0)
    (htail : ∀ᶠ x : ℝ in Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W a ≤ deriv W x)
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hboundary : scaleDeriv W 0 = ⊤ ∨
      (scaleDeriv W 0).toReal = 0 ∨
      deriv W (cstar W).toReal ≤ (scaleDeriv W 0).toReal)
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal)) :
    cstar W < ⊤ ∧ ∀ x b : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ b →
      barrierValue W b x ≤ vcstar W x := by
  have hattain : (cstar W).toReal ∈ cstarSet W :=
    (cstar_finite_attained_of_interior_gap_and_tail
      W hcontDeriv a ha hgap htail).2
  have hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y := hW.2.1
  have hcont : ContinuousOn W (Set.Icc 0 (cstar W).toReal) :=
    hW.2.2.1.mono (by
      intro x hx
      exact hx.1)
  exact cstar_barrier_compare_of_attained_positive_minimal
    W hnonneg hattain hpositive hboundary hcont hdiff
