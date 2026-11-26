-- Prove2me | solution 1 for ClassicalComplexWPT.exactOrderInLastVariable_iff_lastTaylorCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:20.249827+00:00
-- url     : https://prove2.me/submissions/79252885-36b9-4f50-b2ef-b46d42803fca

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Theorems.Thm_ClassicalComplexWPT_lastTaylorCoefficient_zero_iff_iteratedDeriv_zero

set_option autoImplicit true
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    ExactOrderInLastVariable f d ↔
      (∀ k < d, lastTaylorCoefficient p k 0 = 0) ∧
        lastTaylorCoefficient p d 0 ≠ 0 := by
  constructor
  · rintro ⟨hlow, htop⟩
    refine ⟨fun k hk ↦
      (lastTaylorCoefficient_zero_iff_iteratedDeriv_zero p hp).mpr (hlow k hk), ?_⟩
    intro hzero
    exact htop ((lastTaylorCoefficient_zero_iff_iteratedDeriv_zero p hp).mp hzero)
  · rintro ⟨hlow, htop⟩
    refine ⟨fun k hk ↦
      (lastTaylorCoefficient_zero_iff_iteratedDeriv_zero p hp).mp (hlow k hk), ?_⟩
    intro hzero
    exact htop ((lastTaylorCoefficient_zero_iff_iteratedDeriv_zero p hp).mpr hzero)
end ClassicalComplexWPT
