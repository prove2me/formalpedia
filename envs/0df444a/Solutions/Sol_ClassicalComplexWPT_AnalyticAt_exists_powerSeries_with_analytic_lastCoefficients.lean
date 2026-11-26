-- Prove2me | solution 1 for ClassicalComplexWPT.AnalyticAt.exists_powerSeries_with_analytic_lastCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:20.324464+00:00
-- url     : https://prove2.me/submissions/9a51f4ae-f995-4c52-ae8c-18feba5c17ac

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Theorems.Thm_ClassicalComplexWPT_analyticAt_lastTaylorCoefficient

set_option autoImplicit true
open ClassicalComplexWPT
namespace ClassicalComplexWPT
namespace AnalyticAt
theorem _root_.solution
    {n : ℕ} {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ p : FormalMultilinearSeries ℂ (Ambient n) ℂ,
      HasFPowerSeriesAt f p 0 ∧
        ∀ k, AnalyticAt ℂ (lastTaylorCoefficient p k) 0 := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp, fun k ↦ analyticAt_lastTaylorCoefficient p hp.radius_pos⟩
end AnalyticAt
end ClassicalComplexWPT
