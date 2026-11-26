-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_normalizedPreparationTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:10:17.186278+00:00
-- url     : https://prove2.me/submissions/168b0b6c-46c6-4f3f-a690-50b651370508

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Theorems.Thm_ClassicalComplexWPT_analyticAt_analyticNormalizedCoefficientMap


set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    AnalyticAt ℂ (normalizedPreparationTail p r hr d) 0 := by
  exact (analyticAt_analyticNormalizedCoefficientMap p r hr d).sub analyticAt_const
end ClassicalComplexWPT
