-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_normalizedCoefficientMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:03:15.864246+00:00
-- url     : https://prove2.me/submissions/8a1e523c-3915-4ef8-90a6-d84a6e3a16f0

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (C : Base n → OriginSeq) (denom : ℂ) (hC : AnalyticAt ℂ C 0) :
    AnalyticAt ℂ (normalizedCoefficientMap C denom) 0 := by
  change AnalyticAt ℂ (denom⁻¹ • C) 0
  exact hC.const_smul
end ClassicalComplexWPT
