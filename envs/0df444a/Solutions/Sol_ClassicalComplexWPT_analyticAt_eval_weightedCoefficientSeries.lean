-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_eval_weightedCoefficientSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:17:01.313224+00:00
-- url     : https://prove2.me/submissions/a7c77b92-7b52-4c80-874d-0774daccc241

import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Theorems.Thm_ClassicalComplexWPT_analyticAt_weightedCoefficientSeries_sum


set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hrp : (r : ℝ≥0∞) < p.radius) :
    AnalyticAt ℂ (fun x : Base n × ℂ ↦
      evalL1PowerSeries ((weightedCoefficientSeries p r).sum x.1)
        ((r : ℂ)⁻¹ * x.2)) 0 :=
  ClassicalComplexWPT.AnalyticAt.evalL1PowerSeries
    (analyticAt_weightedCoefficientSeries_sum p r hrp) (r : ℂ)⁻¹
end ClassicalComplexWPT
