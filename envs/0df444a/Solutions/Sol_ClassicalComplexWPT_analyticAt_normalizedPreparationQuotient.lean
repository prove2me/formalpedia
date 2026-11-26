-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_normalizedPreparationQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:29:48.196296+00:00
-- url     : https://prove2.me/submissions/34c120eb-b344-4a6b-82e3-221f1ef3c84b

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedPreparationTail
import Theorems.Thm_ClassicalComplexWPT_analyticAt_seqDivisionQuotientGlobal


set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0 := by
  have hin : AnalyticAt ℂ (fun z : Base n ↦
      (normalizedPreparationTail p r hr d z, monomialSeq d)) 0 :=
    (analyticAt_normalizedPreparationTail p r hr d).prod analyticAt_const
  exact (analyticAt_seqDivisionQuotientGlobal d _ hsmall).comp hin
end ClassicalComplexWPT
