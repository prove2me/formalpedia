-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.inner_center_left_of_mean_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:40.810892+00:00
-- url     : https://prove2.me/submissions/bc0dc255-c207-40c3-b58b-ec2fc92e5410

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb

noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
section RealL2
variable {α : Type*} [MeasurableSpace α]
/-- Centering the first argument does not change its pairing with a
mean-zero second argument. The constant term is explicitly removed. -/
theorem solution
    (ν : ProbabilityMeasure α) (F w : Lp ℝ 2 (ν : Measure α))
    (hw : FunctionalInequalities.L2.mean ν w = 0) :
    ⟪FunctionalInequalities.L2.center ν F, w⟫ = ⟪F, w⟫ := by
  have hc :
      FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν F) =
        FunctionalInequalities.L2.mean ν F • FunctionalInequalities.L2.const ν 1 := by
    simpa only [mul_one] using
      (FunctionalInequalities.L2.const_smul ν
        (FunctionalInequalities.L2.mean ν F) 1)
  have hcw : ⟪FunctionalInequalities.L2.const ν 1, w⟫ = 0 := by
    rw [real_inner_comm]
    exact hw
  change
    ⟪F - FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν F), w⟫ =
      ⟪F, w⟫
  rw [inner_sub_left, hc, real_inner_smul_left, hcw, mul_zero, sub_zero]
