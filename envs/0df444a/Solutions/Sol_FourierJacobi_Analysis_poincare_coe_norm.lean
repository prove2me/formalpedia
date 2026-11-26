-- Prove2me | solution 1 for FourierJacobi.Analysis.poincare_coe_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:52.142377+00:00
-- url     : https://prove2.me/submissions/6f0dc5bc-26b9-47e1-8d1f-0f5a320d05ef

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (t : ℝ) : ‖poincare (t : ℂ)‖ = poincare t := by
  have hp : 0 < poincare t := by unfold poincare; positivity
  have hc : poincare (t : ℂ) = ((poincare t : ℝ) : ℂ) := by simp [poincare]
  rw [hc]
  simpa using abs_of_pos hp
end FourierJacobi.Analysis
