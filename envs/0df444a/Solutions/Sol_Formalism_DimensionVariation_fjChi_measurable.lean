-- Prove2me | solution 1 for Formalism.DimensionVariation.fjChi_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:58.415113+00:00
-- url     : https://prove2.me/submissions/bc49630f-4f1b-4bca-b599-4a5ac1a7997b

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution (N : ℕ) : Measurable (fjChi N) := by
  show Measurable fun z : ℂ => if ‖z‖ ≤ (N : ℝ) then (1 : ℂ) else 0
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_const
    measurable_const
end Formalism.DimensionVariation
