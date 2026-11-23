-- Prove2me | solution 1 for Formalism.DimensionVariation.fjChi_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:59.085051+00:00
-- url     : https://prove2.me/submissions/0e35c3c5-acc5-4e55-97d7-1df57742625b

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
theorem _root_.solution (N : ℕ) (z : ℂ) : ‖fjChi N z‖ ≤ 1 := by
  unfold fjChi
  split_ifs <;> simp
end Formalism.DimensionVariation
