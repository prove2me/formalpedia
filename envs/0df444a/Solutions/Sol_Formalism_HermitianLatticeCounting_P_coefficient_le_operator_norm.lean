-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.coefficient_le_operator_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:42.065614+00:00
-- url     : https://prove2.me/submissions/e34a2a6a-16c4-4461-92e6-c1562cda2699

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CoeffLeOp := by
  intro H _ _ E U w hE hw hn
  have : inner ℂ w (U w) = inner ℂ w ((E ∘L U ∘L E) w) := by
    simp only [ContinuousLinearMap.comp_apply, hw]
    rw [← hE, hw]
  rw [this]
  calc ‖inner ℂ w ((E ∘L U ∘L E) w)‖ ≤ ‖w‖ * ‖(E ∘L U ∘L E) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖E ∘L U ∘L E‖ * ‖w‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hn]; ring
end Formalism.HermitianLatticeCounting.P
