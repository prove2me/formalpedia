-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.weight_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:25.002769+00:00
-- url     : https://prove2.me/submissions/6d38194e-8b20-447e-aee8-24030e2054df

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution (n N : ℕ) (v : Bool) : Finsupp.weight (wt n N v) = rho n N v := by
  apply Finsupp.addHom_ext
  intro x y
  rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
  show y • rho n N v (Finsupp.single x 1) = rho n N v (Finsupp.single x y)
  rw [← map_nsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
