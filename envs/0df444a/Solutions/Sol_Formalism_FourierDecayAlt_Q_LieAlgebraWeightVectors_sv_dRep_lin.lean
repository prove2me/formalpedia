-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_dRep_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:42.003839+00:00
-- url     : https://prove2.me/submissions/ce4dd8db-d51d-4371-a668-08febeb78d7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_dRep_diff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (hall : ∀ v : Wp, v ∈ SmVec k r z π) {X : Mx k r} (hX : inLieW k r z X) :
    IsLinearMap ℂ (dRep π X) := by
  constructor
  · intro x y
    unfold dRep
    simp only [map_add]
    exact deriv_add (sv_dRep_diff hall hX x) (sv_dRep_diff hall hX y)
  · intro c x
    unfold dRep
    simp only [map_smul]
    exact deriv_const_smul c (sv_dRep_diff hall hX x)
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
