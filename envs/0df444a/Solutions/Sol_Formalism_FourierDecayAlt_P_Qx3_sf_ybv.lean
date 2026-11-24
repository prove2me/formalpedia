-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_ybv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:44:02.14153+00:00
-- url     : https://prove2.me/submissions/27ed7a01-0bd0-479a-b961-048bc3ed71ee

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_lin

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothFam k r i U₀ (fun _ g => ybv k r z i g j) := by
  refine sf_lin
    { toFun := fun g => herm (Hpk k r) (g *ᵥ bvec (posL k r i j)) (fvec k r z i)
      map_add' := ?_
      map_smul' := ?_ } ?_
  · intro x y
    simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  · intro c x
    simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]
  · intro g _
    rfl
end Formalism.FourierDecayAlt.P.Qx3
