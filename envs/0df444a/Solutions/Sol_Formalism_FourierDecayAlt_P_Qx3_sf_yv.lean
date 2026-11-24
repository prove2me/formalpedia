-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_yv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:44:03.913797+00:00
-- url     : https://prove2.me/submissions/418b7273-579a-4ce9-b2cf-9a4dc186024f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_uh_inv_eq

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
    SmoothFam k r i U₀ (fun _ g => yv k r z i g j) := by
  refine sf_lin
    { toFun := fun g => ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i) (posL k r i j)
      map_add' := ?_
      map_smul' := ?_ } ?_
  · intro x y
    simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
  · intro c x
    simp [Matrix.conjTranspose_smul, Matrix.smul_mulVec]
  · intro g hg
    show (g⁻¹ *ᵥ fvec k r z i) (posL k r i j) = _
    rw [uh_inv_eq hg.1]
    rfl
end Formalism.FourierDecayAlt.P.Qx3
