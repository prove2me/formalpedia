-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.eh_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:36:25.691805+00:00
-- url     : https://prove2.me/submissions/8749d178-35fa-498c-9df2-3c5e4051ab2c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_eh_act
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_bvec_posL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
variable (z z' : Fin (2 * r + k + 1) → ℂ)
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (a b c : Fin (mdim k r i)) (g : Mx k r) :
    EH k r (posL k r i a) (posL k r i b) (fun g => ybv k r z i g c) g = if b = c then ybv k r z i g a else 0 := by
  have h := eh_act (hermL k r (fvec k r z i)) (bvec (posL k r i c)) g (posL k r i a) (posL k r i b)
  rw [bvec_posL] at h
  refine Eq.trans h ?_
  split_ifs
  · rw [one_mul]; rfl
  · rw [zero_mul]
end Formalism.FourierDecayAlt.P.Qx5
