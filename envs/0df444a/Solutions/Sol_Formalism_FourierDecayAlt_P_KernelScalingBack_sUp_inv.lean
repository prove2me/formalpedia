-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.sUp_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:09.207533+00:00
-- url     : https://prove2.me/submissions/31de906d-48bd-41aa-a358-8d611fa79690

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_sUp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_sUp_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (u : upUniG K n) :
    sUp (((u⁻¹ : upUniG K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      - sUp ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 := A5x9.grp_sUp_mul u u⁻¹
  rw [mul_inv_cancel, A5x9.grp_sUp_one] at h1
  linear_combination -h1
end Formalism.FourierDecayAlt.P.KernelScalingBack
