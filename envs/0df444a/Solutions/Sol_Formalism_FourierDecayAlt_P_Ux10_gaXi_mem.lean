-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.gaXi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:52.023125+00:00
-- url     : https://prove2.me/submissions/76b35515-2981-4afd-877a-841d54ff4588

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_detZj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_det_hMat_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Rn_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_detZj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_Rn_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_detZj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (hM : SliceMem) (hR : RadicalParam) {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (hZ : G.detM Z ≠ 0) {γ : B.Mat k ρ}
    (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  have hdet : (ZjH σ d ξ.2 Z).det ≠ 0 := by
    rw [detZj]; exact mul_ne_zero (det_hMat_ne σ d hd) hZ
  unfold gaXi
  refine BetaSesquilinearity.gv_mul (BetaSesquilinearity.gv_mul (BetaSesquilinearity.gv_inv (Rn_mem hR _ _ _ _)) ((hM k (p + s) ρ).1 _ _ hdet hγ))
    (Rn_mem hR _ _ _ _)
end Formalism.FourierDecayAlt.P.Ux10
