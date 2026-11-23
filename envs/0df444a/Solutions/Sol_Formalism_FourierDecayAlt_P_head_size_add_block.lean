-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.head_size_add_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:18.974311+00:00
-- url     : https://prove2.me/submissions/cc6b607d-f3c5-4517-b906-a24ba6ad5fc2

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_modK_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_isUnit_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_det_pt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_prod_addBlock
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A6x9
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.CSizeAddBlock := by
  intro K _ _ _ R ψ hd h m t
  unfold cSize
  rw [A5x5.modK_det_pt, A5x5.modK_det_pt, A5x5.prod_addBlock,
    A5x5.modK_mul' hd (A5x5.isUnit_prod _) (t.isUnit.pow m), modK_pow hd t.isUnit, mul_inv]
end Formalism.FourierDecayAlt.P
