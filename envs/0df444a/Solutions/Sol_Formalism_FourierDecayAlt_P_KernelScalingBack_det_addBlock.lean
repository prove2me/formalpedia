-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.det_addBlock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:29.495302+00:00
-- url     : https://prove2.me/submissions/590b746d-724f-47ad-b666-49ceeb21647c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_det_pt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_prod_addBlock


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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (h : Point K) (s : ℕ) : ∃ c0 : Kˣ, ∀ z : Kˣ,
    (pt (addBlock h s z).1 (addBlock h s z).2).det = ((c0 * z ^ s : Kˣ) : K) := by
  obtain ⟨e, he⟩ := det_pt_eq (K := K) (h.1 ++ [s])
  refine ⟨(∏ a : Fin h.1.sum, h.2 (blk h.1 a)) * e, fun z => ?_⟩
  have h1 : (pt (addBlock h s z).1 (addBlock h s z).2).det =
      (∏ a : Fin (addBlock h s z).1.sum,
        (((addBlock h s z).2 (blk (addBlock h s z).1 a) : Kˣ) : K)) * (e : K) := he _
  rw [h1, A5x5.prod_addBlock]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.KernelScalingBack
