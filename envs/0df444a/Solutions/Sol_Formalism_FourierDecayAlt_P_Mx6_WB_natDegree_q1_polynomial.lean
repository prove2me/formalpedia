-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.natDegree_q1_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:42.154994+00:00
-- url     : https://prove2.me/submissions/7718d683-672b-414f-8ed6-87b44fe0634b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution (P : Par) (hP : P.OK) : (q1P P).natDegree = 2 * (Icc 1 (P.k - 1)).card + 2 := by
  unfold q1P
  rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  have : ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := by
    intro i _
    rw [(monic_X_add_C _).natDegree_mul (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  rw [Finset.sum_congr rfl this]
  have := hP.k_pos
  simp
  omega
end Formalism.FourierDecayAlt.P.Mx6.WB
