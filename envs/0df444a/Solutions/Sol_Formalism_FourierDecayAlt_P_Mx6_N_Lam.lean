-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.N_Lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:53.781841+00:00
-- url     : https://prove2.me/submissions/b8d5f09c-6be3-4397-9d91-ee8e46e89370

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_nab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_cc_sc

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (hS : NabSS) (u : ℂ) : nabA P * abelian₂ P u = abelian₂ P u * nabA P - cc P * abelian₂ P u := by
  unfold abelian₂; rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold lam
  rw [← mul_assoc, ← kap_nab, mul_assoc, (hS P j hj).1, mul_sub, cc_sc, ← mul_assoc (sc P _), ← kap_sc, ← cc_sc]
  simp only [mul_assoc, cc]
end Formalism.FourierDecayAlt.P.Mx6
