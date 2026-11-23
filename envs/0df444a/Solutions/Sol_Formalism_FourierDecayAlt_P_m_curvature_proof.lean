-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.m_curvature_proof
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:29.445887+00:00
-- url     : https://prove2.me/submissions/b98519dc-76b0-41e8-a8cf-5ee8794fae8b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_curv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_kap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.Curvature := by
  intro P
  rw [kap_eq]
  simp only [nabA, nabsA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
  congr 1
  funext π
  exact curv _ _
end Formalism.FourierDecayAlt.P
