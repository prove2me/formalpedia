-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.commutator_l_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:37.263798+00:00
-- url     : https://prove2.me/submissions/c3918f62-80e4-4189-bbc1-c932d982df7d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_raising_pair_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_Lam3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lam_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_N_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_N_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_G_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_N_Lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lam_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_half

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
theorem _root_.solution (hC : SSComm) (hS : NabSS) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (lA P u * lA P v - lA P v * lA P u) = (lA P u - lA P v) * (lA P u - lA P v) := by
  have h := raising_pair_relation (nabA P) (cc P) (ggiA P) (abelian₂ P u) (abelian₂ P v) (u + 1 / 2) (v + 1 / 2)
    (N_cc P) (N_G P) (N_Lam P hS u) (N_Lam P hS v) (G_cc P) (Lam_cc P u) (Lam_cc P v)
    (Lam_sc P _ _) (Lam_sc P _ _) (by rw [half]; exact L3.Lam3 P hC hP u v hu hv)
  rw [half] at h
  rw [lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]
  exact h
end Formalism.FourierDecayAlt.P.Mx6
