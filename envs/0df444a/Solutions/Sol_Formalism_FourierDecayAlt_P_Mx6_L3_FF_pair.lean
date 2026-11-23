-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.FF_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:16.475363+00:00
-- url     : https://prove2.me/submissions/b607f900-8296-4183-a496-ab54450c765a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_FF_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_ee_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_ee_off_diagonal_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_ee_off_diagonal_second
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_comm_tgt

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L3
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L3
theorem _root_.solution (hC : SSComm) (hP : P.OK) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    FF P i j u v + FF P j i u v = 0 := by
  by_cases hne : j = i
  · subst hne
    rw [FF_eq P _ hj, ee_diag P hj u v hu hv, map_zero, zero_mul, add_zero]
  · rw [FF_eq P _ hj, FF_eq P _ hi, ee_off_diagonal_first P hi hj hne u v hu hv, ee_off_diagonal_second P hi hj hne u v hu hv,
      map_neg, ← kap_mul, ← kap_mul, neg_mul, mul_assoc, mul_assoc, comm_tgt P hC hP hi hj hne,
      add_neg_cancel]
end Formalism.FourierDecayAlt.P.Mx6.L3
