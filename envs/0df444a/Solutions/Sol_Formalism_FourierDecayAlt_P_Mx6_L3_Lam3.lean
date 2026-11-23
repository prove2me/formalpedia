-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.Lam3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:02.157397+00:00
-- url     : https://prove2.me/submissions/ef6db88a-5c05-404d-9a68-1e248923c926

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_FF_pair
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_sum_antisymm

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
theorem _root_.solution (hC : SSComm) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (abelian₂ P u * abelian₂ P v - abelian₂ P v * abelian₂ P u) = (abelian₂ P u - abelian₂ P v) * (abelian₂ P u - abelian₂ P v) := by
  have h := sum_antisymm (Icc 1 (P.k - 1)) (fun i j => FF P i j u v)
    (fun i hi j hj => FF_pair P hC hP hi hj u v hu hv)
  rw [← sub_eq_zero, ← h]
  unfold abelian₂ FF
  simp only [← Finset.sum_sub_distrib, Finset.sum_mul_sum, Finset.smul_sum]
end Formalism.FourierDecayAlt.P.Mx6.L3
