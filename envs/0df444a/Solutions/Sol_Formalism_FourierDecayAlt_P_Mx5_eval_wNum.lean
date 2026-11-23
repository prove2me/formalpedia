-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.eval_wNum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:39:46.00581+00:00
-- url     : https://prove2.me/submissions/bb96c34e-eb90-4c23-81e5-b7d3a6ef8b21

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_eval_qP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (π : Ty P) (Y : ℂ) : (wNum P π).eval Y = qC P Y +
    ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1)) := by
  unfold wNum
  rw [Polynomial.eval_add, eval_qP, Polynomial.eval_finset_sum]
  refine congrArg (qC P Y + ·) (Finset.sum_congr rfl fun l _ => ?_)
  unfold xEx
  rw [Finset.sdiff_singleton_eq_erase]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X]
  rw [Finset.prod_congr rfl fun j _ => (add_assoc Y 1 (rho P π j : ℂ)).trans (by rw [add_comm 1])]
end Formalism.FourierDecayAlt.P.Mx5
