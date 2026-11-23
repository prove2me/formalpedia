-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.contDiffAt_phase_function
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:19.971323+00:00
-- url     : https://prove2.me/submissions/f6a64655-77a1-440a-bbe9-c7b93de8858f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_phase_function_eq_sum_add_prod_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_contDiffAt_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_contDiff_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution {n : ℕ} (N : WithTop ℕ∞) (D' : ℂ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) :
    ContDiffAt ℂ N (g0 D') x := by
  rw [phase_function_eq_sum_add_prod_inv]
  exact (a_contDiff_lin N).contDiffAt.add ((a_contDiffAt_prod N x hx).const_smul D')
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
