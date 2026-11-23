-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_fderiv_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:09.422468+00:00
-- url     : https://prove2.me/submissions/12bdf69c-045f-4971-8b83-46440643b68c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_contDiffAt_phase_function
import Theorems.Thm_Formalism_FourierDecayAlt_P_phase_function_deriv


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
theorem _root_.solution {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) (k : Fin n) :
    fderiv ℂ (g0 D') x (Pi.single k 1) = dg0 D' x k := by
  have hd : DifferentiableAt ℂ (g0 D') x := (contDiffAt_phase_function 1 D' x hx).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (g0 D') (fderiv ℂ (g0 D') x) (Function.update x k (x k)) := by
    rw [Function.update_eq_self]; exact hd.hasFDerivAt
  have h2 := h1.comp_hasDerivAt (x k) (hasDerivAt_update x k (x k))
  exact h2.unique ((phase_function_deriv n D' x hx).1 k)
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
