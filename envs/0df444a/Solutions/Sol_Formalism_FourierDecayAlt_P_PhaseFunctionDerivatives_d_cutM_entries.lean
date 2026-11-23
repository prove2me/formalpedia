-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.d_cutM_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:36.49268+00:00
-- url     : https://prove2.me/submissions/d3e64cbe-c4b4-4147-a3e1-0b9074f001c3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution {s : ℕ} (τ : ℝ) (hτ : 0 < τ) (Z : Mat s) (hne : cutM τ Z ≠ 0) (i j : Fin s) :
    ‖Z i j‖ ≤ 2 * τ := by
  by_contra hlt
  push Not at hlt
  apply hne
  unfold cutM
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  unfold chi0
  apply Real.smoothTransition.zero_of_nonpos
  have h2 : (2 * τ) ^ 2 < ‖Z i j‖ ^ 2 := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
  rw [sub_nonpos, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg τ]
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
