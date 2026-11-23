-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.continuous_diagF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:40.286793+00:00
-- url     : https://prove2.me/submissions/e619ceee-cf33-4223-94a6-17c30d23b380

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_continuous_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (β : ℂ) (d : ℕ) (σ : Fin d → ℝ) (t : ℂ) (δ : ℝ) :
    Continuous (diagF β d σ t δ) := by
  unfold diagF
  refine Continuous.mul (by fun_prop) ((continuous_psi β).comp ?_)
  fun_prop
end Formalism.FourierDecayAlt.P.G8
