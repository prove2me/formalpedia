-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.d_continuous_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:53.589885+00:00
-- url     : https://prove2.me/submissions/bf86bbf7-c3f2-4260-adda-fbfb3a6bd6a6

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_continuous_tri

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
theorem _root_.solution (m : ℕ) (x : Fin (m + 1) → ℂ) :
    Continuous (fun y : UT (m + 2) → ℂ => redOf m (x, y)) := by
  have h : ∀ i j, Continuous (fun y : UT (m + 2) → ℂ => triXY x y i j) := fun i j =>
    (d_continuous_tri m x).matrix_elem i j
  unfold redOf
  exact Continuous.prodMk (h _ _) (Continuous.prodMk (continuous_pi fun k => h _ _)
    (Continuous.prodMk (continuous_pi fun q => h _ _) (continuous_pi fun i => h _ _)))
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
