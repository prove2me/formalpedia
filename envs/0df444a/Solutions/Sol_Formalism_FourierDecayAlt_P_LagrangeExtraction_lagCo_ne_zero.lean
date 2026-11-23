-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LagrangeExtraction.lagCo_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:55.774373+00:00
-- url     : https://prove2.me/submissions/a7014a04-758f-47f1-a5c3-eef548fcc9a0

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LagrangeExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.LagrangeExtraction
theorem _root_.solution {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    lagCo y j ≠ 0 := by
  unfold lagCo
  refine Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.mem_erase.mp hi).1 (hy h).symm
end Formalism.FourierDecayAlt.P.LagrangeExtraction
