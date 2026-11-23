-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LagrangeExtraction.sum_prod_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:20.820888+00:00
-- url     : https://prove2.me/submissions/9e8c7585-10cb-4f3e-abc5-34148e9d4762

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
theorem _root_.solution {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ j : Fin K → Fin (d + 1), ∏ a, |lagCo (grid a) (j a)| = ∏ a, ∑ i, |lagCo (grid a) i| := by
  first
  | rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  | exact (Finset.prod_univ_sum (fun a i => |lagCo (grid a) i|)).symm
  | simp [Finset.prod_univ_sum]
end Formalism.FourierDecayAlt.P.LagrangeExtraction
