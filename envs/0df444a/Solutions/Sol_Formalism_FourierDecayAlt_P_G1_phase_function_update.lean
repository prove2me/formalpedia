-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G1.phase_function_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:52.921065+00:00
-- url     : https://prove2.me/submissions/c9e7f53f-85cf-466b-b4ae-1b55e4953ce3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G1
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G1
theorem _root_.solution {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (k : Fin n) (ξ : ℂ) :
    g0 D' (Function.update x k ξ) =
      ξ + ∑ j ∈ univ \ {k}, x j + D' / (ξ * ∏ j ∈ univ \ {k}, x j) := by
  unfold g0
  rw [Finset.prod_update_of_mem (mem_univ k), Finset.sum_update_of_mem (mem_univ k)]
end Formalism.FourierDecayAlt.P.G1
