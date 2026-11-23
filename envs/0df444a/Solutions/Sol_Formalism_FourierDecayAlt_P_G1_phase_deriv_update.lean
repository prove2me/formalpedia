-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G1.phase_deriv_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:52.895799+00:00
-- url     : https://prove2.me/submissions/b8f074c7-0803-484c-b1e0-b5b7c6937107

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
theorem _root_.solution {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (j i : Fin n) (ξ : ℂ) :
    dg0 D' (Function.update x j ξ) i =
      1 - D' / (ξ * ∏ l ∈ univ \ {j}, x l) / (Function.update x j ξ i) := by
  unfold dg0
  rw [Finset.prod_update_of_mem (mem_univ j)]
end Formalism.FourierDecayAlt.P.G1
