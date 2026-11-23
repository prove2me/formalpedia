-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G1.prod_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:52.93321+00:00
-- url     : https://prove2.me/submissions/03a206e8-59a9-4e53-a732-cfdba46b2a51

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
theorem _root_.solution {n : ℕ} (x : Fin n → ℂ) (k : Fin n) :
    ∏ j, x j = x k * ∏ j ∈ univ \ {k}, x j := by
  have := Finset.prod_update_of_mem (Finset.mem_univ k) x (x k)
  rwa [Function.update_eq_self] at this
end Formalism.FourierDecayAlt.P.G1
