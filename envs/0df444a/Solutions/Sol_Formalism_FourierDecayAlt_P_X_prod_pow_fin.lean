-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.X.prod_pow_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:07.06203+00:00
-- url     : https://prove2.me/submissions/c18e83c8-973a-4c64-86a2-76ea9ec23f8a

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalingExponentIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix
open Formalism.FourierDecayAlt.P.X
namespace Formalism.FourierDecayAlt.P.X
theorem _root_.solution {K : Type} [Field K] (κ : K) (l : ℕ) :
    (∏ a : Fin l, κ ^ (a : ℕ)) = κ ^ (∑ a ∈ Finset.range l, a) := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun a => a) l]
end Formalism.FourierDecayAlt.P.X
