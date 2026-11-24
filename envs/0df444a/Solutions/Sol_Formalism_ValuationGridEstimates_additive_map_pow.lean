-- Prove2me | solution 1 for Formalism.ValuationGridEstimates.additive_map_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:57.41968+00:00
-- url     : https://prove2.me/submissions/852e4f76-8159-48c7-a762-8c6939cd2286

import Definitions.Def_Formalism_TowerValuationBounds_HermitianSumValuationBound
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ValuationGridEstimates
open Finset
variable {G : Type} [CommGroup G] {v : G → ℝ}
namespace Formalism.ValuationGridEstimates
theorem _root_.solution (hv : ∀ x y, v (x * y) = v x + v y) (x : G) (n : ℕ) : v (x ^ n) = n * v x := by
  induction n with
  | zero => simpa using additive_map_one hv
  | succ n ih => rw [pow_succ, hv, ih]; push_cast; ring
end Formalism.ValuationGridEstimates
