-- Prove2me | solution 1 for Formalism.ELL.QuadraticDifferenceHypotheses.sum2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:12.989802+00:00
-- url     : https://prove2.me/submissions/52dddc8b-563a-4d60-9c78-7bb5fbca6707

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_qd_comm
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_sum1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ELL Formalism.ELL.QuadraticDifferenceHypotheses
universe u
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]
namespace Formalism.ELL.QuadraticDifferenceHypotheses
theorem _root_.solution {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (a : M) :
    quadDiff ψ a (∑ e ∈ s, x e) = ∑ e ∈ s, quadDiff ψ a (x e) := by
  rw [qd_comm, sum1 H]
  exact Finset.sum_congr rfl fun e _ => qd_comm _ _ _
end Formalism.ELL.QuadraticDifferenceHypotheses
