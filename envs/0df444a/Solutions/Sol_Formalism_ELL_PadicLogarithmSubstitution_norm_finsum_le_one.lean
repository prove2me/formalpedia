-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.norm_finsum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:12.163724+00:00
-- url     : https://prove2.me/submissions/75b39f08-c058-47ce-9dc3-09f99ff84a2a

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicLogarithmSubstitution
theorem _root_.solution {f : ℕ → K} (h : ∀ n, ‖f n‖ ≤ 1) : ‖∑ᶠ n, f n‖ ≤ 1 := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => h i)
  · rw [finsum_of_infinite_support hs]; simp
end Formalism.ELL.PadicLogarithmSubstitution
