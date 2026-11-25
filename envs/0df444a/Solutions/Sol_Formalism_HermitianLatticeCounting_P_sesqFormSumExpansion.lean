-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sesqFormSumExpansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:59:19.621464+00:00
-- url     : https://prove2.me/submissions/f76b064f-6d50-4909-b004-ba99333afe7a

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CommonLiftExpand := by
  intro V _ _ h r e e' l₁ l₂ α α' h1 h2
  have hA : ∀ x, h (∑ a, α a • e a) x = ∑ a, α a * h (e a) x := by
    intro x
    simp [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  have hB : ∀ x, h x (∑ b, α' b • e' b) = ∑ b, conj (α' b) * h x (e' b) := by
    intro x
    simp [map_sum, map_smulₛₗ]
  simp only [map_add, LinearMap.add_apply, hA, hB, h1, h2, mul_zero, Finset.sum_const_zero,
    zero_add, add_zero, Finset.mul_sum, mul_assoc]
end Formalism.HermitianLatticeCounting.P
