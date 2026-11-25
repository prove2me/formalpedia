-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.centralTransvectionProperties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:37.423043+00:00
-- url     : https://prove2.me/submissions/2ec99a8f-e685-49c0-aaf3-ddc8f3910c17

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
theorem _root_.solution : CentreFacts := by
  intro R V _ _ _ _ h r e c
  refine ⟨?_, ?_⟩
  · intro x hx
    simp [hx]
  · intro n f' b
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.mul_apply, Finset.sum_smul]
    simp [Matrix.of_apply]
end Formalism.HermitianLatticeCounting.P
