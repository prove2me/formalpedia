-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:21.591943+00:00
-- url     : https://prove2.me/submissions/c28a0646-0daa-48c9-a560-78eb4dd1ecfe

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ) (hx : x ^ 2 = (c : L)) :
    ∃ X : 𝓞 L, (X : L) = x ∧ X ^ 2 = (c : 𝓞 L) := by
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx, ← eq_intCast (algebraMap ℤ L)]
    exact isIntegral_algebraMap
  refine ⟨⟨x, hint⟩, rfl, ?_⟩
  apply RingOfIntegers.coe_injective
  simp only [map_intCast]
  exact hx
end Formalism.TwoAdicCyclotomicDecomposition
