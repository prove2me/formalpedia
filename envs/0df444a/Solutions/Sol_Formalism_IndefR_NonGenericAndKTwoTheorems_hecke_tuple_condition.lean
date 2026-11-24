-- Prove2me | solution 1 for Formalism.IndefR.NonGenericAndKTwoTheorems.hecke_tuple_condition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:45.237243+00:00
-- url     : https://prove2.me/submissions/92689eee-0c17-4658-902b-4fb5cf483c30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HeckeTupleStatement
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NonGenericAndKTwoTheorems

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.NonGenericAndKTwoTheorems
open NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.L2.Indef Formalism.IndefR.HeckeTupleConditions
namespace Formalism.IndefR.NonGenericAndKTwoTheorems
theorem _root_.solution : UntwistedOfSupportAtTwistedPlaces := by
  intro K _ _ _ Bs Df S N h1 h2 w hw j
  have hμ : S.μ w = Bs.μ0 := by
    by_contra h
    exact hw ((h2 w).2 h)
  have hA : S.Aw j w = Atup S j Bs.μ0 w := by rw [← hμ]; rfl
  by_contra hc
  apply h1 w _ hμ
  refine ⟨j, ?_⟩
  by_cases hF : N.F0 w j = 0
  · left
    intro h0
    exact hc ⟨hA.trans h0, hF⟩
  · exact Or.inr hF
end Formalism.IndefR.NonGenericAndKTwoTheorems
