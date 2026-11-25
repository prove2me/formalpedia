-- Prove2me | solution 1 for Formalism.NG.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:17:27.971365+00:00
-- url     : https://prove2.me/submissions/85f737e8-7818-414f-9b4d-d9a0ce78401f

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.NG
universe uO uT uT' uΩ uR
namespace Formalism.NG
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (f : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, f i) = ∑ i ∈ s, IsDiscreteValuationRing.addVal O (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]
end Formalism.NG
