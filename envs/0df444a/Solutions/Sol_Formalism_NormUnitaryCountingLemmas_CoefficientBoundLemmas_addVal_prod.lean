-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:44.089497+00:00
-- url     : https://prove2.me/submissions/cbc9ea37-77dc-46c1-9ca7-d508e6d62185

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_CoefficientBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
theorem _root_.solution {ι : Type*} (s : Finset ι) (c : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, c i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]
end Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
