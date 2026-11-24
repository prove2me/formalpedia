-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.prod_comp_eq_prod_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:04:44.467981+00:00
-- url     : https://prove2.me/submissions/810f89a9-c369-4a7c-af07-b7f4e141ef5a

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution {K : Type} [CommRing K] {N : ℕ} (f : Fin N → Polynomial K) (g : Polynomial K) :
    (∏ a, f a).comp g = ∏ a, (f a).comp g :=
  map_prod (Polynomial.compRingHom g) f Finset.univ
end Formalism.CohomologicalDescent.WorkedExample
