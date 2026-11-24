-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.precomplete_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:24.888267+00:00
-- url     : https://prove2.me/submissions/59ed4a3c-7b7a-47fc-a924-dd4e5a04ff21

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Theorems.Thm_Formalism_NG_IdemLiftAlt_precomplete_pi
import Theorems.Thm_Formalism_NG_IdemLiftAlt_precomplete_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
namespace Formalism.NG.IdemLiftAlt
theorem _root_.solution (I : Ideal O) [IsNoetherianRing O] [IsAdicComplete I O]
    (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O M
  have := precomplete_pi I n
  exact precomplete_of_surjective I π hπ
end Formalism.NG.IdemLiftAlt
