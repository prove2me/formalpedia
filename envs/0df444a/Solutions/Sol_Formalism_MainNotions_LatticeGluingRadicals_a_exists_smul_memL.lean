-- Prove2me | solution 1 for Formalism.MainNotions.LatticeGluingRadicals.a_exists_smul_memL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:03.346842+00:00
-- url     : https://prove2.me/submissions/ee74b6c8-94b5-4439-b130-d66d81112b3c

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_JExistsNatSmulMemL
import Theorems.Thm_Formalism_MainNotions_LatticeGluingRadicals_c_lat_multL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.LatticeGluingRadicals
open NumberField
open scoped nonZeroDivisors
namespace Formalism.MainNotions.LatticeGluingRadicals
theorem _root_.solution {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : Formalism.BasicNotions.HSpace E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (x : S.V) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ Λ :=
  c_lat_multL hΛ x
end Formalism.MainNotions.LatticeGluingRadicals
