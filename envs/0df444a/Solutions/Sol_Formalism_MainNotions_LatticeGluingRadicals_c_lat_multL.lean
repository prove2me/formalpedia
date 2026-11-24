-- Prove2me | solution 1 for Formalism.MainNotions.LatticeGluingRadicals.c_lat_multL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:50.612701+00:00
-- url     : https://prove2.me/submissions/a8e39b1a-b2ac-4dae-80b6-2efae6b21cef

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_JExistsNatSmulMemL
import Theorems.Thm_Formalism_MainNotions_LatticeGluingRadicals_m_exists_smul_memL

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
    {S : Formalism.BasicNotions.HSpace E} {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsLattice E Λ)
    (v : S.V) : ∃ n : 𝓞 E, n ≠ 0 ∧ n • v ∈ Λ :=
  m_exists_smul_memL Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)
end Formalism.MainNotions.LatticeGluingRadicals
