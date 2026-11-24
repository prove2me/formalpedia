-- Prove2me | solution 1 for Formalism.MainNotions.LatticeGluingRadicals.m_exists_smul_memL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:39.689075+00:00
-- url     : https://prove2.me/submissions/3a100ba2-c3dc-469f-8fbd-ba6f982ff97e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_JExistsNatSmulMemL
import Theorems.Thm_Formalism_MainNotions_LatticeGluingRadicals_j_exists_nat_smul_memL

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
    {S : Formalism.BasicNotions.HSpace E} (M : Submodule (𝓞 E) S.V) {x : S.V}
    (hx : x ∈ Submodule.span E (M : Set S.V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ M := by
  obtain ⟨n, hn, hnx⟩ := j_exists_nat_smul_memL M hx
  refine ⟨(n : 𝓞 E), Nat.cast_ne_zero.mpr hn.ne', ?_⟩
  rwa [Nat.cast_smul_eq_nsmul]
end Formalism.MainNotions.LatticeGluingRadicals
