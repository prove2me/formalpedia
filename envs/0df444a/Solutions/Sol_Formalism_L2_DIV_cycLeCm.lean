-- Prove2me | solution 1 for Formalism.L2.DIV.cycLeCm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:49:10.030448+00:00
-- url     : https://prove2.me/submissions/8b42e3c9-14ed-47a1-8006-5f98760ee651

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_L2_DIV_conj_root
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_conj_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : CycLeCm := by
  intro ι N hN
  rw [cycQ, adjoin_le_iff]
  intro z hz τ
  have hc : conjQb ι z = z⁻¹ := by
    apply ι.injective
    rw [conjQb_spec, conj_root ι hN hz]
  rw [hc, conj_root τ hN hz]
end Formalism.L2.DIV
