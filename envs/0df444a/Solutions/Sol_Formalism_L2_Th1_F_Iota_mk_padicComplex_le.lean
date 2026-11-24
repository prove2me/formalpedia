-- Prove2me | solution 1 for Formalism.L2.Th1.F.Iota.mk_padicComplex_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:58.337163+00:00
-- url     : https://prove2.me/submissions/d29d0c7c-a940-4669-a5a7-3dd83e04b1b9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MkLeOfDenseRange
import Theorems.Thm_Formalism_L2_Th1_F_Iota_mk_le_of_denseRange
import Theorems.Thm_Formalism_L2_Th1_F_Iota_mk_padicAlgCl_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Cardinal Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Iota
namespace Formalism.L2.Th1.F.Iota
theorem _root_.solution (l : ℕ) [Fact l.Prime] : #ℂ_[l] ≤ 𝔠 := by
  have h := mk_le_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l))
  calc #ℂ_[l] ≤ #(PadicAlgCl l) ^ ℵ₀ := h
    _ ≤ 𝔠 ^ ℵ₀ := power_le_power_right (mk_padicAlgCl_le l)
    _ = 𝔠 := continuum_power_aleph0
end Formalism.L2.Th1.F.Iota
