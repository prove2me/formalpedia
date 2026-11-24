-- Prove2me | solution 1 for Formalism.L2.Th1.F.has_cm_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:33:02.532572+00:00
-- url     : https://prove2.me/submissions/d963b399-1dcd-402d-8ff9-a82e68938c16

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
import Theorems.Thm_Formalism_L2_Th1_F_CmBy_normSq_omega

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : HasCMByStable := by
  intro d L hL m n
  refine ⟨?_, CmBy.normSq_omega d m n⟩
  intro w hw
  have h1 : omegaK d * w ∈ L.lattice := hL w hw
  have he : ((m : ℂ) + (n : ℂ) * omegaK d) * w = m • w + n • (omegaK d * w) := by
    simp only [zsmul_eq_mul]; ring
  rw [he]
  exact L.lattice.add_mem (L.lattice.smul_mem m hw) (L.lattice.smul_mem n h1)
end Formalism.L2.Th1.F
