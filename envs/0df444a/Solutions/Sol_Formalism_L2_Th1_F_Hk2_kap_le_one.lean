-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.kap_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:10.885888+00:00
-- url     : https://prove2.me/submissions/209043a0-4540-45e8-8ab0-4e2fc2a58605

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2
namespace Formalism.L2.Th1.F.Hk2
theorem _root_.solution (τ : ℂ) : kap τ ≤ 1 := by
  unfold kap
  have h1 : 0 ≤ |τ.im| := abs_nonneg _
  have h2 : 0 ≤ |τ.re| := abs_nonneg _
  rw [div_le_one (by linarith)]
  linarith
end Formalism.L2.Th1.F.Hk2
