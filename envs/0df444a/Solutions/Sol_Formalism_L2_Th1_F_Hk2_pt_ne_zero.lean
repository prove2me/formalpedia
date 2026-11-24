-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.pt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:32:54.464242+00:00
-- url     : https://prove2.me/submissions/eecd2acb-f6a3-475c-afa9-08aa31ce7e33

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
theorem _root_.solution {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) (m : ℤ) (x : ℝ) :
    (m : ℂ) + (x : ℂ) + (n : ℂ) * τ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  rcases this with h | h
  · exact hn h
  · exact hτ h
end Formalism.L2.Th1.F.Hk2
