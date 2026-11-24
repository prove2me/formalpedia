-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk4.cellOff_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:33:01.413052+00:00
-- url     : https://prove2.me/submissions/8824f8b9-f329-4f71-b009-13929beed84b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit

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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk4
namespace Formalism.L2.Th1.F.Hk4
theorem _root_.solution {τ : ℂ} {b : ℤ × ℤ → ℝ}
    (hbd : ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (p : ℤ × ℤ) : ‖cellOff τ s p‖ ≤ |b p| := by
  unfold cellOff
  split_ifs with hp
  · simp
  · exact (hbd s p h0 h1 hp).trans (le_abs_self _)
end Formalism.L2.Th1.F.Hk4
