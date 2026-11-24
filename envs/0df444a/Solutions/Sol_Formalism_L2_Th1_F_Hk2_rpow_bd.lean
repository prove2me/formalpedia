-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.rpow_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:35:14.896624+00:00
-- url     : https://prove2.me/submissions/51337478-3cd5-4846-953c-97967ab909af

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
theorem _root_.solution {κ x t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hx : κ ≤ x) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    x ^ (-t) ≤ (κ ^ 2)⁻¹ := by
  calc x ^ (-t) ≤ κ ^ (-t) := Real.rpow_le_rpow_of_nonpos hκ hx (by linarith)
    _ ≤ κ ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hκ hκ1 (by linarith)
    _ = (κ ^ 2)⁻¹ := by rw [Real.rpow_neg hκ.le, Real.rpow_two]
end Formalism.L2.Th1.F.Hk2
