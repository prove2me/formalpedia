-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.G_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:23:58.419382+00:00
-- url     : https://prove2.me/submissions/9443c951-8eda-41d7-93ae-322c4bc82630

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_tsum_scale

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
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
namespace Formalism.L2.Th1.F.Homog
theorem _root_.solution (n : ℕ) : (scalePair L c hc).G n = (c ^ n)⁻¹ * L.G n := by
  simp only [PeriodPair.G]
  rw [tsum_scale L c hc (fun w => (w ^ n)⁻¹), ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  rw [mul_pow, mul_inv]
end Formalism.L2.Th1.F.Homog
