-- Prove2me | solution 1 for Formalism.L2.Th1.F.OnePole.zeta_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:25:00.744336+00:00
-- url     : https://prove2.me/submissions/c5bccaee-a8ad-4ac9-9dfc-b718fa21fbb5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OnePole
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_zetaExcept_zero_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.OnePole
open AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F.OnePole
theorem _root_.solution (hq : ZetaQuasi) (L : PeriodPair) (p z₀ : ℂ) (h : z₀ - p ∈ L.lattice) :
    ∀ᶠ w in 𝓝[≠] z₀,
      wZeta L (w - p) = zetaExcept L 0 (w - z₀) + 1 / (w - z₀) + wEta L (z₀ - p) := by
  filter_upwards [eventually_notMem L z₀ z₀] with w hw
  rw [show w - p = w - z₀ + (z₀ - p) by ring, hq L (z₀ - p) (w - z₀) h hw, ← zetaExcept_zero_add]
end Formalism.L2.Th1.F.OnePole
