-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.zeta_norm_le_on_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:36.65794+00:00
-- url     : https://prove2.me/submissions/73346948-81ff-45d2-8633-531727e06424

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqGrowth
import Theorems.Thm_Formalism_ZeroFreeDirichlet_circle_about_two_geometry
import Theorems.Thm_Formalism_ZF_growthBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) : ‖riemannZeta s‖ ≤ 14 := by
  obtain ⟨hre, hn, h1⟩ := circle_about_two_geometry hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at h1
    norm_num at h1
  have hg := Formalism.ZF.growthBound s (by linarith) hs1
  have ha : 1 / ‖s - 1‖ ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hb : 1 / s.re ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hp : 0 ≤ 1 + 1 / s.re := by
    have : 0 < 1 / s.re := by apply div_pos <;> linarith
    linarith
  have hc : ‖s‖ * (1 + 1 / s.re) ≤ 7 / 2 * 3 := by
    calc ‖s‖ * (1 + 1 / s.re) ≤ 7 / 2 * (1 + 1 / s.re) := mul_le_mul_of_nonneg_right hn hp
      _ ≤ 7 / 2 * 3 := by linarith
  linarith
end Formalism.ZeroFreeDirichlet
