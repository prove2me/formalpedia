-- Prove2me | solution 1 for Formalism.REAL.mem_admissible_setting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:26.944604+00:00
-- url     : https://prove2.me/submissions/e02172fe-aab6-4df3-8159-804dc293f300

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_IsRightTranslationIsometric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.REAL
attribute [instance] HidaSetting.ng HidaSetting.ips HidaSetting.cs
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F : UJ ε → E) : F ∈ (settingG ε E).adm := by
  intro s g
  have hs : (s : UJ ε) = 1 := Subgroup.mem_bot.mp s.2
  simp only [settingG, hs, one_mul]
  rfl
end Formalism.REAL
