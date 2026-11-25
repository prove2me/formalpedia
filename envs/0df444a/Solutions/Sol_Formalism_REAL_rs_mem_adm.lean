-- Prove2me | solution 1 for Formalism.REAL.rs_mem_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:37.302699+00:00
-- url     : https://prove2.me/submissions/22801e41-08d1-4664-a5fe-35a15e2bcb81

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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) (F : UJ ε → P.E) (hF : F ∈ P.adm)
    (h : UJ ε) : Rs h F ∈ P.adm := by
  intro s g
  simp only [Rs, mul_assoc]
  exact hF s (g * h)
end Formalism.REAL
