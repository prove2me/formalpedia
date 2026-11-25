-- Prove2me | solution 1 for Formalism.REAL.rs_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:46.215307+00:00
-- url     : https://prove2.me/submissions/4eff05af-6211-46e6-8728-65d778878a93

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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h₁ h₂ : UJ ε) (F : UJ ε → E) :
    Rs (h₁ * h₂) F = Rs h₁ (Rs h₂ F) := by
  funext g
  simp only [Rs, mul_assoc]
end Formalism.REAL
