-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrka_K_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:38.81902+00:00
-- url     : https://prove2.me/submissions/c4e405b2-acf8-45ce-aab9-f63ef64cdefc

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkaMeasKabRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] {Γ : Subgroup G} {φ : G → ℂ}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (δ : Γ) (x y : G) : rrk_K Γ φ ((δ : G) * y) x = rrk_K Γ φ y x := by
  unfold rrk_K
  rw [← (Equiv.mulLeft δ).tsum_eq (fun γ : Γ => φ (((δ : G) * y)⁻¹ * (γ : G) * x))]
  refine tsum_congr fun γ => ?_
  show φ (((δ : G) * y)⁻¹ * ((δ * γ : Γ) : G) * x) = _
  have e : ((δ : G) * y)⁻¹ * ((δ * γ : Γ) : G) * x = y⁻¹ * (γ : G) * x := by simp [mul_assoc]
  rw [e]
end Formalism.MainNotions.LeviCoordinates
