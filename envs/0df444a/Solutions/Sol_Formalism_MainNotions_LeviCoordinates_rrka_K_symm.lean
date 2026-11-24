-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrka_K_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:39.453575+00:00
-- url     : https://prove2.me/submissions/d4396045-2463-4111-a7e6-14e58514192d

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
theorem _root_.solution (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x y : G) : rrk_K Γ φ y x = star (rrk_K Γ φ x y) := by
  unfold rrk_K
  rw [tsum_star, ← (Equiv.inv Γ).tsum_eq (fun γ : Γ => φ (y⁻¹ * (γ : G) * x))]
  refine tsum_congr fun γ => ?_
  show φ (y⁻¹ * ((γ⁻¹ : Γ) : G) * x) = _
  have e : y⁻¹ * ((γ⁻¹ : Γ) : G) * x = (x⁻¹ * (γ : G) * y)⁻¹ := by simp [mul_assoc]
  rw [e, hsa]
end Formalism.MainNotions.LeviCoordinates
