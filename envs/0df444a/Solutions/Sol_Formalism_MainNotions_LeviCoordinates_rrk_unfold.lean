-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrk_unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:26.756921+00:00
-- url     : https://prove2.me/submissions/c9def224-e8b5-4369-abaa-969df2cfac0d

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkbLeOneAddSq
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_step2
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_step1
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_exists_meas_rep


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
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ μ)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, R g v⟫_ℂ ∂μ)
    (hK : ∀ᵐ x ∂μ.restrict D, ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) (f : Lp ℂ 2 (μ.restrict D)) :
    ∀ᵐ x ∂μ.restrict D, ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) x =
      ∫ y in D, rrk_K Γ φ x y * (f : G → ℂ) y ∂μ := by
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep h
  filter_upwards [rrkb_step1 h hφm hrm hr hR T hφ hT f, hK] with x a1 a2
  rw [a1]
  exact rrkb_step2 h hφm hrm hr f x a2
end Formalism.MainNotions.LeviCoordinates
