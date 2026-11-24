-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrka_lint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:08.205424+00:00
-- url     : https://prove2.me/submissions/b00e0dc2-af0c-4a4d-a053-adf122d854aa

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkaMeasKabRight
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_Kab_symm
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_Kab_smul
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_meas_Kab_right
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_isFD


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
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [μ.IsMulLeftInvariant] (h : rr_FD μ Γ D) (hφm : Measurable φ) (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x : G) :
    ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ * rrk_Kab Γ φ y x ∂μ = ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ := by
  rw [(rr_isFD h).lintegral_eq_tsum'']
  have e : ∀ δ : Γ, ∫⁻ y in D, ‖φ (x⁻¹ * (δ • y))‖ₑ * rrk_Kab Γ φ (δ • y) x ∂μ =
      ∫⁻ y in D, ‖φ (x⁻¹ * (δ : G) * y)‖ₑ * rrk_Kab Γ φ x y ∂μ := by
    intro δ
    refine lintegral_congr fun y => ?_
    rw [Subgroup.smul_def, smul_eq_mul, rrka_Kab_smul, rrka_Kab_symm hsa, ← mul_assoc]
  rw [tsum_congr e, ← lintegral_tsum (μ := μ.restrict D)
    (f := fun (δ : Γ) y => ‖φ (x⁻¹ * (δ : G) * y)‖ₑ * rrk_Kab Γ φ x y) (fun δ =>
    ((hφm.comp (measurable_const_mul (x⁻¹ * (δ : G)))).enorm.mul (rrka_meas_Kab_right hφm x)).aemeasurable)]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.tsum_mul_right, sq]
  rfl
end Formalism.MainNotions.LeviCoordinates
