-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_tendsto_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:58.437168+00:00
-- url     : https://prove2.me/submissions/2e5b98b1-8545-47e4-89dd-4b48e75c82ef

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_norm_le

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
open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : G → (H →L[ℂ] H)}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : IsCompact k) {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) :
    Tendsto (fun h => π h w) (𝓝 1) (𝓝 w) := by
  have t1 : Tendsto (fun h : G => μ (h • k \ k)) (𝓝 1) (𝓝 0) :=
    tendsto_measure_smul_sdiff_isCompact_isClosed hk hk.isClosed
  have t2 : Tendsto (fun h : G => μ (k \ h • k)) (𝓝 1) (𝓝 0) := by
    have e : ∀ h : G, μ (k \ h • k) = μ (h⁻¹ • k \ k) := fun h => by
      rw [← measure_smul μ h⁻¹ (k \ h • k), Set.smul_set_sdiff, inv_smul_smul]
    simp only [e]
    have ti : Tendsto (fun h : G => h⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact t1.comp ti
  have r1 : Tendsto (fun h : G => μ.real (h • k \ k)) (𝓝 1) (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp t1
  have r2 : Tendsto (fun h : G => μ.real (k \ h • k)) (𝓝 1) (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp t2
  have r : Tendsto (fun h : G => ‖v‖ * (μ.real (h • k \ k) + μ.real (k \ h • k))) (𝓝 1) (𝓝 0) := by
    simpa using (r1.add r2).const_mul ‖v‖
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => rrc_norm_le hmul hone hn hm hk hw h) r
end Formalism.MainNotions.LeviCoordinates
